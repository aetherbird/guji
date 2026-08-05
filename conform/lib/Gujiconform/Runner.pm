package Gujiconform::Runner;

use strict;
use warnings;
use Errno qw(EAGAIN EWOULDBLOCK EINTR EPIPE);
use Fcntl qw(F_GETFL F_SETFL F_SETFD FD_CLOEXEC O_NONBLOCK);
use File::Spec;
use File::Temp qw(tempdir);
use IO::Select;
use POSIX ();
use Text::ParseWords qw(parse_line);
use Time::HiRes qw(time sleep);

use constant MAX_CAPTURE_BYTES => 16 * 1024 * 1024;

sub new {
    my ($class, $config) = @_;
    return bless { config => $config }, $class;
}

sub validate {
    my ($self) = @_;
    my $engine = $self->{config}{engine};
    my $guji = $self->{config}{guji};
    my $compiler = $self->{config}{compiler};
    my $native_cmd = $self->{config}{native_cmd};
    my $needs_native = $engine eq 'native' || $engine eq 'both';
    my $needs_interp = $engine eq 'interp' || $engine eq 'both';
    my $uses_canonical_compiler = $needs_native
        && !(defined $native_cmd && length $native_cmd)
        && defined $compiler && length $compiler;
    return 'native engine requires --compiler (or $GUJI2C) and --runtime '
        . '(or $GUJI_RUNTIME); use --native-cmd for a custom native runner'
        if $needs_native
            && !(defined $native_cmd && length $native_cmd)
            && !$uses_canonical_compiler;
    my $needs_guji = $needs_interp
        || ($needs_native && defined $native_cmd && $native_cmd =~ /\{guji\}/);
    if ($needs_guji) {
        my $guji_err = _executable_error($guji, 'guji interpreter');
        return $guji_err if $guji_err;
    }
    if ($uses_canonical_compiler) {
        my $compiler_err = _executable_error($compiler, 'guji compiler');
        return $compiler_err if $compiler_err;
        my $runtime = $self->{config}{runtime};
        return 'canonical runtime is required with --compiler; set --runtime or $GUJI_RUNTIME'
            unless defined $runtime && length $runtime;
        return "missing canonical runtime: $runtime" unless -f $runtime && -r $runtime;
    }
    return undef;
}

sub _executable_error {
    my ($program, $label) = @_;
    return "missing $label" unless defined $program && length $program;
    return undef if $program =~ m{/} && -f $program && -x $program;
    for my $dir (split /:/, $ENV{PATH} || '', -1) {
        $dir = File::Spec->curdir unless length $dir;
        my $candidate = File::Spec->catfile($dir, $program);
        return undef if -f $candidate && -x $candidate;
    }
    return "missing $label: $program";
}

sub run_fixture {
    my ($self, $fixture, $engine) = @_;
    return $engine eq 'native'
        ? $self->_run_native($fixture)
        : $self->_run_template(
            $fixture->{meta}{interp_cmd} || $self->{config}{interp_cmd},
            $fixture,
            undef,
        );
}

sub _run_native {
    my ($self, $fixture) = @_;
    if (defined $self->{config}{native_cmd} && length $self->{config}{native_cmd}) {
        return $self->_run_template($self->{config}{native_cmd}, $fixture, undef);
    }
    my $dir = tempdir('gujiconform-XXXXXX', TMPDIR => 1, CLEANUP => 1);
    my $exe = File::Spec->catfile($dir, 'program');
    my $compiler = $self->{config}{compiler};
    my $build = $self->_capture(
        [$compiler, $fixture->{path}, $exe, $self->{config}{runtime}], '');
    return $build if $build->{error};
    if ($build->{exit} != 0) {
        return $build;
    }
    return $self->_capture([$exe, $fixture->args], $fixture->stdin);
}

sub _run_template {
    my ($self, $template, $fixture, $exe) = @_;
    my @cmd = $self->_expand_template($template, $fixture, $exe);
    return $self->_capture(\@cmd, $fixture->stdin);
}

sub _expand_template {
    my ($self, $template, $fixture, $exe) = @_;
    my @words = parse_line(qr/\s+/, 0, $template);
    my @args = $fixture->args;
    my @cmd;
    my $guji = $self->{config}{guji};
    my $file = $fixture->{path};
    my $executable = defined $exe ? $exe : '';
    for my $word (@words) {
        if ($word eq '{args}') {
            push @cmd, @args;
            next;
        }
        $word =~ s/\{guji\}/$guji/g;
        $word =~ s/\{file\}/$file/g;
        $word =~ s/\{exe\}/$executable/g;
        push @cmd, $word;
    }
    return @cmd;
}

sub _capture {
    my ($self, $cmd, $stdin) = @_;
    return { error => 'cannot run an empty command' }
        unless @$cmd && defined $cmd->[0] && length $cmd->[0];

    my ($pid, $in, $out, $err, $spawn_error) = _spawn($cmd);
    if (defined $spawn_error) {
        return { error => 'cannot run ' . _format_command($cmd) . ": $spawn_error" };
    }

    for my $fh ($in, $out, $err) {
        binmode $fh, ':raw';
        my $flags = fcntl($fh, F_GETFL, 0);
        if (!defined $flags || !fcntl($fh, F_SETFL, $flags | O_NONBLOCK)) {
            my $error = $!;
            _terminate_group($pid);
            close $in;
            close $out;
            close $err;
            _wait_for_pid($pid);
            return { error => "cannot configure process pipes: $error" };
        }
    }

    my $readers = IO::Select->new($out, $err);
    my $writers = IO::Select->new;
    my %buf = (stdout => '', stderr => '');
    my %name = (fileno($out) => 'stdout', fileno($err) => 'stderr');
    my $input = defined $stdin ? $stdin : '';
    my $input_offset = 0;
    if (length $input) {
        $writers->add($in);
    } else {
        close $in;
    }

    my $deadline = time + $self->{config}{timeout};
    my $capture_limit = MAX_CAPTURE_BYTES;
    if (defined $self->{config}{_capture_limit}
        && $self->{config}{_capture_limit} =~ /\A\d+\z/
        && $self->{config}{_capture_limit} > 0
        && $self->{config}{_capture_limit} < $capture_limit) {
        $capture_limit = $self->{config}{_capture_limit};
    }
    my $timed_out = 0;
    my $output_limited;
    my $capture_error;
    local $SIG{PIPE} = 'IGNORE';
    while ($readers->count || $writers->count) {
        my $remaining = $deadline - time;
        if ($remaining <= 0) {
            _terminate_group($pid);
            $timed_out = 1;
            last;
        }
        my $wait = $remaining < 0.1 ? $remaining : 0.1;
        my @ready = IO::Select->select($readers, $writers, undef, $wait);
        next unless @ready;
        my ($readable, $writable) = @ready;
        for my $fh (@$readable) {
            my $stream = $name{fileno($fh)};
            my $chunk = '';
            my $read = sysread($fh, $chunk, 8192);
            if (defined $read && $read > 0) {
                my $available = $capture_limit - length $buf{$stream};
                if ($read > $available) {
                    $buf{$stream} .= substr($chunk, 0, $available) if $available > 0;
                    $output_limited = $stream;
                    _terminate_group($pid);
                    last;
                }
                $buf{$stream} .= $chunk;
            } elsif (!defined $read && ($! == EAGAIN || $! == EWOULDBLOCK || $! == EINTR)) {
                next;
            } else {
                if (!defined $read) {
                    $capture_error = "cannot read process $stream: $!";
                    _terminate_group($pid);
                }
                $readers->remove($fh);
                close $fh;
            }
        }
        last if defined $capture_error || defined $output_limited;
        for my $fh (@$writable) {
            my $written = syswrite($fh, $input, length($input) - $input_offset, $input_offset);
            if (defined $written && $written > 0) {
                $input_offset += $written;
                if ($input_offset == length $input) {
                    $writers->remove($fh);
                    close $fh;
                }
            } elsif (!defined $written && ($! == EAGAIN || $! == EWOULDBLOCK || $! == EINTR)) {
                next;
            } elsif (!defined $written && $! == EPIPE) {
                $writers->remove($fh);
                close $fh;
            } else {
                $capture_error = 'cannot write process stdin: ' . (defined $written ? 'short write' : $!);
                _terminate_group($pid);
                last;
            }
        }
    }

    for my $fh ($in, $out, $err) {
        close $fh if defined fileno($fh);
    }
    my $status = _wait_for_pid($pid);
    return { error => $capture_error } if defined $capture_error;
    my $exit = $timed_out ? 124
        : defined $output_limited ? 125
        : ($status == -1 ? 127 : ($status & 127 ? 128 + ($status & 127) : ($status >> 8)));
    $buf{stderr} .= "timeout after $self->{config}{timeout}s\n" if $timed_out;
    $buf{stderr} .= "capture limit exceeded on $output_limited\n" if defined $output_limited;
    return {
        stdout => $buf{stdout}, stderr => $buf{stderr}, exit => $exit,
        timed_out => $timed_out, timeout => $self->{config}{timeout},
        output_limited => $output_limited, capture_limit => $capture_limit,
    };
}

sub _spawn {
    my ($cmd) = @_;
    my ($child_stdin, $parent_stdin, $parent_stdout, $child_stdout);
    my ($parent_stderr, $child_stderr, $exec_reader, $exec_writer);
    for my $pair (
        [\$child_stdin, \$parent_stdin],
        [\$parent_stdout, \$child_stdout],
        [\$parent_stderr, \$child_stderr],
        [\$exec_reader, \$exec_writer],
    ) {
        if (!pipe ${$pair->[0]}, ${$pair->[1]}) {
            my $error = $!;
            for my $fh ($child_stdin, $parent_stdin, $parent_stdout, $child_stdout,
                        $parent_stderr, $child_stderr, $exec_reader, $exec_writer) {
                close $fh if defined $fh;
            }
            return (undef, undef, undef, undef, "cannot create process pipe: $error");
        }
    }
    if (!fcntl($exec_writer, F_SETFD, FD_CLOEXEC)) {
        my $error = $!;
        close $_ for ($child_stdin, $parent_stdin, $parent_stdout, $child_stdout,
                     $parent_stderr, $child_stderr, $exec_reader, $exec_writer);
        return (undef, undef, undef, undef, "cannot protect process pipe: $error");
    }

    my $pid = fork;
    if (!defined $pid) {
        my $error = $!;
        close $_ for ($child_stdin, $parent_stdin, $parent_stdout, $child_stdout,
                     $parent_stderr, $child_stderr, $exec_reader, $exec_writer);
        return (undef, undef, undef, undef, "cannot fork: $error");
    }
    if ($pid == 0) {
        close $parent_stdin;
        close $parent_stdout;
        close $parent_stderr;
        close $exec_reader;
        my $group_result = POSIX::setpgid(0, 0);
        _child_spawn_error($exec_writer, "cannot create process group: $!")
            unless defined $group_result && $group_result == 0;
        for my $dup ([$child_stdin, 0], [$child_stdout, 1], [$child_stderr, 2]) {
            my $result = POSIX::dup2(fileno($dup->[0]), $dup->[1]);
            _child_spawn_error($exec_writer, "cannot connect process pipe: $!")
                unless defined $result;
        }
        close $child_stdin;
        close $child_stdout;
        close $child_stderr;
        exec { $cmd->[0] } @$cmd or _child_spawn_error($exec_writer, "$!");
    }

    close $child_stdin;
    close $child_stdout;
    close $child_stderr;
    close $exec_writer;
    my $exec_error = '';
    while (1) {
        my $read = read $exec_reader, my $chunk, 4096;
        if (!defined $read) {
            next if $! == EINTR;
            $exec_error = "cannot read process status: $!";
            last;
        }
        last if $read == 0;
        $exec_error .= $chunk;
    }
    close $exec_reader;
    if (length $exec_error) {
        close $parent_stdin;
        close $parent_stdout;
        close $parent_stderr;
        _wait_for_pid($pid);
        return (undef, undef, undef, undef, $exec_error);
    }
    return ($pid, $parent_stdin, $parent_stdout, $parent_stderr, undef);
}

sub _child_spawn_error {
    my ($fh, $message) = @_;
    syswrite($fh, $message);
    POSIX::_exit(127);
}

sub _terminate_group {
    my ($pid) = @_;
    kill 'TERM', -$pid;
    sleep 0.1;
    kill 'KILL', -$pid;
}

sub _wait_for_pid {
    my ($pid) = @_;
    while (1) {
        my $waited = waitpid($pid, 0);
        return $? if $waited == $pid;
        return -1 if $waited == -1 && $! != EINTR;
    }
}

sub _format_command {
    my ($cmd) = @_;
    return join ' ', map {
        my $word = defined $_ ? $_ : '';
        $word =~ s/([\\\r\n\t])/sprintf('\\x{%02X}', ord($1))/ge;
        length($word) ? $word : "''";
    } @$cmd;
}

1;
