package Gujiconform::Fixture;

use strict;
use warnings;
use Errno qw(ENOENT);

sub load {
    my ($class, $path) = @_;
    my $base = $path;
    $base =~ s/\.guji\z//;
    my $self = bless {
        path => $path,
        base => $base,
        name => _fixture_name($path),
        expected_path => "$base.expected",
        exit_path => "$base.exit",
        args_path => "$base.args",
        stdin_path => "$base.stdin",
        stderr_path => "$base.stderr",
        meta_path => "$base.meta",
        meta => {},
        _contents => {},
        _present => {},
        _errors => [],
    }, $class;
    for my $kind (qw(expected exit args stdin stderr meta)) {
        my $sidecar = $kind eq 'expected' ? $self->{expected_path} : $self->{"${kind}_path"};
        my ($present, $contents, $error) = _read_optional($sidecar);
        $self->{_present}{$kind} = $present;
        $self->{_contents}{$kind} = $contents if $present && !defined $error;
        push @{$self->{_errors}}, $error if defined $error;
    }
    $self->{meta} = $self->_read_meta;
    return $self;
}

sub expectation_error {
    my ($self) = @_;
    return $self->{_errors}[0] if @{$self->{_errors}};
    return $self->{meta}{_error} if $self->{meta}{_error};
    return "xfail metadata requires a nonempty reason in $self->{meta_path}"
        if exists $self->{meta}{xfail} && !length $self->{meta}{xfail};
    my $has_expected = $self->{_present}{expected};
    my $checks_other = $self->{_present}{exit} || $self->{_present}{stderr};
    return "expected file missing: $self->{expected_path}" unless $has_expected || $checks_other;
    if ($self->{_present}{exit}) {
        my $txt = $self->{_contents}{exit};
        $txt =~ s/^\s+|\s+$//g;
        return "malformed exit file: $self->{exit_path}"
            unless $txt =~ /\A\d+\z/ && $txt <= 255;
    }
    return undef;
}

sub expected_stdout {
    my ($self) = @_;
    return '' unless $self->{_present}{expected};
    return $self->{_contents}{expected};
}

sub expected_stderr {
    my ($self) = @_;
    return undef unless $self->{_present}{stderr};
    return $self->{_contents}{stderr};
}

sub expected_exit {
    my ($self) = @_;
    return 0 unless $self->{_present}{exit};
    my $txt = $self->{_contents}{exit};
    $txt =~ s/^\s+|\s+$//g;
    return $txt =~ /\A\d+\z/ && $txt <= 255 ? int($txt) : 0;
}

sub args {
    my ($self) = @_;
    return () unless $self->{_present}{args};
    my $txt = $self->{_contents}{args};
    my @args = split /\n/, $txt, -1;
    pop @args if @args && $args[-1] eq '';
    return @args;
}

sub stdin {
    my ($self) = @_;
    return '' unless $self->{_present}{stdin};
    return $self->{_contents}{stdin};
}

sub _read_meta {
    my ($self) = @_;
    return {} unless $self->{_present}{meta};
    my %meta;
    for my $line (split /\n/, $self->{_contents}{meta}, -1) {
        $line =~ s/\r\z//;
        next if $line =~ /^\s*(?:#.*)?\z/;
        if ($line =~ /^\s*([A-Za-z_][A-Za-z0-9_-]*)\s*:\s*(.*?)\s*\z/) {
            if (exists $meta{$1}) {
                $meta{_error} = "duplicate meta key '$1' in $self->{meta_path}";
            } else {
                $meta{$1} = $2;
            }
        } else {
            $meta{_error} = "malformed meta line in $self->{meta_path}: $line";
        }
    }
    return \%meta;
}

sub _fixture_name {
    my ($path) = @_;
    $path =~ s/\.guji\z//;
    $path =~ s{^\./}{};
    $path =~ s{^fixtures/}{};
    return $path;
}

sub _read_optional {
    my ($path) = @_;
    if (!lstat $path) {
        return (0, undef, undef) if $! == ENOENT;
        return (0, undef, "cannot inspect $path: $!");
    }
    return (1, undef, "fixture sidecar must not be a symbolic link: $path") if -l _;
    return (1, undef, "fixture sidecar is not a regular file: $path") unless -f _;

    open my $fh, '<:raw', $path or return (1, undef, "cannot read $path: $!");
    my $txt = '';
    while (1) {
        my $read = read $fh, my $chunk, 65536;
        if (!defined $read) {
            my $error = $!;
            close $fh;
            return (1, undef, "cannot read $path: $error");
        }
        last if $read == 0;
        $txt .= $chunk;
    }
    close $fh or return (1, undef, "cannot close $path after reading: $!");
    return (1, $txt, undef);
}

1;
