package Gujiconform::Config;

use strict;
use warnings;
use Getopt::Long ();
use Text::ParseWords qw(parse_line);

sub from_argv {
    my ($class, @argv) = @_;
    my %config = (
        engine => 'native',
        guji => $ENV{GUJI} || 'guji',
        compiler => $ENV{GUJI2C},
        runtime => $ENV{GUJI_RUNTIME},
        native_cmd => undef,
        interp_cmd => '{guji} {file} {args}',
        format => 'plain',
        normalize => '',
        select => [],
        timeout => 30,
        jobs => 1,
        quiet => 0,
        xpass_is_failure => 0,
    );
    my @select;
    my $option_error = '';
    my $ok;
    {
        local $SIG{__WARN__} = sub { $option_error .= join '', @_ };
        my $parser = Getopt::Long::Parser->new(
            config => [qw(no_auto_abbrev no_ignore_case no_bundling no_getopt_compat permute)]);
        $ok = $parser->getoptionsfromarray(
            \@argv,
            'engine=s' => \$config{engine},
            'guji=s' => \$config{guji},
            'compiler=s' => \$config{compiler},
            'runtime=s' => \$config{runtime},
            'native-cmd=s' => \$config{native_cmd},
            'interp-cmd=s' => \$config{interp_cmd},
            'format=s' => \$config{format},
            'normalize=s' => \$config{normalize},
            'select=s' => \@select,
            'xpass-is-failure' => \$config{xpass_is_failure},
            'timeout=i' => \$config{timeout},
            'jobs=i' => \$config{jobs},
            'quiet|q' => \$config{quiet},
            'version' => \$config{version},
            'help' => \$config{help},
        );
    }
    if (!$ok) {
        $option_error =~ s/\s+\z//;
        return (undef, usage_error(length $option_error ? $option_error : 'bad option'));
    }
    $config{select} = \@select;
    $config{paths} = @argv ? \@argv : ['fixtures'];
    return (\%config, undef) if $config{help} || $config{version};
    return (undef, usage_error('--select must not be empty'))
        if grep { !defined $_ || !length $_ } @select;
    return (undef, usage_error('engine must be native, interp, or both'))
        unless $config{engine} =~ /\A(?:native|interp|both)\z/;
    return (undef, usage_error('format must be plain or tap'))
        unless $config{format} =~ /\A(?:plain|tap)\z/;
    return (undef, usage_error('jobs must be at least 1')) if $config{jobs} < 1;
    return (undef, usage_error('parallel jobs are not implemented in this harness slice')) if $config{jobs} != 1;
    return (undef, usage_error('timeout must be at least 1')) if $config{timeout} < 1;
    if (my $normalizer_err = normalizer_error($config{normalize}, '--normalize')) {
        return (undef, usage_error($normalizer_err));
    }
    for my $entry (
        ['--interp-cmd', $config{interp_cmd}],
        ['--native-cmd', $config{native_cmd}],
    ) {
        next unless defined $entry->[1];
        if (my $template_err = template_error($entry->[1], $entry->[0])) {
            return (undef, usage_error($template_err));
        }
    }
    return (\%config, undef);
}

sub normalizers {
    my ($global, $fixture) = @_;
    my @items;
    for my $list ($global, $fixture) {
        next unless defined $list && length $list;
        for my $item (split /,/, $list) {
            $item =~ s/^\s+|\s+$//g;
            push @items, $item;
        }
    }
    my %seen;
    return grep { length && !$seen{$_}++ } @items;
}

sub normalizer_error {
    my ($list, $label) = @_;
    return undef unless defined $list && length $list;
    my %allowed = map { $_ => 1 } qw(trailing-newline trailing-ws crlf);
    for my $item (split /,/, $list, -1) {
        $item =~ s/^\s+|\s+$//g;
        return "$label contains an empty normalizer" unless length $item;
        return "$label contains unknown normalizer '$item'"
            unless $allowed{$item};
    }
    return undef;
}

sub template_error {
    my ($template, $label) = @_;
    return "$label must not be empty" unless defined $template && length $template;
    my $count = parse_line(qr/\s+/, 0, $template);
    return "$label contains malformed shell-style quoting" unless defined $count;
    return "$label must name a command" unless $count;
    my @words = parse_line(qr/\s+/, 0, $template);
    return "$label must name a nonempty command" unless defined $words[0] && length $words[0];
    return undef;
}

sub usage_error {
    my ($msg) = @_;
    return "$msg\n\n" . usage();
}

sub usage {
    return <<'USAGE';
gujiconform [options] [path ...]

Paths are fixture files or directories recursed for *.guji. Default: ./fixtures.

  --engine native|interp|both   Engine(s) to run (default: native)
  --guji PATH                   Path to guji (default: $GUJI or guji)
  --compiler PATH               Canonical guji2c (default: $GUJI2C; required for native)
  --runtime PATH                Runtime prologue (default: $GUJI_RUNTIME; required for native)
  --native-cmd TEMPLATE         Override the compiler + execute native path
  --interp-cmd TEMPLATE         Interpreter template (default: {guji} {file} {args})
  --format plain|tap            Output format (default: plain)
  --normalize LIST              trailing-newline,trailing-ws,crlf
  --select GLOB                 Only run fixtures matching glob (repeatable)
  --xpass-is-failure            Treat xpass as exit 1 instead of exit 3
  --timeout SECS                Per-process timeout (default: 30)
  --jobs N                      Reserved; currently must be 1
  --quiet, -q                   Plain output: summary + failures only
  --version
  --help
USAGE
}

1;
