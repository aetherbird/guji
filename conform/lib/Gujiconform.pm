package Gujiconform;

use 5.016;
use strict;
use warnings;
use File::Find qw(find);
use File::Spec;

use Gujiconform::Compare;
use Gujiconform::Config;
use Gujiconform::Fixture;
use Gujiconform::Reporter;
use Gujiconform::Runner;

our $VERSION = '0.1';

sub new {
    my ($class) = @_;
    return bless {}, $class;
}

sub run {
    my ($self, @argv) = @_;
    my ($config, $config_err) = Gujiconform::Config->from_argv(@argv);
    if ($config_err) {
        print STDERR "$config_err\n";
        return 2;
    }
    if ($config->{help}) {
        print Gujiconform::Config::usage();
        return 0;
    }
    if ($config->{version}) {
        print "gujiconform $VERSION\n";
        return 0;
    }

    my $runner = Gujiconform::Runner->new($config);
    my $binary_err = $runner->validate;
    if ($binary_err) {
        print STDERR "$binary_err\n";
        return 2;
    }

    my ($fixture_paths, $discovery_errors) = _discover($config->{paths}, $config->{select});
    my $reporter = Gujiconform::Reporter->new($config);
    my @results;
    for my $discovery_error (@$discovery_errors) {
        my $result = _classified({
            fixture => $discovery_error->{path}, engine => 'meta', status => 'error',
            message => $discovery_error->{message}, xfail => undef,
        });
        push @results, $result;
        $reporter->result($result);
    }
    for my $path (@$fixture_paths) {
        my $fixture = eval { Gujiconform::Fixture->load($path) };
        if (!$fixture) {
            my $error = $@ || 'unknown fixture loading error';
            $error =~ s/\s+\z//;
            my $result = _classified({
                fixture => $path, engine => 'meta', status => 'error',
                message => "cannot load fixture: $error", xfail => undef,
            });
            push @results, $result;
            $reporter->result($result);
            next;
        }
        my ($engines, $engine_err) = _engines_for($config->{engine}, $fixture->{meta}{engines});
        if ($engine_err) {
            my $result = _classified({
                fixture => $fixture->{name}, engine => 'meta', status => 'error',
                message => $engine_err, xfail => $fixture->{meta}{xfail},
            });
            push @results, $result;
            $reporter->result($result);
            next;
        }
        for my $engine (@$engines) {
            my $result = _run_one($fixture, $engine, $config, $runner);
            push @results, $result;
            $reporter->result($result);
        }
    }
    $reporter->summary(\@results);
    return _exit_code(\@results, $config);
}

sub _run_one {
    my ($fixture, $engine, $config, $runner) = @_;
    my $base = $fixture->{name};
    my $xfail = $fixture->{meta}{xfail};

    my $expect_err = $fixture->expectation_error;
    if ($expect_err) {
        return _classified({
            fixture => $base, engine => $engine, status => 'error',
            message => $expect_err, xfail => $xfail,
        });
    }

    my $normalizer_err = Gujiconform::Config::normalizer_error(
        $fixture->{meta}{normalize}, 'normalize metadata');
    if ($normalizer_err) {
        return _classified({
            fixture => $base, engine => $engine, status => 'error',
            message => $normalizer_err, xfail => $xfail,
        });
    }
    if ($engine eq 'interp' && exists $fixture->{meta}{interp_cmd}) {
        my $template_err = Gujiconform::Config::template_error(
            $fixture->{meta}{interp_cmd}, 'interp_cmd metadata');
        if ($template_err) {
            return _classified({
                fixture => $base, engine => $engine, status => 'error',
                message => $template_err, xfail => $xfail,
            });
        }
    }

    my $actual = $runner->run_fixture($fixture, $engine);
    if ($actual->{error}) {
        return _classified({
            fixture => $base, engine => $engine, status => 'error',
            message => $actual->{error}, xfail => $xfail,
        });
    }

    my @normalizers = Gujiconform::Config::normalizers($config->{normalize}, $fixture->{meta}{normalize});
    my $cmp = Gujiconform::Compare->compare($fixture, $actual, \@normalizers);
    return _classified({
        fixture => $base, engine => $engine, status => ($cmp->{ok} ? 'pass' : 'fail'),
        message => $cmp->{message}, diffs => $cmp->{diffs}, xfail => $xfail,
    });
}

sub _classified {
    my ($result) = @_;
    if ($result->{xfail}) {
        if ($result->{status} eq 'pass') {
            $result->{status} = 'xpass';
        } elsif ($result->{status} eq 'fail') {
            $result->{status} = 'xfail';
        }
    }
    return $result;
}

sub _engines_for {
    my ($selected, $meta_engines) = @_;
    my @selected = $selected eq 'both' ? qw(native interp) : ($selected);
    return (\@selected, undef) unless defined $meta_engines;
    my %allowed;
    for my $engine (split /,/, $meta_engines, -1) {
        $engine =~ s/^\s+|\s+$//g;
        return (undef, 'engines metadata contains an empty engine') unless length $engine;
        if ($engine eq 'both') {
            $allowed{native} = 1;
            $allowed{interp} = 1;
        } elsif ($engine eq 'native' || $engine eq 'interp') {
            $allowed{$engine} = 1;
        } else {
            return (undef, "invalid engines metadata '$engine' (expected native, interp, or both)");
        }
    }
    my @engines = grep { $allowed{$_} } @selected;
    return (undef, "engines metadata selects no engines for --engine $selected")
        unless @engines;
    return (\@engines, undef);
}

sub _discover {
    my ($paths, $selects) = @_;
    my @found;
    my @errors;
    for my $path (@$paths) {
        if (-f $path && $path =~ /\.guji\z/) {
            push @found, $path;
        } elsif (-d $path) {
            my $ok = eval {
                find({
                    wanted => sub {
                        my $candidate = $File::Find::name;
                        return unless $candidate =~ /\.guji\z/;
                        push @found, $candidate if -f $candidate;
                    },
                    no_chdir => 1,
                }, $path);
                1;
            };
            if (!$ok) {
                my $error = $@ || 'unknown discovery error';
                $error =~ s/\s+\z//;
                push @errors, { path => $path, message => "cannot discover fixtures below $path: $error" };
            }
        } elsif (-e $path) {
            push @errors, { path => $path, message => "fixture path is not a .guji file or directory: $path" };
        } else {
            push @errors, { path => $path, message => "fixture path does not exist: $path" };
        }
    }
    @found = sort @found;
    if (@$selects) {
        @found = grep {
            my $path = $_;
            my $ok = 0;
            for my $glob (@$selects) {
                $ok ||= _glob_match($glob, $path);
            }
            $ok;
        } @found;
    }
    my %seen;
    @found = grep {
        my $identity = File::Spec->canonpath(File::Spec->rel2abs($_));
        !$seen{$identity}++;
    } @found;
    return (\@found, \@errors);
}

sub _glob_match {
    my ($glob, $path) = @_;
    my $re = quotemeta($glob);
    $re =~ s/\\\*/.*/g;
    $re =~ s/\\\?/./g;
    return $path =~ /\A$re\z/ || $path =~ /$re/;
}

sub _exit_code {
    my ($results, $config) = @_;
    my %count;
    $count{$_->{status}}++ for @$results;
    return 2 if $count{error};
    return 1 if $count{fail};
    if ($count{xpass}) {
        return $config->{xpass_is_failure} ? 1 : 3;
    }
    return 0;
}

1;
