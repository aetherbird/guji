package Gujiconform::Reporter;

use strict;
use warnings;

sub new {
    my ($class, $config) = @_;
    return bless { config => $config, tap_index => 0 }, $class;
}

sub result {
    my ($self, $result) = @_;
    return if $self->{config}{format} eq 'plain'
        && $self->{config}{quiet}
        && $result->{status} =~ /^(?:pass|xfail)\z/;
    if ($self->{config}{format} eq 'tap') {
        $self->_tap_result($result);
    } else {
        $self->_plain_result($result);
    }
}

sub summary {
    my ($self, $results) = @_;
    my %count = map { $_ => 0 } qw(pass fail xfail xpass error);
    $count{$_->{status}}++ for @$results;
    if ($self->{config}{format} eq 'tap') {
        print '1..' . scalar(@$results) . "\n";
    }
    my $fixtures = scalar @$results;
    my $summary = "$fixtures checks: $count{pass} pass, $count{fail} fail, $count{xfail} xfail, $count{xpass} xpass, $count{error} error";
    $summary .= "  (engine: $self->{config}{engine})";
    print $self->{config}{format} eq 'tap' ? "# $summary\n" : "$summary\n";
}

sub _plain_result {
    my ($self, $r) = @_;
    printf "%-5s %s        (%s)", uc($r->{status}), _display($r->{fixture}), _display($r->{engine});
    print '  ' . _display($r->{xfail}) if $r->{xfail};
    print '  ' . _display($r->{message}) if $r->{message} && $r->{status} eq 'error';
    print "\n";
    if ($r->{diffs}) {
        for my $diff (@{$r->{diffs}}) {
            $diff =~ s/^/      /mg;
            print $diff;
        }
    }
}

sub _tap_result {
    my ($self, $r) = @_;
    my $n = ++$self->{tap_index};
    my $ok = $r->{status} =~ /^(?:pass|xfail)\z/;
    print($ok ? "ok $n" : "not ok $n");
    print ' - ' . _tap_description($r->{fixture}) . ' (' . _tap_description($r->{engine}) . ')';
    print ' # TODO ' . _display($r->{xfail}) if $r->{status} =~ /^(?:xfail|xpass)\z/;
    print "\n";
    if ($r->{message} && $r->{status} eq 'error') {
        print '# error: ' . _display($r->{message}) . "\n";
    }
    if ($r->{diffs}) {
        for my $diff (@{$r->{diffs}}) {
            $diff =~ s/^/# /mg;
            print $diff;
        }
    }
}

sub _display {
    my ($text) = @_;
    return '' unless defined $text;
    $text =~ s/\\/\\\\/g;
    $text =~ s/\r/\\r/g;
    $text =~ s/\n/\\n/g;
    $text =~ s/\t/\\t/g;
    $text =~ s/([\x00-\x08\x0b\x0c\x0e-\x1f\x7f])/sprintf('\\x{%02X}', ord($1))/ge;
    return $text;
}

sub _tap_description {
    my ($text) = @_;
    $text = _display($text);
    $text =~ s/#/\\x{23}/g;
    return $text;
}

1;
