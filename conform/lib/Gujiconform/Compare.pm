package Gujiconform::Compare;

use strict;
use warnings;

sub compare {
    my ($class, $fixture, $actual, $normalizers) = @_;
    my @diffs;
    my $ok = 1;

    if ($actual->{timed_out}) {
        $ok = 0;
        my $seconds = defined $actual->{timeout} ? $actual->{timeout} : 'configured';
        push @diffs, "timeout: process exceeded ${seconds}s\n";
    }
    if ($actual->{output_limited}) {
        $ok = 0;
        my $limit = defined $actual->{capture_limit} ? $actual->{capture_limit} : 16 * 1024 * 1024;
        push @diffs, "capture limit: $actual->{output_limited} exceeded $limit bytes\n";
    }

    my $want_out = _normalize($fixture->expected_stdout, $normalizers);
    my $got_out = _normalize($actual->{stdout}, $normalizers);
    if ($want_out ne $got_out) {
        $ok = 0;
        push @diffs, _diff('stdout', $want_out, $got_out);
    }

    my $want_err = $fixture->expected_stderr;
    if (defined $want_err) {
        $want_err = _normalize($want_err, $normalizers);
        my $got_err = _normalize($actual->{stderr}, $normalizers);
        if ($want_err ne $got_err) {
            $ok = 0;
            push @diffs, _diff('stderr', $want_err, $got_err);
        }
    }

    my $want_exit = $fixture->expected_exit;
    if ($want_exit != $actual->{exit}) {
        $ok = 0;
        push @diffs, "exit: expected $want_exit, actual $actual->{exit}\n";
    }

    return { ok => $ok, diffs => \@diffs, message => $ok ? '' : 'output mismatch' };
}

sub _normalize {
    my ($text, $normalizers) = @_;
    for my $name (@$normalizers) {
        if ($name eq 'trailing-newline') {
            $text =~ s/\n\z//;
        } elsif ($name eq 'trailing-ws') {
            $text =~ s/[ \t]+\n/\n/g;
            $text =~ s/[ \t]+\z//;
        } elsif ($name eq 'crlf') {
            $text =~ s/\r\n/\n/g;
        }
    }
    return $text;
}

sub _diff {
    my ($label, $want, $got) = @_;
    my @want = split /^/m, $want;
    my @got = split /^/m, $got;
    my $out = "--- expected $label\n+++ actual $label\n";
    my $max = @want > @got ? scalar @want : scalar @got;
    for my $i (0 .. $max - 1) {
        my $w = $i < @want ? $want[$i] : undef;
        my $g = $i < @got ? $got[$i] : undef;
        next if defined $w && defined $g && $w eq $g;
        $out .= '@@ line ' . ($i + 1) . " @@\n";
        $out .= '-' . _show($w) if defined $w;
        $out .= '+' . _show($g) if defined $g;
    }
    return $out;
}

sub _show {
    my ($s) = @_;
    $s = '' unless defined $s;
    $s =~ s/([\x00-\x09\x0b-\x1f\x7f])/sprintf('\\x{%02X}', ord($1))/ge;
    return $s =~ /\n\z/ ? $s : "$s\n";
}

1;
