#!/usr/bin/env perl
use strict;
use warnings;
use FindBin;
use lib "$FindBin::Bin/../lib";

use File::Spec;
use File::Temp qw(tempdir);
use Test::More;
use Time::HiRes qw(sleep);

use Gujiconform::Runner;

my $runner = Gujiconform::Runner->new({ timeout => 3 });
my $input = 'i' x 262144;
my $duplex = $runner->_capture([
    $^X, '-e',
    '$|=1; binmode STDIN; binmode STDOUT; print "o" x 262144; '
        . 'local $/; my $input = <STDIN>; print length($input), "\n";',
], $input);
is($duplex->{error}, undef, 'full-duplex capture does not report an error');
is($duplex->{exit}, 0, 'full-duplex child exits zero');
is(length($duplex->{stdout}), 262151, 'full-duplex capture drains output while feeding stdin');
is(substr($duplex->{stdout}, -7), "262144\n", 'full-duplex child received all stdin bytes');
ok(!$duplex->{timed_out}, 'full-duplex capture does not time out');

my $closed_stdin = $runner->_capture([$^X, '-e', 'exit 0'], 'x' x 262144);
is($closed_stdin->{error}, undef, 'early child stdin close is handled without SIGPIPE failure');
is($closed_stdin->{exit}, 0, 'child that ignores stdin keeps its exit status');

my $raw = $runner->_capture([
    $^X, '-e', 'binmode STDOUT; print pack("C*", 0, 255, 10);',
], '');
is($raw->{stdout}, pack('C*', 0, 255, 10), 'capture preserves raw output bytes');

my $bounded_runner = Gujiconform::Runner->new({ timeout => 3, _capture_limit => 1024 });
my $bounded = $bounded_runner->_capture([
    $^X, '-e', 'binmode STDOUT; print "z" x 2048;',
], '');
is($bounded->{exit}, 125, 'capture limit uses a distinct synthetic exit code');
is($bounded->{output_limited}, 'stdout', 'capture limit identifies the overflowing stream');
is(length($bounded->{stdout}), 1024, 'capture limit bounds retained output bytes');

my $missing = $runner->_capture(['/definitely/missing/gujiconform-command'], '');
like($missing->{error}, qr/^cannot run .*No such file or directory/, 'exec failure is a runner error');

my $dir = tempdir('gujiconform-runner-XXXXXX', TMPDIR => 1, CLEANUP => 1);
my $marker = File::Spec->catfile($dir, 'escaped-descendant');
my $timeout_runner = Gujiconform::Runner->new({ timeout => 0.2 });
my $timed = $timeout_runner->_capture([
    $^X, '-e',
    'my $marker = shift; my $pid = fork; die $! unless defined $pid; '
        . 'if (!$pid) { $SIG{TERM} = "IGNORE"; select undef, undef, undef, 0.7; '
        . 'open my $fh, ">", $marker or die $!; print {$fh} "escaped\n"; exit 0; } '
        . '$SIG{TERM} = "IGNORE"; waitpid($pid, 0);',
    $marker,
], '');
is($timed->{exit}, 124, 'timeout uses the documented synthetic exit code');
ok($timed->{timed_out}, 'timeout result is explicitly marked');
sleep 0.8;
ok(!-e $marker, 'timeout terminates descendants in the child process group');

done_testing();
