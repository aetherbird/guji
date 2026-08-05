#!/usr/bin/env perl
use strict;
use warnings;

my @args = @ARGV;
if (@args && $args[0] eq 'repl') {
    local $/;
    my $txt = <STDIN>;
    print "REPL:$txt";
    exit 0;
}
if (@args && $args[0] eq 'sleep') {
    sleep 20;
    exit 0;
}
my $src = $args[0] or exit 2;
open my $fh, '<', $src or die $!;
local $/;
my $txt = <$fh>;
print STDERR "$1\n" if $txt =~ /STDERR:(.*)/;
exit $1 if $txt =~ /EXIT:(-?\d+)/;
print "$1\n" if $txt =~ /PRINT:(.*)/;
exit 0;
