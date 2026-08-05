#!/usr/bin/env perl
use strict;
use warnings;
use B qw(perlstring);

my ($src, $out, $runtime) = @ARGV;
exit 2 unless defined $src && defined $out && defined $runtime && -f $runtime;

open my $source_fh, '<', $src or die "read $src: $!";
local $/;
my $source = <$source_fh>;
close $source_fh;
sleep 20 if defined $source && $source =~ /COMPILE_SLEEP/;

open my $fh, '>', $out or die "write $out: $!";
print {$fh} "#!/usr/bin/env perl\n";
print {$fh} "use strict; use warnings;\n";
print {$fh} 'my $src = ' . perlstring($src) . ";\n";
print {$fh} "open my \$fh, '<', \$src or die \$!; local \$/; my \$txt = <\$fh>;\n";
print {$fh} "if (\$txt =~ /STDERR:(.*)/) { print STDERR \"\$1\\n\"; }\n";
print {$fh} "if (\$txt =~ /EXIT:(-?\\d+)/) { exit \$1; }\n";
print {$fh} "if (\$txt =~ /PRINT:(.*)/) { print \"\$1\\n\"; }\n";
print {$fh} "exit 0;\n";
close $fh;
chmod 0755, $out;
exit 0;
