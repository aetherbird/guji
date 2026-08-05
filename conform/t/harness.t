#!/usr/bin/env perl
use strict;
use warnings;
use File::Path qw(make_path);
use File::Spec;
use File::Temp qw(tempdir tempfile);
use Test::More;

my $root = File::Spec->rel2abs(File::Spec->catdir(File::Spec->curdir, 'conform'));
my $bin = File::Spec->catfile($root, 'gujiconform');
my $fake = File::Spec->catfile($root, 't', 'fake_guji.pl');
my $fake_compiler = File::Spec->catfile($root, 't', 'fake_guji2c.pl');

sub fixture_dir {
    my $dir = tempdir('gujiconform-test-XXXXXX', TMPDIR => 1, CLEANUP => 1);
    make_path(File::Spec->catdir($dir, 'fixtures'));
    return File::Spec->catdir($dir, 'fixtures');
}

sub write_file {
    my ($path, $text) = @_;
    open my $fh, '>', $path or die "write $path: $!";
    print {$fh} $text;
    close $fh;
}

sub run_harness {
    my ($dir, @extra) = @_;
    my $runtime = File::Spec->catfile($dir, 'runtime.c');
    write_file($runtime, "/* canonical test runtime */\n") unless -e $runtime;
    return run_command(
        $^X, $bin, '--guji', $fake, '--compiler', $fake_compiler,
        '--runtime', $runtime, @extra, $dir,
    );
}

sub run_canonical_harness {
    my ($dir, @extra) = @_;
    return run_harness($dir, @extra);
}

sub run_command {
    my (@cmd) = @_;
    my ($fh, $path) = tempfile('gujiconform-output-XXXXXX', TMPDIR => 1, UNLINK => 1);
    binmode $fh, ':raw';
    my $pid = fork;
    die "fork test command: $!" unless defined $pid;
    if ($pid == 0) {
        open STDOUT, '>&', $fh or die "redirect stdout: $!";
        open STDERR, '>&', $fh or die "redirect stderr: $!";
        close $fh;
        exec { $cmd[0] } @cmd or die "exec $cmd[0]: $!";
    }
    waitpid($pid, 0);
    my $status = $?;
    seek $fh, 0, 0 or die "rewind test output: $!";
    local $/;
    my $out = <$fh>;
    close $fh;
    my $exit = $status & 127 ? 128 + ($status & 127) : $status >> 8;
    return ($exit, defined $out ? $out : '');
}

my $d1 = fixture_dir();
write_file("$d1/pass.guji", "PRINT:ok\n");
write_file("$d1/pass.expected", "ok\n");
my ($exit, $out) = run_harness($d1, '--engine', 'both');
is($exit, 0, 'matching fixture exits zero');
like($out, qr/PASS\s+.*pass.*\(native\)/, 'native pass reported');
like($out, qr/PASS\s+.*pass.*\(interp\)/, 'interp pass reported');

my $d2 = fixture_dir();
write_file("$d2/fail.guji", "PRINT:actual\n");
write_file("$d2/fail.expected", "expected\n");
($exit, $out) = run_harness($d2);
is($exit, 1, 'mismatch exits one');
like($out, qr/FAIL/, 'failure reported');
like($out, qr/--- expected stdout/, 'stdout diff reported');

my $d3 = fixture_dir();
write_file("$d3/xfail.guji", "PRINT:actual\n");
write_file("$d3/xfail.expected", "expected\n");
write_file("$d3/xfail.meta", "xfail: known bug\n");
($exit, $out) = run_harness($d3);
is($exit, 0, 'expected failure exits zero');
like($out, qr/XFAIL/, 'xfail reported');

my $d4 = fixture_dir();
write_file("$d4/xpass.guji", "PRINT:ok\n");
write_file("$d4/xpass.expected", "ok\n");
write_file("$d4/xpass.meta", "xfail: fixed bug\n");
($exit, $out) = run_harness($d4);
is($exit, 3, 'unexpected pass exits three');
like($out, qr/XPASS/, 'xpass reported');

my $d5 = fixture_dir();
write_file("$d5/missing.guji", "PRINT:ok\n");
($exit, $out) = run_harness($d5);
is($exit, 2, 'missing expected exits two');
like($out, qr/ERROR/, 'missing expectation reported');

my $d6 = fixture_dir();
write_file("$d6/norm.guji", "PRINT:ok\n");
write_file("$d6/norm.expected", "ok");
($exit, $out) = run_harness($d6, '--normalize', 'trailing-newline');
is($exit, 0, 'trailing-newline normalization works');

my $d7 = fixture_dir();
write_file("$d7/bad_meta.guji", "PRINT:ok\n");
write_file("$d7/bad_meta.expected", "ok\n");
write_file("$d7/bad_meta.meta", "not a header\n");
($exit, $out) = run_harness($d7);
is($exit, 2, 'malformed meta exits two');
like($out, qr/malformed meta line/, 'malformed meta reported');

my $d8 = fixture_dir();
write_file("$d8/bad_exit.guji", "PRINT:ok\n");
write_file("$d8/bad_exit.expected", "ok\n");
write_file("$d8/bad_exit.exit", "nope\n");
($exit, $out) = run_harness($d8);
is($exit, 2, 'malformed exit exits two');
like($out, qr/malformed exit file/, 'malformed exit reported');

my $d9 = fixture_dir();
write_file("$d9/repl.guji", "# metadata selects REPL mode\n");
write_file("$d9/repl.stdin", "hello\n");
write_file("$d9/repl.expected", "REPL:hello\n");
write_file("$d9/repl.meta", "engines: interp\ninterp_cmd: {guji} repl\n");
($exit, $out) = run_harness($d9, '--engine', 'both');
is($exit, 0, 'fixture interp_cmd overrides the default interpreter template');
like($out, qr/PASS\s+.*repl.*\(interp\)/, 'interp_cmd override fixture passes');

my $d10 = fixture_dir();
write_file("$d10/both.guji", "PRINT:ok\n");
write_file("$d10/both.expected", "ok\n");
write_file("$d10/both.meta", "engines: both\n");
($exit, $out) = run_harness($d10, '--engine', 'both');
is($exit, 0, 'engines both metadata expands to both concrete engines');
like($out, qr/PASS\s+.*both.*\(native\)/, 'engines both runs native');
like($out, qr/PASS\s+.*both.*\(interp\)/, 'engines both runs interp');

my $d11 = fixture_dir();
write_file("$d11/none.guji", "PRINT:ok\n");
write_file("$d11/none.expected", "ok\n");
write_file("$d11/none.meta", "engines: interp\n");
($exit, $out) = run_harness($d11, '--engine', 'native');
is($exit, 2, 'metadata selecting no requested engines exits two');
like($out, qr/ERROR\s+.*none.*\(meta\).*selects no engines/, 'empty engine selection is reported');

my $d12 = fixture_dir();
write_file("$d12/canonical.guji", "PRINT:owned\n");
write_file("$d12/canonical.expected", "owned\n");
($exit, $out) = run_canonical_harness($d12, '--engine', 'both');
is($exit, 0, 'canonical guji2c and interpreter invocation exits zero');
like($out, qr/PASS\s+.*canonical.*\(native\)/, 'canonical compiler pass reported');
like($out, qr/PASS\s+.*canonical.*\(interp\)/, 'canonical interpreter pass reported');

my $d13 = fixture_dir();
write_file("$d13/native_only.guji", "PRINT:owned\n");
write_file("$d13/native_only.expected", "owned\n");
my $runtime = File::Spec->catfile($d13, 'runtime.c');
write_file($runtime, "/* canonical test runtime */\n");
my @cmd = (
    $^X, $bin, '--engine', 'native', '--guji', '/definitely/missing/guji',
    '--compiler', $fake_compiler, '--runtime', $runtime, $d13,
);
($exit, $out) = run_command(@cmd);
is($exit, 0, 'canonical native-only run does not require an interpreter');
like($out, qr/PASS\s+.*native_only.*\(native\)/, 'canonical native-only pass reported');

my $d14 = fixture_dir();
my $missing_path = File::Spec->catfile($d14, 'does_not_exist.guji');
my $d14_runtime = File::Spec->catfile($d14, 'runtime.c');
write_file($d14_runtime, "/* canonical test runtime */\n");
($exit, $out) = run_command(
    $^X, $bin, '--guji', $fake, '--compiler', $fake_compiler,
    '--runtime', $d14_runtime, $missing_path,
);
is($exit, 2, 'nonexistent explicit fixture path exits two');
like($out, qr/fixture path does not exist/, 'nonexistent fixture path is reported');

my $d15 = fixture_dir();
write_file("$d15/once.guji", "PRINT:once\n");
write_file("$d15/once.expected", "once\n");
($exit, $out) = run_harness($d15, "$d15/once.guji");
is($exit, 0, 'overlapping fixture inputs still pass');
like($out, qr/^1 checks:/m, 'overlapping fixture inputs are deduplicated');

my $d16 = fixture_dir();
write_file("$d16/duplicate_meta.guji", "PRINT:ok\n");
write_file("$d16/duplicate_meta.expected", "ok\n");
write_file("$d16/duplicate_meta.meta", "engines: interp\nengines: interp\n");
($exit, $out) = run_harness($d16, '--engine', 'interp');
is($exit, 2, 'duplicate metadata key exits two');
like($out, qr/duplicate meta key 'engines'/, 'duplicate metadata key is reported');

my $d17 = fixture_dir();
write_file("$d17/bad_sidecar.guji", "PRINT:ok\n");
write_file("$d17/bad_sidecar.expected.target", "ok\n");
symlink "$d17/bad_sidecar.expected.target", "$d17/bad_sidecar.expected"
    or die "create sidecar symlink: $!";
($exit, $out) = run_harness($d17);
is($exit, 2, 'symbolic-link expectation exits two');
like($out, qr/sidecar must not be a symbolic link/, 'symbolic-link expectation is reported');

my $d17_source = fixture_dir();
write_file("$d17_source/source-target", "PRINT:linked\n");
symlink "$d17_source/source-target", "$d17_source/linked.guji"
    or die "create source symlink: $!";
write_file("$d17_source/linked.expected", "linked\n");
($exit, $out) = run_harness($d17_source);
is($exit, 0, 'fixture source symlink remains supported for co-located import modules');
like($out, qr/PASS\s+.*linked/, 'fixture source symlink is discovered');

my $d18 = fixture_dir();
write_file("$d18/bad_args.guji", "PRINT:ok\n");
write_file("$d18/bad_args.expected", "ok\n");
make_path("$d18/bad_args.args");
($exit, $out) = run_harness($d18);
is($exit, 2, 'non-file optional sidecar exits two');
like($out, qr/sidecar is not a regular file/, 'non-file optional sidecar is reported');

my $d19 = fixture_dir();
write_file("$d19/timeout.guji", "# intentional timeout\n");
write_file("$d19/timeout.exit", "124\n");
write_file("$d19/timeout.meta", "engines: interp\ninterp_cmd: {guji} sleep\n");
($exit, $out) = run_harness($d19, '--engine', 'interp', '--timeout', '1');
is($exit, 1, 'timeout cannot pass by expecting exit 124');
like($out, qr/FAIL\s+.*timeout/, 'timeout is classified as a fixture failure');
like($out, qr/timeout: process exceeded 1s/, 'timeout diagnostic is reported');

my $d19_native = fixture_dir();
write_file("$d19_native/compiler_timeout.guji", "COMPILE_SLEEP\n");
write_file("$d19_native/compiler_timeout.exit", "124\n");
($exit, $out) = run_harness($d19_native, '--engine', 'native', '--timeout', '1');
is($exit, 1, 'compiler timeout cannot pass by expecting exit 124');
like($out, qr/timeout: process exceeded 1s/, 'compiler timeout marker reaches comparison');

my $d20 = fixture_dir();
write_file("$d20/tap.guji", "PRINT:ok\n");
write_file("$d20/tap.expected", "ok\n");
write_file("$d20/tap.meta", "engines: interp\n");
($exit, $out) = run_harness($d20, '--engine', 'interp', '--format', 'tap', '--quiet');
is($exit, 0, 'quiet TAP run exits zero');
like($out, qr/^ok 1 - /m, 'quiet does not suppress required TAP test rows');
like($out, qr/^1\.\.1$/m, 'quiet TAP output has a matching plan');

($exit, $out) = run_harness($d20, '--normalize', 'unknown');
is($exit, 2, 'unknown normalizer exits two');
like($out, qr/unknown normalizer 'unknown'/, 'unknown normalizer is reported');

($exit, $out) = run_harness($d20, '--interp-cmd', '"unterminated');
is($exit, 2, 'malformed command template exits two');
like($out, qr/malformed shell-style quoting/, 'malformed command template is reported');

my $shell_marker = File::Spec->catfile($d20, 'shell-marker');
my $literal_template = "$fake {file} {args} ; touch $shell_marker";
($exit, $out) = run_harness(
    $d20, '--engine', 'interp', '--interp-cmd', $literal_template,
);
is($exit, 0, 'shell metacharacters in a template remain ordinary arguments');
ok(!-e $shell_marker, 'command template is never evaluated by a shell');

{
    local $ENV{GUJI2C} = '/definitely/missing/compiler';
    local $ENV{GUJI_RUNTIME} = '/definitely/missing/runtime';
    ($exit, $out) = run_command(
        $^X, $bin, '--engine', 'interp', '--guji', $fake, $d20,
    );
}
is($exit, 0, 'interp-only run ignores unrelated compiler environment settings');

($exit, $out) = run_command(
    $^X, $bin, '--engine', 'native', '--guji', $fake, $d20,
);
is($exit, 2, 'default native run requires the configured compiler and runtime');
like($out, qr/native engine requires --compiler/, 'missing native compiler guidance is explicit');

my $native_template = "$fake {file} {args}";
($exit, $out) = run_command(
    $^X, $bin, '--engine', 'native', '--guji', '/definitely/missing/guji',
    '--native-cmd', $native_template, "$d15/once.guji",
);
is($exit, 0, 'custom native command need not depend on the interpreter');

($exit, $out) = run_command($^X, $bin, '--help', '--engine', 'not-an-engine');
is($exit, 0, '--help bypasses unrelated semantic option validation');
like($out, qr/^gujiconform \[options\]/m, 'help text is printed');

my $d21 = fixture_dir();
write_file("$d21/empty_xfail.guji", "PRINT:ok\n");
write_file("$d21/empty_xfail.expected", "ok\n");
write_file("$d21/empty_xfail.meta", "xfail:\n");
($exit, $out) = run_harness($d21);
is($exit, 2, 'empty xfail reason exits two');
like($out, qr/xfail metadata requires a nonempty reason/, 'empty xfail reason is reported');

my $d22 = fixture_dir();
write_file("$d22/empty_engine.guji", "PRINT:ok\n");
write_file("$d22/empty_engine.expected", "ok\n");
write_file("$d22/empty_engine.meta", "engines: native,\n");
($exit, $out) = run_harness($d22);
is($exit, 2, 'empty engine metadata entry exits two');
like($out, qr/engines metadata contains an empty engine/, 'empty engine metadata entry is reported');

my $d23 = fixture_dir();
write_file("$d23/exit_range.guji", "EXIT:0\n");
write_file("$d23/exit_range.exit", "256\n");
($exit, $out) = run_harness($d23);
is($exit, 2, 'out-of-range expected exit exits two');
like($out, qr/malformed exit file/, 'out-of-range expected exit is reported');

($exit, $out) = run_harness($d20, '--select', '');
is($exit, 2, 'empty selection glob exits two');
like($out, qr/--select must not be empty/, 'empty selection glob is reported');

{
    local $ENV{POSIXLY_CORRECT} = 1;
    ($exit, $out) = run_command(
        $^X, $bin, $d20, '--engine', 'interp', '--guji', $fake,
    );
}
is($exit, 0, 'option ordering is deterministic under POSIXLY_CORRECT');

($exit, $out) = run_command($^X, $bin, '--eng', 'interp', $d20);
is($exit, 2, 'abbreviated long option is rejected');
like($out, qr/Unknown option: eng/, 'rejected abbreviated option is identified');

done_testing();
