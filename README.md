# Guji

Guji is a statically typed, compiled, functional-first language with first-class
text processing. Regex literals and PEG grammars are language features rather
than library additions.

This repository contains the Guji-written compiler and interpreter, their
maintained C runtime, the Perl conformance harness, language fixtures, and the
language specification. It intentionally does not contain the retired Go
implementation.

Guji is under active development. [`guji-spec.md`](guji-spec.md) is the
language definition.

## Requirements

Building the native tools requires Bash, a C compiler available as `cc`,
`sha256sum`, and standard Unix utilities. The conformance harness additionally requires Perl 5 and uses
only core Perl modules.

The current build and test scripts are exercised on Linux x86-64.

## Build

From the repository root:

```sh
bash selfhost/build_toolchain.sh
```

This creates the following local artifacts under `dist/`:

- `guji` — interpreter
- `guji2c` — compiler launcher
- `guji2c.bin` — self-hosted compiler

The checked-in generated C seed under `bootstrap/` is used only to enter the
self-hosting chain. The build verifies its recorded SHA-256 digest and requires
the reproduced compiler generations to match.

## Use

Interpret a source file:

```sh
./dist/guji program.guji
```

Compile a source file to a native executable:

```sh
./dist/guji2c program.guji program selfhost/rt/runtime_prologue.c
./program
```

The compiler emits C and invokes the system C compiler.

## Example

```guji
sub main(): Int {
    $name = "world"
    print("hello, $name")

    @nums = [1, 2, 3, 4, 5]
    $even = @nums.filter({ $_ % 2 == 0 }).map({ $_ * 2 })
    print("sum: { $even.sum() }")

    0
}
```

Output:

```text
hello, world
sum: 12
```

## Conformance harness

The harness tests do not require a built Guji toolchain:

```sh
prove -v conform/t
```

After building Guji, fixtures can be checked against both the compiler and
interpreter:

```sh
GUJI=dist/guji \
GUJI2C=dist/guji2c \
GUJI_RUNTIME=selfhost/rt/runtime_prologue.c \
  conform/gujiconform --engine both conform/fixtures
```

## Source layout

| Path | Contents |
| --- | --- |
| `selfhost/lexer.guji` | Shared front end, evaluator, and compiler implementation |
| `selfhost/compile_driver.guji` | Native compiler entry point |
| `selfhost/eval_driver.guji` | Interpreter entry point |
| `selfhost/rt/` | Maintained C runtime sources |
| `bootstrap/` | Digest-pinned generated C bootstrap seed |
| `conform/` | Perl conformance harness and fixtures |
| `tests/` | Guji programs and expected outputs |
| `guji-spec.md` | Language specification |

## Author

Guji was created by [Toby](https://github.com/aetherbird).

## License

See [`LICENSE-APACHE`](LICENSE-APACHE) and [`LICENSE-MIT`](LICENSE-MIT).
