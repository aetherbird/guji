# guji — Language Specification (v0)

> **Status:** Starting specification for a new, statically-typed, compiled,
> functional-first language. This document is the single source of truth for
> the v0 implementation. Anything not described here is out of scope for v0.

---

## 1. Overview

guji is a compiled, statically-typed, functional-first language with strong,
first-class text-processing facilities. Programs compile ahead-of-time to a
single self-contained native executable.

### 1.1 Design principles

1. **One obvious way.** For any given task there is exactly one idiomatic
   construct. The language deliberately omits redundant or overlapping syntax.
2. **Functional-first.** Bindings are immutable by default; data is transformed
   rather than mutated; functions are first-class values; control constructs are
   expressions that yield values.
3. **Inferred static types.** Every binding and expression has a type known at
   compile time, but type annotations are rarely required — the compiler infers
   them.
4. **Text is a first-class concern.** Regular expressions and grammars are part
   of the language, not a library, and are the language's signature capability.
5. **Compiles to a single binary.** The output of the compiler is one native
   executable with no external runtime dependency.

### 1.2 A first program

```guji
sub main(): Int {
    $name = "world"
    print("hello, $name")
    0
}
```

---

## 2. Lexical Structure

### 2.1 Encoding

Source files are UTF-8 text. Their external bytes are converted by the exact
§3.1 rule before lexing, so each malformed input byte is presented to the lexer
as one U+FFFD rather than as a raw byte. The file extension is `.guji`. One file
is one **module** (see §16).

### 2.2 Comments

```guji
# Line comment: runs to end of line.

#[
  Block comment.
  May span multiple lines. Block comments do not nest.
]#
```

### 2.3 Identifiers

- **Bindings, fields, subs, modules:** `snake_case` (lowercase letters, digits,
  underscores; must not start with a digit). **Emoji are also accepted** in these
  identifiers, including as a whole identifier — a binding may be named `$🚀`, `@🎯`,
  or `%🗺` (see below).
- **Types, enums, classes, enum variants:** `PascalCase`.
- **Type parameters:** single uppercase letters or `PascalCase` (`T`, `K`, `V`,
  `Elem`).

Identifiers are case-sensitive. Casing is a **convention**, not a visibility
mechanism (visibility is governed by §16).

**Emoji identifiers.** Characters carrying the Unicode `Emoji` property — together
with emoji ZWJ sequences and the variation selectors and skin-tone modifiers that
compose them — are explicitly permitted in the `snake_case` identifier class, and may
form an entire identifier. Emoji are not case-bearing, so they are exempt from the
`snake_case` shape and do **not** name types (which remain `PascalCase`); the sigil
keeps an emoji binding unambiguous (`$🚀`, `@🎯`, `%🗺`). The recognized emoji set
follows the pinned Unicode version (§13.5).

### 2.4 Sigils

Every value binding is prefixed by a sigil that declares its broad shape. The
sigil is part of the name and is **invariant**: it never changes regardless of
how the value is accessed.

| Sigil | Shape   | Example binding        |
|-------|---------|------------------------|
| `$`   | scalar  | `$count = 3`           |
| `@`   | list    | `@items = [1, 2, 3]`   |
| `%`   | map     | `%ages = {"ada": 30}`|

A "scalar" is any single value: an `Int`, `Float`, `Str`, `Bool`, an instance of
a `class`, a value of an `enum`, an `Option`, a `Result`, a function value, etc.
Lists and maps are the only two compound bindings that receive their own sigil.

Accessing an element keeps the container's sigil:

```guji
@items = [10, 20, 30]
@items[0]          # the element 10 (sigil stays @)
%ages = {"ada": 30}
%ages{"ada"}       # the value 30 (sigil stays %)
```

The sigil indicates shape; the type system tracks the precise element type
(e.g. `@items` has type `List[Int]`, so `@items[0]` has type `Int`).

### 2.5 Keywords

Reserved words, unavailable as identifiers:

```
sub  class  enum  has  match  if  else  for  while  in
mut  pub  import  return  grammar  rule  token  regex
hatch  select
true  false  and  not  or
```

(`and`, `or`, `not` are reserved but `&&`, `||`, `!` are the operators; see
§5.2. The word forms are reserved to keep them free for future use.)

### 2.6 Literals

| Kind    | Examples                                  |
|---------|-------------------------------------------|
| Int     | `42`, `0`, `1_000_000`, `0xFF`, `0b1010`  |
| Float   | `3.14`, `1.0`, `6.022e23`                 |
| Str     | `"interpolated"`, `'literal'` (see §12)   |
| Bool    | `true`, `false`                           |
| List    | `[1, 2, 3]`, `[]`                         |
| Map     | `{"a": 1, "b": 2}`, `{}`                  |
| Unit    | `()`                                      |
| Regex   | `/\w+/` (see §13)                         |

Underscores may be used as digit separators in numeric literals.

### 2.7 Statement separation

A physical newline and a semicolon `;` are the two explicit **item
separators** at an item-sequence boundary. They separate statements, top-level
declarations, match/select arms, and members of declaration bodies. Runs of
separators are allowed. A separator may be omitted when the preceding item is
syntactically complete and the next token unambiguously begins another item,
and before a closing brace or end of input; thus a compact block such as
`{ note($error) return 1 }` is legal.

While the parser is inside expression, type, parameter, or pattern delimiters,
physical newlines are ordinary layout whitespace and may occur between tokens.
This lets calls, groupings, collection literals, indexes, type arguments,
parameter lists, and variant patterns span lines. A physical newline also
continues after a binary operator and before a syntactically required body
brace, `else`, or `else if`. A semicolon is never layout whitespace in any of
those positions: it ends an item, so `f(1;, 2)` is a syntax error.

Braces introduced in statement/declaration position delimit item sequences and
retain item-separator behavior. In expression position, braces delimit either
a map literal, whose entries use newline layout, or a topic-block lambda, whose
body is an item sequence (§7.4); the parser distinguishes them as described in
the §20 notes.

---

## 3. Types

### 3.1 Built-in types

- **Scalars:** `Int` (64-bit signed), `Float` (64-bit), `Str` (well-formed UTF-8
  string),
  `Bool`, `Unit` (the type of `()`).
- **Compound:** `List[T]`, `Map[K, V]`. In v0, map keys are always `Str`
  (§15.2): a map literal key or `Map[K, V]` annotation with a concrete
  non-`Str` key type is a compile-time error. Generalized key types are
  deferred (§21).
- **Standard sum types:** `Option[T]`, `Result[T, E]` (see §11).
- **Concurrency:** `Chan[T]`, and `Closed` — the unit-like channel-error type with
  the single value `Closed`, the `E` in the channel operations'
  `Result[Unit, Closed]` (see §17.3).
- **Text:** `Regex`, `Match`, `Bush` (see §13–14).
- **Bottom:** `Never`, the type of an expression that does not return (e.g. a `panic`,
  §11.2); it unifies with every type, so a diverging branch fits any context.

A `Str` is a sequence of Unicode scalar values represented as well-formed
UTF-8. Its storage carries an explicit byte extent. That extent, rather than a
NUL terminator, determines the equality, ordering, collection display, map-key,
and exact I/O content and capture rules defined below. An implementation may
keep a trailing NUL sentinel, but that sentinel is not part of the value.
U+0000 is an ordinary scalar and may occur anywhere in the value. Guji does not
implicitly apply NFC, NFD, or any other Unicode normalization, so distinct
scalar sequences remain distinct.

Text received from an operating-system boundary is converted to this invariant
form before it becomes a `Str`. Decode from left to right. A valid UTF-8
sequence is copied unchanged. At any malformed lead byte, invalid continuation,
overlong encoding, surrogate encoding, out-of-range encoding, or truncated
sequence, append U+FFFD and advance exactly one input byte, then resume
decoding. Thus each malformed input byte produces one replacement scalar; a
valid encoded U+FFFD remains one scalar. This rule applies to command-line
arguments, standard input, file reads, handle reads, and captured child-process
output (§15.4, §15.6). At boundaries that supply a byte length, valid UTF-8
bytes, including embedded NUL bytes, round trip unchanged. Host command-line
interfaces do not supply embedded NUL bytes. A raw byte type and lossless
malformed-byte IO are deferred (§21).

### 3.2 Type annotations

Annotations are optional; the compiler infers types where omitted. When written,
the form is `name: Type`.

```guji
$count: Int = 0
@names: List[Str] = []
sub area($s: Shape): Float { ... }
```

### 3.3 Generics

Type parameters are written in square brackets after the name.

```guji
enum Option[T] { Some($value: T), None }

sub first[T](@xs: List[T]): Option[T] {
    if @xs.is_empty() { None } else { Some(@xs[0]) }
}
```

### 3.4 Type inference

Inference is local and complete within a function body: any binding or
sub-expression whose type can be determined from its initializer, its uses, or
the surrounding context does not require an annotation. Top-level `pub`
declarations (§16) **must** annotate their parameter and return types to form a
stable module interface; non-exported declarations may rely on inference.

---

## 4. Bindings and Mutability

A binding is introduced by writing a sigil-name and `=`:

```guji
$x = 5          # immutable binding
@xs = [1, 2, 3] # immutable binding
```

Immutable bindings cannot be reassigned. Mutable bindings are opt-in with `mut`:

```guji
mut $total = 0
$total = $total + 1   # allowed: $total is mut
```

Reassigning an immutable binding is a compile-time error. Introducing a new
binding with the same name in a nested scope (shadowing) is permitted. Mutability
is a property of the binding, not the value.

---

## 5. Expressions and Operators

Everything that produces a value is an expression, including `if`, `match`, and
blocks (§6). The value of a block is the value of its final expression.

### 5.1 Arithmetic

`+`  `-`  `*`  `/`  `%`  `**` (power). Defined on `Int` and `Float`; the two
operands of a binary arithmetic operator must be the same numeric type.

Integer `/` truncates toward zero and `%` is the matching remainder. Dividing an `Int`
by zero panics (§11.2), and `Int` arithmetic that overflows the 64-bit range panics
rather than wrapping silently. `Float` follows IEEE-754: division by zero yields `inf`
or `nan` and does not panic.

### 5.2 Comparison and logical

Comparison: `==`  `!=`  `<`  `<=`  `>`  `>=` (yield `Bool`).
Logical: `&&`  `||`  `!` (operate on `Bool`; `&&` and `||` short-circuit).

Equality operands must have compatible types. `!=` is the logical negation of
`==`. Scalars compare by value: `Str` compares its complete scalar sequence
(including embedded U+0000), and `Float` uses IEEE-754 equality, so NaN is not
equal to itself and the two signed zeros are equal. Compound equality is
structural and recursive: List and Map rules are in §§15.1-15.2, class rules in
§8, enum rules in §9, and the deliberately opaque function rule in §7.4.

Ordering operators are defined only for matching `Int`, `Float`, or `Str`
operands. `Int` uses signed numeric order and `Float` uses the corresponding
IEEE-754 relational predicate (every ordering predicate involving NaN is
false). `Str` uses lexicographic Unicode-scalar order: compare the first
differing scalar, or place the shorter prefix first. Because run-time strings
are well-formed UTF-8 (§3.1), unsigned bytewise UTF-8 comparison with a length
fallback gives the same order and treats embedded NUL as data. Ordering a
List, Map, class, enum, Bool, Unit, function, or other compound/opaque value is
a compile-time error.

### 5.3 String concatenation

The `~` operator concatenates `Str` values:

```guji
$greeting = "hello" ~ ", " ~ "world"
```

(Most concatenation is better expressed by interpolation; see §12.)

### 5.4 Ranges

`a .. b` produces an inclusive range of `Int`. `a ..< b` produces a half-open
range (excludes `b`). Ranges are iterable and usable in `for` (§6.3).

### 5.5 Precedence (highest to lowest)

1. Postfix: call `()`, index `[]`/`{}`, field/method `.`, error-propagation `?`
2. Unary: `!`, unary `-`
3. `**`
4. `*`  `/`  `%`
5. `+`  `-`  `~`
6. `..`  `..<`
7. `<`  `<=`  `>`  `>=`
8. `==`  `!=`  `~~`
9. `&&`
10. `||`

Parentheses override precedence. `**` is right-associative; all other binary
operators are left-associative. Precedence and associativity determine grouping;
they do not change the evaluation order below.

### 5.6 Expression evaluation order

Guji evaluates strict expression operands exactly once. Unless a construct below
states a different order, immediate subexpressions are evaluated in written
left-to-right order. If an earlier subexpression completes abruptly through `?`,
`return`, `panic`, or `exit`, later subexpressions in the containing expression
are not evaluated.

- A binary expression evaluates its left operand before its right operand.
  `&&` and `||` first evaluate the left operand and evaluate the right operand
  only when required by their short-circuit rule (§5.2).
- A postfix chain evaluates its base once and then applies its suffixes in
  written order. A call evaluates its function-valued callee once, then its
  arguments in written order, and invokes the function only after those
  evaluations finish. An index evaluates the indexed value before its index or
  key.
- A method-style call evaluates its receiver before its explicit arguments. The
  uniform-call rewrite in §7.2 neither duplicates nor delays the receiver.
- A list literal evaluates its element expressions in written left-to-right
  order. A map literal evaluates its entries in written left-to-right order,
  evaluating each entry's key before that entry's value (§15.1, §15.2).
- Enum payload expressions use ordinary written argument order. Class
  construction is the deliberate exception: named initializer expressions are
  evaluated exactly once in the class's **field declaration order**, regardless
  of the order in which the named arguments are written (§8.2). Argument names
  map the resulting values to fields.
- An interpolating string evaluates interpolation markers as they are
  encountered from left to right. Each braced expression is evaluated once and
  its display is appended before evaluation continues (§12).

These rules specify observable Guji behavior. A native backend must not inherit
the unspecified operand or argument evaluation order of an implementation
language such as C.

---

## 6. Control Flow

### 6.1 `if`

`if` is an expression. Branch bodies are blocks; the chosen branch's value is the
value of the whole `if`. When used as a value, an `else` is required and both
branches must yield the same type.

```guji
$label = if $n > 0 { "positive" } else { "non-positive" }

if $ready {
    start()
} else if $waiting {
    wait()
} else {
    halt()
}
```

### 6.2 `match`

`match` is an expression that selects among patterns (§10). It must be
**exhaustive**: the compiler rejects a `match` that does not cover every possible
value. Each arm is `pattern { block }`; arms use the item separators and
inferred boundaries of §2.7. The arm's block yields the arm's value (§5).

```guji
$area = match $shape {
    Circle($r)   { 3.14159 * $r * $r }
    Rect($w, $h) { $w * $h }
}
```

### 6.3 Loops

`for` iterates over a list, map, range, or channel (§17.4). `while` repeats while a
condition holds. Both are statements yielding `()`.

Lists and ranges bind one loop variable. Maps bind two loop variables: key, then
value. A map loop with only one binding is a compile-time error.

```guji
for $x in @items {
    print($x)
}

for $name, $age in %ages {
    print("$name: $age")
}

mut $i = 0
while $i < 10 {
    $i = $i + 1
}
```

Idiomatic transformation and aggregation use collection methods (§15) rather
than explicit loops; `for`/`while` are for side-effecting iteration.

---

## 7. Functions

### 7.1 Declaration

Two forms. Block form for multiple statements; expression form (`= expr`) for a
single expression.

```guji
sub double($x: Int): Int {
    $x * 2
}

sub triple($x: Int): Int = $x * 3
```

Parameter and return type annotations are optional except on `pub` declarations
(§3.4). Functions are values and may be passed, returned, and stored.

### 7.2 Calls and uniform call syntax

A function may be called in two equivalent ways:

```guji
double($x)      # ordinary call
$x.double()     # method-style call
```

`$receiver.f($a, $b)` is **exactly** equivalent to `f($receiver, $a, $b)`. This
"first argument is the receiver" rule (the **data-first** convention) is what
makes method-style calls and chaining work uniformly for every function. All
standard-library functions take the value they operate on as their first
parameter. The receiver is evaluated once before the explicit arguments, as
specified by §5.6.

### 7.3 Chaining

Because every call can be written method-style, transformations compose
left-to-right with `.`:

```guji
@nums.filter({ $_ % 2 == 0 }).map({ $_ * 2 }).sum()
```

There is no separate pipeline operator; `.` is the single composition mechanism.

### 7.4 Lambdas

Anonymous functions have two forms:

- **Topic block** `{ ... }`: a single-parameter lambda whose parameter is the
  implicit topic `$_`.
- **Parameterized lambda** `sub(params) { ... }`: an anonymous `sub` (a `sub` with
  no name, §7.1) naming one or more parameters.

```guji
@nums.map({ $_ * 2 })                 # implicit single parameter
@pairs.map(sub($a, $b) { $a + $b })   # explicit parameters
```

`$_` is only in scope inside a topic block and always refers to that block's sole
argument. Use the parameterized form when you need to name parameters or take
more than one.

**Capture semantics.** A lambda (either form) is a closure: its body may
reference bindings from enclosing scopes. Closures capture **immutable**
bindings only. Because captured data can never change, capture-by-value and
capture-by-reference are observationally identical, and an implementation may
use either. Referencing a `mut` binding (§4) from inside a closure — whether
reading it or assigning to it — is a **compile-time error**. To use the
current value of a `mut` binding, bind it immutably first:

```guji
mut $total = 0
# ... $total updated in a loop ...
$t = $total                # snapshot the current value, immutably
@xs.map({ $_ + $t })       # ok: captures the immutable $t
@xs.map({ $_ + $total })   # error: cannot capture mut binding $total
```

This rule holds for every closure form: topic blocks, parameterized lambdas,
`sub`s declared in an enclosing function's scope, and `hatch` blocks (§17.1,
which states the same rule for tasks). It is what guarantees that a closure's
environment can never change after creation and that no value can ever come to
reference itself, so guji's heap remains acyclic.

**Named local subs.** A named `sub` may appear as a statement in any block. The
declaration yields `()` and introduces an immutable function binding in that
block at the declaration point. Its name is visible in its own body and in
following statements and nested scopes, but not in preceding statements or
after the block. The self-name is resolved statically rather than captured,
which permits direct recursion without creating a value cycle. Any other local
sub must already be in scope: forward sibling references and mutual recursion
through a later declaration are compile-time errors. A duplicate local sub in
the same block is an error; shadowing an enclosing name in a nested block is
permitted.

The function captures immutable bindings from its declaration environment when
the declaration executes, and those captures remain live if the function
escapes the block. Capturing a `mut` binding is rejected by the closure rule
above. A local named sub uses the ordinary `sub` syntax, including type
parameters and block or expression bodies. It cannot be `pub` (§16.2), so its
annotations follow the non-exported inference rule (§3.4).

**Display and equality.** A function value is opaque: its display form is
`<function>`. Function values do not expose code or capture identity through
equality. Consequently `$f == $g` is always `false` and `$f != $g` is always
`true`, even when `$g` is an alias of `$f`; both operands are still evaluated
normally.
This keeps capture representation unobservable, as required by the capture
semantics above.

### 7.5 Associated functions

A Pascal-named type — a `class`, `enum`, or `grammar`, or a built-in type such as
`Regex` — may expose **associated functions**, invoked as `TypeName.func(args)`. An
associated function is namespaced under the type and has no `$self` receiver, which
distinguishes it from a method (§8.3). The call `TypeName.func(a, b)` is an ordinary
call: unlike a data-first method call (§7.2), it inserts no implicit first argument.
Its explicit arguments follow the ordinary written order in §5.6.

A user type declares one by writing a `sub` in its body whose first parameter is not
`$self`:

```guji
class Account {
    has $.owner: Str
    has $.balance: Float

    sub opened($owner: Str): Account {        # associated function (no $self)
        Account(owner: $owner, balance: 0.0)
    }
}

$a = Account.opened("ada")                    # call on the type, not a value
```

Built-in associated functions include `Regex.compile`, `Regex.escape`, and
`Regex.literal` (§13.4); every `grammar` exposes `parse` (§14.2). Construction (`Account(...)`, §8.2) is the type's built-in
constructor; an associated function such as `opened` is a named alternative
constructor in the same namespace.

Because lambdas are written as anonymous `sub`s (§7.4), the keyword `sub` spans every
function shape, distinguished by name presence and by `$self`:

| Form                          | What it is                              |
|-------------------------------|-----------------------------------------|
| `sub area($s) { ... }`        | top-level function (§7.1)               |
| `sub deposit($self, …) { … }` | method — data-first `.call` (§8.3)      |
| `sub opened($owner) { ... }`  | associated function — `Type.call` (§7.5)|
| `sub($a, $b) { ... }`         | lambda — a function value (§7.4)        |

---

## 8. Product Types — `class`

A `class` declares a type that holds several fields simultaneously ("has all of
these"), with field-level visibility and associated behavior.

### 8.1 Fields

Fields are declared with `has` and a twigil that sets visibility:

- `$.name` — **public**: readable from outside via `$obj.name`.
- `$!name` — **private**: accessible only within the class body.

The twigil applies to list (`@.items` / `@!items`) and map (`%.opts` / `%!opts`)
fields as well.

```guji
class Account {
    has $.owner: Str
    has $.balance: Float
    has $!pin: Str
}
```

### 8.2 Construction

A class is constructed by naming all of its fields as named arguments. Argument
names use the bare field name without the visibility twigil. Private fields may
be set during construction, but are not readable from outside the class after
construction. The names may be written in any order, but their initializer
expressions are evaluated once in class field declaration order (§5.6). Thus
reordering field declarations can observably reorder initializer side effects.

```guji
$acct = Account(owner: "ada", balance: 100.0, pin: "1234")
$acct.owner     # "ada"
$acct.balance   # 100.0
```

### 8.3 Methods

A method is a `sub` declared inside the class body whose first parameter is
`$self`. It is invoked with method-call syntax, where `$self` binds to the
receiver. Inside a method, private fields are reached as `$!field`. A `sub` in the
class body without a `$self` first parameter is an **associated function** (§7.5),
called on the type rather than on a value.

```guji
class Account {
    has $.balance: Float
    has $!pin: Str

    sub deposit($self, $amount: Float): Account {
        Account(balance: $self.balance + $amount, pin: $!pin)
    }

    sub check_pin($self, $guess: Str): Bool {
        $!pin == $guess
    }
}

$acct2 = $acct.deposit(50.0)   # equivalent to deposit($acct, 50.0)
```

Because bindings and values are immutable by default, methods that "modify" an
object return a new instance rather than mutating in place.

**Display and equality.** A class value displays as its declared type name,
followed by every field inside parentheses:
`Type(field: value, other: value)`. Field names are the bare names without
twigils and are ordered by the `Str` order in §5.2, independently of declaration
or constructor-argument order. Public and private fields both participate; field
privacy controls source-level access, not whole-value display. Each field value
uses the same recursive display rules as `print` (§15.4), and a `Str` field is
therefore unquoted.

Two class values are equal exactly when they have the same nominal class type
and every corresponding field is equal recursively. Field declaration order,
constructor argument order, and allocation identity do not affect equality.
Different class types are not compatible equality operands (§5.2).

---

## 9. Sum Types — `enum`

An `enum` declares a type that is exactly one of several labeled variants ("is
one of these"). Each variant may carry its own typed fields.

```guji
enum Shape {
    Circle($radius: Float)
    Rect($width: Float, $height: Float)
}
```

Variants are separated by newlines, semicolons, or commas; an inferred boundary
is also permitted when the next variant is unambiguous (§2.7). A variant with
no fields is written as a bare name:

```guji
enum Direction { North, South, East, West }
```

Enums may be generic:

```guji
enum Tree[T] {
    Leaf($value: T)
    Node($left: Tree[T], $right: Tree[T])
}
```

A value of an enum is produced by naming a variant:

```guji
$s = Circle(2.0)
$d = North
```

The only way to read the fields of an enum value is to `match` on it (§10).

Like a `class` (§8.3), an `enum` body may also contain `sub` declarations: a `sub`
with a `$self` first parameter is a method (its body typically `match`es on `$self`),
and a `sub` without `$self` is an associated function (§7.5), e.g. a `from_name`
constructor called as `Color.from_name(...)`.

**Display and equality.** A nullary enum value displays as its variant name,
such as `North`. A payload variant displays its variant name followed by the
payload values in declaration order, such as `Rect(3, 4)`. Payload values use
the recursive `print` display (§15.4); field names and the enclosing enum type
name are not included.

Two enum values are equal exactly when they have the same nominal enum type,
the same active variant, and pairwise-equal active payloads in declaration
order. Inactive payload storage is unobservable. Different enum types are not
compatible equality operands (§5.2).

---

## 10. Pattern Matching

`match` (§6.2) tests a value against patterns in order and evaluates the arm of
the first pattern that matches, binding any captured fields.

### 10.1 Patterns

| Pattern            | Matches                                          |
|--------------------|--------------------------------------------------|
| scalar or Unit literal (`3`, `3.0`, `"x"`, `true`, `()`) | exactly that value |
| binding (`$x`)     | anything; binds the value to `$x`                |
| wildcard (`_`)     | anything; binds nothing                          |
| variant (`Circle($r)`) | that enum variant; binds its fields          |
| nested (`Node(Leaf($a), $b)`) | structurally, recursively              |

Literal patterns are limited to `Int`, `Float`, interpolation-free `Str`,
`Bool`, and `Unit`. An interpolating string is an expression, not a pattern:
pattern selection never evaluates interpolation markers. `List`, `Map`, and
`Regex` literals are likewise expression forms, not patterns; v0 defines no
List or Map destructuring pattern.

### 10.2 Guards

An arm may add a boolean guard with `if`. A guarded arm matches only when the
pattern matches and the guard is true.

```guji
$desc = match $n {
    0            { "zero" }
    $x if $x < 0 { "negative" }
    _            { "positive" }
}
```

### 10.3 Exhaustiveness

The compiler verifies that the arms cover all possible values. A non-exhaustive
`match` is a compile-time error; the compiler reports which cases are missing.
A wildcard `_` arm covers all remaining cases.

---

## 11. Error Handling

guji has no exceptions. Operations that may be absent or may fail return one of
two standard sum types:

```guji
enum Option[T] {
    Some($value: T)
    None
}

enum Result[T, E] {
    Ok($value: T)
    Err($error: E)
}
```

### 11.1 The `?` operator

The postfix `?` operator propagates absence or failure. Applied to an expression
of type `Result[T, E]` (or `Option[T]`) inside a function that returns
`Result[_, E]` (or `Option[_]`):

- if the value is `Ok($v)` / `Some($v)`, the expression yields `$v`;
- if the value is `Err($e)` / `None`, the enclosing function returns immediately
  with that `Err($e)` / `None`.

```guji
sub parse_age($s: Str): Result[Int, Str] {
    $n = parse_int($s)?              # unwrap, or return the Err early
    if $n >= 0 { Ok($n) } else { Err("age must be non-negative") }
}
```

This keeps every possible failure visible in the type signature while removing
the boilerplate of checking each result by hand.

`?` requires a matching carrier and error type: it propagates an `Option` only inside
an `Option`-returning sub, and a `Result[_, E]` only inside a sub that returns
`Result[_, E]` with the **same** `E`. To bridge types, convert first — `ok_or` turns an
`Option` into a `Result`, and `map_err` adapts the error type (§15.5):

```guji
$n = parse_int($s).map_err(sub($e) { BadInput($e) })?   # Result[_, Str] → Result[_, BadInput]
```

Automatic error conversion (a trait-based `From`) is deferred together with traits
(§21).

### 11.2 Unrecoverable errors — `panic`

Some failures are bugs, not conditions to handle: a violated invariant, an `unwrap` of
`None`, an out-of-bounds index. For these guji has `panic`:

```guji
panic($message: Str): Never
```

`panic` writes `$message` and the source location to standard error and aborts the
**process** with a non-zero exit code. It returns `Never` (§3.1), so it may stand in any
expression position (e.g. one branch of an `if` whose other branch yields a value).
There is no exception to catch and no recovery: panics are for unrecoverable states,
while expected failure uses `Option` / `Result` (§11.1).

The runtime panics on an `Int` divide or modulo by zero, `Int` overflow (§5.1), an
out-of-bounds index `@xs[i]` or `$s` character index, and `unwrap` / `expect` on `None`
or `Err` (§15.5). An unrecovered panic in any task (§17) aborts the whole process.
`panic` is a built-in intrinsic, available in every module without import (like
`print`, §15).

---

## 12. Strings and Interpolation

Two string literal forms:

- **Double-quoted** `"..."`: interpolating.
- **Single-quoted** `'...'`: literal (no interpolation, no escapes except `\'`).

Inside a double-quoted string:

- `$name`, `@list`, `%map` interpolate the named binding.
- `{ expr }` interpolates the value of an arbitrary expression.

Markers are processed from left to right. Each braced expression is evaluated
exactly once and converted to its display form before processing continues with
the next marker (§5.6).

```guji
$name = "ada"
@scores = [10, 20]
"hi $name, scores: @scores, total: { @scores.sum() }"
# value: "hi ada, scores: [10, 20], total: 30"
```

Escape sequences in double-quoted strings: `\n`, `\t`, `\\`, `\"`, `\$`, `\@`,
`\%`, `\{`.

---

## 13. Text Processing — Regular Expressions

Regular expressions are a built-in type, written as a literal between slashes.

```guji
$re = /\w+@\w+\.\w+/
```

**Regex engine.** guji regexes are matched by a *backtracking* engine — the same
engine, with identical semantics, in the reference interpreter and in native-compiled
binaries. Backtracking is what makes the full dialect below (lookaround,
backreferences, atomic groups, the `<{ … }>` splice) expressible, but it is not
linear-time: a pathological pattern such as `(a+)+$` over a long non-matching input
backtracks exponentially, and v0 imposes no step budget — a match runs until it
finishes. When a pattern faces untrusted input, prune backtracking with possessive
quantifiers (`a*+`) or atomic groups (`(?> … )`); for recursion, nesting, or
heavyweight structure, use a `grammar` (§14).

### 13.1 Supported syntax

- **Character classes:** `\w` `\d` `\s` and negations `\W` `\D` `\S`; bracket
  classes `[a-z]`, `[^0-9]`; Unicode properties `\p{Name}` / `\P{Name}`; `.` (any
  char except newline, or any char under `(?s)`).
- **Grapheme:** `\X` matches one extended grapheme cluster (§13.6).
- **Anchors:** `^` (start of line/input), `$` (end of line/input), `\A` / `\z` /
  `\Z` (absolute input boundaries), `\b` / `\B` (word boundary / non-boundary).
- **Quantifiers:** `*` `+` `?` `{n}` `{n,}` `{n,m}`, greedy by default; append `?`
  for lazy (`*?`, `+?`, …) or `+` for possessive (`*+`, `++`, …).
- **Grouping:** `( ... )` capturing, `(?: ... )` non-capturing, `(?> ... )` atomic.
- **Named capture:** `(?<name> ... )`; backreferences `\1`…`\9`, `\k<name>`.
- **Lookaround:** `(?= )`, `(?! )`, `(?<= )`, `(?<! )` (lookbehind is
  bounded-width in v0).
- **Inline modifiers:** `(?imsxa)` and scoped `(?imsxa: ... )`, where `i` is
  case-insensitive, `m` makes `^`/`$` match at line breaks, `s` makes `.` match a
  newline, `x` ignores unescaped whitespace, and `a` makes the shorthand classes
  ASCII-only (§13.5).
- **Alternation:** `|`. **Splice:** `<{ expr }>` embeds a `Regex` value (§13.4).
- Literal text and escaped metacharacters (`\.`, `\/`, `\(`, …).

Recursive and conditional matching are intentionally **not** part of regex; express
them with a `grammar` (§14). The compiler rejects regex recursion (`(?R)`, `(?1)`)
and conditionals (`(?(1)…)`) with a message pointing to grammars.

### 13.2 Matching

The match operator `~~` tests a string against a regex and yields
`Option[Match]`:

```guji
match $line ~~ /(?<user>\w+)@(?<host>\w+)/ {
    Some($m) { "user { $m<user>.unwrap_or('?') } at host { $m<host>.unwrap_or('?') }" }
    None     { "no match" }
}
```

The equivalent method form is `$line.match(/.../)`, also returning
`Option[Match]`.

### 13.3 The `Match` value

A `Match` exposes captures:

- Positional groups: `$m[0]` (whole match), `$m[1]`, `$m[2]`, …
- Named groups: `$m<name>`.

Each capture is itself `Option[Str]` (a group that did not participate yields
`None`). This `Match` is the result of a **regex** match; grammar parsing instead
yields a `Bush` parse tree whose captures are sub-nodes rather than flat text
(§14.2).

The named-capture form is a postfix operator on `Match` values. In expression
lexing, `<ident>` immediately following a postfix expression is tokenized as a
single capture accessor; otherwise `<` and `>` are ordinary comparison tokens.

### 13.4 Dynamic construction

A `Regex` is a first-class value and may be built at run time as well as written as
a literal.

**From a string.** `Regex.compile` builds a pattern from a `Str`, returning a
`Result` because validity is not known until run time:

```guji
Regex.compile($pattern: Str): Result[Regex, Str]
```

Data-driven patterns use ordinary string interpolation (§12) and then compile:

```guji
$prefix = read_prefix()
$re = Regex.compile("(?<id>{ Regex.escape($prefix) }\\d+)")?
```

**Composing values.** Inside a literal, `<{ expr }>` splices a value of type `Regex`
into the pattern:

```guji
$word = /\w+/
$list = /<{ $word }>(,\s*<{ $word }>)*/
```

Bare `$name` / `{ … }` interpolation is **not** available inside `/…/`, because `$`
is the end anchor and `{n,m}` is a quantifier. Build patterns from data with
`Regex.compile`; compose `Regex` values with `<{ … }>`.

**Literal text and escaping.** The string passed to `Regex.compile` is **regex
source**: an interpolated value is read as pattern syntax, so any metacharacters in it
are active, and an unescaped value can change or break the pattern. A value that must
match literally is escaped first:

- `Regex.escape($s: Str): Str` returns regex source matching `$s` verbatim, with every
  metacharacter escaped. Use it when interpolating into a pattern string for
  `Regex.compile`.
- `Regex.literal($s: Str): Regex` is the compiled form — a `Regex` matching `$s`
  verbatim. Escaping always yields a valid pattern, so it cannot fail (it returns
  `Regex`, not `Result`) and composes through the `<{ … }>` splice.

```guji
# both match $prefix literally, whatever characters it contains
$re1 = Regex.compile("(?<id>{ Regex.escape($prefix) }\\d+)")?
$re2 = /(?<id><{ Regex.literal($prefix) }>\d+)/
```

**Captures in a splice.** A `<{ … }>` splice matches as a single non-capturing unit:
the spliced regex's own positional and named groups are *not* exposed in the host
pattern. Positional numbering (`$m[1]`, `$m[2]`, …) counts only the capturing groups
written literally in the host, left to right; splices contribute none, so positional
and named access stay statically determinable even when the spliced value is built at
run time. To capture the span a splice matched, wrap it in a host group —
`(?<w><{ $re }>)` (named) or `(<{ $re }>)` (positional) — which captures its text,
not its internal structure. Backreferences are scoped to their own pattern. Within
one pattern, two named groups with the same name are a compile-time error. For
composition that exposes nested, addressable structure, use a `grammar` (§14), whose
`<name>` productions build a `Bush` tree (§14.2).

**Capture checking.** Named access on a `Match` is a *static refinement* for regex
**literals** only: when a literal's group names are statically known, `$m<name>` is
checked at compile time for existence. A regex produced by `Regex.compile`, or a
literal containing a `<{ … }>` splice of a non-literal value, has capture structure
unknown at compile time; named access on its `Match` is checked only at run time.
Either way the runtime type of a capture is always `Option[Str]` (§13.3) — the
refinement never changes the value type, it only rejects provably absent names on
literals.

The same rule applies to positional access `$m[i]`: when the index is a literal and
the pattern's group count is statically known, an out-of-range index is a compile-time
error; a computed index `$m[$i]`, or a dynamically-built pattern, is checked at run
time and yields `None` when the name or index is absent. A group that exists but did
not participate in the match also yields `None` (§13.3). `$m[0]` is the whole match
and is present whenever the overall match succeeded.

### 13.5 Unicode

guji targets a single Unicode version, fixed per compiler release and stated in its
documentation (the v0 baseline is Unicode 15.0). All property data below comes from
that version.

**Shorthand classes are Unicode-aware by default**, matching over a UTF-8 `Str` (§3.1):

- `\d` is `\p{Nd}` (decimal digit); `\w` is `[\p{Alphabetic}\p{M}\p{Nd}\p{Pc}]`; `\s`
  is `\p{White_Space}`; `\b` is a boundary between a `\w` and a non-`\w` position.
  `\D` `\W` `\S` `\B` are their negations.
- The `(?a)` modifier restricts these to ASCII for the rest of its enclosing pattern
  or group: `\d` is `[0-9]`, `\w` is `[0-9A-Za-z_]`, `\s` is `[ \t\n\r\f\v]`, and `\b`
  uses the ASCII word definition.

**Properties.** `\p{Name}` (and its negation `\P{Name}`) accept:

- **General_Category** values, both top-level (`L`, `N`, `P`, `S`, `Z`, `M`, `C`) and
  specific (`Lu`, `Ll`, `Nd`, `Pc`, …);
- a curated set of **binary properties** — at least `Alphabetic`, `White_Space`,
  `Uppercase`, `Lowercase`, `Emoji`, and `Extended_Pictographic` — listed in the
  compiler's documentation;
- **scripts** via `\p{Script=Name}` (e.g. `\p{Script=Greek}`), with the bare
  `\p{Greek}` form accepted as a script shorthand.

Emoji are not `\p{Alphabetic}` (nor `M` / `Nd` / `Pc`), so `\w` does **not** match an
emoji even though emoji are valid in identifiers (§2.3); match emoji with `\p{Emoji}`
or `\p{Extended_Pictographic}`. (Matching a *whole* multi-scalar emoji depends on the
matching unit — see §13.6.)

Property and category names use Unicode loose matching (case, spaces, underscores, and
hyphens are insignificant). A name unrecognized for the bundled version is a
compile-time error in a literal, or a `compile` `Err` (§13.4) for a runtime pattern.
Case-insensitive matching (`(?i)`) uses Unicode simple case folding.

Every regex subject is already a well-formed run-time `Str`. Malformed external
UTF-8 has therefore been converted by §3.1 before matching: each malformed
input byte is observed as one U+FFFD scalar. U+FFFD has its ordinary Unicode
15.0 properties; in particular it is not a `\w` or `\d` character. Regex
matching never exposes or reconstructs the malformed source bytes.

### 13.6 Matching unit

The matching unit is the **Unicode scalar value** (code point). `.`, character classes,
quantifiers, bounded-width lookbehind, and captures all count scalar values; "character"
elsewhere in §13 means one scalar value. Match positions and lengths are measured in
scalar values over the UTF-8 `Str` (§3.1). This keeps matching cheap, predictable, and
stable across Unicode versions.

A multi-scalar grapheme is therefore several units by default: `.` matches one scalar,
so `.` applied to a flag (🇯🇵, two regional indicators), a skin-toned emoji (👍🏽), or a
ZWJ sequence (👨‍👩‍👧‍👦, seven scalars) matches each scalar separately. To match
user-perceived characters, opt in:

- `\X` matches one **extended grapheme cluster** (UAX #29, at the pinned Unicode version
  §13.5) — a base plus its combining marks, a full ZWJ emoji sequence, a flag, and so
  on. So `\X` matches 👨‍👩‍👧‍👦 once, and `\X{3}` matches three grapheme clusters.
- `\p{RGI_Emoji}` matches one complete **RGI emoji sequence** (UTS #51) — the
  recommended-for-interchange emoji, including modifier and ZWJ sequences. Unlike the
  single-scalar `\p{Emoji}` / `\p{Extended_Pictographic}` of §13.5, this is a property
  of *strings* and matches the whole sequence.

The safety is opt-in: the naive `.` and `{n}` split multi-scalar emoji and combining
sequences. Reach for `\X` (or `\p{RGI_Emoji}` for emoji specifically) when clusters must
stay whole — e.g. so a `replace` (§15.3) never emits a broken cluster. Storage is never
normalized implicitly: graphemes are a segmentation view over the preserved scalar
sequence, so `Str` bytes round-trip unchanged.

---

## 14. Text Processing — Grammars

Grammars are the language's signature feature: a `grammar` is a named, reusable,
structured parser built from the same primitives as regexes. Grammars use
ordered-choice (PEG) semantics with backtracking.

### 14.1 Declaration

A `grammar` contains named productions of three kinds:

- `token` — matches a pattern with no implicit whitespace handling; the smallest
  building block.
- `rule` — like `token`, but whitespace between adjacent terms is matched
  automatically (for higher-level structure).
- `regex` — a production that participates in backtracking like a token but is
  written purely as a regex body.

A production named `TOP` is the entry point.

```guji
grammar Email {
    rule  TOP    { <user> '@' <domain> }
    token user   { \w+ }
    token domain { \w+ '.' \w+ }
}
```

Within a production:

- `<name>` references another production in the same grammar (and captures it
  under that name).
- Quoted text (`'@'`) matches a literal.
- All regex syntax from §13.1 is available.
- Alternation between whole productions uses ordered choice: the first
  alternative that matches wins.

### 14.2 Parsing

`GrammarName.parse($input)` returns `Option[Bush]` — a parse tree. A `Bush` is a
node in that tree:

- `$b<name>` reaches the sub-node captured by production `<name>`, of type
  `Option[Bush]` (`None` if that production did not participate). Because a
  grammar's production names are known statically, `$b<name>` is checked at compile
  time for existence, like named access on a regex literal (§13.4).
- `$b.text` is the `Str` span this node matched.
- Descending into a structured production threads through the `Option`: each step is
  `Option[Bush]`, so chain with `and_then` (§15.5) or `match` — e.g.
  `$b<expr>.and_then(sub($e) { $e<term> })`.

A `Bush` is therefore distinct from a regex `Match` (§13.3): a `Match` capture is
flat text (`Option[Str]`), while a `Bush` capture is a sub-tree (`Option[Bush]`)
whose text is reached with `.text`. The named accessor `$x<name>` is shared; its
result type follows the receiver — a `Match` yields `Option[Str]`, a `Bush` yields
`Option[Bush]`.

```guji
match Email.parse("ada@example.com") {
    Some($b) {
        match $b<user> {
            Some($u) { print($u.text) }   # prints "ada"
            None     { () }
        }
    }
    None { print("invalid") }
}
```

A grammar is a **recognizer**: `parse` produces a `Bush` tree of named sub-matches,
and semantic processing — building a typed value, evaluating, or validating — is a
separate pass that walks that tree with `match` (§10). Productions carry no embedded
actions, and matching has no side effects, so a grammar stays a pure, declarative
description. Context-sensitive parsing (decisions that depend on previously parsed
meaning, e.g. "this name must already be declared") is handled in the semantic pass
rather than during the match.

---

## 15. Collections and the Prelude

`List[T]` and `Map[K, V]` are built in. The following functions are available in
every module without import. All follow the data-first convention (§7.2), so all
are usable method-style and chainable.

### 15.1 List functions

| Function                         | Result        | Meaning                                  |
|----------------------------------|---------------|------------------------------------------|
| `map(@xs, $f)`                   | `List[U]`     | apply `$f` to each element               |
| `filter(@xs, $pred)`             | `List[T]`     | keep elements where `$pred` is true      |
| `reduce(@xs, $init, $f)`         | `U`           | fold left into a single value            |
| `each(@xs, $f)`                  | `Unit`        | run `$f` for side effects                |
| `find(@xs, $pred)`               | `Option[T]`   | first element matching `$pred`           |
| `count(@xs)`                     | `Int`         | number of elements                       |
| `is_empty(@xs)`                  | `Bool`        | whether the list has no elements         |
| `sum(@xs)` / `min` / `max`       | `T`           | aggregate numeric lists                  |
| `sort(@xs)` / `sort_by(@xs,$f)`  | `List[T]`     | ordered copy                             |
| `reverse(@xs)`                   | `List[T]`     | reversed copy                            |
| `take(@xs, $n)` / `drop(@xs,$n)` | `List[T]`     | prefix / suffix                          |
| `contains(@xs, $v)`              | `Bool`        | membership test                          |
| `join(@xs, $sep)`                | `Str`         | join string elements with `$sep`         |
| `get(@xs, $i)`                   | `Option[T]`   | element at `$i`, or `None` if out of range |

Indexing `@xs[i]` returns the element directly and **panics** (§11.2) when `i` is out
of bounds; `get` is the checked alternative that yields `None` instead.

A List displays as `[` followed by its elements' recursive display forms in
index order, separated by `, `, and then `]`; the empty List displays as `[]`.
Two Lists are equal exactly when they have the same element type and length and
each pair of elements at the same index is equal. List equality is therefore
order-sensitive and recursive.

`sort` is available when the element type has the natural ordering defined in
§5.2 and returns an ascending ordered copy; it does not add an ordering for
compound values. `sort_by` orders by the callback's `Int`, `Float`, or `Str`
key under the same rules. In particular, sorting strings compares the complete
value, including embedded U+0000.

### 15.2 Map functions

| Function                  | Result          | Meaning                          |
|---------------------------|-----------------|----------------------------------|
| `get(%m, $k)`             | `Option[V]`     | value for key, if present        |
| `set(%m, $k, $v)`         | `Map[K, V]`     | copy with key set                |
| `remove(%m, $k)`          | `Map[K, V]`     | copy with key removed            |
| `keys(%m)` / `values(%m)` | `List[K/V]`     | keys or values                   |
| `has_key(%m, $k)`         | `Bool`          | membership test                  |

In v0, maps are `Str`-keyed: the key type `K` is always `Str`. A map literal
whose key expression is not a `Str`, or a `Map[K, V]` annotation whose key
type is a concrete non-`Str` type, is rejected at compile time. Generalized
key types are deferred (§21).

A Map has one canonical observation order: ascending key order under §5.2.
Map display, `keys`, `values`, and two-binder `for` iteration all use that same
order; `values` and the loop value always remain aligned with their sorted key.
Insertion order, updates, removals, and backing-storage order are not
observable.

A Map displays as `{` followed by its ordered entries separated by `, `, and
then `}`; the empty Map displays as `{}`. An entry is a quoted key, `: `, and
the value's recursive display. Key quoting is deterministic: `"` and `\` become
`\"` and `\\`; newline, tab, carriage return, alert, backspace, form feed, and
vertical tab become `\n`, `\t`, `\r`, `\a`, `\b`, `\f`, and `\v`; other ASCII
control bytes and DEL use lowercase `\xhh`; other Unicode text is emitted as
UTF-8 unchanged. This quoting applies only to Map keys. A `Str` used as a List
element, class field, enum payload, or standalone value remains unquoted.

Two Maps are equal exactly when they have the same key and value types, the same
set of complete `Str` keys, and recursively equal values for every key. Equality
is independent of canonical observation order and insertion/storage order.
`get`, `has_key`, `set`, and `remove` likewise compare complete keys, including
embedded U+0000; the key `"a"` is distinct from a run-time key consisting of
`a`, U+0000, and `b`.

### 15.3 String functions

| Function                       | Result        | Meaning                          |
|--------------------------------|---------------|----------------------------------|
| `split($s, $sep)`              | `List[Str]`   | split on a separator             |
| `lines($s)`                    | `List[Str]`   | split into lines                 |
| `trim($s)`                     | `Str`         | strip surrounding whitespace     |
| `upper($s)` / `lower($s)`      | `Str`         | case conversion                  |
| `replace($s, $re, $template)`  | `Str`         | replace matches via a template (`$0`,`$1`,`$<name>`,`$$`) |
| `replace_with($s, $re, $f)`    | `Str`         | replace matches via a `Match`-to-`Str` function |
| `match($s, $re)`               | `Option[Match]` | regex match (§13.2)            |
| `parse_int($s)`                | `Result[Int, Str]` | parse a base-10 integer    |

In a `replace` template, `$0` is the whole match, `$1`…`$9` are positional groups,
`$<name>` is a named group, and `$$` is a literal `$`; write templates as
single-quoted strings (§12) so these tokens are not consumed by string
interpolation. Use `replace_with` when the replacement must be computed from the
match. Build patterns dynamically with `Regex.compile` (§13.4).

A template token for a group that did not participate, or that the pattern does not
define, substitutes the empty string; any `$` not followed by a digit, `<name>`, or
`$` stands for a literal `$`. A template therefore never fails at run time. When the
template and the regex are **both** literals, the compiler instead rejects an
out-of-range or unknown group reference, and an unterminated `$<…`.

`split($s, $sep)` divides `$s` at each non-overlapping occurrence of the literal
separator `$sep`, returning the text between separators; `$n` separators therefore
yield `$n + 1` pieces, and a separator at either end contributes an empty piece.
Splitting on the empty separator `""` yields the individual characters (Unicode
scalar values, §3) of `$s`.

Arguments supplied to string functions are already well-formed `Str` values
under §3.1. Malformed external bytes have therefore become individual U+FFFD
scalars before `split`, `lines`, trimming, case conversion, replacement, or
parsing begins.

`lines($s)` splits a string into its lines, **chomping** the terminators rather than
keeping them. Six behaviours define it:

- **Terminators are stripped.** Each returned `Str` is one line's content without
  its trailing newline.
- **A final terminator adds no empty line.** `"a\nb\nc\n"` yields
  `["a", "b", "c"]` — three lines, with no trailing `""` for the final newline.
- **The empty string yields no lines.** `""` → `[]` (zero lines).
- **A lone terminator yields one empty line.** `"\n"` → `[""]` — one line, the empty
  string.
- **Blank interior lines are kept.** `"a\n\nb"` → `["a", "", "b"]` (three lines).
- **A carriage return is normalized.** A `\r\n` pair, or a lone `\r` (carriage
  return, U+000D), terminates a line, and the carriage return is never part of the
  yielded line — so a CRLF-terminated text splits into the same lines a LF-terminated
  one would. Carriage returns reach `lines` from runtime text such as files or
  standard input; a double-quoted string literal cannot write one, as there is no
  `\r` escape (§12).

The streaming Handle form `$h.lines()` (§15.4) applies these exact rules to a
handle's text, delivering each chomped line over a `Chan[Str]`.

Membership of the form "is `$x` one of these values" is expressed with
`contains`/`has_key`, e.g. `["admin", "mod"].contains($role)`. There is no
special set-membership operator.

### 15.4 IO functions

| Function          | Result  | Meaning                                              |
|-------------------|---------|------------------------------------------------------|
| `print($value)`   | `Unit`  | write the display form of `$value` and a newline to **stdout** |
| `note($value)`    | `Unit`  | write the display form of `$value` and a newline to **stderr** |
| `exit($code: Int)`| `Never` | flush stdout, then terminate the program with exit status `$code` |
| `args()`          | `List[Str]` | command-line arguments, excluding the program/source name |
| `read_file($path: Str)` | `Result[Str, Str]` | read a whole file as text without chomping, or an error message |
| `write_file($path: Str, $content: Str)` | `Result[Unit, Str]` | truncate-or-create a file and write the exact `Str` |
| `append_file($path: Str, $content: Str)` | `Result[Unit, Str]` | append the exact `Str`, creating the file if absent |
| `open($path: Str)` | `Result[Handle, Str]` | open a text input handle, or an error message |
| `create($path: Str)` | `Result[Handle, Str]` | open a text output handle, truncating or creating the file |
| `stdin`           | `Handle` | the always-open standard-input handle (a value, not a call) |
| `stdout`          | `Handle` | the always-open standard-output handle (a value, not a call) |
| `stderr`          | `Handle` | the always-open standard-error handle (a value, not a call) |
| `$h.slurp()`      | `Str`   | read the remaining text without chomping |
| `$h.lines()`      | `Chan[Str]` | read remaining `Handle` text as chomped lines |
| `$h.write($s: Str)` | `Unit` | write the exact `Str`, with no added newline |

The **display form** is recursive and deterministic but is intended for people,
not as a parser or serialization format. `Str` displays as its text without
quotes; `Int`, `Float`, `Bool`, and Unit use their ordinary scalar spellings.
Lists and Maps use §§15.1-15.2, classes use §8, and enums use §9, including at
arbitrary nesting depth. Consequently a `Str` nested as a value remains
unquoted; only a Map key receives the escaping required by §15.2.

`print` and `note` are display twins: both render this same display form and add
one newline, differing only in the destination stream. `note` is for
diagnostics that must not pollute the program's stdout (e.g. the data a
downstream tool consumes). Output to stdout and stderr is independently
ordered; a program that must interleave them deterministically should not rely
on cross-stream ordering.

`exit($code)` ends the program immediately with the given status (`0` means
success). Like `panic` (§11.2) it is `Never`-typed — it yields no value, so it
may stand in any branch or expression position without constraining the result
type — and it flushes buffered stdout before terminating so preceding `print`
output is never lost. Unlike `panic`, the status is caller-chosen rather than a
fixed failure code, and `exit` writes no message of its own. A `main` that falls
off its end (or returns `Unit`) still exits `0`; a `main` returning an `Int` uses
that value as the status, so `exit($n)` and `return $n` from `main` agree.

`args()` returns the command-line arguments supplied after the source path (for
interpreted runs) or after the native executable name (for compiled runs). The
program/binary name and the source file path are excluded. Arguments are kept
as individual `Str` values, including empty-string arguments; no shell parsing,
quoting, or expansion is performed by guji. Each argument is converted from the
operating system's bytes by §3.1 before it is exposed.

All paths in §15.4 are `Str` paths resolved relative to the process's current
working directory unless they are absolute. The IO API is text-only in v0:
contents become well-formed UTF-8 `Str` values, and a dedicated binary/bytes
path is deferred. Every input boundary uses §3.1's exact lossy conversion:
valid UTF-8 and U+0000 are preserved, while each malformed input byte becomes
one U+FFFD. This conversion happens once, when external bytes enter Guji; later
string operations do not repeat it.
Operating-system path interfaces cannot represent U+0000. A path containing
U+0000 is rejected before any file operation and yields that operation's
documented `Err`, with the complete counted path retained in the error `Str`.
When an IO operation can fail, its error is intentionally a bare `Str` that names
the path but **not** the operating-system reason; a structured IO error type
carrying the underlying cause is deferred, and OS-reason-free messages keep the
interpreter and the native compiler byte-identical.

`read_file($path)` reads the entire contents of the file at `$path` and yields
`Ok($content)`, where `$content` is §3.1-converted text. Line terminators are
preserved and nothing is chomped, so a file ending in a newline yields a `Str`
ending in a newline. Valid UTF-8 bytes, including embedded NUL, are otherwise
unchanged. When the file cannot be read, it yields
`Err("cannot read file: " + $path)`. `read_file` is the whole-file convenience
over the handle API; reading does not change the file.

`write_file($path, $content)` truncates the file at `$path` if it exists, or
creates it if it does not, writes the exact UTF-8 representation of `$content`,
and yields `Ok(())`. It adds no newline and performs no display conversion;
embedded NUL is written as its one zero byte. If the file cannot be written, it
yields `Err("cannot write file: " + $path)`.

`append_file($path, $content)` opens the file at `$path` for appending, creating
it if it does not exist, writes the exact UTF-8 representation of `$content` at
the end, and yields `Ok(())`. It adds no newline and performs no display
conversion. If the append cannot be performed, it yields
`Err("cannot append file: " + $path)`.

`Handle` is the built-in text IO handle type. A handle may be readable, writable,
or both; v0 exposes read-only handles (`stdin`, `open`) and write-only handles
(`stdout`, `stderr`, `create`). Compile-time read/write capability tracking is
deferred. In alpha, using the wrong operation for a handle's capability is a
runtime error: `$h.write($s)` on a read-only handle aborts, and `$h.slurp()` or
`$h.lines()` on a write-only handle aborts.

The display form of a `Handle` is the legacy alpha string `<reader>`, even for
write-only handles. Programs should not depend on this spelling; it is retained
only for byte compatibility during v0 alpha.

`open($path)` opens the file at `$path` for reading and yields `Ok($h)`, or
`Err("cannot open file: " + $path)` if the file cannot be opened.

`create($path)` opens the file at `$path` for writing and yields `Ok($h)`,
truncating the file if it exists or creating it if it does not. The handle is
write-only. If the file cannot be created, it yields
`Err("cannot create file: " + $path)`.

`$h.slurp()` reads all remaining text from a readable handle, applies §3.1 once,
and returns the resulting `Str`: line terminators are preserved and nothing is
chomped.

`$h.write($s)` writes the exact UTF-8 representation of `$s` to a writable
handle and returns `()`. It adds no newline, performs no display conversion,
and flushes the write so a same-program read-after-write round trip can observe
the bytes, including embedded NUL.

`stdin`, `stdout`, and `stderr` are already-open `Handle` values referenced by
their bare names (they are values, not calls, so there are no parentheses).
`stdin` is readable and exposes the read operations; `stdout` and `stderr` are
writable and expose `write`. `stdin.slurp()` reads all of standard input
with §3.1 conversion (terminators intact, nothing chomped), exactly like
slurping a file handle. Standard input is a single stream, so its contents are
consumed as they are read: once a `slurp` has drained it, a further `slurp` of
`stdin` yields `""`. The standard handles are never explicitly closed by the
program.

`$h.lines()` reads the remaining text from that handle and returns a
`Chan[Str]`. Each delivered string is one chomped line using the same line
splitting rules as §15.3 `Str.lines()`: line terminators are stripped, a final
terminator does not produce an extra empty line, blank middle lines are kept,
and CRLF is normalized so the `\r` is not part of the yielded line. The channel
is closed after the final line, so `for $line in $h.lines()` terminates at EOF.
Lossy UTF-8 conversion occurs before line splitting, not separately per line.

### 15.5 Option and Result functions

`Option[T]` and `Result[T, E]` (§11) carry functions for transforming and unwrapping
them without an explicit `match`. All follow the data-first convention (§7.2), so they
are usable method-style and chainable; `$f` arguments are functions (lambdas, §7.4).

For `Option[T]`:

| Function | Result | Meaning |
|---|---|---|
| `is_some($o)` / `is_none($o)` | `Bool` | whether it is `Some` / `None` |
| `unwrap($o)` | `T` | the value, or **panic** if `None` (§11.2) |
| `expect($o, $msg)` | `T` | the value, or panic with `$msg` |
| `unwrap_or($o, $default)` | `T` | the value, or `$default` |
| `unwrap_or_else($o, $f)` | `T` | the value, or the result of `$f()` |
| `map($o, $f)` | `Option[U]` | apply `$f` to a `Some` value |
| `and_then($o, $f)` | `Option[U]` | flat-map: `$f` returns an `Option` |
| `or($o, $other)` | `Option[T]` | itself if `Some`, else `$other` |
| `filter($o, $pred)` | `Option[T]` | keep the `Some` only if `$pred` holds |
| `ok_or($o, $err)` | `Result[T, E]` | `Some(v)` → `Ok(v)`, `None` → `Err($err)` |

For `Result[T, E]`:

| Function | Result | Meaning |
|---|---|---|
| `is_ok($r)` / `is_err($r)` | `Bool` | whether it is `Ok` / `Err` |
| `unwrap($r)` | `T` | the `Ok` value, or **panic** with the error (§11.2) |
| `expect($r, $msg)` | `T` | the `Ok` value, or panic with `$msg` |
| `unwrap_or($r, $default)` | `T` | the `Ok` value, or `$default` |
| `unwrap_or_else($r, $f)` | `T` | the `Ok` value, or the result of `$f($error)` |
| `map($r, $f)` | `Result[U, E]` | apply `$f` to an `Ok` value |
| `map_err($r, $f)` | `Result[T, F]` | apply `$f` to an `Err` value (adapt `E`) |
| `and_then($r, $f)` | `Result[U, E]` | flat-map: `$f` returns a `Result` |
| `or_else($r, $f)` | `Result[T, F]` | on `Err`, `$f($error)` returns a `Result` |
| `ok($r)` | `Option[T]` | `Ok(v)` → `Some(v)`, `Err` → `None` |
| `err($r)` | `Option[E]` | `Err(e)` → `Some(e)`, `Ok` → `None` |

These make `?` (§11.1) the common path and `match` the exception, e.g.
`$count.unwrap_or(0)` or `read($path).map_err(sub($e) { Io($e) })?`.

### 15.6 Process spawning

guji can run an external operating-system program and capture its result. This is
the platform capability a self-hosting compiler uses to invoke a C toolchain
(`cc`) on generated C.

| Function | Result | Meaning |
|---|---|---|
| `run($cmd: Str, $args: List[Str])` | `Result[Proc, Str]` | run `$cmd` with `$args`, wait for it, and capture its result |

`Proc` is the built-in record describing a finished process:

```guji
class Proc {
  has $.exit_code: Int
  has $.stdout: Str
  has $.stderr: Str
}
```

`Proc` is an ordinary readable record — its three fields are public, so
`$p.exit_code`, `$p.stdout`, and `$p.stderr` read like any class field (§8). It
carries no methods; programs inspect the fields directly.

`run($cmd, $args)` spawns the program named by `$cmd`, waits for it to finish
(it is **synchronous and blocking**), and yields its result. Spawning is
**shell-free**: `$cmd` is resolved against `PATH` like `execvp`, and `$args` is
the explicit argument vector — guji performs no globbing, word-splitting,
quoting, or variable expansion, so an empty-string argument is passed through
verbatim. By convention the spawned program's own argv is `[$cmd] ++ $args` (the
program name followed by the supplied arguments); `$args` does **not** include
the program name.

Operating-system process interfaces cannot represent U+0000 in a command or
argument. If `$cmd` or any element of `$args` contains U+0000, no process is
started and `run` yields `Err("cannot run command: " + $cmd)`; the complete
counted command is retained in that error `Str`.

The child's standard output and standard error are captured separately and
converted by §3.1 into the `$.stdout` and `$.stderr` fields. Nothing is chomped
or display-converted. Valid UTF-8 bytes are retained exactly, including interior
NUL; each malformed byte becomes one encoded U+FFFD. Capture is therefore
NUL-safe and text-preserving, not a raw-byte channel. `$.exit_code` is the
child's exit status. A process that terminates by exit code `n` yields
`$.exit_code == n`; a process killed by signal `s` yields
`$.exit_code == 128 + s` (the conventional shell encoding), pinned so the
interpreter and the native compiler agree.

`run` distinguishes *the process failing* from *the process never starting*:

- **`Ok($proc)` whenever the process actually ran**, regardless of its exit code.
  A non-zero exit is a successful run that the program chose to fail (a `cc` that
  could not compile its input exits non-zero but still *ran*); the caller decides
  what a non-zero `$.exit_code` means by inspecting it.
- **`Err($msg)` only when the process could not be spawned at all** — the command
  was not found on `PATH` (ENOENT) or could not be executed (permission denied).
  The error is a fixed, OS-agnostic `Str`: `"cannot run command: " + $cmd`. As
  with the §15.4 IO errors, it names the command but **not** the operating-system
  reason, so the message is byte-identical between the interpreter and the native
  compiler.

---

## 16. Visibility and Modules

### 16.1 Modules

A source file is a module. A module's path is its file path relative to the
project root, with `/` written as `::`.

```guji
import text::email
import util::lists

$m = email::Email.parse($input)
```

An `import` brings a module into scope under its final path segment; members are
accessed with `::`. (A future revision may add selective imports; for v0,
qualified access is the single mechanism.)

### 16.2 Top-level visibility

Top-level declarations (`sub`, `class`, `enum`, `grammar`) are **private to
their module** by default. Prefix a declaration with `pub` to export it:

```guji
pub sub area($s: Shape): Float { ... }   # visible to importers
sub helper($x: Int): Int { ... }         # module-private
```

Visibility is therefore governed by two complementary mechanisms, each at its own
level: `pub` controls what a module exposes; field twigils (`$.` / `$!`, §8.1)
control what a class exposes. Identifier casing carries no visibility meaning.

`pub` declarations must fully annotate their parameter and return types (§3.4).

#### Top-level names are unique (no overloading)

guji has no overloading, so each **user-introduced top-level value name** may be
defined only once. Two top-level `sub`s with the same name, or a top-level `sub`
whose name equals an `import` alias (an `import a::b` binds the value name `b`,
§16.1), are **compile-time errors**, reported identically by the interpreter and
the native compiler.

Shadowing a **prelude builtin** (§15) with a top-level `sub` is permitted: a
user `sub sum` or `sub find` provides the sole definition of that name in the
module, and calls resolve to it consistently. This mirrors ordinary shadowing
(§4) — a name may shadow a binding from an enclosing scope (here, the implicit
prelude scope) — and is distinct from defining the same name twice in one scope.
PascalCase type names (`class`/`enum`/`grammar`/variant, §2.3) occupy a separate
namespace from lowercase value names and never collide with a `sub`.

---

## 17. Concurrency

**Status.** Concurrency is **implemented** in both engines (the v1 memory &
concurrency pass); it is no longer a post-v0 reservation. The interpreter, the static
checker, and the native compiler all implement the channel surface: `Chan[T]` is a
real type, `channel()` infers its element type from context (§17.2), the data-first
`send`/`recv`/`close` methods type as in §17.3, `hatch` bodies are checked (capturing
a `mut` binding is rejected, §17.1) and run concurrently, `for` over a channel binds
the element type and drains it (§17.4), the `Closed` error type (§17.3) is built in,
`select` (§17.5) chooses among ready channel arms (with an optional `else`), and the
§17.6 all-tasks-blocked deadlock detector panics identically under both engines. The
native runtime schedules tasks on per-task reference-counted heaps with copy-on-send
channels (RFC-003 §7). The only native limits that remain are the general
deeply-nested value-shape limits shared with non-concurrent code (e.g. some depth-3
`List`/`Map` element types, and channels of complex element type passed as `sub`
parameters/returns); these are reported as clear codegen diagnostics, never
miscompiled, and are not specific to §17.

guji's concurrency model follows Go's goroutines-and-channels (CSP), with one guji
change: ordinary guji values captured by a task or crossing a channel are immutable
(§4), and channel payloads are detached from the sender. A guji binding therefore
cannot be used as shared mutable user data. Channel control blocks and external
effects are runtime-mediated shared resources; programs use channels when they need
ordering between tasks.

Tasks are logical units of concurrent work. Their cost and their mapping to operating
system threads, worker pools, fibers, or another runtime mechanism are implementation
details. Programs cannot inspect or rely on that mapping.

> Implementation note: the design below is part of the language. It depends on the
> runtime scheduler and was built after the core pipeline (§19), so it did not block
> the evaluator/compiler milestones; it now runs on the reference-counted per-task
> heap model (RFC-003 §7) in both the interpreter and native binaries.

### 17.1 Tasks

`hatch { ... }` starts a new task that runs the block concurrently and returns
immediately, yielding `()`:

```guji
hatch {
    print("running in another task")
}
```

The block is a closure (§7.4) and may capture **immutable** bindings from its enclosing
scope; capturing a `mut` binding (§4) is a compile-time error. To hand a current value
to a task, bind it immutably first or send it over a channel. Because every captured
value is therefore immutable, a task can never observe another task mutating shared
data. Tasks are fire-and-forget; coordinate them and collect results through channels
(§17.2), not through a task handle.

**Program exit.** When `main` returns, the process terminates immediately; live tasks
are not waited for, and any output they have not yet produced is simply never produced
(Go's rule). A program that needs a task's result or side effects must synchronize
with the task — receive from a channel it sends on, or rendezvous on an unbuffered
channel — before `main` returns. There is no implicit join.

### 17.2 Channels

A channel carries values of one type between tasks. `channel()` builds one:

```guji
$ch: Chan[Int] = channel()      # unbuffered (synchronous rendezvous)
$buf: Chan[Str] = channel(16)   # buffered, capacity 16
```

- An **unbuffered** channel rendezvouses: a `send` blocks until another task `recv`s.
- A **buffered** channel holds up to `$capacity` values; `send` blocks only when the
  buffer is full, `recv` only when it is empty.

`Chan[T]` is a built-in type (§3.1). A channel is a first-class value: it may be stored,
passed to subs and tasks, and sent over other channels.

`channel()` itself carries no element type; the context of the call must determine
`T` — a binding annotation (`$ch: Chan[Int] = channel()`), a `pub` sub's declared
parameter or return type the call flows into, or any other position whose expected
type is a concrete `Chan[T]`. If no surrounding context fixes `T`, the program is
ill-typed: the checker reports a static "cannot infer channel element type" diagnostic
and the fix is to annotate. There is no default element type and no deferred runtime
inference.

A channel value is an opaque handle. Its display form is `<chan>`. Equality is handle
identity: two aliases of the same channel compare equal, while separately-created
channels compare unequal; comparison does not inspect buffered values or closed state.

### 17.3 Send, receive, close

All three are data-first methods (§7.2):

| Call | Result | Meaning |
|---|---|---|
| `$ch.send($v)` | `Result[Unit, Closed]` | deliver `$v`; `Err(Closed)` if the channel is closed |
| `$ch.recv()` | `Option[T]` | next value as `Some`, or `None` once closed and drained |
| `$ch.close()` | `Result[Unit, Closed]` | close the channel; `Err(Closed)` if already closed |

`Closed` is a built-in type (§3.1) with exactly one value, also written `Closed` —
a unit-like error type, analogous to `None` but carrying "the channel is closed" as
its meaning. It exists so the channel operations' only failure mode fits
`Result[Unit, Closed]` (§11) without inventing a payload. In `match`, `Closed` is a
bare nullary pattern, used inside `Err`:

```guji
match $ch.send($v) {
    Ok(())      { print("delivered") }
    Err(Closed) { print("receiver is gone") }
}
```

`recv` returning `Option[T]` folds Go's "value, ok" pair into guji's standard sum type:
`None` means "closed and empty." Where Go *panics* — sending on a closed channel, or
double-closing — guji returns an `Err` instead, since guji has no exceptions (§11). By
convention only the sending side closes a channel, and only to signal "no more values";
closing is unnecessary for a channel that is simply abandoned.

```guji
$jobs: Chan[Int] = channel()
hatch {
    for $n in [1, 2, 3] { $jobs.send($n) }
    $jobs.close()
}
match $jobs.recv() {
    Some($n) { print("got $n") }
    None     { print("done") }
}
```

### 17.4 Ranging over a channel

`for` (§6.3) over a channel receives values until the channel is closed and drained:

```guji
for $job in $jobs {
    handle($job)
}
# the loop ends when $jobs is closed
```

### 17.5 `select`

`select` waits on several channel operations and runs one ready arm. If several arms
are ready, the choice is unspecified; source order does not grant priority, and no
fairness between repeatedly-ready arms is guaranteed. Each arm is a channel operation
followed by a block:

```guji
select {
    $v = $in.recv()  { handle($v) }     # $v : Option[T] (None once $in is closed)
    $out.send($x)    { print("sent") }   # ready when the send can proceed
    else             { print("idle") }   # optional: non-blocking poll
}
```

Without an `else`, `select` blocks until an arm is ready. With `else`, it runs the
`else` block immediately when no operation is ready. A `recv` arm binds the `Option[T]`
the receive yields (so a closed channel makes its arm ready, binding `None`). A `send`
arm on a **closed** channel likewise becomes ready: its operation completes with
`Err(Closed)` (it never blocks forever on a channel nobody will drain), and the bound
name — if the arm binds one — receives that `Result[Unit, Closed]`. `select` is a
statement yielding `()`.

### 17.6 The runtime

Guji specifies observable task and channel behavior, not a scheduler topology. A
runtime may use one operating-system thread per task, multiplex tasks over a worker
pool, or use another strategy, and may change strategies without changing the
language. A runnable task needed to complete a channel operation remains eligible to
run while another task is blocked on `send`, `recv`, or a `select` without `else`.
Parent and child start order, runnable-task interleaving, preemption, bounded
scheduling latency, and fairness are otherwise unspecified. Programs synchronize
through the channel rules above rather than depending on incidental scheduling order.
The runtime remains part of the single self-contained binary (§18); there is no
separate runtime to install.

**Deadlock.** If every live guji task — including the main task — is stably blocked on
a channel operation and no channel operation can make progress, the runtime writes
`panic: all tasks are blocked — deadlock` followed by a newline to standard error and
terminates the process with exit status 1. The detection covers only this global
all-tasks-blocked state. A subset of tasks may remain blocked while another task runs;
that is not a deadlock, and §17.1 still applies when `main` returns without joining
those tasks.

> Implementation note: the maintained v2-alpha runtime currently uses one joinable
> pthread per task, reaps completed threads, and implements channels with locked
> control blocks and detached message payloads on per-task reference-counted heaps
> (RFC-003 §7). None of that topology is a language guarantee.

---

## 18. Compilation Model

- **Static, fully checked.** All types are resolved and checked at compile time;
  there is no runtime type information required for dispatch.
- **Inferred.** Most annotations are optional (§3.4).
- **Ahead-of-time, native.** The compiler emits a single self-contained native
  executable. There is no separate runtime to install.
- **Entry point.** Execution begins at `sub main()`. `main` may return `Unit`
  or `Int` (an `Int` return is the process exit code).

The reference pipeline is: source → tokens → syntax tree → typed tree (inference
+ checking) → intermediate code → native executable. (§19 sequences how this is
built.)

---

## 19. Implementation Roadmap

The v0 implementation is built in this order. Each stage is independently
testable.

1. **Lexer.** Source text → token stream. Tokens: identifiers, sigil-names,
   keywords, literals, operators, punctuation, comments, newlines.
2. **Parser.** Tokens → syntax tree, per the grammar in §20. Produce clear
   syntax-error messages with source positions.
3. **Tree-walking evaluator.** Execute the syntax tree directly. This makes the
   language runnable early and is where semantics are validated. Target: small
   programs (arithmetic, bindings, `sub`, `if`, `match`, `class`, `enum`,
   lists/maps, the prelude) run correctly.
4. **Type checker + inference.** Annotate the tree with types; enforce §3, §10.3
   exhaustiveness, and `?`-operator rules (§11.1).
5. **Code generation.** Lower the typed tree to intermediate code and emit a
   native executable (§18).
6. **First-class regex** (§13).
7. **Grammars** (§14) — the signature feature, built on the regex engine.

Modules/imports (§16) are v0 scope and build on the seven stages above: the loader
resolves the import closure, each module passes the same pipeline, and the checker
enforces `pub` across module boundaries. Concurrency (§17) was **not part of the v0
milestone**; it requires the task scheduler and was built after the seven stages
above, as the v1 memory & concurrency pass. The type `Chan[T]`, `channel()`, channel
operations, channel `for`, and the `hatch`/`select` keywords were reserved from the
start (§2.5, §3.1) so the language did not change shape as concurrency arrived; they
are now implemented in the interpreter, the static checker, and the native compiler.

### 19.1 Testing strategy

- **Lexer:** assert exact token streams for sample inputs.
- **Parser:** assert syntax-tree shape (compare a canonical printed form).
- **Type checker:** assert that valid programs check and invalid ones produce the
  expected errors (including missing-`match`-case and unannotated-`pub` errors).
- **Evaluator / end-to-end:** a directory of `.guji` programs each paired with
  expected output; run all on every change. This is the primary regression net.
- A read-eval-print loop (REPL) over the evaluator is provided from stage 3 for
  manual exploration.

---

## 20. Formal Grammar (core)

EBNF for the v0 surface syntax. `{ X }` means zero-or-more; `[ X ]` means
optional; `|` is alternation; quoted text is literal.

```ebnf
program     = item_gap { import item_gap } { decl item_gap } ;

import      = "import" module_path ;
module_path = ident { "::" ident } ;

decl        = [ "pub" ] ( sub_decl | class_decl | enum_decl | grammar_decl ) ;

sub_decl    = "sub" ident [ type_params ] "(" [ params ] ")" [ ":" type ]
              ( block | "=" expr ) ;
params      = param { "," param } ;
param       = sigil_name [ ":" type ] ;
type_params = "[" Pascal { "," Pascal } "]" ;

class_decl  = "class" Pascal "{" item_gap
              { ( has_field | sub_decl ) item_gap } "}" ;
has_field   = "has" field_name [ ":" type ] ;
field_name  = sigil "." ident | sigil "!" ident ;

enum_decl   = "enum" Pascal [ type_params ] "{" { sep }
              { ( variant | sub_decl ) { sep } } "}" ;
variant     = Pascal [ "(" params ")" ] ;

grammar_decl = "grammar" Pascal "{" item_gap
               { production item_gap } "}" ;
production   = ( "rule" | "token" | "regex" ) ident "{" rx_body "}" ;

type        = Pascal [ "[" type { "," type } "]" ] ;

block       = "{" item_gap { stmt item_gap } "}" ;
stmt        = sub_decl | binding | expr_stmt | for_stmt | while_stmt
            | return_stmt | hatch_stmt | select_stmt ;
binding     = [ "mut" ] sigil_name [ ":" type ] "=" expr ;
expr_stmt   = expr ;
for_stmt    = "for" for_binding "in" expr block ;
for_binding = sigil_name | sigil_name "," sigil_name ;
while_stmt  = "while" expr block ;
return_stmt = "return" [ expr ] ;
hatch_stmt  = "hatch" block ;
select_stmt = "select" "{" item_gap
              { select_arm item_gap } [ "else" block item_gap ] "}" ;
select_arm  = [ sigil_name "=" ] expr block ;   (* channel op, then block *)

expr        = match_expr | if_expr | lambda | binary ;

if_expr     = "if" expr block { "else" "if" expr block } [ "else" block ] ;
match_expr  = "match" expr "{" item_gap { arm item_gap } "}" ;
arm         = pattern [ "if" expr ] block ;

pattern     = pattern_literal
            | "_"
            | sigil_name
            | Pascal [ "(" pattern { "," pattern } ")" ] ;
pattern_literal = int | float | string | "true" | "false" | "(" ")" ;

lambda      = "{" item_gap { stmt item_gap } "}"     (* topic block, param $_ *)
            | "sub" "(" [ params ] ")" block ;       (* anonymous sub *)

binary      = unary { binop unary } ;                (* precedence per §5.5 *)
unary       = [ "!" | "-" ] postfix ;
postfix     = primary { call | index | field | capture | "?" } ;
call        = "(" [ args ] ")" ;
index       = "[" expr "]" | "{" expr "}" ;
field       = "." ident ;
capture     = "<" ident ">" ;
args        = arg { "," arg } ;
arg         = [ ident ":" ] expr ;                   (* named args for ctors *)

primary     = literal
            | ident                                  (* ordinary sub value *)
            | sigil_name
            | Pascal                                 (* type / variant ref *)
            | regex_literal
            | "(" expr ")"
            | "(" ")" ;                              (* unit *)

literal     = int | float | string | "true" | "false"
            | list_literal | map_literal ;
list_literal = "[" [ expr { "," expr } ] "]" ;
map_literal  = "{" [ pair { "," pair } ] "}" ;       (* value position *)
pair        = expr ":" expr ;

sigil       = "$" | "@" | "%" ;
sigil_name  = sigil ident ;
binop       = "+" | "-" | "*" | "/" | "%" | "**" | "~"
            | "==" | "!=" | "<" | "<=" | ">" | ">="
            | "&&" | "||" | "~~" | ".." | "..<" ;
item_sep    = newline | ";" ;
item_gap    = { item_sep } ;
sep         = item_sep | "," ;
```

**Parser notes.**

- *Map vs. block.* A `{ ... }` in **value/expression position** whose entries are
  comma-separated `key: value` pairs (or which is empty) is a map literal; a
  `{ ... }` introduced by `sub`, `class`, `enum`, `grammar`, `if`, `else`, `for`,
  `while`, or `match` is a block. The parser resolves the ambiguity by position and
  by the lambda-vs-map argument rule below.
- *Map pair vs. annotated binding.* A map pair is `expr : expr`; a binding is
  `[ "mut" ] sigil_name [ ":" type ] "=" expr`. They are distinguished by the `=`:
  a value-position `{ ... }` that contains an `=` assignment is a block/lambda,
  never a map.
- *Lambda vs. map argument.* A `{ ... }` passed as a call argument is a topic-block
  lambda when it contains statements (and no `key: value` pairs); a call argument of
  `key: value` pairs is a map literal. The empty `{}` call argument is the empty map;
  an empty parameterized lambda is written `sub() { }`.
- *Sub declaration vs. anonymous-`sub` lambda.* After `sub`, an identifier begins a
  named declaration (`sub_decl`); a `(` begins an anonymous-`sub` lambda (an
  expression, §7.4). In a block the named form is a declaration statement; the
  `decl`-only optional `pub` means a local `sub_decl` cannot be public. A named
  `sub` whose first parameter is `$self` is a method; one without `$self` declared
  in a `class`/`enum` body is an associated function (§7.5), called as
  `TypeName.func(args)` — an ordinary postfix `field` + `call`, not a data-first
  method call.
- *Separators and layout.* `item_sep` represents physical newline and `;` as
  distinct tokens; `item_gap` permits runs or an inferred zero-width boundary
  between syntactically complete items (§2.7). The EBNF elides a contextual
  layout rule: within source `(...)` and `[...]` delimiters, and within
  expression-map `{...}` and braced-interpolation delimiters, a physical newline
  may occur between any two grammar symbols. A nested block, topic-block lambda,
  declaration body, match-arm body, or select body instead uses `item_gap`.
  Newlines also continue immediately after `binop` and before a required body
  brace or `else`; a `;` is never consumed by any layout rule.
- *`rx_body`.* The regex/grammar production body (§13.1, §14.1) is lexed in a
  dedicated regex mode and is not further specified in this core grammar. Two
  constructs switch the lexer out of that mode: a `<{ expr }>` splice (§13.4) lexes its
  body as a normal expression, and a `<name>` subrule reference (§14.1) lexes an
  identifier; both return to regex mode at the closing `>` or `}`.
- *Identifiers.* `ident` and `Pascal` are the lexical identifier classes of §2.3 —
  `ident` is `snake_case` and may include emoji; `Pascal` is `PascalCase`. The exact
  token classes (including emoji sequences) are fixed by the lexer (§19, stage 1) and
  left as terminals here.

---

## 21. Deferred (explicitly out of scope for v0)

The following are intentionally **not** in v0. They are recorded so the
implementation does not accidentally depend on or preclude them.

- **Traits / interfaces.** A lightweight, stateless mechanism for "any type that
  supports these operations." To be designed after the core; v0 has no
  user-defined polymorphism beyond generics.
- **Lazy / infinite sequences.** Evaluation is strict in v0. Opt-in lazy streams
  may be added later as an explicit construct (not lazy-by-default).
- **Refinement constraints** (e.g. "an `Int` that is positive"). Possible later
  as runtime-checked contracts.
- **Selective / aliased imports.** v0 has whole-module import with qualified
  access only.
- **Concurrency.** No longer deferred: `hatch`, `Chan[T]`, channel `for`, and
  `select` (§17) left this list when the v1 memory & concurrency pass began;
  §17's status note tracks what is implemented.
- **Generalized map key types.** v0 maps are `Str`-keyed (§15.2); `Map[K, V]`
  with a non-`Str` key awaits a value-equality/hashing design for compound and
  user-defined keys.

These are deferrals, not rejections. Two features were considered and
**rejected** outright to preserve "one obvious way": dispatch chosen by the types
of multiple arguments (covered by `match` over sum types), and implicit
multi-value "superposition" operands (covered by explicit membership tests).
