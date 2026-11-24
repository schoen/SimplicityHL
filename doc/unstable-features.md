# Unstable features

Unstable features are experimental compiler capabilities. They may change
or be removed before stabilization.

## Viewing available unstable features

Run `simc --help`; the features are listed under the `-Z` flag.

## Enabling an unstable feature

Pass `-Z <feature-name>` to `simc`.

## `raw_hash`

`raw_hash::<T>(tuple)` hashes a tuple of unsigned integers with SHA-256:

```rust
let digest: u256 = raw_hash::<(u8, u256)>((0x02, public_key));
```

This is the same as:

```rust
let ctx: Ctx8 = jet::sha_256_ctx_8_init();
let ctx: Ctx8 = jet::sha_256_ctx_8_add_1(ctx, 0x02);
let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, public_key);
let digest: u256 = jet::sha_256_ctx_8_finalize(ctx);
```

In particular, the type parameter selects which `add_N` jets run; the digest does not
commit to it. `raw_hash::<(u8, u8)>((0x01, 0x02))` and `raw_hash::<(u16,)>((0x0102,))`
produce the same digest, as does any other type with the same bytes, such as an alias
of `u32` versus a plain `u32`. If your protocol needs the digest to be unambiguous,
commit to the type yourself, for example by hashing a domain-separation tag first.

## `infix_operators`

Operators on booleans and unsigned integers:

| Operators | Operand types | Result type |
| --- | --- | --- |
| `==` `!=` | `bool` and every unsigned integer type | `bool` |
| `<` `<=` `>` `>=` | every unsigned integer type | `bool` |
| `&` `\|` `^` | `bool` and every unsigned integer type | the operand type |
| `&&` `\|\|` | `bool` | `bool` |
| `!` (prefix) | `bool` | `bool` |

Both operands of a binary operator must have the same type.

```rust
fn is_in_range(x: u32, low: u32, high: u32) -> bool {
    low <= x && x < high
}
```

Where a jet exists for the operator and type, the operator compiles to it, so
`a < b` on `u8` values is the same as `jet::lt_8(a, b)`, and `a & b` is the same as
`jet::and_8(a, b)`. For other types, the compiler builds the operation from
other jets. For example, `u2` and `u4` values are extended to `u8`, `<` on
`u128` and `u256` values subtracts them in 64-bit parts, and `!=` is the
complement of `==`.

### Precedence

From the tightest binding to the loosest:

1. `!`
2. `&`
3. `^`
4. `|`
5. `==` `!=` `<` `<=` `>` `>=`
6. `&&`
7. `||`

The bitwise operators bind more tightly than the comparisons, so
`flags & 0x02 != 0` means `(flags & 0x02) != 0`. Comparisons can't be chained:
instead of `a < b < c`, write `a < b && b < c`. The other binary operators
associate to the left.

Write `>=` without a space between `>` and `=`.

### Evaluation

`&&` evaluates its right operand only if its left operand is `true`, and `||`
only if its left operand is `false`. The other operators evaluate both operands,
including `&`, `|` and `^` on booleans. `>` and `>=` evaluate their right operand
first, so `dbg!` in their operands prints the right operand's value first.

### Operand types

A comparison needs the type of at least one of its operands from the operand
itself. Variables, function calls, jet calls and boolean expressions have such a
type. Integer literals, witnesses and parameters take their type from the other
operand, so `x == 3` works when `x` is a variable, but `3 == 4` is an error. To
compare two such values, assign one of them to a variable with a declared type
first.

## Adding or stabilizing a feature

See the rustdoc on `UnstableFeature` in `src/unstable.rs`; the procedures
live next to the code they mutate, so they cannot drift.
