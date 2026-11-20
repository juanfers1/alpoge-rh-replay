# Statement check with Mathlib-only expected propositions

`Audit.lean` writes the expected propositions in a file that imports `Main`, so they are elaborated
with every project instance, notation and declaration in scope. The files here pin the same five
statements in a module that imports **only Mathlib**, then compare the project's types with them.
This addresses point 2 of [#85](https://github.com/rohanarun/alpoge-rh-replay/issues/85).

| File | Imports | Purpose |
|---|---|---|
| `ExpectedStatements.lean` | `Mathlib` | Literal and independently worded forms of the five statements, Mathlib-only proofs that the two forms are equivalent, and sanity checks. |
| `StatementCheck.lean` | `Lean` | Comparison and axiom-check commands. |
| `CompareMain.lean` | the three above and `Main` | Checks the five theorems of `Main`. Optional step in `verify.sh`. |
| `CompareStatements.lean` | the three above and `Statements` | Checks the four definitions in `Statements` and Mathlib's `RiemannHypothesis`. Needs only `lake build Statements`. |
| `statement-check.sh` | | Compiles the first two modules into an output directory and runs one comparison. |

## What a comparison checks

For each pair `(project constant, pinned proposition)`, `StatementCheck.checkPairs`:

1. takes the constant's type if it is a theorem, or its value if it is a `Prop` definition;
2. unfolds every definition from a module outside Mathlib's import closure, and every
   elaborator-generated `_proof_N` auxiliary, whose name depends on the generating module;
3. requires α-equivalence with the pinned proposition, `Lean.Kernel.isDefEq` on the original terms,
   and no remaining constant from outside Mathlib on either side.

`CompareMain.lean` also states `theorem … : RHExpected.RHLit := riemannHypothesis` and similar for
the other four. The kernel therefore checks that each theorem of `Main` proves the pinned
proposition, and the Mathlib-only equivalences then give the independently worded forms. Each result
is restricted to `propext`, `Classical.choice` and `Quot.sound`. The full types are printed with
`pp.all` so that any implicit argument or instance hypothesis is visible.

## Sanity checks in `ExpectedStatements.lean`

- Excluding the trivial zeros is necessary: `ζ(-2) = 0`.
- The hypothesis `s ≠ 1` is harmless, because Mathlib's `ζ(1) ≠ 0`.
- The `Re s ≥ 1` part of the non-vanishing statement is already a Mathlib theorem, so its new
  content is `1/2 < Re s < 1`.
- The statement for all Dirichlet characters implies RH in the critical strip, through the
  character mod 1, and also implies the statement for primitive characters.

## Running it

The check is opt-in and is not part of the default `verify.sh` path.

**Against a completed checkout.** Use the `lean/` directory of a replay where `lake build +Main:olean`
has succeeded, for example the one `verify.sh` creates in its output directory:

```bash
cd /path/to/replay-directory/lean
export ELAN_HOME=/path/to/replay-directory/elan   # if elan was installed there by verify.sh
elan run leanprover/lean4:v4.33.1 lake env \
  bash /path/to/alpoge-rh-replay/audit/statement-check.sh main /path/to/empty/output-dir
```

Exit status 0 and the line `All 5 checks passed` mean the comparison and the axiom checks passed.
The output directory holds only the two compiled audit modules; the checkout is not modified.

**Statement definitions only.** This mode needs `lake build Statements` (depth 0) instead of `Main`:

```bash
elan run leanprover/lean4:v4.33.1 lake build Statements
elan run leanprover/lean4:v4.33.1 lake env \
  bash /path/to/alpoge-rh-replay/audit/statement-check.sh statements /path/to/empty/output-dir
```

**Inside `verify.sh`.** `REPLAY_STATEMENT_CHECK=1 ./verify.sh /path/to/empty/replay-directory` runs the
`main` mode after `REPLAY_FRESH_KERNEL_PASSED`, so a failure cannot prevent the existing checks
from running.

## Results so far

The `statements` mode passed 5/5 on macOS (Apple M5 Max, Lean 4.33.1, Mathlib `0df444a3`), with
`Statements.lean` matching its index SHA-256. In the `pp.all` output, the only instance binder in
any statement is `[NeZero N]`.

The `main` mode has **not** been run against a genuine `Main.olean` yet. Once it passes there, it
could be considered for the default `verify.sh` path.
