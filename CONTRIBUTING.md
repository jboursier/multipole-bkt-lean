# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get   # prebuilt mathlib oleans
lake build           # the library
```

The toolchain is pinned in `lean-toolchain` and managed by
[elan](https://github.com/leanprover/elan). Lake fetches Mathlib and the companion library
`TwoComponentCoulomb`, pinned at `ea3906a5850aaece11adee4b5562041e7512cfb6`. Use its existing
results through imports.

The library must build with **no warnings**. The only files containing a `sorry` are the seven
comparator challenges `MultipoleBKTAudit/*/Challenge.lean`, each with exactly one, in its final
theorem. `lake build MultipoleBKT` builds the library, and `lake build MultipoleBKTAudit` builds
the comparator files. `scripts/check_all.sh` runs the zero-warning build, the source sweep and
the axiom report.

## The main results and the axiom report

The seven public statements are in `MultipoleBKT/Frozen/`, together with the MultipoleBKT
definitions they use. They also use two frozen definitions of the imported companion library,
the square `TwoComponentCoulomb.box` and the kernel `TwoComponentCoulomb.logKernel`. Each public
theorem is proved `by exact` a theorem of the same name in an ordinary module, its provider. Its
axiom report must consist of exactly `propext`, `Classical.choice` and `Quot.sound`:

```bash
lake env lean MultipoleBKT/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

`MultipoleBKT/Meta/AxiomsAudit.lean` is not imported by the root module, because a
`#print axioms` command runs again whenever its module is rebuilt.

## Conventions for Lean files

- Use the module system (`module`, `public import`, `@[expose] public section`). Keep each file
  within 1500 lines.
- No `sorry`, `admit`, `native_decide`, new `axiom`, `opaque` declaration, heartbeat override or
  recursion-depth override in the library. `scripts/check_sources.py` enforces these rules and
  rejects foreign implementations and kernel type-check bypasses.
- Keep the statements and definitions in `MultipoleBKT/Frozen/` faithful to the paper. Check
  changes against the revised version (2026), including the order of constants and quantifiers,
  the ranges of `β`, `λ`, `M` and `ε_0`, and the summability and finiteness conclusions. Refer to
  paper results by that version's numbering.
- Copy any changed frozen definition into every audit pair's `Definitions.lean` that uses it.
  Preserve the text and dependency order. This includes the definitions imported from
  `.lake/packages/TwoComponentCoulomb/TwoComponentCoulomb/Frozen/`. Do not edit the fetched
  dependency to change its results.
- Update both `Challenge.lean` and `Solution.lean` when their final statement changes. Keep
  their mathematical statements the same and retain the solution's direct `by exact` proof.
- Keep each pair's copied definitions in its single shared `Definitions.lean`. Some definitions
  contain proofs that create private auxiliary lemmas whose names depend on the module. Separate
  copies in challenge and solution modules would give these lemmas different names.
- Update the README, challenge documentation and `formalization.yaml` when a public statement
  or its encoding changes. Recheck all seven comparator pairs after changes to shared
  definitions.

## Comparators

Each pair under `MultipoleBKTAudit/` has a Mathlib-only `Definitions.lean`, a `Challenge.lean`
importing it, a `Solution.lean` importing it and the library, and a `comparator.json` permitting
exactly `propext`, `Classical.choice` and `Quot.sound`.

```bash
lake build MultipoleBKTAudit
./scripts/run_comparators.sh
```

On macOS, use `./scripts/run_comparators.sh --no-sandbox`. On Linux the default runner uses
`bubblewrap`. The runner checks all seven pairs unless pair names are supplied, and adds the
NanoDa and con-ron kernels bundled with the toolchain. A missing pair, missing tool or failed
kernel check is a failure. Logs are kept under `.lake/comparator-logs/`. See
[`MultipoleBKTAudit/README.md`](MultipoleBKTAudit/README.md) for the pair structure.

## Continuous integration

`.github/workflows/build.yml` builds the library, rejects warnings, sweeps the sources and checks
the axiom report. `.github/workflows/comparator.yml` runs after a successful build on `main`
and checks the seven pairs with the kernels bundled with the Lean toolchain, one job per pair.
