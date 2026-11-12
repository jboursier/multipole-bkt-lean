# Multipole and Berezinskii–Kosterlitz–Thouless transitions in the two-component plasma

A machine-checked **Lean 4** formalization of the paper

> Jeanne Boursier and Sylvia Serfaty,
> *Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*,
> [arXiv:2509.09449](https://arxiv.org/abs/2509.09449).

The two main results of the paper, Theorems 1 and 2, are proved for every inverse temperature
`β > 2`, together with the five intermediate results on which their proofs rest: Propositions
4.23, 4.62, 5.43 and 5.45 and Lemma 5.46. The formalization follows the revised version of the
paper (2026). Its numbering is used below and may differ from earlier arXiv versions.

The development builds on [mathlib](https://github.com/leanprover-community/mathlib4) and the
[formalization of the companion paper](https://github.com/serfatysylvia/two-component-coulomb-dipoles-dev),
*Dipole formation in the two-component plasma*
([arXiv:2410.01025](https://arxiv.org/abs/2410.01025)). Lake imports the companion library as
`TwoComponentCoulomb`, pinned at commit `ea3906a`. This development uses its box, its logarithmic
kernel and its potential-theory and integration lemmas.

[![CI](https://github.com/jboursier/multipole-bkt-lean/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/jboursier/multipole-bkt-lean/actions/workflows/build.yml)
[![Comparator audit](https://github.com/jboursier/multipole-bkt-lean/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/jboursier/multipole-bkt-lean/actions/workflows/comparator.yml)

## What is proved

The paper studies `N` positive charges `x_1, …, x_N` and `N` negative charges `y_1, …, y_N` in
the square `Λ = [0, √N]²`, with charges smeared on discs of radius `λ ∈ (0,1)`:

> `g(x) = -log |x|`, `δ_z^{(λ)} = λ^{-2} χ((· - z)/λ)`, `κ = ∬ g(x-y) δ_0^{(1)}(x) δ_0^{(1)}(y)`,
> `F_λ(X_N, Y_N) = ½ ∬ g(x-y) d(Σ_i δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)})(x) d(Σ_i δ_{x_i}^{(λ)} - δ_{y_i}^{(λ)})(y) - N(g(λ) + κ)`,
> `Z_{N,β}^λ = ∫_{(Λ²)^N} e^{-βF_λ}`, `dP_{N,β}^λ = (Z_{N,β}^λ)^{-1} e^{-βF_λ} dX_N dY_N`.

Here `χ` is a radial, nonnegative, bounded mollifier supported in the unit disc with `∫ χ = 1`.
For `β > 2` the charges bind into dipoles, the pairs `(x_i, y_{σ_N(i)})` of the stable matching
`σ_N` (Definition 2.1), and dipoles group into multipoles (Definition 2.2). The transition
temperatures are `β_q = 4 - 2/q`, and `p*(β)` is the number of them below `β` (infinite for
`β ≥ 4`). The series truncation parameter is `p(β) = p*(β)` for `2 < β < 4` and a fixed integer
`p_0 ≥ 1` for `β ≥ 4` (Definition 2.8). The error rate `δ_{β,λ}` is `R_{β,λ}^{-2}` for
`2 < β < 4`, multiplied by `1 + |log λ|` when `β` is a transition temperature, and `λ^{2p_0}`
for `β ≥ 4`; here `R_{β,λ} = λ^{-(β-2)/(4-β)}` is the critical length.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1 | [`MultipoleBKT.theorem_1`](MultipoleBKT/Frozen/Theorem1.lean) | Free energy expansion: `log Z_{N,β}^λ` up to `O(N δ_{β,λ})`, by a cluster expansion in the dipole activities (1); existence and size `O(λ^{2(k-1)})` of the coefficients `k^dip(k)` for `k ≤ p*(β)` (2); the cluster series as `-N Mayer_{β,p(β),λ}` (3) |
| Theorem 2 | [`MultipoleBKT.theorem_2`](MultipoleBKT/Frozen/Theorem2.lean) | Multipole distribution: the coefficients of the rate function `I_{β,p,λ}` (1), `log Z` through the minimum of `I` (2), control of large multipoles and long dipoles (3), large deviations for the multipole counts (4), the unique minimizer `γ*` and its size (5), the typical number of `2k`-poles (6) |
| Proposition 4.23 | [`MultipoleBKT.proposition_4_23`](MultipoleBKT/Frozen/Proposition423.lean) | Control of the activity of bounded-size clusters |
| Proposition 4.62 | [`MultipoleBKT.proposition_4_62`](MultipoleBKT/Frozen/Proposition462.lean) | Large deviations lower bound |
| Proposition 5.43 | [`MultipoleBKT.proposition_5_43`](MultipoleBKT/Frozen/Proposition543.lean) | Large deviations upper bound |
| Proposition 5.45 | [`MultipoleBKT.proposition_5_45`](MultipoleBKT/Frozen/Proposition545.lean) | Reduction of `Z` to multipoles of size at most `p(β)` |
| Lemma 5.46 | [`MultipoleBKT.lemma_5_46`](MultipoleBKT/Frozen/Lemma546.lean) | The reduced partition function as a sum over disjoint clusters of dipole activities |

Each statement, and each of the definitions it uses, lives alone in a file under
[`MultipoleBKT/Frozen/`](MultipoleBKT/Frozen/). The authors approved every one of them in its
exact Lean form before it was proved. Each frozen theorem is proved `by exact` a theorem of the
same name in an ordinary module (its *provider*), for example `MultipoleBKT.Main.theorem_1`.

## Standing assumptions and scope

1. **Parameters and constants.** Every result takes a mollifier `χ` (`IsMollifier`: measurable,
   nonnegative, radial, bounded, zero outside the closed unit disc, with integral 1) and `β > 2`,
   and the integer `p_0 ≥ 1` when `p(β)` or `δ_{β,λ}` appears, and quantifies its constants after
   them. Each `O(·)` term of the paper
   becomes explicit constants with their own quantifiers: there are `C > 0` and `λ_0 ∈ (0,1]`
   such that for every `λ ∈ (0, λ_0)` there is `N_0(λ)` with the bound for every `N ≥ N_0(λ)`.
   Where the paper takes `M` large, the statements give `M_0 > 20` with the conclusion for every
   `M ≥ M_0`; where it takes `ε_0` small, they give `ε_1` with the conclusion for every
   `ε_0 ∈ (0, ε_1)`, followed by `C`, `λ_0` and `N_0(λ)`. In Theorem 2(4), `N_0` is uniform in `γ`,
   and in Propositions 4.62 and 5.43 it is uniform in the multipole profile. In Theorem 2(6), `λ_0`
   and `N_0` are chosen after `C_0` is taken large.
2. **The model.** The plane is `ℂ`. A configuration is `c : Fin N → ℂ × ℂ` with
   `c i = (x_i, y_i)`, so labels start at 0. The square `Λ = [0, √N]²` and the kernel `g` are
   those of `TwoComponentCoulomb`. The partition function is a lower Lebesgue integral in
   `[0, ∞]`; the statements conclude `0 < Z < ∞` and write `log Z` for the logarithm of its real
   value. A bound `log P(E) ≤ X` is written `P(E) ≤ e^X`, and the two-sided estimate (2.52) is
   written as two bounds on `P(E)`.
3. **Dipoles and multipoles.** The stable matching `σ_N` is the greedy rule of Definition 2.1,
   with ties broken lexicographically. The multipole relation uses closed inequalities and the
   minimum of the four distances between two dipoles, and `𝒩_k` counts multipoles of `k` dipoles.
   The bad and good points of a configuration are those of its matched dipoles
   `(x_i, y_{σ_N(i)})`. Ties in the clustering of bad points are broken by the smallest label.
4. **Coefficients and series.** The coefficients `k^dip(k)`, `m(k)` and `k^mult` of (2.34),
   (2.45) and (2.46) are not definitions: the theorems assert that coefficient families with
   these limits exist for every `λ ∈ (0,1)`, and the bounds (2.39), (2.47) and (2.48) hold for
   `λ < λ_0`. `Mayer` and the rate function `I` are functions of the coefficients, and every result
   about `I` holds for every family with these limits. Infinite sums are Mathlib's `tsum`, and
   each statement concludes the absolute convergence it uses: of the cluster series in `n`, and
   jointly in both indices for `Mayer` and for the series of `I`. Infima are infima of images,
   and Theorem 2(5) concludes that the infimum of `I` is attained at a unique point.
5. **Proposition 4.23.** The frozen statement covers the three activities that Theorems 1 and 2
   use, `𝖬_{β,λ}`, `𝖪^mult_{β,λ}` and `𝖪^dip_{β,λ}`: the bounds (4.38)–(4.40) for each size
   `k ≤ p*(β)` and every `M ≥ M_0(β, k)`, and (4.41). The bounds for the finite-cutoff activities
   `𝖬^-_{ε_0}`, `𝖬^0_{ε_0}`, `𝖪^-_{ε_0}` and `𝖪^0_{ε_0}` are proved in the library on the way.
6. **Total definitions.** Definitions are total in their parameters and take Mathlib's
   conventional values outside the ranges of the paper. The theorems carry the ranges.
7. **Scope.** Results of the paper that the proofs of the seven results do not use, the heuristic
   and expository remarks, and Appendix B (the Sine–Gordon correspondence) are not formalized.

## Guarantees

- **No `sorry` in the library.** The seven comparator challenges under
  [`MultipoleBKTAudit/`](MultipoleBKTAudit/) each contain one intentional statement-level
  `sorry`, which the corresponding solution proves.
- **Standard axioms only.** The axiom report of each main result lists exactly `propext`,
  `Classical.choice` and `Quot.sound`.
  [`MultipoleBKT/Meta/AxiomsAudit.lean`](MultipoleBKT/Meta/AxiomsAudit.lean) prints the reports,
  and `scripts/check_axioms.py` rejects any other axiom, `sorryAx`, and missing or unexpected
  reports.
- **Builds from a clean checkout.** `lake build` of a fresh clone of this repository completed
  its 4,242 jobs with 0 warnings and no errors. Continuous integration rejects any warning.
  `scripts/check_sources.py` rejects `sorry`, `admit`, new axioms, `opaque`, `native_decide`,
  `implemented_by`, `extern`, kernel type-check bypasses, and heartbeat or recursion-depth
  overrides.
- **Independent statement comparisons.** Each main result has a Mathlib-only restatement under
  [`MultipoleBKTAudit/`](MultipoleBKTAudit/). Its definitions are copied from the frozen
  definitions of this library and of `TwoComponentCoulomb`. The solution proves the restatement
  from the library, and [leanprover/comparator](https://github.com/leanprover/comparator)
  compares the statements and their definitions and replays the solution with Lean, NanoDa and
  con-ron. See [`MultipoleBKTAudit/README.md`](MultipoleBKTAudit/README.md).
- **Statements checked before the proofs.** The statements and their definitions were written
  before the proofs, compared with the paper by independent audits, and approved by the authors
  in their exact Lean form.
- **Proofs that follow the paper.** The proofs on the dependency path of the seven results follow
  the written proofs of the revised version. Independent read-only reviews compared each part of
  the Lean proofs with the corresponding section of the paper, and every difference they found
  was resolved in the Lean.
- **Pinned dependencies.** Lean and Mathlib `v4.35.0-rc2`, and `TwoComponentCoulomb` at
  `ea3906a5850aaece11adee4b5562041e7512cfb6`. Exact revisions are recorded in
  [`lake-manifest.json`](lake-manifest.json).

## Size

The library contains 879 Lean files with 184,792 physical lines, on top of Mathlib and the
imported companion library. The 29 comparator files under `MultipoleBKTAudit/`, with
6,529 lines, are not included in these counts.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches Mathlib and `TwoComponentCoulomb`.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

With Mathlib downloaded, a fresh build takes about 5 minutes on a 20-core Linux machine.

To reproduce the axiom reports:

```bash
lake env lean MultipoleBKT/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

`scripts/check_all.sh` runs the zero-warning build, the source sweep and the axiom report.

## Running the comparators

Each pair has a `MultipoleBKTAudit/<Pair>/comparator.json` permitting exactly `propext`,
`Classical.choice` and `Quot.sound`. Each challenge and its solution import the same
Mathlib-only `Definitions.lean`. The solution additionally imports the library and proves the
theorem `by exact` the corresponding library theorem.

```bash
lake build MultipoleBKTAudit     # the challenges and their solutions
./scripts/run_comparators.sh     # all seven pairs, or name some pairs
```

The comparator builds inside a `bubblewrap` sandbox, which is available on Linux. On macOS,
`./scripts/run_comparators.sh --no-sandbox` runs the same checks without the sandbox. Logs are
kept under `.lake/comparator-logs/`. The runner adds the NanoDa and con-ron kernels bundled
with the toolchain.

**CI** builds the library, rejects warnings and checks the axiom reports. **Comparator audit**
checks the seven pairs, one job per pair, after a successful build on `main`. Both workflows can
be started from the [Actions page](https://github.com/jboursier/multipole-bkt-lean/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
MultipoleBKT.lean           root module, importing the seven results
MultipoleBKT/
  Frozen/                   the seven statements and the definitions they use
  Main/                     proofs of Theorems 1 and 2 and of Proposition 5.45
  Potential/                Section 3: electric formulation and energy bounds
  Energy/                   dipole energies and interactions
  Matching/                 the stable matching
  Multipole/                multipoles, their partitions and activities
  Cluster/                  cluster expansions, Ursell functions and hypertrees
  Gibbs/                    the Gibbs measure
  LowerBound/               Section 4: the large deviations lower bound
  UpperBound/               Section 5: bad points and the large deviations upper bound
  RateFunction/             the rate function and its minimizer
  Limits/                   the limiting activities
  Appendix/                 Appendix A: auxiliary estimates
  Meta/AxiomsAudit.lean     axiom reports, built but not imported by the root
MultipoleBKTAudit/          seven Mathlib-only definitions modules, challenges and solutions
scripts/                    source sweep, axiom check and comparator runner
.github/workflows/          build and comparator workflows
.lake/packages/TwoComponentCoulomb/   imported companion formalization, fetched by Lake
```

## How this was built

The Lean code was written with AI assistance under the direction of the authors, who fixed the
statements to be formalized. OpenAI's GPT-6.1 Sol, through the Codex CLI, wrote the statements
and the proofs and audited the statements and the proofs against the paper. Anthropic's Claude
Opus 5.5 coordinated the agents, reviewed their work and prepared this release through Claude
Code. Every proof is checked by the Lean kernel. The models, tooling and review status are
disclosed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

We thank Scott Armstrong for sharing the setup used for the formalization.

## Authors and citation

The Lean development is by **Jeanne Boursier** and **Sylvia Serfaty**. To cite it, use
[`CITATION.cff`](CITATION.cff).

S. Serfaty was supported by NSF grant DMS-2000205 and by the Simons Foundation through the
Simons Investigator program.

## License

The Lean development is licensed under the Apache License 2.0. See [`LICENSE`](LICENSE).
