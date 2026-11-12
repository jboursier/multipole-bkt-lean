# Independent statement comparisons

The seven results of the paper are each restated here using only Mathlib and copies of the
definitions their statements use. Each restatement is proved from the library, and
[leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
proved from the library is the restated one. To read a result independently of the library,
read its `Challenge.lean` together with its `Definitions.lean`.

## How a pair is built and checked

Each subdirectory is one comparator pair:

| File | Role |
| --- | --- |
| `Definitions.lean` | Only the definitions the statement needs, transitively, copied in dependency order from `MultipoleBKT/Frozen/` and the imported `TwoComponentCoulomb/Frozen/`, inside `MultipoleBKTAudit.<Pair>`. It imports Mathlib only. |
| `Challenge.lean` | Imports `Definitions.lean` and states the theorem. Its final proof is the only `sorry`. Read this file and its definitions module. |
| `Solution.lean` | Imports `Definitions.lean` and the library. It states the same theorem and proves it `by exact` the corresponding library theorem. |
| `comparator.json` | The challenge and solution modules, the theorem name, and the permitted axioms. |

For example, the library's `MultipoleBKT.energy` is
`MultipoleBKTAudit.Theorem1.MultipoleBKT.energy` in that pair's definitions. Imported companion
definitions keep their `TwoComponentCoulomb` namespace inside the pair namespace, for example
`MultipoleBKTAudit.Theorem1.TwoComponentCoulomb.box`. The solution can therefore import both
the copied definitions and the library. The two statements agree after unfolding the
definitions, and Lean's kernel checks the application of the library theorem.

The challenge and solution import the same Mathlib-only `Definitions.lean`. Definition code
and docstrings are copied verbatim. Each challenge's module documentation states the result
in mathematical language and explains how its objects are specified.

The comparator checks the theorem and every definition it depends on. `comparator.json` permits
exactly `propext`, `Classical.choice` and `Quot.sound`. `scripts/run_comparators.sh` adds the
NanoDa and con-ron kernels bundled with the Lean toolchain, so that the solution is replayed
by three independent kernels. See the [README](../README.md#running-the-comparators) for commands.

## The pairs

| Pair | Paper statement | Library declaration |
| --- | --- | --- |
| [`Theorem1`](Theorem1/) | Theorem 1 | `MultipoleBKT.theorem_1` |
| [`Theorem2`](Theorem2/) | Theorem 2 | `MultipoleBKT.theorem_2` |
| [`Proposition423`](Proposition423/) | Proposition 4.23 | `MultipoleBKT.proposition_4_23` |
| [`Proposition462`](Proposition462/) | Proposition 4.62 | `MultipoleBKT.proposition_4_62` |
| [`Proposition543`](Proposition543/) | Proposition 5.43 | `MultipoleBKT.proposition_5_43` |
| [`Proposition545`](Proposition545/) | Proposition 5.45 | `MultipoleBKT.proposition_5_45` |
| [`Lemma546`](Lemma546/) | Lemma 5.46 | `MultipoleBKT.lemma_5_46` |

Numbering follows the revised version of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, 2026).

## Conventions shared by the challenges

- Every result takes an admissible mollifier `χ` and `β > 2`, with `p₀ ≥ 1` when needed,
  before its constants. `IsMollifier` requires measurability, nonnegativity, radial symmetry,
  boundedness, vanishing outside the closed unit disc, and integral one. Asymptotic estimates
  give `C > 0`, then `λ₀ ∈ (0,1]`, then for each `λ ∈ (0,λ₀)` a threshold `N₀(λ)` and a
  bound for every `N ≥ N₀(λ)`. Large `M` means `M₀ > 20` and every `M ≥ M₀`; small `ε₀`
  means every `ε₀ ∈ (0,ε₁)`, followed by `C`, `λ₀`, `N₀(λ)`. In Theorem 2(4), `N₀` is
  uniform in `γ`; in Propositions 4.62 and 5.43 it is uniform in the profile. Theorem 2(6)
  chooses `λ₀` and `N₀` after large `C₀`. Lemma 5.46 is an exact identity for all `N`.
- The plane is `ℂ`, and a configuration is `c : Fin N → ℂ × ℂ`, with `c i = (x_i,y_i)`.
  Labels start at zero. The square `Λ = [0,√N]²` and logarithmic kernel come from
  `TwoComponentCoulomb`; their definitions are included in each pair, so the challenges
  require neither plasma library. Partition integrals are lower Lebesgue integrals in
  `[0,∞]`. Where logarithms of partition functions occur, positivity and finiteness are
  conclusions, and the logarithm is `Real.log Z.toReal`. Logarithmic probability estimates
  are exponential inequalities; (2.52) is expressed by two bounds on the probability.
- The stable matching is the greedy rule of Definition 2.1, with lexicographic tie breaking.
  The multipole relation uses closed inequalities and the minimum of the four distances
  between two dipoles. Multipole counts count components by number of dipoles. Bad and good
  points are computed on the matched dipoles `(x_i,y_{σ_N(i)})`; ties in the clustering of bad
  points are broken by the smallest label.
- The coefficient families in (2.34), (2.45) and (2.46) are quantified, with their limits
  imposed for every `λ ∈ (0,1)`. Theorems 1 and 2 conclude their existence and their bounds
  (2.39), (2.47) and (2.48) for sufficiently small `λ`. The rate function and Mayer series
  are functions of these coefficients; the large deviations propositions hold for every
  family with the specified limits. Infinite sums are Mathlib's `tsum`. Statements conclude
  the absolute convergence they use, including joint convergence in both series indices.
  Infima are infima of images, and Theorem 2(5) concludes attainment at a unique minimizer.
- Proposition 4.23 quantifies each size `k ≤ p*(β)` before `M₀(β,k)` in (4.38)–(4.40),
  as in the revised paper. Its dipole activity bound (4.41) does not depend on `M`.
- Definitions are total, taking Mathlib's conventional values outside the paper's ranges;
  the theorems impose those ranges. Scope is the seven results and the results needed for
  their proofs. Other paper results, heuristic and expository remarks, and Appendix B
  (the Sine–Gordon correspondence) are outside the formalization.
