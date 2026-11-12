/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Lemma546.Definitions

/-!
# Lemma 5.46 (disjoint-cluster expansion): the statement

Mathlib-only statement of Lemma 5.46 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

For every admissible mollifier `χ`, `p₀ ≥ 1`, `β > 2`, every `M > 20`, `λ ∈ (0,1)`
and every `N`, the reduced sum `∑_{π ∈ Π_p([N])} Ẑ(π)`, divided by
`(N C_{β,λ})^N`, is exactly the sum over disjoint dipole clusters in (5.164):
`∑_{n ≥ 0} (1/n!) ∑_{V_1,…,V_n disjoint, 2 ≤ |V_i| ≤ p} ∏_i K^dip(V_i)`.
Here `p = p(β)`. This identity has no asymptotic error.

## How the objects are specified

`IsMollifier` specifies the radial unit-disc mollifier. `pBeta` gives Definition 2.8,
using `pStar` and `transitionBeta`. `dipoleNormalization` is the one-dipole integral
on the companion square `box N`, with `smearedKernel` specifying the regularized
interaction. `boundedBlockPartitions` consists of nonempty disjoint blocks that
cover the labels and have size at most `p`.
`truncatedPartitionWeight` gives (5.160), using the block integrals
`multipolePartitionFunction` and activities `multipoleActivity` under
`hierarchicalModel`. `dipoleActivity` is the connected-graph expectation of
Definition 2.5 under `dipoleMeasure`, with `IsStableDipolePair` determined by the
greedy stable matching. The disjointness and size constraints are explicit in the
finite label sums. Both sums over cluster number are Mathlib's `tsum`; their
terms vanish for sufficiently large cluster number.

Configurations are `Fin N → ℂ × ℂ`, with the paper's labels shifted to start at zero.
All definitions are total; the theorem imposes the admissible parameter ranges.
The theorem below uses the definitions shared by the challenge and solution, which
import Mathlib only. Its final proof is the only `sorry`.
-/

@[expose] public section

namespace MultipoleBKTAudit.Lemma546

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

open scoped Classical in
/-- **Lemma 5.46**, eq. (5.164):
`(N C_{β,λ})^{-N} ∑_{π ∈ 𝚷_p([N])} Ẑ(π) = ∑_{n ≥ 0} (1/n!) ∑_{V_1, …, V_n ⊂ [N] disjoint,
2 ≤ |V_i| ≤ p} ∏ᵢ 𝖪^dip_{β,λ}(V_i)`. -/
theorem lemma_5_46
    -- `χ` and `p₀` outermost
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- an exact identity for every `M > 20` (Definition 2.2), every
    -- `λ ∈ (0,1)` and every `N`
    ∀ M : ℝ, 20 < M → ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ N : ℕ,
      (((N : ℝ) * dipoleNormalization χ N β lam) ^ N)⁻¹ *
          ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π
        -- the series over `n` is a `tsum` with finitely many nonzero terms
        = ∑' n : ℕ, 1 / (n.factorial : ℝ) *
            ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter (fun V =>
                (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
              ∏ i, dipoleActivity χ N β lam (V i) :=
  sorry

end MultipoleBKT

end MultipoleBKTAudit.Lemma546

end
