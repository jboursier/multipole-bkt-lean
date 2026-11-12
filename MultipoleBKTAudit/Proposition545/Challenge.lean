/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Proposition545.Definitions

/-!
# Proposition 5.45 (reduction to bounded-size multipoles): the statement

Mathlib-only statement of Proposition 5.45 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

For every admissible mollifier `χ`, `p₀ ≥ 1` and `β > 2`, for all sufficiently large
`M`, small `λ` and large `N`, the logarithm of the partition integral restricted to
identity stable matching differs by at most `C N δ_{β,λ}` from the logarithm of
`∑_{π ∈ Π_p([N])} Ẑ(π)`, where `p = p(β)`. This is (5.161).
The restricted integral is positive and finite, and the reduced sum is positive.

## How the objects are specified

`IsMollifier` specifies the mollifier, and `energy` gives the smeared Coulomb energy.
The restricted integral is a lower Lebesgue integral over the companion square
`box N` for each endpoint. `stableMatching` uses the greedy rule with lexicographic
tie breaking; its identity event is imposed explicitly. `boundedBlockPartitions`
is the set of partitions of the labels into nonempty blocks of size at most `p`.
`truncatedPartitionWeight` gives (5.160), using `dipoleNormalization`, the block
partition functions `multipolePartitionFunction` and disjoint clusters weighted by
`multipoleActivity`. These activities use the normalized `hierarchicalModel`, the
closed multipole relation `MultipoleLinked` and the two-dipole stability event.
`pBeta` and `errorRate` give the truncation and the error. Constants are chosen as
`M₀`, then for every `M ≥ M₀`, `C`, `λ₀`, and `N₀(λ)`.

Configurations are `Fin N → ℂ × ℂ`, with the paper's labels shifted to start at zero.
All definitions are total; the theorem imposes the admissible parameter ranges.
The theorem below uses the definitions shared by the challenge and solution, which
import Mathlib only. Its final proof is the only `sorry`.
-/

@[expose] public section

namespace MultipoleBKTAudit.Proposition545

open MeasureTheory Filter Topology
open scoped ENNReal
open _root_.MultipoleBKTAudit.Proposition545.TwoComponentCoulomb (box)

namespace MultipoleBKT

open scoped Classical in
/-- **Proposition 5.45**, eq. (5.161):
`log ∫_{σ_N = Id} e^{-βF_λ} = log ∑_{π ∈ 𝚷_p([N])} Ẑ(π) + O_{β,p,M}(Nδ_{β,λ})`. -/
theorem proposition_5_45
    -- `χ` and `p₀` outermost
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- "For `M` large enough with respect to `β, p`"
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      -- "`λ` small enough and `N` large enough depending on `λ`";
      -- `O_{β,p,M}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          -- `∫_{σ_N = Id}` as `∫⁻` over `(Λ²)^N ∩ {σ_N = Id}`
          let zId : ℝ≥0∞ := ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
              {c | stableMatching c = Equiv.refl (Fin N)},
            ENNReal.ofReal (Real.exp (-β * energy χ lam c))
          let zHat : ℝ := ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π
          -- both logarithms are of positive finite
          -- quantities, asserted; then the two-sided bound
          0 < zId ∧ zId < ∞ ∧ 0 < zHat ∧
            |Real.log zId.toReal - Real.log zHat| ≤ C * N * errorRate p₀ β lam :=
  sorry

end MultipoleBKT

end MultipoleBKTAudit.Proposition545

end
