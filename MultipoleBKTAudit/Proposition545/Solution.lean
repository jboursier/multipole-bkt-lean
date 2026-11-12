/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Proposition545.Definitions
public import MultipoleBKT.Frozen.Proposition545

/-!
# Proposition 5.45 (reduction to bounded-size multipoles): the proof

The challenge's statement, proved from `proposition_5_45` of the library. The shared
copied definitions unfold to the library's definitions, so Lean checks the direct
application of the library theorem.
-/

-- Compare the recursive definitions by ordinary unfolding.
set_option smartUnfolding false

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
  by exact _root_.MultipoleBKT.proposition_5_45 χ hχ p₀ hp₀ β hβ

end MultipoleBKT

end MultipoleBKTAudit.Proposition545

end
