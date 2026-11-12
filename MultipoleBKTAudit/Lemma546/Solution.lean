/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Lemma546.Definitions
public import MultipoleBKT.Frozen.Lemma546

/-!
# Lemma 5.46 (disjoint-cluster expansion): the proof

The challenge's statement, proved from `lemma_5_46` of the library. The shared
copied definitions unfold to the library's definitions, so Lean checks the direct
application of the library theorem.
-/

-- Compare the recursive definitions by ordinary unfolding.
set_option smartUnfolding false

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
  by exact _root_.MultipoleBKT.lemma_5_46 χ hχ p₀ hp₀ β hβ

end MultipoleBKT

end MultipoleBKTAudit.Lemma546

end
