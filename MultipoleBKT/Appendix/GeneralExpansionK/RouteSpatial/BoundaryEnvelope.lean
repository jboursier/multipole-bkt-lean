/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.MixedNormalization

/-!
# The actual mixed boundary on every configuration

See Step 3 of
the proof of Lemma A.7. Every vanishing branch is
removed explicitly. The selected root and complete tree are then included
in a fixed finite envelope before integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Internal zero-common-factor elimination for the exact pointwise alternatives. -/
theorem internal_paper_zero {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} {d g : Sym2 ℕ → ℝ}
    {τ v : X.biUnion id → ℝ} {b J : Sym2 (X.biUnion id) → ℝ}
    {T : Finset (Sym2 (X.biUnion id))} {P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)}
    {R t : ℝ} (H : PaperPointwise hX hOX hpar r d g τ v b J T P R 0 t) : t = 0 := by
  rcases H with ⟨F,i,hh | ⟨-,hh⟩⟩ | ⟨F,i,j,-,hh⟩
  all_goals
    simp only [zero_mul] at hh
    exact abs_nonpos_iff.1 hh

/-- Internal passage from the exact boundary to the fixed finite envelope.
Concrete model entry points supply the root comparison. -/
theorem internal_boundary_envelope {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} [Nonempty (X.biUnion id)] {χ : ℂ → ℝ} {β lam M h K W : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (hK : 0 ≤ K) (hW : 0 ≤ W)
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {τ u v : ℂ × ℂ → ℝ}
    {Near Far : Finset (ℕ × ℕ)} (hOF : O ⊆ Far)
    {Dz : Finset (Sym2 (X.biUnion id))} {c : ℕ → ℂ × ℂ}
    (H : MixedBoundary hX hOX hpar χ β lam M h K W w τ u v Near Far Dz c)
    (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)) (hne : P ≠ (∅,∅,∅,∅,∅))
    (hP : P ∈ fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) (RouteCases.intraEdges (Limits.blockOf X)) univ)
    (F : (X.biUnion id → ℂ × ℂ) → X.biUnion id → ℝ≥0∞) (B : ℝ≥0∞)
    (hroot : ∀ i : X.biUnion id,
      ENNReal.ofReal ((τ (c i) ^ 2)⁻¹ + |v (c i)| / maxRad lam (fun i : X.biUnion id => c i) ^ 2) ≤
        B * F (fun i : X.biUnion id => c i) i) :
    ENNReal.ofReal |mixedIntegrand χ β lam M h w u v (Limits.blockOf X)
      (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) (symOf (X.biUnion id) O)
      (fun i : X.biUnion id => c i) P| ≤
      (ENNReal.ofReal (W ^ ((X.biUnion id).card * (X.biUnion id).card) *
        K ^ factorCount (symOf (X.biUnion id) O)
          (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P) * B) *
        spatialEnvelope χ β M lam h F (fun i : X.biUnion id => c i) := by
  let cfg := fun i : X.biUnion id => c i
  let A := W ^ ((X.biUnion id).card * (X.biUnion id).card) * K ^ factorCount
    (symOf (X.biUnion id) O) (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg hW _) (pow_nonneg hK _)
  obtain ⟨Tb,hTb,-,hb⟩ := H
  rcases hb P hne hP with hz | hp
  · rw [hz,abs_zero,ENNReal.ofReal_zero]
    exact bot_le
  · by_cases hS : clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz cfg = 0
    · rw [hS,mul_zero,zero_mul] at hp
      rw [internal_paper_zero hp,abs_zero,ENNReal.ofReal_zero]
      exact bot_le
    by_cases hD : mixedDensity χ β lam h (symOf (X.biUnion id) Far) cfg = 0
    · rw [hD,mul_zero] at hp
      rw [internal_paper_zero hp,abs_zero,ENNReal.ofReal_zero]
      exact bot_le
    obtain ⟨T,hT,Ao,Eo,mark,i,hn⟩ := internal_paper_normalized hX hOX hpar hlam hM hA τ v Near Far hOF
      Dz c Tb hTb P hP hS hD hp
    refine hn.trans ?_
    calc
      _ ≤ ENNReal.ofReal A * ((B * F cfg i) * activityTree M lam h T Ao Eo mark cfg *
          activityDensity χ β lam h cfg) := mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' (hroot i) le_rfl) le_rfl)
      _ = (ENNReal.ofReal A * B) * (F cfg i * activityTree M lam h T Ao Eo mark cfg *
          activityDensity χ β lam h cfg) := by ring
      _ ≤ _ := mul_le_mul' le_rfl (le_spatialEnvelope χ β M lam h F cfg T hT Ao Eo mark i)

/-- The number of factors is uniformly bounded before summing the original choices. -/
theorem factorCount_le_label_count {W : Type*} [Fintype W] (A B : Finset (Sym2 W))
    (P : FiveSubsets (Sym2 W) W) :
    factorCount A B P ≤ 3 * Fintype.card (Sym2 W) + 2 * Fintype.card W := by
  have ha := card_le_univ A
  have hb := card_le_univ B
  have hc := card_le_univ P.2.2.1
  have hd := card_le_univ P.2.2.2.1
  have he := card_le_univ P.2.2.2.2
  unfold factorCount
  omega

end MultipoleBKT.ExpansionK.RouteSpatial

end
