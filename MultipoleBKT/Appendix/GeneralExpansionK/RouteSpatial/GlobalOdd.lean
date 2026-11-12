/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailTransport

/-!
# The original global tail and the coupled odd profile

See the proof of Lemma A.7.
The longest-edge tail on the full retained odd forest is compared with
the joint profile, without distributing any decay among its edges.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- Constant radii identify the fold-min tail with the maximum-tail convention. -/
theorem globalTail_eq_tailJ {W : Type*} [Fintype W] [Nonempty W]
    {R : ℝ} (hR : 0 ≤ R) (d : Sym2 W → ℝ) (A : Finset (Sym2 W))
    (hd : ∀ e ∈ A, 0 < d e) :
    globalTail R d A = tailJ (fun _ : W => R) d A := by
  have hfold : univ.fold max 0 (fun _ : W => R) = R := by
    apply le_antisymm ((fold_max_le _).2 ⟨hR,fun _ _ => le_rfl⟩)
    obtain ⟨i⟩ := ‹Nonempty W›
    exact (le_fold_max _).2 (Or.inr ⟨i,mem_univ i,le_rfl⟩)
  by_cases hA : A.Nonempty
  · obtain ⟨e,he,hmax⟩ := exists_max_image A d hA
    have hs : A.sup' hA d = d e := le_antisymm ((sup'_le_iff _ _).2 hmax) (le_sup' d he)
    rw [globalTail_eq_of_max he hd hmax,tailJ,dite_eq_left hA,hfold,hs]
    have hx : 0 ≤ R / d e := div_nonneg hR (hd e he).le
    rw [← div_pow]
    rcases le_total (R / d e) 1 with h | h
    · rw [min_eq_left h,min_eq_right (pow_le_one₀ hx h)]
    · rw [min_eq_right h,min_eq_left (one_le_pow₀ h)]
      norm_num
  · have hz : A = ∅ := not_nonempty_iff_eq_empty.1 hA
    simp only [hz,globalTail,fold_empty,tailJ,Finset.not_nonempty_empty,dite_false]

/-- The full inverse-square odd product with its single global tail is below
the coupled profile. The hypothesis about positive distances is supplied by
far support on the actual original edges. -/
theorem globalTail_kept_le_jointOdd {W : Type*} [Fintype W] [Nonempty W]
    {M lam R : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (hR : 0 ≤ R)
    (c : W → ℂ × ℂ) (A : Finset (Sym2 W))
    (hd : ∀ e ∈ A, 0 < dipoleDistOn c e) :
    ENNReal.ofReal (globalTail R (dipoleDistOn c) A * ∏ e ∈ A, keptE M lam c e) ≤
      jointOdd (minRad lam c) R (fun e : A => (dipoleDistOn c e : ℂ)) := by
  rw [globalTail_eq_tailJ hR _ _ hd]
  apply tailJ_mul_kept_le_jointOdd _ _ _ _ _ _ (minRad_pos hlam c)
  · exact (fold_max_le _).2 ⟨hR,fun _ _ => le_rfl⟩
  · exact fun e _ => Peeling.dipoleDistOn_nonneg c e
  · intro e _
    refine ⟨keptE_nonneg c e,?_⟩
    induction e using Sym2.ind with
    | h i j =>
      change (if MultipoleLinked M lam (c i) (c j) then 0 else _) ≤ _
      split_ifs <;> first | positivity | exact le_rfl
  · intro e _ he
    induction e using Sym2.ind with
    | h i j =>
      change (if MultipoleLinked M lam (c i) (c j) then 0 else _) = 0
      apply ite_eq_left
      exact he.trans ((le_min (minRad_le lam c i) (minRad_le lam c j)).trans
        (le_mul_of_one_le_left (le_min (rhoD_pos hlam _).le (rhoD_pos hlam _).le) hM))

/-- The joint-profile comparison also covers coincident original dipoles.
A nonpositive edge distance forces the single global tail to vanish. -/
theorem globalTail_kept_le_jointOdd_all {W : Type*} [Fintype W] [Nonempty W]
    {M lam R : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (hR : 0 ≤ R)
    (c : W → ℂ × ℂ) (A : Finset (Sym2 W)) :
    ENNReal.ofReal (globalTail R (dipoleDistOn c) A * ∏ e ∈ A, keptE M lam c e) ≤
      jointOdd (minRad lam c) R (fun e : A => (dipoleDistOn c e : ℂ)) := by
  by_cases hd : ∀ e ∈ A, 0 < dipoleDistOn c e
  · exact globalTail_kept_le_jointOdd hM hlam hR c A hd
  · push Not at hd
    obtain ⟨e,he,hd⟩ := hd
    have hz : dipoleDistOn c e = 0 := le_antisymm hd (Peeling.dipoleDistOn_nonneg c e)
    have ht : globalTail R (dipoleDistOn c) A = 0 := by
      apply le_antisymm _ (globalTail_nonneg _ _ _)
      simpa only [hz,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,div_zero,min_eq_right zero_le_one]
        using globalTail_le (R := R) (d := dipoleDistOn c) he
    rw [ht,zero_mul,ENNReal.ofReal_zero]
    exact bot_le

end MultipoleBKT.ExpansionK.RouteSpatial

end
