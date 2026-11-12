/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Definitions
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.OddEdges

/-!
# Keeping the original odd maximum tail in the spatial majorant

See Lemma A.4. The original tail and all inverse
square odd weights are bounded by one joint profile at fixed dipole vectors.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Limits Peeling
open scoped Classical ENNReal

private theorem min_one_sq {x : ℝ} (hx : 0 ≤ x) : min x 1 ^ 2 = min 1 (x ^ 2) := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h, min_eq_right (pow_le_one₀ hx h)]
  · rw [min_eq_right h, min_eq_left (one_le_pow₀ h)]
    norm_num

/-- Compare the odd factor with one joint profile on its edge subtype.
The hypotheses express the local inverse-square cutoff, rather than any
integrated estimate. The empty-family value is exactly one on both sides. -/
theorem tailJ_mul_kept_le_jointOdd {V : Type*} [Fintype V]
    (r : V → ℝ) (d : Sym2 V → ℝ) (A : Finset (Sym2 V)) (w : Sym2 V → ℝ)
    (a R : ℝ) (ha : 0 < a) (hR : univ.fold max 0 r ≤ R)
    (hd : ∀ e ∈ A, 0 ≤ d e)
    (hw : ∀ e ∈ A, 0 ≤ w e ∧ w e ≤ (d e ^ 2)⁻¹)
    (hzero : ∀ e ∈ A, d e ≤ a → w e = 0) :
    ENNReal.ofReal (tailJ r d A * ∏ e ∈ A, w e) ≤
      jointOdd a R (fun e : A => (d e : ℂ)) := by
  classical
  by_cases hA : A.Nonempty
  · have hne : Nonempty A := hA.to_subtype
    let := hne
    by_cases hz : ∃ e ∈ A, w e = 0
    · obtain ⟨e, he, heq⟩ := hz
      rw [prod_eq_zero he heq, mul_zero, ENNReal.ofReal_zero]
      exact bot_le
    push Not at hz
    have hda : ∀ e ∈ A, a < d e := fun e he => lt_of_not_ge (fun h => hz e he (hzero e he h))
    have hn (e : A) : ‖(d e : ℂ)‖ = d e := by simp [abs_of_nonneg (hd e e.property)]
    have hsup : univ.sup' univ_nonempty (fun e : A => ‖(d e : ℂ)‖) = A.sup' hA d := by
      simp_rw [hn]
      apply le_antisymm
      · exact (sup'_le_iff _ _).mpr fun e _ => le_sup' d e.property
      · exact (sup'_le_iff _ _).mpr fun e he =>
          le_sup' (fun e : A => d e) (mem_univ ⟨e, he⟩)
    have hraw : 0 ≤ univ.fold max 0 r := (le_fold_max _).mpr (Or.inl le_rfl)
    have hA' := hA
    obtain ⟨e, he⟩ := hA'
    have hD : 0 < A.sup' hA d := (ha.trans (hda e he)).trans_le (le_sup' d he)
    have ht : tailJ r d A ≤ min 1 ((R / A.sup' hA d) ^ 2) := by
      unfold tailJ
      rw [dite_eq_left hA, min_one_sq (div_nonneg hraw hD.le)]
      apply min_le_min le_rfl
      exact pow_le_pow_left₀ (div_nonneg hraw hD.le)
        (div_le_div_of_nonneg_right hR hD.le) 2
    unfold jointOdd
    rw [dite_eq_left hne,
      Set.indicator_of_mem (show (fun e : A => (d e : ℂ)) ∈ {z : A → ℂ | ∀ e, a < ‖z e‖} by
        intro e
        rw [hn]
        exact hda e e.property), hsup]
    have hp : (∏ e ∈ A, ENNReal.ofReal ((d e ^ 2)⁻¹)) =
        ∏ e : A, ENNReal.ofReal ((‖(d e : ℂ)‖ ^ 2)⁻¹) := by
      simp_rw [hn]
      exact Finset.prod_subtype A (fun _ => Iff.rfl) _
    rw [← hp, ENNReal.ofReal_mul (by unfold tailJ; rw [dite_eq_left hA]; positivity),
      ENNReal.ofReal_prod_of_nonneg (fun e he => (hw e he).1)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal ht)
      (prod_le_prod fun e he => ENNReal.ofReal_le_ofReal (hw e he).2)
  · have hi : IsEmpty A := ⟨fun e => hA ⟨e, e.property⟩⟩
    have hAe : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    have hp : (∏ e ∈ A, w e) = 1 := by rw [hAe, prod_empty]
    unfold tailJ jointOdd
    rw [dite_eq_right hA, dite_eq_right (not_nonempty_iff.mpr hi), hp]
    norm_num


/-- The original odd factor for `J` is dominated without splitting its tail.
See the proof of Lemma A.4. -/
theorem odd_factor_le_jointOdd {V : Type*} [Fintype V] [Nonempty V]
    {M lam : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (c : V → ℂ × ℂ)
    (A : Finset (Sym2 V)) :
    ENNReal.ofReal (tailJ (fun i => dipoleLength (c i)) (dipoleDistOn c) A *
      ∏ e ∈ A, keptE M lam c e) ≤
        jointOdd (minRad lam c) (maxRad lam c) (fun e : A => (dipoleDistOn c e : ℂ)) := by
  apply tailJ_mul_kept_le_jointOdd _ _ _ _ _ _ (minRad_pos hlam c)
  · exact (fold_max_le _).mpr ⟨hlam.le.trans (lam_le_maxRad lam c), fun i _ =>
      (le_max_left _ _).trans (rhoD_le_maxRad lam c i)⟩
  · intro e _
    exact Peeling.dipoleDistOn_nonneg c e
  · intro e _
    refine ⟨keptE_nonneg c e, ?_⟩
    induction e using Sym2.ind with
    | h i j =>
      change (if MultipoleLinked M lam (c i) (c j) then 0 else _) ≤ _
      split_ifs <;> first | positivity | exact le_rfl
  · intro e _ he
    induction e using Sym2.ind with
    | h i j =>
      change (if MultipoleLinked M lam (c i) (c j) then 0 else _) = 0
      apply ite_eq_left
      have hs : minRad lam c ≤ min (rhoD lam (c i)) (rhoD lam (c j)) :=
        le_min (minRad_le lam c i) (minRad_le lam c j)
      exact he.trans (hs.trans (le_mul_of_one_le_left
        (le_min (rhoD_pos hlam _).le (rhoD_pos hlam _).le) hM))

end MultipoleBKT.SmallIntegral.RouteJ

end
