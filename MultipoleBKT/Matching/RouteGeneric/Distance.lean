/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Matching.RouteGeneric.PolynomialNull
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Squared-distance exceptional polynomials

Section 4.1 of the paper. Real and imaginary
coordinates turn squared distances into polynomials. Distinct unordered pairs have
an endpoint belonging to just one pair, which proves nontriviality by evaluation.
-/

@[expose] public section

open MeasureTheory MvPolynomial

namespace MultipoleBKT.RouteGeneric

variable {ι : Type*} [Fintype ι]

/-- Real coordinates of a finite complex configuration. -/
noncomputable def realCoordinates (ι : Type*) [Fintype ι] :
    (ι → ℂ) ≃ᵐ (ι ⊕ ι → ℝ) :=
  (MeasurableEquiv.piCongrRight fun _ : ι => Complex.measurableEquivRealProd).trans
    ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℝ).symm)

theorem measurePreserving_realCoordinates :
    MeasurePreserving (realCoordinates ι) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm _).comp
    ((volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).comp
      (volume_preserving_pi fun _ => Complex.volume_preserving_equiv_real_prod))

/-- The polynomial `|z_i-z_j|²`. -/
noncomputable def squaredDistance (i j : ι) : MvPolynomial (ι ⊕ ι) ℝ :=
  (X (Sum.inl i) - X (Sum.inl j)) ^ 2 + (X (Sum.inr i) - X (Sum.inr j)) ^ 2

theorem eval_squaredDistance (z : ι → ℂ) (i j : ι) :
    eval (realCoordinates ι z) (squaredDistance i j) = ‖z i - z j‖ ^ 2 := by
  simp only [squaredDistance, map_add, map_pow, map_sub, eval_X]
  change ((z i).re - (z j).re) ^ 2 + ((z i).im - (z j).im) ^ 2 = _
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

omit [Fintype ι] in
private theorem eval_spike [DecidableEq ι] (a i j : ι) :
    eval (fun u : ι ⊕ ι => if u = Sum.inl a then 1 else 0) (squaredDistance i j) =
      ((if i = a then 1 else 0) - (if j = a then 1 else 0)) ^ 2 := by
  simp [squaredDistance]

omit [Fintype ι] in
private theorem weighted_ne_of_endpoint {i j k l : ι} (hij : i ≠ j)
    (hik : i ≠ k) (hil : i ≠ l) {a b : ℝ} (ha : a ≠ 0) :
    C a * squaredDistance i j - C b * squaredDistance k l ≠ 0 := by
  classical
  intro h
  have he := congrArg (eval (fun u : ι ⊕ ι => if u = Sum.inl i then 1 else 0)) h
  simp [eval_spike, hij.symm, hik.symm, hil.symm] at he
  exact ha he

omit [Fintype ι] in
/-- Distinct unordered pairs give a nonzero squared-distance difference. -/
theorem distanceDifference_ne_zero {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    squaredDistance i j - squaredDistance k l ≠ 0 := by
  classical
  have hsym : squaredDistance j i = squaredDistance i j := by
    unfold squaredDistance
    ring
  have hsym' : squaredDistance l k = squaredDistance k l := by
    unfold squaredDistance
    ring
  by_cases hi : i = k ∨ i = l
  · have hj : j ≠ k ∧ j ≠ l := by
      rcases hi with rfl | rfl <;> constructor <;> intro h <;> apply hne <;> simp_all
    simpa [hsym] using weighted_ne_of_endpoint hij.symm hj.1 hj.2 (a := 1) (b := 1) one_ne_zero
  · obtain ⟨hik, hil⟩ := not_or.1 hi
    simpa using weighted_ne_of_endpoint hij hik hil (a := 1) (b := 1) one_ne_zero

/-- Nullity follows from the nonzero polynomial after squaring, rather than circle slicing. -/
theorem volume_distance_eq {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l)
    (hne : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    volume {z : ι → ℂ | ‖z i - z j‖ = ‖z k - z l‖} = 0 := by
  have hp := volume_polynomial_zero _ (distanceDifference_ne_zero hij hkl hne)
  have hn := (measurePreserving_realCoordinates (ι := ι)).measure_preimage_equiv
    {x | eval x (squaredDistance i j - squaredDistance k l) = 0}
  refine measure_mono_null (fun z hz => ?_) (hn.trans hp)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, map_sub, eval_squaredDistance]
  rw [hz, sub_self]

omit [Fintype ι] in
/-- The contact-cutoff polynomial is nonzero for every fixed cutoff. -/
theorem distanceCutoff_ne_zero {i j : ι} (hij : i ≠ j) (h : ℝ) :
    squaredDistance i j - C (4 * h ^ 2) ≠ 0 := by
  classical
  intro heq
  have h0 := congrArg (eval (fun _ : ι ⊕ ι => (0 : ℝ))) heq
  have h1 := congrArg (eval (fun u : ι ⊕ ι => if u = Sum.inl i then 1 else 0)) heq
  simp [squaredDistance] at h0
  simp [eval_spike, hij.symm] at h1
  simp [h0] at h1

/-- Contacts with the stopping cutoff occur only on a polynomial null set. -/
theorem volume_contact_cutoff {i j : ι} (hij : i ≠ j) (h : ℝ) :
    volume {z : ι → ℂ | ‖z i - z j‖ / 2 = h} = 0 := by
  have hp := volume_polynomial_zero _ (distanceCutoff_ne_zero hij h)
  have hn := (measurePreserving_realCoordinates (ι := ι)).measure_preimage_equiv
    {x | eval x (squaredDistance i j - C (4 * h ^ 2)) = 0}
  refine measure_mono_null (fun z hz => ?_) (hn.trans hp)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, map_sub, eval_squaredDistance, eval_C]
  have : ‖z i - z j‖ = 2 * h := by
    change ‖z i - z j‖ / 2 = h at hz
    linarith
  rw [this]
  ring

omit [Fintype ι] in
/-- A same-sign contact and a matched opposite-sign stopping time give a nonzero
polynomial. The matching `σ` is fixed before constructing the polynomial. -/
theorem contactStop_ne_zero (σ : Equiv.Perm ι) (i j k : ι) :
    C 4 * squaredDistance (Sum.inl i) (Sum.inl j) -
      squaredDistance (Sum.inl k) (Sum.inr (σ k)) ≠ 0 := by
  have hs : squaredDistance (Sum.inr (σ k)) (Sum.inl k) =
      squaredDistance (Sum.inl k) (Sum.inr (σ k)) := by unfold squaredDistance; ring
  have hn := weighted_ne_of_endpoint (i := Sum.inr (σ k)) (j := Sum.inl k)
    (k := Sum.inl i) (l := Sum.inl j) Sum.inr_ne_inl Sum.inr_ne_inl Sum.inr_ne_inl
    (a := 1) (b := 4) one_ne_zero
  simp only [hs, C_1, one_mul, ne_eq, sub_eq_zero] at hn ⊢
  exact Ne.symm hn

omit [Fintype ι] in
/-- Negative contacts use the positive endpoint of the fixed matched dipole to
prove that their stopping-time polynomial is nonzero. -/
theorem contactStopMinus_ne_zero (σ : Equiv.Perm ι) (i j k : ι) :
    C 4 * squaredDistance (Sum.inr i) (Sum.inr j) -
      squaredDistance (Sum.inl k) (Sum.inr (σ k)) ≠ 0 := by
  have hn := weighted_ne_of_endpoint (i := Sum.inl k) (j := Sum.inr (σ k))
    (k := Sum.inr i) (l := Sum.inr j) Sum.inl_ne_inr Sum.inl_ne_inr Sum.inl_ne_inr
    (a := 1) (b := 4) one_ne_zero
  simp only [C_1, one_mul, ne_eq, sub_eq_zero] at hn ⊢
  exact Ne.symm hn

end MultipoleBKT.RouteGeneric

end
