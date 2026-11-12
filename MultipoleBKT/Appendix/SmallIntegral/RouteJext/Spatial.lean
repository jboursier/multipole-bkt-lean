/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.EdgeIntegral
public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Root

/-!
# The logarithmic cutoff tree integral with an external root gain

See Lemma A.4. Endpoint coordinates preserve
volume. The common translation is integrated first. Each remaining coordinate
contributes one logarithmic factor.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Finset SimpleGraph Limits Peeling RouteJ
open scoped Classical ENNReal

/-- Weighted integration of the original retained tree in endpoint coordinates. -/
theorem lintegral_cutTree_weighted_le {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {M lam h : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) (u : V → ℂ)
    (hu : ∀ i, rho lam (u i) ≤ h) (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree)
    (A E : Finset (Sym2 V)) (root : V) (H : ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x : V → ℂ, H (x root) * ∏ e ∈ T.edgeFinset,
      ENNReal.ofReal (cutProfile A E M lam h u e (dipoleDistOn (ofPosVec x u) e))) ≤
      (∫⁻ t, H t) * ENNReal.ofReal
        ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card V - 1) *
          (1 + Real.log (17 * h / minRho lam u)) ^ (Fintype.card V - 1)) := by
  obtain ⟨par, hpar, hinj, himg⟩ := exists_parent_of_isTree hT root
  let I := {i : V // i ≠ root}
  let eOf (i : I) : Sym2 V := s(i.val, par i.val)
  let f (i : I) (d : ℝ) := ENNReal.ofReal (cutProfile A E M lam h u (eOf i) d)
  have hf (i : I) : Measurable (f i) :=
    ENNReal.measurable_ofReal.comp (measurable_cutProfile A E M lam h u (eOf i))
  have hp (x : V → ℂ) : (∏ e ∈ T.edgeFinset,
      ENNReal.ofReal (cutProfile A E M lam h u e (dipoleDistOn (ofPosVec x u) e))) =
      ∏ i : I, f i (dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) := by
    rw [← himg, prod_image hinj]
    exact (prod_subtype (univ.erase root) (p := fun i => i ≠ root) (by simp)
      (fun i => ENNReal.ofReal (cutProfile A E M lam h u s(i, par i)
        (dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))))))
  simp_rw [hp]
  have hb := lintegral_endpoint_product_le root par (fun i => T.dist i root)
    (fun i hi => (hpar i hi).2) u H hH f hf
  have hc : Fintype.card I = Fintype.card V - 1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_subtype_eq]
  let C := Real.pi * (M ^ 2 + 5)
  let L := 1 + Real.log (17 * h / minRho lam u)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hL : 0 ≤ L := by
    obtain ⟨i⟩ := ‹Nonempty V›
    have ha := minRho_pos hlam u
    have hah := (minRho_le_rho lam u i).trans (hu i)
    have := Real.log_nonneg ((one_le_div ha).2 (show minRho lam u ≤ 17 * h by linarith))
    dsimp only [L]
    linarith
  have hi : (∏ i : I, ∫⁻ z : ℂ, f i ‖z‖) ≤ ENNReal.ofReal (C * L) ^ Fintype.card I := by
    calc
      _ ≤ ∏ _i : I, ENNReal.ofReal (C * L) := prod_le_prod fun i _ =>
        lintegral_cutProfile_le A E hM hlam u hu (eOf i)
      _ = _ := by simp
  refine hb.trans ((mul_le_mul' le_rfl (mul_le_mul' le_rfl hi)).trans_eq ?_)
  rw [hc, ← ENNReal.ofReal_pow (mul_nonneg hC hL),
    show (4 : ℝ≥0∞) ^ (Fintype.card V - 1) = ENNReal.ofReal ((4 : ℝ) ^ (Fintype.card V - 1)) by
      rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
  rw [mul_left_comm, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  dsimp only [C, L]
  simp only [mul_pow]
  ring

/-- The remaining tree integrals after the logarithmic common translation.
The squared largest radius is kept for the cancellation (A.25). -/
theorem lintegral_cutTree_gain_le {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {N p₀ : ℕ} {β lam M eps : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
    (u : W → ℂ) (hu : ∀ i, rho lam (u i) ≤ eps * truncationScale p₀ β lam)
    (T : SimpleGraph W) [DecidableRel T.Adj] (hT : T.IsTree) (A E : Finset (Sym2 W))
    (root : W) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    (∫⁻ x : W → ℂ, (TwoComponentCoulomb.box N).indicator 1 (x root) *
      ENNReal.ofReal (gainW p₀ β lam eps V Z (maxRho lam u) (ofPosVec x u root)) *
        ∏ e ∈ T.edgeFinset, ENNReal.ofReal
          (cutProfile A E M lam (eps * truncationScale p₀ β lam) u e
            (dipoleDistOn (ofPosVec x u) e))) ≤
      ENNReal.ofReal (maxRho lam u ^ 2 *
        (N / (16 * (eps * truncationScale p₀ β lam) ^ 2) +
          8 * Real.pi * V.card * (1 + Real.log (17 * (eps * truncationScale p₀ β lam) / minRho lam u))) *
        ((4 * Real.pi * (M ^ 2 + 5)) ^ (Fintype.card W - 1) *
          (1 + Real.log (17 * (eps * truncationScale p₀ β lam) / minRho lam u)) ^ (Fintype.card W - 1))) := by
  let h := eps * truncationScale p₀ β lam
  let R := maxRho lam u
  let a := minRho lam u
  have hR : 0 < R := maxRho_pos hlam u
  have ha : 0 < a := minRho_pos hlam u
  have hRh : R ≤ h := (fold_max_le _).2 ⟨(le_max_right _ _).trans (hu (Classical.arbitrary W)), fun i _ => hu i⟩
  have hah : a ≤ h := (minRho_le_rho lam u (Classical.arbitrary W)).trans (hu _)
  have hh := hR.trans_le hRh
  let H (t : ℂ) := (TwoComponentCoulomb.box N).indicator 1 t *
    ENNReal.ofReal (gainW p₀ β lam eps V Z R (t, t + u root))
  have hH : Measurable H :=
    (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).mul
      ((measurable_gainW R).comp (by fun_prop)).ennreal_ofReal
  have hr := lintegral_gainW_log_le hh hR hRh (u root) (V := V) (Z := Z)
  have hlog : 1 / 2 + Real.log (4 * h / R) ≤ 1 + Real.log (17 * h / a) := by
    have hd : 4 * h / R ≤ 17 * h / a :=
      div_le_div₀ (by positivity) (by linarith) ha
        ((minRho_le_rho lam u (Classical.arbitrary W)).trans (rho_le_maxRho lam u _))
    have := Real.log_le_log (by positivity : 0 < 4 * h / R) hd
    linarith
  have hL : 0 ≤ 1 + Real.log (17 * h / a) := by
    have := Real.log_nonneg ((one_le_div ha).2 (show a ≤ 17 * h by linarith))
    linarith
  have hr' : (∫⁻ t, H t) ≤ ENNReal.ofReal (R ^ 2 *
      (N / (16 * h ^ 2) + 8 * Real.pi * V.card * (1 + Real.log (17 * h / a)))) := by
    refine hr.trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_left hlog
      (show 0 ≤ 8 * Real.pi * (V.card : ℝ) * R ^ 2 by positivity)
    dsimp only [R, h, a] at *
    simp only [div_eq_mul_inv] at *
    nlinarith
  exact (lintegral_cutTree_weighted_le hM hlam u hu T hT A E root H hH).trans
    ((mul_le_mul' hr' le_rfl).trans_eq (ENNReal.ofReal_mul (by positivity)).symm)

end MultipoleBKT.SmallIntegral.RouteJext

end
