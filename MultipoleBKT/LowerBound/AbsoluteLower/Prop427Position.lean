/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Core
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Radial
public import MultipoleBKT.Appendix.SmallIntegral.TreeTerm
public import MultipoleBKT.LowerBound.AbsoluteLower.RoutePosition.EndpointProduct
public import MultipoleBKT.Appendix.RouteLog.Spatial

/-!
# Endpoint coordinates and logarithmic spatial integration

The proof of Lemma 4.58, using (A.8), (A.9)
and Lemma A.1.

At fixed dipole vectors, `RoutePosition.lintegral_endpoint_product_le`
expands the four closest-endpoint sectors on every edge of the fixed
tree. Jacobian-one change of variables makes these edge coordinates
independent. The root has area at most N. A normalized near indicator
costs `4πM²`. The exact disc-plus-annulus formula gives the far factor
`8π ell(17h, min(ρᵢ,ρⱼ))`, where `ell(R,r) = 1 + log⁺(R/r)`.

`lintegral_treeTerm_le` preserves this logarithm on every far edge and
keeps the original single-dipole density in the remaining vector integral.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Set Finset SimpleGraph Limits SmallIntegral
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {M lam : ℝ}

/-! ### The far weight -/

/-- The far weight `𝟙_{d ≤ R'} max(d, M min(ρ_d, ρ_e))^{-2}`. -/
noncomputable def farW (M lam R' : ℝ) (d e : ℂ × ℂ) : ℝ :=
  (if dipoleDist d e ≤ R' then 1 else 0) *
    (max (dipoleDist d e) (M * min (rhoD lam d) (rhoD lam e)) ^ 2)⁻¹

theorem farW_comm (M lam R' : ℝ) (d e : ℂ × ℂ) : farW M lam R' d e = farW M lam R' e d := by
  unfold farW
  rw [dipoleDist_comm, min_comm (rhoD lam d)]

theorem farW_nonneg (M lam R' : ℝ) (d e : ℂ × ℂ) : 0 ≤ farW M lam R' d e := by
  unfold farW
  split_ifs <;> positivity

/-- The far weight as a function of unordered pairs of labels. -/
noncomputable def farE {ι : Type*} (M lam R' : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => farW M lam R' (c i) (c j)) fun _ _ => farW_comm M lam R' _ _

theorem farE_nonneg {ι : Type*} (M lam R' : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    0 ≤ farE M lam R' c e := by
  induction e using Sym2.ind with
  | h i j => exact farW_nonneg M lam R' _ _

theorem measurable_farW (M lam R' : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => farW M lam R' q.1 q.2 := by
  unfold farW
  have hd : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => dipoleDist q.1 q.2 := measurable_dipoleDist
  have hr : ∀ f : (ℂ × ℂ) × (ℂ × ℂ) → ℂ × ℂ, Measurable f →
      Measurable fun q => rhoD lam (f q) := fun f hf =>
    ((measurable_fst.sub measurable_snd).norm.max measurable_const).comp hf
  refine Measurable.mul ?_ ?_
  · exact Measurable.ite (measurableSet_le hd measurable_const) measurable_const measurable_const
  · exact ((hd.max (measurable_const.mul ((hr _ measurable_fst).min
      (hr _ measurable_snd)))).pow_const
      2).inv

theorem measurable_farE {ι : Type*} (M lam R' : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => farE M lam R' c e := by
  induction e using Sym2.ind with
  | h i j =>
    exact (measurable_farW M lam R').comp (f := fun c : ι → ℂ × ℂ => (c i, c j)) (by fun_prop)

/-- `1 + log⁺(R'/x)`. -/
noncomputable def ell (R' x : ℝ) : ℝ := 1 + max (Real.log (R' / x)) 0

theorem one_le_ell (R' x : ℝ) : 1 ≤ ell R' x := le_add_of_nonneg_right (le_max_right _ _)

/-- `ell` is nonincreasing in `x > 0`. -/
theorem ell_anti {R' x y : ℝ} (hR' : 0 ≤ R') (hx : 0 < x) (hxy : x ≤ y) : ell R' y ≤ ell R' x := by
  unfold ell
  refine add_le_add le_rfl (max_le_max ?_ le_rfl)
  rcases hR'.eq_or_lt with h | h
  · rw [← h, zero_div, zero_div]
  · exact Real.log_le_log (div_pos h (hx.trans_le hxy)) (div_le_div_of_nonneg_left h.le hx hxy)

/-- A normalized near indicator gives the area of a disc in an edge coordinate. -/
theorem lintegral_nearProfile_le {s : ℝ} (hs : 0 < s) (hM : 0 ≤ M) :
    4 * (∫⁻ z : ℂ, ENNReal.ofReal ((if ‖z‖ ≤ M * s then 1 else 0) / s ^ 2)) ≤
      ENNReal.ofReal (4 * Real.pi * M ^ 2) := by
  have heq (z : ℂ) : ENNReal.ofReal ((if ‖z‖ ≤ M * s then 1 else 0) / s ^ 2) =
      ENNReal.ofReal (s ^ 2)⁻¹ * (Iic (M * s)).indicator 1 ‖z‖ := by
    by_cases hz : ‖z‖ ≤ M * s
    · rw [ite_eq_left hz, indicator_of_mem (show ‖z‖ ∈ Iic (M * s) from hz), Pi.one_apply, mul_one, one_div,
        ENNReal.ofReal_inv_of_pos (by positivity)]
    · rw [ite_eq_right hz, indicator_of_notMem (show ‖z‖ ∉ Iic (M * s) from hz), zero_div, ENNReal.ofReal_zero, mul_zero]
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator_norm_le]
  have heq : ENNReal.ofReal (s ^ 2)⁻¹ *
      (4 * (ENNReal.ofReal (M * s) ^ 2 * NNReal.pi)) =
      ENNReal.ofReal (4 * Real.pi * M ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_pow (mul_nonneg hM hs.le),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 4,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  exact le_of_eq (by rw [← heq]; ring)

/-- The truncated inverse-square profile integrates logarithmically.
This uses the exact disc-plus-annulus calculation before estimating the logarithm.
proof of Lemma 4.58. -/
theorem lintegral_farProfile_le {ρ : ℝ} (hρ0 : 0 < ρ) (hM : 1 ≤ M) (R' : ℝ) :
    4 * (∫⁻ z : ℂ, ENNReal.ofReal
      ((if ‖z‖ ≤ R' then 1 else 0) * (max ‖z‖ (M * ρ) ^ 2)⁻¹)) ≤
      ENNReal.ofReal (8 * Real.pi * ell R' ρ) := by
  set m := M * ρ with hm
  have hm0 : 0 < m := mul_pos (by linarith) hρ0
  set φ : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal
    ((if r ≤ R' then 1 else 0) * (max r m ^ 2)⁻¹) with hφ

  set H := max R' m with hH
  have hmH : m ≤ H := le_max_right _ _
  have hz : ∀ z : ℂ, φ ‖z‖ ≤ (Metric.closedBall (0 : ℂ) H).indicator
      (fun z => ENNReal.ofReal (max ‖z‖ m ^ (-2 : ℝ))) z := by
    intro z
    simp only [hφ]
    by_cases hz : ‖z‖ ≤ R'
    · have hmem : z ∈ Metric.closedBall (0 : ℂ) H := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hz.trans (le_max_left _ _)
      rw [Set.indicator_of_mem hmem, ite_eq_left hz, one_mul]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [Real.rpow_neg (lt_max_of_lt_right hm0).le, Real.rpow_two]
    · rw [ite_eq_right hz, zero_mul, ENNReal.ofReal_zero]
      exact bot_le
  have hball := RouteLog.lintegral_planar_truncated_inverse_square hm0 hmH
  have hset : {z : ℂ | ‖z‖ ≤ H} = Metric.closedBall (0 : ℂ) H := by
    ext z
    simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  rw [hset] at hball
  have hlog : Real.log (H / m) ≤ max (Real.log (R' / ρ)) 0 := by
    rcases le_total R' m with h | h
    · rw [hH, max_eq_right h, div_self hm0.ne', Real.log_one]
      exact le_max_right _ _
    · rw [hH, max_eq_left h]
      refine le_max_of_le_left ?_
      have hR'0 : 0 < R' := hm0.trans_le h
      refine Real.log_le_log (div_pos hR'0 hm0) (div_le_div_of_nonneg_left hR'0.le hρ0 ?_)
      rw [hm]
      nlinarith
  calc 4 * ∫⁻ z : ℂ, φ ‖z‖
      ≤ 4 * ∫⁻ z : ℂ, (Metric.closedBall (0 : ℂ) H).indicator
          (fun z => ENNReal.ofReal (max ‖z‖ m ^ (-2 : ℝ))) z :=
        mul_le_mul' le_rfl (lintegral_mono hz)
    _ ≤ 4 * ENNReal.ofReal (2 * Real.pi * (1 + Real.log (H / m))) := by
        have heq : (fun z : ℂ => ENNReal.ofReal (max ‖z‖ m ^ (-2 : ℝ))) =
            (fun z : ℂ => ENNReal.ofReal (max ‖z‖ m ^ 2)⁻¹) := by
          funext z
          rw [Real.rpow_neg (lt_max_of_lt_right hm0).le, Real.rpow_two]
        rw [lintegral_indicator measurableSet_closedBall, heq, hball]
        gcongr
        norm_num
    _ = ENNReal.ofReal (4 * (2 * Real.pi * (1 + Real.log (H / m)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (8 * Real.pi * ell R' ρ) := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold ell
        have := Real.pi_pos
        nlinarith

/-! ### A tree term -/

section TreeTerm

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem radF_ofPosVec (lam : ℝ) (x u : ι → ℂ) : radF lam (ofPosVec x u) = radiusFactor lam u := by
  unfold radF radiusFactor
  rw [maxRad_ofPosVec_eq]
  congr 1
  exact prod_congr rfl fun i _ => by rw [ofPosVec_apply, rhoD_mk]

omit [Nonempty ι] in
theorem measurable_radF (lam : ℝ) : Measurable (radF (ι := ι) lam) := by
  unfold radF
  refine (Finset.measurable_prod _ fun i _ => ?_).mul ?_
  · exact ((measurable_norm.comp ((measurable_fst.sub measurable_snd).comp
      (measurable_pi_apply i))).max measurable_const).pow_const _
  · exact (measurable_maxRad lam).pow_const _

open scoped Classical in
/-- **A tree term, integrated** (see the module docstring): the positions are integrated along
`T`, the near edges cost `4πM²` and the far edges `8π ell R' (min(ρ_i, ρ_j))`. -/
theorem lintegral_treeTerm_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M)
    (β : ℝ) {h : ℝ} (hh : 0 ≤ h) (a R' : ℝ) {T : SimpleGraph ι} (hT : T.IsTree)
    (N : Finset (Sym2 ι))
    (hN : N ⊆ T.edgeFinset) (Nb : ℕ) :
    ∫⁻ c in boxConfig ι Nb, ENNReal.ofReal (radF lam c *
        ((∏ e ∈ N, nearE M lam c e) * ∏ e ∈ T.edgeFinset \ N, farE M lam R' c e) *
        ∏ i, dipoleWeight χ β lam h a ((c i).2 - (c i).1)) ≤
      (Nb : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ N.card *
        ∫⁻ u : ι → ℂ, ENNReal.ofReal (radiusFactor lam u * ∏ i, dipoleWeight χ β lam h a (u i)) *
          ∏ e ∈ T.edgeFinset \ N,
            ENNReal.ofReal (8 * Real.pi * ell R' (edgeMin id (fun i => rho lam (u i)) e)) := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  set r : ι := Classical.arbitrary ι
  set w : (ι → ℂ × ℂ) → Sym2 ι → ℝ := fun c e =>
    if e ∈ N then nearE M lam c e else farE M lam R' c e with hw
  have hw0 : ∀ c e, 0 ≤ w c e := fun c e => by
    simp only [hw]
    split_ifs
    · exact nearE_nonneg M lam c e
    · exact farE_nonneg M lam R' c e
  have hwm : ∀ e, Measurable fun c : ι → ℂ × ℂ => w c e := fun e => by
    simp only [hw]
    split_ifs
    · exact measurable_nearE M lam e
    · exact measurable_farE M lam R' e
  set D : (ι → ℂ × ℂ) → ℝ := fun c => radF lam c *
    ∏ i, dipoleWeight χ β lam h a ((c i).2 - (c i).1) with hD
  have hD0 : ∀ c, 0 ≤ D c := fun c => by
    simp only [hD]
    exact mul_nonneg (radF_nonneg hlam c) (prod_nonneg fun i _ =>
      dipoleWeight_nonneg χ β lam hh _)
  have hDm : Measurable D := (measurable_radF lam).mul (Finset.measurable_prod _ fun i _ =>
    (measurable_dipoleWeight hχ hlam β h a).comp
      ((measurable_snd.sub measurable_fst).comp (measurable_pi_apply i)))
  set G : (ι → ℂ × ℂ) → ℝ≥0∞ := fun c => (box Nb).indicator 1 (c r).1 *
    (ENNReal.ofReal (D c) * ∏ e ∈ T.edgeFinset, ENNReal.ofReal (w c e)) with hG
  have hGm : Measurable G := by
    refine ((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box Nb)).comp
      (measurable_fst.comp (measurable_pi_apply r))).mul
      (hDm.ennreal_ofReal.mul (Finset.measurable_prod _ fun e _ => (hwm e).ennreal_ofReal))
  -- step 1: the integrand is below `G`
  have hstep1 : ∫⁻ c in boxConfig ι Nb, ENNReal.ofReal (radF lam c *
      ((∏ e ∈ N, nearE M lam c e) * ∏ e ∈ T.edgeFinset \ N, farE M lam R' c e) *
      ∏ i, dipoleWeight χ β lam h a ((c i).2 - (c i).1)) ≤ ∫⁻ c, G c := by
    rw [← lintegral_indicator (measurableSet_boxConfig Nb)]
    refine lintegral_mono fun c => ?_
    by_cases hc : c ∈ boxConfig ι Nb
    · rw [indicator_of_mem hc]
      have hcr : (c r).1 ∈ box Nb := ((Set.mem_univ_pi.1 hc) r).1
      simp only [hG, indicator_of_mem hcr, Pi.one_apply, one_mul]
      rw [← ENNReal.ofReal_prod_of_nonneg fun e _ => hw0 c e, ← ENNReal.ofReal_mul (hD0 c)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      have hsplit : ∏ e ∈ T.edgeFinset, w c e =
          (∏ e ∈ N, nearE M lam c e) * ∏ e ∈ T.edgeFinset \ N, farE M lam R' c e := by
        rw [← prod_sdiff hN, mul_comm]
        congr 1
        · refine prod_congr rfl fun e he => ?_
          simp only [hw, ite_eq_left he]
        · refine prod_congr rfl fun e he => ?_
          simp only [hw, ite_eq_right (mem_sdiff.1 he).2]
      rw [hsplit, hD]
      ring
    · rw [indicator_of_notMem hc]
      exact zero_le
  -- step 2: positions and dipole vectors
  set K : (ι → ℂ) → Sym2 ι → ℝ≥0∞ := fun u e => if e ∈ N then ENNReal.ofReal (4 * Real.pi * M ^ 2)
    else ENNReal.ofReal (8 * Real.pi * ell R' (edgeMin id (fun i => rho lam (u i)) e)) with hK
  have hstep2 : ∫⁻ c, G c ≤ ∫⁻ u : ι → ℂ, ENNReal.ofReal (radiusFactor lam u *
      ∏ i, dipoleWeight χ β lam h a (u i)) * ((Nb : ℝ≥0∞) * ∏ e ∈ T.edgeFinset, K u e) := by
    rw [lintegral_eq_lintegral_pos_vec G hGm]
    refine lintegral_mono fun u => ?_
    have hDu : ∀ x : ι → ℂ, D (fun i => (x i, x i + u i)) =
        radiusFactor lam u * ∏ i, dipoleWeight χ β lam h a (u i) := fun x => by
      simp only [hD]
      rw [show (fun i => ((x i, x i + u i) : ℂ × ℂ)) = ofPosVec x u from rfl, radF_ofPosVec]
      congr 1
      refine prod_congr rfl fun i _ => ?_
      simp
    simp only [hG, hDu]
    set W : Sym2 ι → (ι → ℂ) → ℝ≥0∞ := fun e x => ENNReal.ofReal (w (ofPosVec x u) e) with hW
    let s : Sym2 ι → ℝ := edgeMin id (fun i => rho lam (u i))
    let φ : Sym2 ι → ℝ → ℝ≥0∞ := fun e d => if e ∈ N then
      ENNReal.ofReal ((if d ≤ M * s e then 1 else 0) / s e ^ 2) else
      ENNReal.ofReal ((if d ≤ R' then 1 else 0) * (max d (M * s e) ^ 2)⁻¹)
    have hφ (e : Sym2 ι) : Measurable (φ e) := by
      dsimp only [φ]
      split_ifs
      · exact ((Measurable.ite measurableSet_Iic measurable_const measurable_const).div
          measurable_const).ennreal_ofReal
      · exact ((Measurable.ite measurableSet_Iic measurable_const measurable_const).mul
          (((measurable_id.max measurable_const).pow_const 2).inv)).ennreal_ofReal
    have hprofile (x : ι → ℂ) (e : Sym2 ι) : W e x =
        φ e (Peeling.dipoleDistOn (ofPosVec x u) e) := by
      simp only [W, hw, φ]
      by_cases he : e ∈ N
      · simp only [ite_eq_left he]
        induction e using Sym2.ind with
        | h i j =>
          simp only [nearE, symmLift_mk, nearW, rhoD_mk,
            ofPosVec_apply, s, edgeMin_mk, id_eq, Peeling.dipoleDistOn_mk]
          rfl
      · simp only [ite_eq_right he]
        induction e using Sym2.ind with
        | h i j =>
          simp only [farE, symmLift_mk, farW, rhoD_mk,
            ofPosVec_apply, s, edgeMin_mk, id_eq, Peeling.dipoleDistOn_mk]
          rfl
    have hb (e : Sym2 ι) : 4 * (∫⁻ z : ℂ, φ e ‖z‖) ≤ K u e := by
      have hs : 0 < s e := by
        induction e using Sym2.ind with
        | h i j => exact lt_min (rho_pos hlam _) (rho_pos hlam _)
      simp only [φ, hK]
      split_ifs
      · exact lintegral_nearProfile_le hs hM0
      · exact lintegral_farProfile_le hs hM R'
    have htree := RoutePosition.lintegral_endpoint_product_le hT r u φ hφ
      ((box Nb).indicator 1) (measurable_one.indicator (TwoComponentCoulomb.measurableSet_box Nb))
    have htree' : (∫⁻ x : ι → ℂ, (box Nb).indicator (1 : ℂ → ℝ≥0∞) (x r) *
        ∏ e ∈ T.edgeFinset, W e x) ≤ (Nb : ℝ≥0∞) * ∏ e ∈ T.edgeFinset, K u e := by
      simp_rw [hprofile]
      refine htree.trans ?_
      rw [lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box Nb),
        TwoComponentCoulomb.volume_box]
      exact mul_le_mul' le_rfl (prod_le_prod fun e _ => hb e)
    have hre : ∀ x : ι → ℂ, (box Nb).indicator 1 (x r) *
        (ENNReal.ofReal (radiusFactor lam u * ∏ i, dipoleWeight χ β lam h a (u i)) *
          ∏ e ∈ T.edgeFinset, ENNReal.ofReal (w (fun i => (x i, x i + u i)) e)) =
        ENNReal.ofReal (radiusFactor lam u * ∏ i, dipoleWeight χ β lam h a (u i)) *
          ((box Nb).indicator 1 (x r) * ∏ e ∈ T.edgeFinset, W e x) := fun x => by
      rw [mul_left_comm]
      rfl
    rw [lintegral_congr fun x => hre x, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl htree'
  refine hstep1.trans (hstep2.trans (le_of_eq ?_))
  rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.natCast_ne_top Nb)
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  refine lintegral_congr fun u => ?_
  have hKsplit : ∏ e ∈ T.edgeFinset, K u e = ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ N.card *
      ∏ e ∈ T.edgeFinset \ N,
        ENNReal.ofReal (8 * Real.pi * ell R' (edgeMin id (fun i => rho lam (u i)) e)) := by
    rw [← prod_sdiff hN, mul_comm]
    congr 1
    · rw [← prod_const]
      exact prod_congr rfl fun e he => by simp only [hK, ite_eq_left he]
    · exact prod_congr rfl fun e he => by simp only [hK, ite_eq_right (mem_sdiff.1 he).2]
  rw [hKsplit]
  ring

end TreeTerm

end AbsoluteLower

end MultipoleBKT

end
