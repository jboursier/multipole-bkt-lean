/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.OddEdges
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EvenEdge
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ProductCoordinates

/-!
# Mixed spatial integration with one odd maximum tail

See Lemma A.4. The odd coordinates are integrated
together. Every remaining coordinate contributes either a near-disc area
or the even-edge logarithm.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Set Limits MultipoleBKT.RouteLog
open scoped Classical ENNReal

/-- The radial profile for a near edge, or for a hatted even edge. -/
noncomputable def spatialProfile (even : Bool) (M s t d : ℝ) : ℝ :=
  if even then evenEdgeProfile M s t d else if d ≤ M * s then 1 else 0

/-- The near-disc and even-annulus calculations, with the same explicit
coefficient. The near profile has no logarithmic loss when `t=s`.
See the proof of Lemma A.4. -/
theorem lintegral_spatialProfile_le (even : Bool) {M s t : ℝ}
    (hM : 1 ≤ M) (hs : 0 < s) (hst : s ≤ t) :
    (∫⁻ z : ℂ, ENNReal.ofReal (spatialProfile even M s t ‖z‖)) ≤
      ENNReal.ofReal (Real.pi * (M ^ 2 + 3) * s ^ 2 *
        (if even then 1 + Real.log (t / s) else 1)) := by
  cases even with
  | true => exact lintegral_evenEdgeProfile_le hM hs hst
  | false =>
    have hMs : 0 ≤ M * s := mul_nonneg (by linarith) hs.le
    have heq : (fun z : ℂ => ENNReal.ofReal (spatialProfile false M s t ‖z‖)) =
        fun z => (Iic (M * s)).indicator (1 : ℝ → ℝ≥0∞) ‖z‖ := by
      funext z
      simp only [spatialProfile, Bool.false_eq_true, ite_false, Set.indicator, Set.mem_Iic,
        Pi.one_apply]
      split_ifs <;> simp
    rw [heq, lintegral_indicator_norm_le]
    have hnear : ENNReal.ofReal (M * s) ^ 2 * (NNReal.pi : ℝ≥0∞) =
        ENNReal.ofReal (Real.pi * M ^ 2 * s ^ 2) := by
      rw [← ENNReal.ofReal_pow hMs, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
        ← ENNReal.ofReal_mul (sq_nonneg (M * s))]
      congr 1
      ring
    change ENNReal.ofReal (M * s) ^ 2 * (NNReal.pi : ℝ≥0∞) ≤ _
    rw [hnear]
    apply ENNReal.ofReal_le_ofReal
    simp only [Bool.false_eq_true, ite_false, mul_one]
    nlinarith [Real.pi_pos, sq_nonneg s]

/-- Tonelli for the three edge families after the tree-coordinate change.
The right side retains the separate near and even factors and one jointly
integrated odd family. This is the spatial estimate preceding (A.25). -/
theorem lintegral_mixed_profiles (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I] (odd : I → Prop) [DecidablePred odd],
      Fintype.card {i // odd i} = q →
      ∀ (even : {i // ¬odd i} → Bool) (s t : {i // ¬odd i} → ℝ) (M a R : ℝ),
      1 ≤ M → 0 < a → a ≤ R → (∀ i, 0 < s i ∧ s i ≤ t i) →
      (∫⁻ z : I → ℂ,
        jointOdd a R (fun i : {i // odd i} => z i) *
          ∏ i : {i // ¬odd i}, ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) ‖z i‖)) ≤
        ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ q) *
          ∏ i : {i // ¬odd i}, ENNReal.ofReal (Real.pi * (M ^ 2 + 3) * s i ^ 2 *
            (if even i then 1 + Real.log (t i / s i) else 1)) := by
  obtain ⟨C, hC, hodd⟩ := lintegral_jointOdd q
  refine ⟨C, hC, fun I _ odd _ hq even s t M a R hM ha haR hst => ?_⟩
  have hm (i : {i // ¬odd i}) :
      Measurable fun z : ℂ => ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) ‖z‖) := by
    have hnear : MeasurableSet {z : ℂ | ‖z‖ ≤ M * s i} :=
      measurableSet_le (by fun_prop) measurable_const
    cases even i <;> simp only [spatialProfile, Bool.false_eq_true, ite_false, ite_true]
    · exact Measurable.ennreal_ofReal (Measurable.ite hnear measurable_const measurable_const)
    · unfold evenEdgeProfile
      apply Measurable.ennreal_ofReal
      exact Measurable.ite hnear measurable_const (by fun_prop)

  rw [lintegral_separate_coordinates odd _ (measurable_jointOdd a R) _ hm]
  exact mul_le_mul' (hodd {i // odd i} hq a R ha haR)
    (Finset.prod_le_prod fun i _ => lintegral_spatialProfile_le (even i) hM (hst i).1 (hst i).2)

/-- The normalized mixed-coordinate estimate. There is one logarithmic factor
per odd or even edge, and enlarging the exponent to the total number of tree
edges also covers the near edges.
See the proof of Lemma A.4. -/
theorem lintegral_normalized_mixed_profiles {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I], Fintype.card I ≤ k →
      ∀ (odd : I → Prop) [DecidablePred odd] (even : {i // ¬odd i} → Bool)
        (s t : {i // ¬odd i} → ℝ) (a R : ℝ),
      0 < a → a ≤ R → (∀ i, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ R) →
      (∫⁻ z : I → ℂ,
        jointOdd a R (fun i : {i // odd i} => z i) *
          ∏ i : {i // ¬odd i}, ENNReal.ofReal
            (spatialProfile (even i) M (s i) (t i) ‖z i‖ / s i ^ 2)) ≤
        ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ k) := by
  classical
  choose C hC hb using lintegral_jointOdd
  let K := 1 + Real.pi * (M ^ 2 + 3)
  let B := 1 + ∑ j ∈ range (k + 1), C j
  have hK : 1 ≤ K := by dsimp only [K]; nlinarith [Real.pi_pos, sq_nonneg M]
  have hB : 0 < B := by
    dsimp only [B]
    have := sum_nonneg (fun j (_ : j ∈ range (k + 1)) => (hC j).le)
    linarith
  refine ⟨B * K ^ k, mul_pos hB (pow_pos (lt_of_lt_of_le zero_lt_one hK) _),
    fun I _ hI odd _ even s t a R ha haR hst => ?_⟩
  let L := 1 + Real.log (R / a)
  have hL : 1 ≤ L := by
    have := Real.log_nonneg ((one_le_div ha).mpr haR)
    dsimp only [L]
    linarith
  have hq : Fintype.card {i // odd i} ≤ k := (Fintype.card_subtype_le _).trans hI
  have hp : Fintype.card {i // ¬odd i} ≤ k := (Fintype.card_subtype_le _).trans hI
  have hcnt : Fintype.card {i // odd i} + Fintype.card {i // ¬odd i} = Fintype.card I := by
    rw [Fintype.card_subtype_compl]
    have := Fintype.card_subtype_le odd
    omega
  have hCB : C (Fintype.card {i // odd i}) ≤ B := by
    have hx := single_le_sum (f := C) (fun j (_ : j ∈ range (k + 1)) => (hC j).le)
      (mem_range.mpr (Nat.lt_succ_of_le hq))
    dsimp only [B]
    linarith
  have hscalar (i : {i // ¬odd i}) :
      (∫⁻ z : ℂ, ENNReal.ofReal (spatialProfile (even i) M (s i) (t i) ‖z‖ / s i ^ 2)) ≤
        ENNReal.ofReal (K * L) := by
    have hs : 0 < s i := ha.trans_le (hst i).1
    have hlog : (if even i then 1 + Real.log (t i / s i) else 1) ≤ L := by
      split_ifs
      · have hquot : t i / s i ≤ R / a := div_le_div₀ (ha.le.trans haR) (hst i).2.2 ha (hst i).1
        have ht : 0 < t i / s i := div_pos (hs.trans_le (hst i).2.1) hs
        dsimp only [L]
        linarith [Real.log_le_log ht hquot]
      · exact hL
    have hnonneg (z : ℂ) : 0 ≤ spatialProfile (even i) M (s i) (t i) ‖z‖ := by
      unfold spatialProfile evenEdgeProfile
      split_ifs <;> positivity
    simp_rw [div_eq_mul_inv, ENNReal.ofReal_mul (hnonneg _)]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    calc
      _ ≤ ENNReal.ofReal (Real.pi * (M ^ 2 + 3) * s i ^ 2 *
          (if even i then 1 + Real.log (t i / s i) else 1)) * ENNReal.ofReal ((s i ^ 2)⁻¹) :=
        mul_le_mul_left (lintegral_spatialProfile_le (even i) hM hs (hst i).2.1) _
      _ = ENNReal.ofReal (Real.pi * (M ^ 2 + 3) *
          (if even i then 1 + Real.log (t i / s i) else 1)) := by
        rw [← ENNReal.ofReal_mul' (by positivity : 0 ≤ (s i ^ 2)⁻¹)]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal (K * L) := by
        apply ENNReal.ofReal_le_ofReal
        have hP : 0 ≤ Real.pi * (M ^ 2 + 3) := by positivity
        calc
          _ ≤ Real.pi * (M ^ 2 + 3) * L := mul_le_mul_of_nonneg_left hlog hP
          _ ≤ K * L := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (zero_le_one.trans hL)
  have hm (i : {i // ¬odd i}) :
      Measurable fun z : ℂ => ENNReal.ofReal
        (spatialProfile (even i) M (s i) (t i) ‖z‖ / s i ^ 2) := by
    unfold spatialProfile evenEdgeProfile
    have hnear : MeasurableSet {z : ℂ | ‖z‖ ≤ M * s i} := measurableSet_le (by fun_prop) measurable_const
    split_ifs <;> first
      | fun_prop
      | exact Measurable.ennreal_ofReal ((Measurable.ite hnear measurable_const (by fun_prop)).div_const _)
  rw [lintegral_separate_coordinates odd _ (measurable_jointOdd a R) _ hm]
  calc
    _ ≤ ENNReal.ofReal (C (Fintype.card {i // odd i}) * L ^ Fintype.card {i // odd i}) *
        ENNReal.ofReal (K * L) ^ Fintype.card {i // ¬odd i} := by
      apply mul_le_mul' (hb _ _ rfl a R ha haR)
      exact (prod_le_prod fun i _ => hscalar i).trans_eq (by simp)
    _ = ENNReal.ofReal (C (Fintype.card {i // odd i}) *
        K ^ Fintype.card {i // ¬odd i} * L ^ Fintype.card I) := by
      rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ K * L),
        ← ENNReal.ofReal_mul (mul_nonneg (hC _).le (pow_nonneg (zero_le_one.trans hL) _)),
        mul_pow]
      congr 1
      rw [← hcnt, pow_add]
      ring
    _ ≤ ENNReal.ofReal (B * K ^ k * L ^ k) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul (mul_le_mul hCB (pow_le_pow_right₀ hK hp)
        (pow_nonneg (zero_le_one.trans hK) _) hB.le) (pow_le_pow_right₀ hL hI)
          (pow_nonneg (zero_le_one.trans hL) _) (mul_nonneg hB.le (pow_nonneg (zero_le_one.trans hK) _))

end MultipoleBKT.SmallIntegral.RouteJ

end
