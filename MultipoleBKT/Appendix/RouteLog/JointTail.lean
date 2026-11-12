/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Spatial
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The joint odd-edge maximum tail

See the proof of Lemma A.4. The odd edges share one maximum-distance tail. We integrate
that maximum jointly by shells. The logarithmic cube volume is computed before
summing the shells. The coefficient depends only on the number of edges.
-/

@[expose] public section

namespace MultipoleBKT.RouteLog

open MeasureTheory Set Finset
open scoped ENNReal

/-- Product logarithmic radial measure `∏ dtᵢ/tᵢ` above the common lower cutoff. -/
noncomputable def jointLogMeasure (a : ℝ) (q : ℕ) : Measure (Fin q → ℝ) :=
  (volume.restrict (Set.univ.pi fun _ : Fin q => Ioi a)).withDensity
    (fun x => ∏ i, ENNReal.ofReal ((x i)⁻¹))

private theorem measurable_log_density (q : ℕ) :
    Measurable (fun x : Fin q → ℝ => ∏ i, ENNReal.ofReal ((x i)⁻¹)) := by fun_prop

/-- The joint logarithmic cube volume is the `q`th power of one logarithm. -/
theorem jointLogMeasure_cube {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (q : ℕ) :
    jointLogMeasure a q (Set.univ.pi fun _ => Iic s) =
      ENNReal.ofReal (Real.log (s / a)) ^ q := by
  rw [jointLogMeasure, withDensity_apply _ (MeasurableSet.univ_pi fun _ => measurableSet_Iic),
    Measure.restrict_restrict (MeasurableSet.univ_pi fun _ => measurableSet_Iic)]
  have he : (Set.univ.pi fun _ : Fin q => Iic s) ∩ (Set.univ.pi fun _ : Fin q => Ioi a) =
      Set.univ.pi fun _ : Fin q => Ioc a s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic,
      Set.mem_Ioi, Set.mem_Ioc, forall_and]
    tauto
  rw [he]
  change (∫⁻ x : Fin q → ℝ, ∏ i, ENNReal.ofReal ((x i)⁻¹)
    ∂((Measure.pi fun _ : Fin q => (volume : Measure ℝ)).restrict
      (Set.univ.pi fun _ : Fin q => Ioc a s))) = _
  rw [Measure.restrict_pi_pi, TwoComponentCoulomb.lintegral_fin_prod_eq_prod
    (fun _ => volume.restrict (Ioc a s)) (fun _ t => ENNReal.ofReal (t⁻¹)) (fun _ => by fun_prop)]
  have hi : (∫⁻ t in Ioc a s, ENNReal.ofReal (t⁻¹)) = ENNReal.ofReal (Real.log (s / a)) := by
    convert lintegral_annular_inverse_square ha has using 1
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    congr 1
    field_simp
  simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem summable_shell (q : ℕ) :
    Summable (fun n : ℕ => Real.exp (-2) ^ n * ((n : ℝ) + 2) ^ q) := by
  have hr : ‖Real.exp (-2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) q hr
  have hs' : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ q * Real.exp (-2) ^ (n + 2)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).mpr hs
  have he : (fun n : ℕ => Real.exp (-2) ^ n * ((n : ℝ) + 2) ^ q) =
      fun n : ℕ => (Real.exp (-2) ^ 2)⁻¹ *
        (((n : ℝ) + 2) ^ q * Real.exp (-2) ^ (n + 2)) := by
    funext n
    rw [pow_add]
    field_simp
  rw [he]
  exact hs'.mul_left _

/-- A finite shell coefficient, independent of either radius. -/
noncomputable def jointTailConstant (q : ℕ) : ℝ :=
  1 + ∑' n : ℕ, Real.exp (-2) ^ n * ((n : ℝ) + 2) ^ q

private theorem jointTailConstant_pos (q : ℕ) : 0 < jointTailConstant q := by
  unfold jointTailConstant
  have : 0 ≤ ∑' n : ℕ, Real.exp (-2) ^ n * ((n : ℝ) + 2) ^ q :=
    tsum_nonneg fun n => by positivity
  linarith

private theorem exists_exp_shell {R m : ℝ} (hR : 0 < R) (hRm : R < m) :
    ∃ n : ℕ, R * Real.exp n < m ∧ m ≤ R * Real.exp (n + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.log (m / R))
  have hm : 0 < m := hR.trans hRm
  have hmN : m ≤ R * Real.exp N := by
    have he := Real.exp_le_exp.mpr hN
    rw [Real.exp_log (div_pos hm hR)] at he
    simpa [mul_comm] using (div_le_iff₀ hR).mp he
  have hmem : m ∈ Ioc (R * Real.exp (0 : ℕ)) (R * Real.exp N) := by
    simpa using And.intro hRm hmN
  have hi := Ioc_subset_biUnion_Ioc N (fun n : ℕ => R * Real.exp n) hmem
  simp only [Set.mem_iUnion, Set.mem_Ioc] at hi
  obtain ⟨n, _, hn⟩ := hi
  exact ⟨n, by simpa only [Nat.cast_add, Nat.cast_one] using hn⟩

/-- Joint integration of the odd edges with their single maximum-distance tail.
Here `q+1` allows any positive number of odd edges. -/
theorem lintegral_joint_maximum_tail_le {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) (q : ℕ) :
    ∫⁻ x : Fin (q + 1) → ℝ,
      ENNReal.ofReal (min 1 ((R / (Finset.univ.sup' Finset.univ_nonempty x)) ^ 2))
        ∂jointLogMeasure a (q + 1) ≤
      ENNReal.ofReal (jointTailConstant (q + 1) * (1 + Real.log (R / a)) ^ (q + 1)) := by
  have hR : 0 < R := ha.trans_le haR
  let m : (Fin (q + 1) → ℝ) → ℝ := fun x => Finset.univ.sup' Finset.univ_nonempty x
  let f : (Fin (q + 1) → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (min 1 ((R / m x) ^ 2))
  let μ := jointLogMeasure a (q + 1)
  let B : Set (Fin (q + 1) → ℝ) := {x | m x ≤ R}
  let S : ℕ → Set (Fin (q + 1) → ℝ) := fun n =>
    {x | R * Real.exp n < m x ∧ m x ≤ R * Real.exp (n + 1)}
  have hmeas : Measurable m := by
    have he : (Finset.univ.sup' Finset.univ_nonempty
        (fun i (x : Fin (q + 1) → ℝ) => x i)) = m := by
      funext x
      rw [Finset.sup'_apply]
    rw [← he]
    exact Finset.measurable_sup' Finset.univ_nonempty fun i _ => measurable_pi_apply i
  have hB : MeasurableSet B := measurableSet_le hmeas measurable_const
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_lt measurable_const hmeas).inter (measurableSet_le hmeas measurable_const)
  have hcover : Set.univ ⊆ B ∪ ⋃ n, S n := by
    intro x _
    by_cases hx : m x ≤ R
    · exact Or.inl hx
    · obtain ⟨n, hn⟩ := exists_exp_shell hR (lt_of_not_ge hx)
      exact Or.inr (Set.mem_iUnion.mpr ⟨n, hn⟩)
  have hcube (s : ℝ) : {x | m x ≤ s} = Set.univ.pi fun _ => Iic s := by
    ext x
    simp only [m, Finset.sup'_le_iff, Finset.mem_univ, true_implies, Set.mem_pi, Set.mem_univ,
      Set.mem_ofPred_eq, Set.mem_Iic]
  have hbase : ∫⁻ x in B, f x ∂μ ≤ ENNReal.ofReal (1 + Real.log (R / a)) ^ (q + 1) := by
    calc
      _ ≤ ∫⁻ x in B, 1 ∂μ := by
        apply setLIntegral_mono' hB
        intro x hx
        apply ENNReal.ofReal_le_one.mpr
        exact min_le_left _ _
      _ = ENNReal.ofReal (Real.log (R / a)) ^ (q + 1) := by
        rw [setLIntegral_one, show μ B = jointLogMeasure a (q + 1)
          (Set.univ.pi fun _ => Iic R) by rw [← hcube],
          jointLogMeasure_cube ha haR]
      _ ≤ _ := by gcongr; linarith
  have hshell (n : ℕ) : ∫⁻ x in S n, f x ∂μ ≤
      ENNReal.ofReal (Real.exp (-2) ^ n * ((n : ℝ) + 2) ^ (q + 1)) *
        ENNReal.ofReal (1 + Real.log (R / a)) ^ (q + 1) := by
    have hsn : a ≤ R * Real.exp (n + 1) := by
      calc a ≤ R := haR
           _ ≤ R * Real.exp (n + 1) := le_mul_of_one_le_right hR.le (Real.one_le_exp (by positivity))
    have htail (x : Fin (q + 1) → ℝ) (hx : x ∈ S n) :
        f x ≤ ENNReal.ofReal (Real.exp (-2) ^ n) := by
      have hm : 0 < m x := (mul_pos hR (Real.exp_pos _)).trans hx.1
      have hdiv : R / m x ≤ (Real.exp n)⁻¹ := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ hm (Real.exp_pos _)).2
        simpa only [one_mul] using hx.1.le
      have hmin : 0 ≤ R / m x := div_nonneg hR.le hm.le
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ ((Real.exp (n : ℝ))⁻¹) ^ 2 :=
          (min_le_right _ _).trans (pow_le_pow_left₀ hmin hdiv 2)
        _ = Real.exp (-2) ^ n := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1
          ring
    calc
      _ ≤ ∫⁻ x in S n, ENNReal.ofReal (Real.exp (-2) ^ n) ∂μ :=
        setLIntegral_mono' (hS n) htail
      _ = ENNReal.ofReal (Real.exp (-2) ^ n) * μ (S n) := by rw [setLIntegral_const, mul_comm]
      _ ≤ ENNReal.ofReal (Real.exp (-2) ^ n) *
          μ {x | m x ≤ R * Real.exp (n + 1)} := by
        gcongr
        exact fun x hx => hx.2
      _ = ENNReal.ofReal (Real.exp (-2) ^ n) *
          ENNReal.ofReal (Real.log ((R * Real.exp (n + 1)) / a)) ^ (q + 1) := by
        rw [hcube, jointLogMeasure_cube ha hsn]
      _ ≤ _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        rw [Real.log_div (mul_pos hR (Real.exp_pos _)).ne' ha.ne',
          Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp,
          Real.log_div hR.ne' ha.ne']
        rw [ENNReal.ofReal_pow (by positivity : 0 ≤ (n : ℝ) + 2),
          mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul (by positivity)]
        gcongr
        have hlog : 0 ≤ Real.log R - Real.log a := by
          rw [← Real.log_div hR.ne' ha.ne']
          exact Real.log_nonneg ((one_le_div ha).2 haR)
        nlinarith
  calc
    _ = ∫⁻ x in Set.univ, f x ∂μ := by rw [Measure.restrict_univ]
    _ ≤ ∫⁻ x in B ∪ ⋃ n, S n, f x ∂μ := lintegral_mono_set hcover
    _ ≤ (∫⁻ x in B, f x ∂μ) + ∫⁻ x in ⋃ n, S n, f x ∂μ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (1 + Real.log (R / a)) ^ (q + 1) +
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (-2) ^ n * ((n : ℝ) + 2) ^ (q + 1)) *
          ENNReal.ofReal (1 + Real.log (R / a)) ^ (q + 1) := by
      apply add_le_add hbase
      exact (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hshell)
    _ = _ := by
      rw [ENNReal.tsum_mul_right,
        ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (summable_shell (q + 1)),
        jointTailConstant, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_add (by norm_num) (tsum_nonneg fun n => by positivity), ENNReal.ofReal_one,
        add_mul, one_mul, ENNReal.ofReal_pow (by
          have := Real.log_nonneg ((one_le_div ha).2 haR); linarith)]

/-- The joint maximum-tail integral in the paper's literal `∏ dtᵢ/tᵢ` form. -/
theorem joint_maximum_tail_integral (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a R : ℝ, 0 < a → a ≤ R →
      (∫⁻ x in Set.univ.pi (fun _ : Fin (q + 1) => Ioi a),
        ENNReal.ofReal (min 1 ((R / (Finset.univ.sup' Finset.univ_nonempty x)) ^ 2)) *
          ∏ i, ENNReal.ofReal ((x i)⁻¹)) ≤
        ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ (q + 1)) := by
  refine ⟨jointTailConstant (q + 1), jointTailConstant_pos (q + 1), fun a R ha haR => ?_⟩
  have hm : Measurable (fun x : Fin (q + 1) → ℝ =>
      Finset.univ.sup' Finset.univ_nonempty x) := by
    have he : (Finset.univ.sup' Finset.univ_nonempty
        (fun i (x : Fin (q + 1) → ℝ) => x i)) =
        (fun x : Fin (q + 1) → ℝ => Finset.univ.sup' Finset.univ_nonempty x) := by
      funext x
      rw [Finset.sup'_apply]
    rw [← he]
    exact Finset.measurable_sup' Finset.univ_nonempty fun i _ => measurable_pi_apply i
  have hf : Measurable (fun x : Fin (q + 1) → ℝ =>
      ENNReal.ofReal (min 1 ((R / (Finset.univ.sup' Finset.univ_nonempty x)) ^ 2))) := by
    fun_prop
  have he := lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (Set.univ.pi fun _ : Fin (q + 1) => Ioi a))
    (measurable_log_density (q + 1)) hf
  have hb := lintegral_joint_maximum_tail_le ha haR q
  change (∫⁻ x, _ ∂(volume.restrict _).withDensity _) ≤ _ at hb
  rw [he] at hb
  simpa only [Pi.mul_apply, mul_comm] using hb

end MultipoleBKT.RouteLog

end
