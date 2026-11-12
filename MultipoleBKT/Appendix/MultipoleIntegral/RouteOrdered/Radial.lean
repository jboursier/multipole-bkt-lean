/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.Basic
public import MultipoleBKT.Appendix.RouteLog.API
public import MultipoleBKT.Appendix.RadialIntegral

/-!
# The ordered multipole radial integral

See (A.13) and (A.14). This file keeps the literal nested radial integral.
The comparison with the separated-core logarithmic majorant is proved
here, before applying its bounds in the separate temperature regimes.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Set Finset
open scoped ENNReal

/-- The polar integral of a non-root radius, with the upper limit fixed by
the root radius. It is defined on the whole real carrier. -/
noncomputable def orderedInner (β lam r : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 r, ENNReal.ofReal (t * max t lam ^ (2 - β))

/-- The literal ordered integral in (A.13). The exponent `n` counts the
non-root radii. Choosing `D = Ioi 0` gives the infinite cutoff. -/
noncomputable def orderedRadial (β lam : ℝ) (D : Set ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ r in D, ENNReal.ofReal (r * max r lam ^ (-β)) * orderedInner β lam r ^ n

/-- The inner integral is monotone in its upper limit. -/
theorem orderedInner_mono (β lam : ℝ) : Monotone (orderedInner β lam) := by
  intro r s hrs
  exact lintegral_mono_set (Ioc_subset_Ioc_right hrs)

/-- At and above the core radius, the inner integral is the zeroth
logarithmic moment. -/
theorem orderedInner_eq_moment {β lam r : ℝ} (hlam : 0 < lam) (hlr : lam ≤ r) :
    orderedInner β lam r = ENNReal.ofReal (RouteLog.radialLogMoment (4 - β) lam r 0) := by
  have he : 4 - β - 2 = 2 - β := by ring
  simpa only [orderedInner, he, pow_zero, mul_one] using
    RouteLog.lintegral_radialLogMoment (4 - β) 0 hlam hlr

/-- The exact inner core integral. -/
theorem orderedInner_core {β lam : ℝ} (hlam : 0 < lam) :
    orderedInner β lam lam = ENNReal.ofReal (lam ^ (4 - β) / 2) := by
  rw [orderedInner_eq_moment hlam le_rfl, RouteLog.radialLogMoment_split (4 - β) 0 hlam le_rfl]
  simp

/-- On the core the inner moment is bounded by its value at `λ`. -/
theorem orderedInner_le_core {β lam r : ℝ} (hlam : 0 < lam) (hr : r ≤ lam) :
    orderedInner β lam r ≤ ENNReal.ofReal (lam ^ (4 - β)) := by
  calc
    _ ≤ orderedInner β lam lam := orderedInner_mono β lam hr
    _ = ENNReal.ofReal (lam ^ (4 - β) / 2) := orderedInner_core hlam
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Real.rpow_pos_of_pos hlam (4 - β)])

/-- The full root-core contribution, with all inner radii retained. -/
theorem orderedRadial_core_le {β lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    orderedRadial β lam (Ioc 0 lam) n ≤
      ENNReal.ofReal (lam ^ ((4 - β) * (n + 1) - 2)) := by
  have hbase : (∫⁻ r in Ioc 0 lam, ENNReal.ofReal (r * lam ^ (-β))) =
      ENNReal.ofReal (lam ^ (2 - β) / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_mul_const]
      have hid : (∫ r in Ioc 0 lam, r) = lam ^ 2 / 2 := by
        rw [← intervalIntegral.integral_of_le hlam.le, integral_id]
        ring
      rw [hid]
      congr 1
      rw [div_mul_eq_mul_div, ← Real.rpow_two, ← Real.rpow_add hlam]
      congr 2
    · exact (continuous_id.mul continuous_const).continuousOn.integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun r hr => mul_nonneg hr.1.le (Real.rpow_nonneg hlam.le _))
  unfold orderedRadial
  calc
    _ ≤ ∫⁻ r in Ioc 0 lam, ENNReal.ofReal (r * lam ^ (-β)) *
        ENNReal.ofReal (lam ^ (4 - β)) ^ n := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro r hr
      rw [max_eq_right hr.2]
      gcongr
      exact orderedInner_le_core hlam hr.2
    _ = ENNReal.ofReal (lam ^ (2 - β) / 2) * ENNReal.ofReal (lam ^ (4 - β)) ^ n := by
      rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), hbase]
    _ ≤ ENNReal.ofReal (lam ^ (2 - β)) * ENNReal.ofReal (lam ^ (4 - β)) ^ n := by
      gcongr
      nlinarith [Real.rpow_pos_of_pos hlam (2 - β)]
    _ = _ := by
      rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hlam.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _),
        ← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
      congr 2
      ring

/-- Tonelli identifies the zeroth-logarithm inner product with the power
of the literal inner integral. -/
theorem orderedInner_pow_eq {β lam r : ℝ} (hlam : 0 < lam) (n : ℕ) :
    orderedInner β lam r ^ n =
      ∫⁻ t in Set.univ.pi (fun _ : Fin n => Ioc 0 r),
        ∏ i, ENNReal.ofReal (t i * max (t i) lam ^ (2 - β)) := by
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (t * max t lam ^ (2 - β)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (continuous_id.mul ((continuous_id.max continuous_const).rpow_const
      (fun t => Or.inl (lt_max_of_lt_right hlam).ne'))).measurable
  rw [volume_pi, Measure.restrict_pi_pi,
    lintegral_pi_prod_eq' (0 : ℝ) (fun _ => volume.restrict (Ioc 0 r))
      (fun _ t => ENNReal.ofReal (t * max t lam ^ (2 - β))) (fun _ => hm)]
  simp only [prod_const, card_univ, Fintype.card_fin, orderedInner]

/-- The necessary consumer comparison with the logarithmic radial majorant. The largest-radius core
is estimated separately, while the annulus keeps the exact ordered
inner product. -/
theorem orderedRadial_le_logMajorant {β lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h)
    (k : ℕ) :
    orderedRadial β lam (Ioc 0 h) (k + 1) ≤ RouteLog.orderedLogIntegral β lam h k 0 := by
  have hunion : Ioc (0 : ℝ) h = Ioc 0 lam ∪ Ioc lam h :=
    (Ioc_union_Ioc_eq_Ioc hlam.le hlh).symm
  have hdis : Disjoint (Ioc (0 : ℝ) lam) (Ioc lam h) := by
    apply Set.disjoint_left.mpr
    intro r hr hs
    exact (not_lt_of_ge hr.2) hs.1
  have htail : (∫⁻ r in Ioc lam h,
      ENNReal.ofReal (r * max r lam ^ (-β)) * orderedInner β lam r ^ (k + 1)) =
      ∫⁻ r in Ioc lam h, ENNReal.ofReal (r ^ (1 - β)) *
        ∫⁻ t in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 r),
          ENNReal.ofReal ((1 + Real.log (r / RouteLog.minimumRadius lam t)) ^ 0) *
            ∏ i, ENNReal.ofReal (t i * max (t i) lam ^ (2 - β)) := by
    apply setLIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [max_eq_left hr.1.le, orderedInner_pow_eq hlam]
    simp only [pow_zero, ENNReal.ofReal_one, one_mul]
    congr 2
    rw [show 1 - β = -β + 1 by ring, Real.rpow_add_one (hlam.trans hr.1).ne', mul_comm]
  unfold orderedRadial
  rw [hunion, lintegral_union measurableSet_Ioc hdis, htail]
  change orderedRadial β lam (Ioc 0 lam) (k + 1) + _ ≤ _
  unfold RouteLog.orderedLogIntegral
  apply add_le_add _ le_rfl
  have he : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
  simpa only [he] using orderedRadial_core_le (β := β) hlam (k + 1)

/-- Below four the ordered integral reduces to the single power integral
of (A.2), including its separate core contribution. -/
theorem orderedRadial_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam (Ioc 0 h) (k + 1) ≤
        ENNReal.ofReal (C * (lam ^ ((4 - β) * (k + 2) - 2) +
          ∫ r in lam..h, r ^ ((4 - β) * (k + 2) - 3))) := by
  obtain ⟨C, hC, hbound⟩ := RouteLog.ordered_radial_lt_four hβ hβ4 k 0
  exact ⟨C, hC, fun lam h hlam hlh =>
    (orderedRadial_le_logMajorant hlam hlh k).trans (hbound lam h hlam hlh)⟩

/-- At the critical temperature the inner logarithm remains inside the
ordered integral. Logarithmic integration evaluates its convergent outer logarithmic moment. -/
theorem orderedRadial_four (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial 4 lam (Ioc 0 h) (k + 1) ≤ ENNReal.ofReal (C * lam ^ (-2 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := RouteLog.ordered_radial_ge_four_bound (β := 4) le_rfl k 0
  refine ⟨C, hC, fun lam h hlam hlh => ?_⟩
  simpa using (orderedRadial_le_logMajorant (β := 4) hlam hlh k).trans (hbound lam h hlam hlh)

/-- Above four, scaling all ordered radii gives the same power of `λ` as
in (A.14). The constant is uniform in the upper cutoff. -/
theorem orderedRadial_gt_four {β : ℝ} (hβ : 4 < β) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam (Ioc 0 h) (k + 1) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  obtain ⟨C, hC, hbound⟩ := RouteLog.ordered_radial_ge_four_bound hβ.le k 0
  exact ⟨C, hC, fun lam h hlam hlh =>
    (orderedRadial_le_logMajorant hlam hlh k).trans (hbound lam h hlam hlh)⟩

/-- Internal monotone exhaustion for the ordered outer radius. -/
theorem internal_orderedRadial_infinite_of_finite {β lam : ℝ} (hlam : 0 < lam)
    (n : ℕ) {K : ℝ≥0∞}
    (hbound : ∀ h : ℝ, lam ≤ h → orderedRadial β lam (Ioc 0 h) n ≤ K) :
    orderedRadial β lam (Ioi 0) n ≤ K := by
  let F (r : ℝ) := ENNReal.ofReal (r * max r lam ^ (-β)) * orderedInner β lam r ^ n
  have hm : Measurable F := by
    apply Measurable.mul
    · apply ENNReal.measurable_ofReal.comp
      exact (continuous_id.mul ((continuous_id.max continuous_const).rpow_const
        (fun r => Or.inl (lt_max_of_lt_right hlam).ne'))).measurable
    · exact (orderedInner_mono β lam).measurable.pow_const n
  have hcover : Ioi (0 : ℝ) = ⋃ j : ℕ, Ioc 0 (lam + j) := by
    ext r
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · intro hr
      obtain ⟨j, hj⟩ := exists_nat_gt (r - lam)
      exact ⟨j, hr, by linarith⟩
    · rintro ⟨j, hr, _⟩
      exact hr
  have heq : (Ioi (0 : ℝ)).indicator F =
      fun r => ⨆ j : ℕ, (Ioc 0 (lam + j)).indicator F r := by
    rw [hcover]
    ext r
    by_cases hr : r ∈ ⋃ j : ℕ, Ioc 0 (lam + j)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hr
      rw [indicator_of_mem hr]
      apply le_antisymm
      · exact le_iSup_of_le j (by rw [indicator_of_mem hj])
      · apply iSup_le
        intro i
        by_cases hi : r ∈ Ioc 0 (lam + i)
        · rw [indicator_of_mem hi]
        · rw [indicator_of_notMem hi]; exact zero_le
    · rw [indicator_of_notMem hr]
      apply le_antisymm bot_le
      apply iSup_le
      intro j
      rw [indicator_of_notMem (fun hj => hr (mem_iUnion.mpr ⟨j, hj⟩))]
      exact le_rfl
  change ∫⁻ r in Ioi 0, F r ≤ K
  rw [← lintegral_indicator measurableSet_Ioi, heq,
    lintegral_iSup (fun j => hm.indicator measurableSet_Ioc)]
  · apply iSup_le
    intro j
    rw [lintegral_indicator measurableSet_Ioc]
    exact hbound (lam + j) (by linarith [Nat.cast_nonneg (α := ℝ) j])
  · intro i j hij r
    dsimp only
    by_cases hi : r ∈ Ioc 0 (lam + i)
    · have hj : r ∈ Ioc 0 (lam + j) :=
        ⟨hi.1, hi.2.trans (by linarith [show (i : ℝ) ≤ j from Nat.cast_le.mpr hij])⟩
      rw [indicator_of_mem hi, indicator_of_mem hj]
    · rw [indicator_of_notMem hi]
      exact zero_le

/-- Above and at four, the infinite cutoff is allowed for every fixed
number of radii, with the exact scaling exponent of (A.14). -/
theorem orderedRadial_infinite_ge_four {β : ℝ} (hβ : 4 ≤ β) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedRadial β lam (Ioi 0) (k + 1) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  by_cases heq : β = 4
  · subst β
    obtain ⟨C, hC, hb⟩ := orderedRadial_four k
    refine ⟨C, hC, fun lam hlam => internal_orderedRadial_infinite_of_finite hlam (k + 1) ?_⟩
    intro h hlh
    simpa only [sub_self, zero_mul, zero_sub] using hb lam h hlam hlh
  · obtain ⟨C, hC, hb⟩ := orderedRadial_gt_four (lt_of_le_of_ne hβ (Ne.symm heq)) k
    exact ⟨C, hC, fun lam hlam => internal_orderedRadial_infinite_of_finite hlam (k + 1)
      (fun h hlh => hb lam h hlam hlh)⟩

/-- Below four, the infinite cutoff is allowed precisely in the
negative-exponent regime used for `|S| ≤ p*(β)`. -/
theorem orderedRadial_infinite_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4)
    (k : ℕ) (hE : (4 - β) * (k + 2) - 2 < 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedRadial β lam (Ioi 0) (k + 1) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  obtain ⟨C, hC, hbound⟩ := orderedRadial_lt_four hβ hβ4 k
  let E : ℝ := (4 - β) * (k + 2) - 2
  have hEn : E < 0 := hE
  have hneg : 0 < -E := neg_pos.mpr hEn
  refine ⟨C * (1 + 1 / (-E)), by positivity, fun lam hlam => ?_⟩
  apply internal_orderedRadial_infinite_of_finite hlam (k + 1)
  intro h hlh
  have hp : (∫ r in lam..h, r ^ ((4 - β) * (k + 2) - 3)) ≤ lam ^ E / (-E) := by
    rw [Appendix.integral_rpow_of_ne hlam hlh (by linarith :
      (4 - β) * (k + 2) - 3 ≠ -1)]
    have he : (4 - β) * (k + 2) - 3 + 1 = E := by dsimp only [E]; ring
    rw [he]
    have hh : 0 < h := hlam.trans_le hlh
    have hn : 0 ≤ h ^ E := Real.rpow_nonneg hh.le _
    apply (div_le_iff_of_neg hEn).mpr
    have hE0 : E ≠ 0 := hEn.ne
    field_simp
    nlinarith
  refine (hbound lam h hlam hlh).trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ C * (lam ^ E + lam ^ E / (-E)) := by gcongr
    _ = _ := by ring

end MultipoleBKT.MultipoleIntegral

end
