/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.JointTail
public import TwoComponentCoulomb.LowerBound.PolarPi

/-!
# Joint integration of the odd-edge coordinates

See Lemma A.4. Polar coordinates turn the planar inverse-square weights
into `dt/t`. Logarithmic integration evaluates their shared maximum tail.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Set Finset
open MultipoleBKT.RouteLog
open scoped ENNReal

/-- Polar coordinates for a function of several norms. The angular integral
contributes `(2π)^n` even when the radial variables remain coupled.
See the proof of Lemma A.4. -/
theorem lintegral_pi_norm {n : ℕ} (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : Fin n → ℂ, F (fun i => ‖z i‖)) =
      ENNReal.ofReal (2 * Real.pi) ^ n *
        ∫⁻ r in Set.univ.pi (fun _ : Fin n => Ioi 0), (∏ i, ENNReal.ofReal (r i)) * F r := by
  have hm : Measurable fun z : Fin n → ℂ => F (fun i => ‖z i‖) := by fun_prop
  rw [TwoComponentCoulomb.lintegral_pi_complex_eq_polar _ hm]
  have heq (r : Fin n → ℝ) (hr : r ∈ Set.univ.pi (fun _ => Ioi 0)) :
      (∫⁻ θ in Set.univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi),
        (∏ i, ENNReal.ofReal (r i)) * F (fun i => ‖circleMap 0 (r i) (θ i)‖)) =
      ENNReal.ofReal (2 * Real.pi) ^ n * ((∏ i, ENNReal.ofReal (r i)) * F r) := by
    have hn (θ : Fin n → ℝ) : (fun i => ‖circleMap 0 (r i) (θ i)‖) = r := by
      funext i
      rw [norm_circleMap_zero, abs_of_pos (mem_univ_pi.mp hr i)]
    simp_rw [hn]
    rw [setLIntegral_const]
    have hvol : volume (Set.univ.pi (fun _ : Fin n => Ioo (-Real.pi) Real.pi)) =
        ENNReal.ofReal (2 * Real.pi) ^ n := by
      rw [volume_pi, Measure.pi_pi]
      simp only [Real.volume_Ioo, show Real.pi - -Real.pi = 2 * Real.pi by ring,
        prod_const, card_univ, Fintype.card_fin]
    rw [hvol, mul_comm]
  rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioi) heq,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]

/-- The planar odd-edge integral with one maximum tail. No tail factor is
assigned to an individual edge. The extra angular coefficient is explicit.
See the proof of Lemma A.4. -/
theorem lintegral_joint_odd_edges (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a R : ℝ, 0 < a → a ≤ R →
      (∫⁻ z in {z : Fin (q + 1) → ℂ | ∀ i, a < ‖z i‖},
        ENNReal.ofReal (min 1 ((R / (univ.sup' univ_nonempty (fun i => ‖z i‖))) ^ 2)) *
          ∏ i, ENNReal.ofReal ((‖z i‖ ^ 2)⁻¹)) ≤
        ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ (q + 1)) := by
  obtain ⟨C, hC, hb⟩ := joint_maximum_tail_integral q
  refine ⟨(2 * Real.pi) ^ (q + 1) * C, by positivity, fun a R ha haR => ?_⟩
  let A := Set.univ.pi (fun _ : Fin (q + 1) => Ioi a)
  have hA : MeasurableSet A := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  let f : (Fin (q + 1) → ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (min 1 ((R / (univ.sup' univ_nonempty r)) ^ 2)) *
      ∏ i, ENNReal.ofReal ((r i ^ 2)⁻¹)
  have hsup : Measurable fun r : Fin (q + 1) → ℝ => univ.sup' univ_nonempty r := by
    have he : (univ.sup' univ_nonempty (fun i (r : Fin (q + 1) → ℝ) => r i)) =
        (fun r : Fin (q + 1) → ℝ => univ.sup' univ_nonempty r) := by
      funext r
      rw [Finset.sup'_apply]
    rw [← he]
    exact Finset.measurable_sup' univ_nonempty fun i _ => measurable_pi_apply i
  have hf : Measurable f := by unfold f; fun_prop
  have hnorm : Measurable fun z : Fin (q + 1) → ℂ => fun i => ‖z i‖ := by fun_prop
  have hset : MeasurableSet {z : Fin (q + 1) → ℂ | ∀ i, a < ‖z i‖} := by
    simpa only [A, Set.preimage, Set.mem_univ_pi, Set.mem_Ioi] using hA.preimage hnorm
  have he : (∫⁻ z in {z : Fin (q + 1) → ℂ | ∀ i, a < ‖z i‖},
      ENNReal.ofReal (min 1 ((R / (univ.sup' univ_nonempty (fun i => ‖z i‖))) ^ 2)) *
        ∏ i, ENNReal.ofReal ((‖z i‖ ^ 2)⁻¹)) =
      ENNReal.ofReal (2 * Real.pi) ^ (q + 1) *
        ∫⁻ r in A, ENNReal.ofReal (min 1 ((R / (univ.sup' univ_nonempty r)) ^ 2)) *
          ∏ i, ENNReal.ofReal ((r i)⁻¹) := by
    rw [← lintegral_indicator hset]
    have hind : (fun z : Fin (q + 1) → ℂ =>
        {z : Fin (q + 1) → ℂ | ∀ i, a < ‖z i‖}.indicator
          (fun z => f (fun i => ‖z i‖)) z) = fun z => A.indicator f (fun i => ‖z i‖) := by
      funext z
      simp only [Set.indicator, A, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ioi]
    change (∫⁻ z : Fin (q + 1) → ℂ,
      {z : Fin (q + 1) → ℂ | ∀ i, a < ‖z i‖}.indicator (fun z => f (fun i => ‖z i‖)) z) = _
    rw [hind, lintegral_pi_norm _ (hf.indicator hA)]
    congr 1
    have hpoint (r : Fin (q + 1) → ℝ) (hr : r ∈ Set.univ.pi (fun _ => Ioi 0)) :
        (∏ i, ENNReal.ofReal (r i)) * A.indicator f r =
          A.indicator (fun r => ENNReal.ofReal (min 1 ((R / (univ.sup' univ_nonempty r)) ^ 2)) *
            ∏ i, ENNReal.ofReal ((r i)⁻¹)) r := by
      by_cases h : r ∈ A
      · rw [indicator_of_mem h, indicator_of_mem h]
        unfold f
        rw [← mul_assoc, mul_comm (∏ i, ENNReal.ofReal (r i)), mul_assoc, ← prod_mul_distrib]
        congr 1
        apply prod_congr rfl
        intro i _
        rw [← ENNReal.ofReal_mul (mem_univ_pi.mp hr i).le]
        congr 1
        field_simp
      · simp only [indicator_of_notMem h, mul_zero]
    rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioi) hpoint,
      lintegral_indicator hA, Measure.restrict_restrict hA]
    congr 1
    congr 1
    apply Set.inter_eq_left.mpr
    intro r hr
    exact mem_univ_pi.mpr fun i => ha.trans (mem_univ_pi.mp hr i)
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.pi) ^ (q + 1) *
        ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ (q + 1)) :=
      mul_le_mul_right (hb a R ha haR) _
    _ = _ := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

open scoped Classical

/-- The odd-coordinate integrand, including its empty-family convention.
The cutoff is the smallest regularized radius. The tail is a single maximum.
See the proof of Lemma A.4. -/
noncomputable def jointOdd {I : Type*} [Fintype I] (a R : ℝ) (z : I → ℂ) : ℝ≥0∞ :=
  if hn : Nonempty I then
    let := hn
    {z : I → ℂ | ∀ i, a < ‖z i‖}.indicator
      (fun z => ENNReal.ofReal (min 1 ((R / (univ.sup' univ_nonempty (fun i => ‖z i‖))) ^ 2)) *
        ∏ i, ENNReal.ofReal ((‖z i‖ ^ 2)⁻¹)) z
  else 1

/-- The coupled odd integrand is measurable, including for the empty family. -/
theorem measurable_jointOdd {I : Type*} [Fintype I] (a R : ℝ) :
    Measurable (jointOdd (I := I) a R) := by
  classical
  unfold jointOdd
  split_ifs with hn
  · let := hn
    have hs : Measurable fun z : I → ℂ => univ.sup' univ_nonempty (fun i => ‖z i‖) := by
      have hm := Finset.measurable_sup' (univ_nonempty (α := I))
        (fun i _ => (show Measurable (fun z : I → ℂ => ‖z i‖) by fun_prop))
      have he : (univ.sup' (univ_nonempty (α := I)) (fun i (z : I → ℂ) => ‖z i‖)) =
          (fun z : I → ℂ => univ.sup' univ_nonempty (fun i => ‖z i‖)) := by
        funext z
        rw [Finset.sup'_apply]
      rw [← he]
      exact hm
    apply Measurable.indicator
    · fun_prop
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const
        (show Measurable (fun z : I → ℂ => ‖z i‖) by fun_prop)
  · exact measurable_const

/-- Relabel the whole odd family at once. This preserves the shared maximum. -/
theorem jointOdd_reindex {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (a R : ℝ) (z : J → ℂ) : jointOdd a R (z ∘ e) = jointOdd a R z := by
  classical
  by_cases hn : Nonempty I
  · let := hn
    have hnJ : Nonempty J := Nonempty.map e hn
    let := hnJ
    have hsup : univ.sup' univ_nonempty (fun i => ‖z (e i)‖) =
        univ.sup' univ_nonempty (fun j => ‖z j‖) := by
      apply le_antisymm
      · exact (sup'_le_iff _ _).mpr fun i _ => le_sup' (fun j : J => ‖z j‖) (mem_univ (e i))
      · exact (sup'_le_iff _ _).mpr fun j _ => by
          obtain ⟨i, rfl⟩ := e.surjective j
          exact le_sup' (fun i : I => ‖z (e i)‖) (mem_univ i)
    have hset : (∀ i, a < ‖z (e i)‖) ↔ ∀ j, a < ‖z j‖ :=
      ⟨fun h j => by obtain ⟨i, rfl⟩ := e.surjective j; exact h i, fun h i => h (e i)⟩
    have hprod := e.prod_comp (fun j : J => ENNReal.ofReal ((‖z j‖ ^ 2)⁻¹))
    simp only [jointOdd, dite_eq_left hn, dite_eq_left hnJ, Set.indicator, Set.mem_ofPred_eq,
      Function.comp_apply, hsup, hset, hprod]
  · have hnJ : ¬Nonempty J := fun h => hn (Nonempty.map e.symm h)
    simp only [jointOdd, dite_eq_right hn, dite_eq_right hnJ]

/-- The maximum-tail bound for any finite odd family. The estimate is applied
after one simultaneous relabelling, with no tail assigned to individual edges. -/
theorem lintegral_jointOdd (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I], Fintype.card I = n →
      ∀ a R : ℝ, 0 < a → a ≤ R →
        (∫⁻ z : I → ℂ, jointOdd a R z) ≤ ENNReal.ofReal (C * (1 + Real.log (R / a)) ^ n) := by
  classical
  rcases n with _ | q
  · refine ⟨1, one_pos, fun I _ hI a R _ _ => ?_⟩
    have : IsEmpty I := Fintype.card_eq_zero_iff.mp hI
    simp [jointOdd, not_nonempty_iff.mpr this, volume_pi]
  · obtain ⟨C, hC, hb⟩ := lintegral_joint_odd_edges q
    refine ⟨C, hC, fun I _ hI a R ha haR => ?_⟩
    let e : Fin (q + 1) ≃ I := (Fintype.equivOfCardEq (by simpa using hI.symm))
    have hre := (volume_measurePreserving_piCongrLeft (fun _ : I => ℂ) e).lintegral_comp
      (measurable_jointOdd (I := I) a R)
    have hcomp (z : Fin (q + 1) → ℂ) :
        jointOdd a R ((MeasurableEquiv.piCongrLeft (fun _ : I => ℂ) e) z) = jointOdd a R z := by
      have h := jointOdd_reindex e a R ((MeasurableEquiv.piCongrLeft (fun _ : I => ℂ) e) z)
      have heq : ((MeasurableEquiv.piCongrLeft (fun _ : I => ℂ) e) z) ∘ e = z := by
        funext i
        simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      rw [heq] at h
      exact h.symm
    simp_rw [hcomp] at hre
    rw [← hre]
    have hset : MeasurableSet {z : Fin (q + 1) → ℂ | ∀ i, a < ‖z i‖} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const
        (show Measurable (fun z : Fin (q + 1) → ℂ => ‖z i‖) by fun_prop)
    simp only [jointOdd, dite_eq_left (inferInstance : Nonempty (Fin (q + 1)))]
    rw [lintegral_indicator hset]
    exact hb a R ha haR

/-- The odd profile depends only on the coordinate norms. -/
theorem jointOdd_congr_norm {I : Type*} [Fintype I] (a R : ℝ) (z w : I → ℂ)
    (h : ∀ i, ‖z i‖ = ‖w i‖) : jointOdd a R z = jointOdd a R w := by
  classical
  unfold jointOdd
  split_ifs with hn
  · let := hn
    simp only [Set.indicator, Set.mem_ofPred_eq, h]
  · rfl

/-- Joint measurability when the two radius parameters and all edge coordinates
vary with the configuration. -/
theorem measurable_jointOdd_comp {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (a R : Ω → ℝ) (z : Ω → I → ℂ) (ha : Measurable a) (hR : Measurable R)
    (hz : Measurable z) : Measurable fun ω => jointOdd (a ω) (R ω) (z ω) := by
  classical
  unfold jointOdd
  split_ifs with hn
  · let := hn
    have hs : Measurable fun ω => univ.sup' univ_nonempty (fun i => ‖z ω i‖) := by
      have hm := Finset.measurable_sup' (univ_nonempty (α := I))
        (fun i _ => ((measurable_pi_apply i).comp hz).norm)
      have he : (univ.sup' (univ_nonempty (α := I)) (fun i (ω : Ω) => ‖z ω i‖)) =
          (fun ω => univ.sup' univ_nonempty (fun i => ‖z ω i‖)) := by
        funext ω
        rw [Finset.sup'_apply]
      rw [← he]
      exact hm
    have heq : (fun ω => {z : I → ℂ | ∀ i, a ω < ‖z i‖}.indicator
        (fun z => ENNReal.ofReal (min 1 ((R ω / univ.sup' univ_nonempty (fun i => ‖z i‖)) ^ 2)) *
          ∏ i, ENNReal.ofReal ((‖z i‖ ^ 2)⁻¹)) (z ω)) =
        {ω | ∀ i, a ω < ‖z ω i‖}.indicator (fun ω =>
          ENNReal.ofReal (min 1 ((R ω / univ.sup' univ_nonempty (fun i => ‖z ω i‖)) ^ 2)) *
            ∏ i, ENNReal.ofReal ((‖z ω i‖ ^ 2)⁻¹)) := by
      funext ω
      rfl
    rw [heq]
    apply Measurable.indicator
    · fun_prop
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt ha (((measurable_pi_apply i).comp hz).norm)
  · exact measurable_const


end MultipoleBKT.SmallIntegral.RouteJ

end
