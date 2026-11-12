/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Radial
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.OddEdges
public import MultipoleBKT.Appendix.SmallIntegral.Radial

/-!
# Polar reduction of the ordered dipole-vector integral

See Lemma A.4, (A.26). All inner dipole vectors
are bounded by the length of the distinguished outer vector. Polar coordinates
produce the literal `orderedRadial` family, including its core below λ.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Set Finset
open MultipoleBKT.RouteLog Limits
open scoped ENNReal

private theorem measurable_minimum_radius (lam : ℝ) (k : ℕ) :
    Measurable (minimumRadius (k := k) lam) := by
  have heq : (univ.inf' (univ_nonempty (α := Fin (k + 1)))
      (fun i (r : Fin (k + 1) → ℝ) => max (r i) lam)) = minimumRadius lam := by
    funext r
    rw [Finset.inf'_apply]
    rfl
  rw [← heq]
  exact Finset.inf'_induction univ_nonempty _ (fun f hf g hg => hf.inf hg)
    fun i _ => (measurable_pi_apply i).max measurable_const

/-- The inner integral in dipole vectors before polar coordinates. -/
noncomputable def innerVector (β lam : ℝ) (k q : ℕ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in {v : Fin (k + 1) → ℂ | ∀ i, ‖v i‖ ≤ u},
    ENNReal.ofReal ((1 + Real.log (max u lam / minRho lam v)) ^ q) *
      ∏ i, ENNReal.ofReal (rho lam (v i) ^ (2 - β))

/-- Polar coordinates in all inner vectors, with their coupled minimum radius.
See (A.26). -/
theorem innerVector_eq (β lam : ℝ) (k q : ℕ) (u : ℝ) :
    innerVector β lam k q u = ENNReal.ofReal (2 * Real.pi) ^ (k + 1) *
      innerRadial β lam k q u := by
  let A : Set (Fin (k + 1) → ℝ) := {r | ∀ i, r i ≤ u}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le (measurable_pi_apply i) measurable_const
  let F : (Fin (k + 1) → ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal ((1 + Real.log (max u lam / minimumRadius lam r)) ^ q) *
      ∏ i, ENNReal.ofReal (max (r i) lam ^ (2 - β))
  have hF : Measurable F := by
    have hm := measurable_minimum_radius lam k
    unfold F
    fun_prop
  have hnorm : Measurable fun v : Fin (k + 1) → ℂ => fun i => ‖v i‖ := by fun_prop
  have hpre : MeasurableSet {v : Fin (k + 1) → ℂ | ∀ i, ‖v i‖ ≤ u} := hA.preimage hnorm
  unfold innerVector
  rw [← lintegral_indicator hpre]
  have heq : (fun v : Fin (k + 1) → ℂ =>
      {v : Fin (k + 1) → ℂ | ∀ i, ‖v i‖ ≤ u}.indicator
        (fun v => ENNReal.ofReal ((1 + Real.log (max u lam / minRho lam v)) ^ q) *
          ∏ i, ENNReal.ofReal (rho lam (v i) ^ (2 - β))) v) =
        fun v => A.indicator F (fun i => ‖v i‖) := by
    funext v
    rfl
  rw [heq, lintegral_pi_norm _ (hF.indicator hA)]
  congr 1
  have hpt (r : Fin (k + 1) → ℝ) (hr : r ∈ Set.univ.pi (fun _ => Ioi 0)) :
      (∏ i, ENNReal.ofReal (r i)) * A.indicator F r =
        A.indicator (fun r => ENNReal.ofReal ((1 + Real.log (max u lam / minimumRadius lam r)) ^ q) *
          ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))) r := by
    by_cases ha : r ∈ A
    · rw [indicator_of_mem ha, indicator_of_mem ha]
      unfold F
      rw [mul_left_comm]
      congr 1
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i _ => (ENNReal.ofReal_mul (mem_univ_pi.mp hr i).le).symm
    · rw [indicator_of_notMem ha, indicator_of_notMem ha, mul_zero]
  rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioi) hpt,
    lintegral_indicator hA, Measure.restrict_restrict hA]
  unfold innerRadial
  congr 1
  congr 1
  ext r
  simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Ioi, Set.mem_Ioc]
  exact ⟨fun h i => ⟨h.2 i, h.1 i⟩, fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩⟩

/-- Measurability in the distinguished radius, needed for the final polar step. -/
theorem measurable_innerRadial (β lam : ℝ) (k q : ℕ) :
    Measurable (innerRadial β lam k q) := by
  let F : ℝ × (Fin (k + 1) → ℝ) → ℝ≥0∞ := fun p =>
    {p : ℝ × (Fin (k + 1) → ℝ) | ∀ i, 0 < p.2 i ∧ p.2 i ≤ p.1}.indicator
      (fun p => ENNReal.ofReal ((1 + Real.log (max p.1 lam / minimumRadius lam p.2)) ^ q) *
        ∏ i, ENNReal.ofReal (p.2 i * max (p.2 i) lam ^ (2 - β))) p
  have hm : Measurable F := by
    apply Measurable.indicator
    · have hmin : Measurable (fun p : ℝ × (Fin (k + 1) → ℝ) => minimumRadius lam p.2) :=
        (measurable_minimum_radius lam k).comp measurable_snd
      fun_prop
    · simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      change MeasurableSet ({p : ℝ × (Fin (k + 1) → ℝ) | 0 < p.2 i} ∩ {p | p.2 i ≤ p.1})
      have hi : Measurable (fun p : ℝ × (Fin (k + 1) → ℝ) => p.2 i) := by fun_prop
      exact (measurableSet_lt measurable_const hi).inter (measurableSet_le hi measurable_fst)
  have heq : innerRadial β lam k q = fun u => ∫⁻ r, F (u, r) := by
    funext u
    unfold innerRadial F
    rw [← lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)]
    apply lintegral_congr
    intro r
    simp only [Set.indicator, Set.mem_univ_pi, Set.mem_Ioc, Set.mem_ofPred_eq]
  rw [heq]
  exact hm.lintegral_prod_right

/-- Exact reduction of the ordered dipole-vector integral to the scalar
ordered family. No power replaces the logarithm.
See (A.26). -/
theorem orderedVector_eq (β lam h : ℝ) (k q : ℕ) (hlam : 0 < lam) :
    (∫⁻ v in {v : ℂ | ‖v‖ ≤ h}, ENNReal.ofReal (rho lam v ^ (-β)) *
      innerVector β lam k q ‖v‖) =
        ENNReal.ofReal (2 * Real.pi) ^ (k + 2) * orderedRadial β lam h k q := by
  simp_rw [innerVector_eq]
  let F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (max u lam ^ (-β)) * innerRadial β lam k q u
  have hF : Measurable F := by
    have hm := measurable_innerRadial β lam k q
    fun_prop
  have heq (v : ℂ) : ENNReal.ofReal (rho lam v ^ (-β)) *
      (ENNReal.ofReal (2 * Real.pi) ^ (k + 1) * innerRadial β lam k q ‖v‖) =
      ENNReal.ofReal (2 * Real.pi) ^ (k + 1) * F ‖v‖ := by
    unfold F rho
    ring
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hp := TwoComponentCoulomb.lintegral_radial_set (Iic h) measurableSet_Iic F hF
  change ENNReal.ofReal (2 * Real.pi) ^ (k + 1) *
    (∫⁻ v in {v : ℂ | ‖v‖ ∈ Iic h}, F ‖v‖) = _
  rw [hp]
  have hint : (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u *
      ((Iic h).indicator F u * ENNReal.ofReal (2 * Real.pi))) =
        ENNReal.ofReal (2 * Real.pi) * orderedRadial β lam h k q := by
    have hpt (u : ℝ) : ENNReal.ofReal u * ((Iic h).indicator F u * ENNReal.ofReal (2 * Real.pi)) =
        ENNReal.ofReal (2 * Real.pi) * (Iic h).indicator
          (fun u => ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u) u := by
      by_cases hu : u ≤ h
      · rw [indicator_of_mem (show u ∈ Iic h from hu), indicator_of_mem (show u ∈ Iic h from hu)]
        dsimp only [F]
        rw [ENNReal.ofReal_mul' (Real.rpow_nonneg (hlam.le.trans (le_max_right _ _)) _)]
        ring
      · rw [indicator_of_notMem (show u ∉ Iic h from hu), indicator_of_notMem (show u ∉ Iic h from hu), mul_zero, zero_mul, mul_zero]
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic]
    have hs : Iic h ∩ Ioi (0 : ℝ) = Ioc 0 h := by
      ext u
      simp only [mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc, and_comm]
    rw [hs]
    rfl
  rw [hint, ← mul_assoc, ← pow_succ]

/-- The same polar reduction without a radial cutoff.
See Lemma A.4. -/
theorem orderedVectorInfinity_eq (β lam : ℝ) (k q : ℕ) (hlam : 0 < lam) :
    (∫⁻ v : ℂ, ENNReal.ofReal (rho lam v ^ (-β)) * innerVector β lam k q ‖v‖) =
      ENNReal.ofReal (2 * Real.pi) ^ (k + 2) * orderedRadialInfinity β lam k q := by
  simp_rw [innerVector_eq]
  let F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (max u lam ^ (-β)) * innerRadial β lam k q u
  have hF : Measurable F := by
    have hm := measurable_innerRadial β lam k q
    fun_prop
  have heq (v : ℂ) : ENNReal.ofReal (rho lam v ^ (-β)) *
      (ENNReal.ofReal (2 * Real.pi) ^ (k + 1) * innerRadial β lam k q ‖v‖) =
      ENNReal.ofReal (2 * Real.pi) ^ (k + 1) * F ‖v‖ := by
    unfold F rho
    ring
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  have hp := TwoComponentCoulomb.lintegral_radial_set univ MeasurableSet.univ F hF
  simp only [mem_univ, Set.ofPred_true, Measure.restrict_univ, indicator_univ] at hp
  rw [hp]
  have hpt (u : ℝ) : ENNReal.ofReal u * (F u * ENNReal.ofReal (2 * Real.pi)) =
      ENNReal.ofReal (2 * Real.pi) *
        (ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u) := by
    dsimp only [F]
    rw [ENNReal.ofReal_mul' (Real.rpow_nonneg (hlam.le.trans (le_max_right _ _)) _)]
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← pow_succ]
  rfl

/-- The ordered region with a distinguished largest vector. The remaining
labels are listed by `succAbove`, so every original label occurs exactly once. -/
noncomputable def orderedVectorTerm (D : Set ℝ) (β lam : ℝ) (k q : ℕ)
    (i₀ : Fin (k + 2)) (v : Fin (k + 2) → ℂ) : ℝ≥0∞ :=
  {v : Fin (k + 2) → ℂ | ‖v i₀‖ ∈ D ∧ ∀ j, ‖v (i₀.succAbove j)‖ ≤ ‖v i₀‖}.indicator
    (fun v => ENNReal.ofReal (rho lam (v i₀) ^ (-β)) *
      (ENNReal.ofReal ((1 + Real.log (rho lam (v i₀) /
        minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)))) ^ q) *
        ∏ j, ENNReal.ofReal (rho lam (v (i₀.succAbove j)) ^ (2 - β)))) v

/-- The distinguished-vector integral is exactly the iterated vector integral.
This is the finite-family relabelling and Tonelli step in (A.26). -/
theorem lintegral_orderedVectorTerm (D : Set ℝ) (hD : MeasurableSet D)
    (β lam : ℝ) (k q : ℕ) (i₀ : Fin (k + 2)) :
    (∫⁻ v, orderedVectorTerm D β lam k q i₀ v) =
      ∫⁻ v in {v : ℂ | ‖v‖ ∈ D}, ENNReal.ofReal (rho lam v ^ (-β)) * innerVector β lam k q ‖v‖ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) => ℂ) i₀
  let F : ℂ × (Fin (k + 1) → ℂ) → ℝ≥0∞ := fun p =>
    {p : ℂ × (Fin (k + 1) → ℂ) | ‖p.1‖ ∈ D ∧ ∀ j, ‖p.2 j‖ ≤ ‖p.1‖}.indicator
      (fun p => ENNReal.ofReal (rho lam p.1 ^ (-β)) *
        (ENNReal.ofReal ((1 + Real.log (rho lam p.1 / minRho lam p.2)) ^ q) *
          ∏ j, ENNReal.ofReal (rho lam (p.2 j) ^ (2 - β)))) p
  have hm : Measurable F := by
    apply Measurable.indicator
    · have hmin : Measurable (fun p : ℂ × (Fin (k + 1) → ℂ) => minRho lam p.2) :=
        (measurable_minRho lam).comp measurable_snd
      unfold rho
      fun_prop
    · change MeasurableSet ({p : ℂ × (Fin (k + 1) → ℂ) | ‖p.1‖ ∈ D} ∩
        {p | ∀ j, ‖p.2 j‖ ≤ ‖p.1‖})
      apply MeasurableSet.inter
      · exact hD.preimage (by fun_prop)
      · simp only [Set.ofPred_forall]
        apply MeasurableSet.iInter
        intro j
        exact measurableSet_le
          (show Measurable (fun p : ℂ × (Fin (k + 1) → ℂ) => ‖p.2 j‖) by fun_prop)
          (by fun_prop)
  have heq : orderedVectorTerm D β lam k q i₀ = F ∘ e := by rfl
  rw [heq]
  change (∫⁻ v, F (e v)) = _
  rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (k + 2) => ℂ) i₀).lintegral_comp hm]
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have hS : MeasurableSet {v : ℂ | ‖v‖ ∈ D} := hD.preimage measurable_norm
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro v
  by_cases hv : ‖v‖ ∈ D
  · rw [indicator_of_mem (show v ∈ {v : ℂ | ‖v‖ ∈ D} from hv)]
    unfold innerVector
    rw [← lintegral_indicator (by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le
        (show Measurable (fun w : Fin (k + 1) → ℂ => ‖w j‖) by fun_prop) measurable_const),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr
    intro w
    simp only [F, Set.indicator, Set.mem_ofPred_eq, hv, true_and]
    split_ifs <;> first | rfl | exact (mul_zero _).symm
  · rw [indicator_of_notMem (show v ∉ {v : ℂ | ‖v‖ ∈ D} from hv)]
    simp only [F, Set.indicator, Set.mem_ofPred_eq, hv, false_and, ite_false, lintegral_zero]

/-- The logarithmic radial majorant after (A.25), with any finite label type. -/
noncomputable def logRadialWeight {I : Type*} [Fintype I] [Nonempty I]
    (β lam : ℝ) (q : ℕ) (v : I → ℂ) : ℝ :=
  (1 + Real.log (maxRho lam v / minRho lam v)) ^ q *
    (maxRho lam v ^ (-2 : ℝ) * ∏ i, rho lam (v i) ^ (2 - β))

private theorem minRho_omit (lam : ℝ) (k : ℕ) (i₀ : Fin (k + 2))
    (v : Fin (k + 2) → ℂ) (hmax : ∀ i, ‖v i‖ ≤ ‖v i₀‖) :
    minRho lam v = minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) := by
  apply le_antisymm
  · exact (le_inf'_iff _ _).mpr fun j _ => minRho_le_rho lam v _
  · apply (le_inf'_iff _ _).mpr
    intro i _
    rcases i₀.eq_self_or_eq_succAbove i with hi | ⟨j, hi⟩
    · rw [hi]
      exact (minRho_le_rho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) 0).trans
        (max_le_max (hmax _) le_rfl)
    · rw [hi]
      exact minRho_le_rho lam _ j

private theorem measurable_orderedVectorTerm (D : Set ℝ) (hD : MeasurableSet D)
    (β lam : ℝ) (k q : ℕ) (i₀ : Fin (k + 2)) :
    Measurable (orderedVectorTerm D β lam k q i₀) := by
  unfold orderedVectorTerm
  apply Measurable.indicator
  · have hm : Measurable (fun v : Fin (k + 2) → ℂ =>
        minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j))) :=
      (measurable_minRho lam).comp (by fun_prop)
    unfold rho
    fun_prop
  · change MeasurableSet ({v : Fin (k + 2) → ℂ | ‖v i₀‖ ∈ D} ∩
      {v | ∀ j, ‖v (i₀.succAbove j)‖ ≤ ‖v i₀‖})
    apply MeasurableSet.inter
    · exact hD.preimage (by fun_prop)
    · simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le
        (show Measurable (fun v : Fin (k + 2) → ℂ => ‖v (i₀.succAbove j)‖) by fun_prop)
        (by fun_prop)

/-- Split the vector integral according to an index of largest original radius.
Ties can be counted more than once. The logarithm is still coupled through
the minimum of all inner radii.
See (A.26). -/
theorem lintegral_logRadialWeight_le (D : Set ℝ) (hD : MeasurableSet D)
    (β lam : ℝ) (k q : ℕ) (hlam : 0 < lam) :
    (∫⁻ v in {v : Fin (k + 2) → ℂ | ∀ i, ‖v i‖ ∈ D},
      ENNReal.ofReal (logRadialWeight β lam q v)) ≤
        (k + 2) * ∫⁻ v in {v : ℂ | ‖v‖ ∈ D},
          ENNReal.ofReal (rho lam v ^ (-β)) * innerVector β lam k q ‖v‖ := by
  have hS : MeasurableSet {v : Fin (k + 2) → ℂ | ∀ i, ‖v i‖ ∈ D} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => hD.preimage (by fun_prop)
  rw [← lintegral_indicator hS]
  have hpoint (v : Fin (k + 2) → ℂ) :
      {v : Fin (k + 2) → ℂ | ∀ i, ‖v i‖ ∈ D}.indicator
        (fun v => ENNReal.ofReal (logRadialWeight β lam q v)) v ≤
          ∑ i₀, orderedVectorTerm D β lam k q i₀ v := by
    by_cases hv : ∀ i, ‖v i‖ ∈ D
    · rw [indicator_of_mem (show v ∈ {v : Fin (k + 2) → ℂ | ∀ i, ‖v i‖ ∈ D} from hv)]
      obtain ⟨i₀, _, hi₀⟩ := exists_max_image univ (fun i => ‖v i‖) univ_nonempty
      have hmax : ∀ i, ‖v i‖ ≤ ‖v i₀‖ := fun i => hi₀ i (mem_univ _)
      have hR : maxRho lam v = rho lam (v i₀) := by
        apply le_antisymm
        · exact (fold_max_le _).mpr ⟨lam_le_rho lam _, fun i _ => max_le_max (hmax i) le_rfl⟩
        · exact rho_le_maxRho lam v i₀
      have heq : ENNReal.ofReal (logRadialWeight β lam q v) = orderedVectorTerm D β lam k q i₀ v := by
        unfold orderedVectorTerm
        rw [indicator_of_mem (show v ∈ {v : Fin (k + 2) → ℂ | ‖v i₀‖ ∈ D ∧ ∀ j, ‖v (i₀.succAbove j)‖ ≤ ‖v i₀‖} from
          ⟨hv i₀, fun j => hmax _⟩)]
        unfold logRadialWeight
        rw [hR, minRho_omit lam k i₀ v hmax, Fin.prod_univ_succAbove _ i₀]
        have hr := rho_pos hlam (v i₀)
        have hpower : rho lam (v i₀) ^ (-2 : ℝ) * rho lam (v i₀) ^ (2 - β) =
            rho lam (v i₀) ^ (-β) := by
          rw [← Real.rpow_add hr]
          congr 1
          ring
        rw [← mul_assoc (rho lam (v i₀) ^ (-2 : ℝ)) (rho lam (v i₀) ^ (2 - β)), hpower]
        have hpow0 : 0 ≤ rho lam (v i₀) ^ (-β) := Real.rpow_nonneg hr.le _
        have hlog0 : 0 ≤ (1 + Real.log (rho lam (v i₀) /
            minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)))) ^ q := by
          apply pow_nonneg
          have hp := minRho_pos hlam (fun j : Fin (k + 1) => v (i₀.succAbove j))
          have hm : minRho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) ≤ rho lam (v i₀) := (minRho_le_rho lam (fun j : Fin (k + 1) => v (i₀.succAbove j)) 0).trans
            (max_le_max (hmax _) le_rfl)
          have := Real.log_nonneg ((one_le_div hp).mpr hm)
          linarith
        rw [ENNReal.ofReal_mul hlog0, ENNReal.ofReal_mul hpow0,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg (rho_pos hlam _).le _)]
        ring
      rw [heq]
      exact single_le_sum (f := fun i => orderedVectorTerm D β lam k q i v)
        (fun _ _ => bot_le) (mem_univ i₀)
    · rw [indicator_of_notMem (show v ∉ {v : Fin (k + 2) → ℂ | ∀ i, ‖v i‖ ∈ D} from hv)]
      exact bot_le
  calc
    _ ≤ ∫⁻ v, ∑ i₀, orderedVectorTerm D β lam k q i₀ v := lintegral_mono hpoint
    _ = ∑ i₀, ∫⁻ v, orderedVectorTerm D β lam k q i₀ v :=
      lintegral_finsetSum _ fun i₀ _ => measurable_orderedVectorTerm D hD β lam k q i₀
    _ = _ := by
      simp_rw [lintegral_orderedVectorTerm D hD β lam k q]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]

/-- The vector majorant in the normalization of (A.27), after the largest
radius split, polar coordinates, and the logarithmic radial calculation. -/
theorem logRadialWeight_bound {β eps : ℝ} (hβ : 2 < β) (heps : 0 < eps) (heps1 : eps < 1)
    (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam ≤ Appendix.lamBound eps (k + 2) →
      (∫⁻ v in {v : Fin (k + 2) → ℂ | ∀ i, ‖v i‖ ≤ eps * truncationScale p₀ β lam},
        ENNReal.ofReal (logRadialWeight β lam q v)) ≤
          ENNReal.ofReal (C * (lam ^ ((2 - β) * (k + 2)) * Appendix.gammaBeta p₀ β lam (k + 2))) := by
  obtain ⟨C, hC, hb⟩ := orderedRadial_bound hβ heps heps1 k q
  refine ⟨(k + 2) * (2 * Real.pi) ^ (k + 2) * C, by positivity, fun p₀ lam hlam hlamB => ?_⟩
  have h := lintegral_logRadialWeight_le (Iic (eps * truncationScale p₀ β lam))
    measurableSet_Iic β lam k q hlam
  simp only [Set.mem_Iic] at h
  rw [orderedVector_eq β lam _ k q hlam] at h
  refine h.trans ((mul_le_mul_right (mul_le_mul_right (hb p₀ lam hlam hlamB) _) _).trans_eq ?_)
  rw [show (k : ℝ≥0∞) + 2 = ENNReal.ofReal ((k : ℝ) + 2) by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num)]
      norm_cast,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ (k + 2)),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)]
  congr 1
  ring

/-- Infinite-cutoff convergence for the complete ordered vector majorant.
The restriction `k+2 ≤ p*(β)` enters only the outer logarithmic moment.
See Lemma A.4. -/
theorem logRadialWeightInfinity_bound {β : ℝ} (hβ : 2 < β) (k q : ℕ)
    (hsize : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam →
      (∫⁻ v : Fin (k + 2) → ℂ, ENNReal.ofReal (logRadialWeight β lam q v)) ≤
        ENNReal.ofReal (C * (lam ^ ((2 - β) * (k + 2)) * Appendix.gammaBeta p₀ β lam (k + 2))) := by
  obtain ⟨C, hC, hb⟩ := orderedRadialInfinity_gamma hβ k q hsize
  refine ⟨(k + 2) * (2 * Real.pi) ^ (k + 2) * C, by positivity, fun p₀ lam hlam => ?_⟩
  have h := lintegral_logRadialWeight_le univ MeasurableSet.univ β lam k q hlam
  simp only [mem_univ, implies_true, Set.ofPred_true, Measure.restrict_univ] at h
  rw [orderedVectorInfinity_eq β lam k q hlam] at h
  refine h.trans ((mul_le_mul_right (mul_le_mul_right (hb p₀ lam hlam) _) _).trans_eq ?_)
  rw [show (k : ℝ≥0∞) + 2 = ENNReal.ofReal ((k : ℝ) + 2) by
      rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num)]
      norm_cast,
    ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 * Real.pi) ^ (k + 2)),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2)]
  congr 1
  ring

end MultipoleBKT.SmallIntegral.RouteJ

end
