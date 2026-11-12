/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.GlobalOdd
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailSectors
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.SpatialTree
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Density

/-!
# The configuration integral with its unbounded joint odd tail

See case F in the proof of Lemma A.7. Position integration is performed
before the largest-vector sectors. The same maximum tail remains coupled
until the logarithmic vector integral.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext
open TwoComponentCoulomb (box)
open scoped Classical ENNReal

/-- The literal normalized unbounded-tree density. -/
noncomputable def jointTreeDensity {W : Type*} [Fintype W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam : ℝ) (A E N : Finset (Sym2 W)) (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  treeProfile M lam A E N c * ENNReal.ofReal (radialFactor lam c) *
    ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i))

/-- Measurability includes the one global odd maximum. -/
theorem measurable_jointTreeDensity {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {χ : ℂ → ℝ} (hχ : IsMollifier χ) (β M : ℝ) {lam : ℝ} (hlam : 0 < lam)
    (A E N : Finset (Sym2 W)) : Measurable (jointTreeDensity χ β M lam A E N) := by
  unfold jointTreeDensity treeProfile radialFactor
  have hd (e : Sym2 W) : Measurable (fun c : W → ℂ × ℂ => dipoleDistOn c e) := by
    induction e using Sym2.ind with
    | h i j => exact measurable_dipoleDist.comp (show Measurable (fun c : W → ℂ × ℂ => (c i,c j)) by fun_prop)
  have hodd : Measurable (fun c : W → ℂ × ℂ =>
      jointOdd (minRad lam c) (maxRad lam c) (fun e : A => (dipoleDistOn c e : ℂ))) :=
    measurable_jointOdd_comp _ _ _ (measurable_minRad lam) (measurable_maxRad lam)
      (measurable_pi_iff.mpr fun e : A => Complex.measurable_ofReal.comp (hd e.val))
  have hp (b : Bool) (e : Sym2 W) : Measurable (fun c : W → ℂ × ℂ => ENNReal.ofReal (edgeProfile b M lam c e)) := by
    induction e using Sym2.ind with
    | h i j =>
      have hdij : Measurable (fun c : W → ℂ × ℂ => dipoleDist (c i) (c j)) := by
        simpa only [dipoleDistOn_mk] using hd s(i,j)
      simp only [edgeProfile_mk]
      unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile rhoD
      split_ifs <;> apply Measurable.ennreal_ofReal <;>
        first | fun_prop | exact Measurable.div (Measurable.ite (measurableSet_le hdij (by fun_prop))
          measurable_const (by fun_prop)) (by fun_prop)
  have hrad : Measurable (fun c : W → ℂ × ℂ => ENNReal.ofReal
      ((∏ i, rhoD lam (c i) ^ 2) * maxRad lam c ^ (-2 : ℝ))) := by
    exact ((Finset.measurable_prod _ fun i _ => ((measurable_rhoD lam).comp (measurable_pi_apply i)).pow_const 2).mul
      ((measurable_maxRad lam).pow_const (-2 : ℝ))).ennreal_ofReal
  exact ((hodd.mul ((Finset.measurable_prod _ fun e _ => hp true e).mul
    (Finset.measurable_prod _ fun e _ => hp false e))).mul hrad).mul
      (Finset.measurable_prod _ fun i _ => ((measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)).ennreal_ofReal)

/-- Position integration of the normalized unbounded original tree leaves
exactly the unordered logarithmic vector tail. -/
theorem jointTree_tail_le_vectors {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W],
      Fintype.card W = k + 1 → ∀ (T : SimpleGraph W), T.IsTree →
      ∀ (A E N : Finset (Sym2 W)), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ {χ : ℂ → ℝ} (_hχ : IsMollifier χ)
        (β lam h : ℝ), 0 < lam → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n ∩ {c : W → ℂ × ℂ | h < maxRad lam c},
        jointTreeDensity χ β M lam A E N c) ≤
          ENNReal.ofReal (C * n) * ∫⁻ u in {u : W → ℂ | h < SmallIntegral.maxRho lam u},
            ENNReal.ofReal (logDensityWeight χ β lam k u) := by
  obtain ⟨C,hC,hb⟩ := lintegral_treeProfile hM k
  refine ⟨C,hC,?_⟩
  intro W _ _ _ hW T hT A E N hpart hA hEN χ hχ β lam h hlam n
  let root : W := Classical.arbitrary W
  let G (c : W → ℂ × ℂ) := {c : W → ℂ × ℂ | h < maxRad lam c}.indicator
    (fun c => (box n).indicator (1 : ℂ → ℝ≥0∞) (c root).1 * jointTreeDensity χ β M lam A E N c) c
  have htail : MeasurableSet {c : W → ℂ × ℂ | h < maxRad lam c} :=
    measurableSet_lt measurable_const (measurable_maxRad lam)
  have hG : Measurable G := (((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box n)).comp
    (measurable_fst.comp (measurable_pi_apply root))).mul
      (measurable_jointTreeDensity hχ β M hlam A E N)).indicator htail
  have hbox : (∫⁻ c in boxConfig W n ∩ {c : W → ℂ × ℂ | h < maxRad lam c},
      jointTreeDensity χ β M lam A E N c) ≤ ∫⁻ c, G c := by
    rw [← lintegral_indicator ((measurableSet_boxConfig n).inter htail)]
    apply lintegral_mono
    intro c
    by_cases hc : c ∈ boxConfig W n ∩ {c : W → ℂ × ℂ | h < maxRad lam c}
    · rw [indicator_of_mem hc]
      simp only [G,indicator_of_mem hc.2,indicator_of_mem (((Set.mem_univ_pi.mp hc.1) root).1),Pi.one_apply,one_mul,le_refl]
    · rw [indicator_of_notMem hc]
      exact bot_le
  refine hbox.trans ?_
  rw [lintegral_eq_lintegral_pos_vec G hG,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hU : MeasurableSet {u : W → ℂ | h < SmallIntegral.maxRho lam u} :=
    measurableSet_lt measurable_const (SmallIntegral.measurable_maxRho lam)
  rw [← lintegral_indicator hU]
  apply lintegral_mono
  intro u
  change (∫⁻ x : W → ℂ, G (ofPosVec x u)) ≤ _
  by_cases hu : h < SmallIntegral.maxRho lam u
  · rw [indicator_of_mem (show u ∈ {u : W → ℂ | h < SmallIntegral.maxRho lam u} from hu)]
    let dens := ENNReal.ofReal (radialFactor lam (ofPosVec (fun _ : W => 0) u)) *
      ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (u i)))
    have hre (x : W → ℂ) : G (ofPosVec x u) =
        ((box n).indicator (1 : ℂ → ℝ≥0∞) (x root) * treeProfile M lam A E N (ofPosVec x u)) * dens := by
      dsimp only [G]
      rw [indicator_of_mem (show ofPosVec x u ∈ {c | h < maxRad lam c} by
        simpa only [Set.mem_ofPred_eq,maxRad_ofPosVec_eq] using hu)]
      unfold jointTreeDensity dens radialFactor
      simp only [ofPosVec_apply,rhoD_mk,maxRad_ofPosVec_eq,pairDensity_mk hχ]
      ring
    simp_rw [hre]
    rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top))]
    refine (mul_le_mul' (hb W hW T hT A E N hpart hA hEN root u lam hlam n) le_rfl).trans_eq ?_
    unfold logDensityWeight
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul' (prod_nonneg fun _ _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg hC.le (Nat.cast_nonneg _)),
      ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg _))
        (pow_nonneg (logRatio_nonneg hlam u) k))]
    congr 1
    ring
  · rw [indicator_of_notMem (show u ∉ {u : W → ℂ | h < SmallIntegral.maxRho lam u} from hu)]
    have hz (x : W → ℂ) : G (ofPosVec x u) = 0 := by
      unfold G
      exact indicator_of_notMem (by simpa only [Set.mem_ofPred_eq,maxRad_ofPosVec_eq] using hu) _
    change (∫⁻ x : W → ℂ, G (ofPosVec x u)) ≤ 0
    simp only [hz,lintegral_zero,le_refl]

end MultipoleBKT.ExpansionK.RouteSpatial

end
