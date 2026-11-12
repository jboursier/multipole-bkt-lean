/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RetainedSpatial
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Measurability
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Density

/-!
# The configuration integral reduces to the logarithmic vector integral

See Lemma A.4, (A.26). Apply Tonelli in
positions and displacements, integrate the retained spatial tree, and keep
the original density in the remaining vector integral.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Set Limits TwoComponentCoulomb
open scoped Classical ENNReal

/-- The complete configuration-to-vector comparison for one retained original tree. The length set is arbitrary, covering both hatted cutoff conventions. -/
theorem lintegral_retainedTreeTerm_density {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V B : Type*) [Fintype V] [Fintype B]
      [DecidableEq V] [DecidableEq B] [Nonempty V], Fintype.card V = k + 1 →
      ∀ (blk : V → B) (R : NearTreeFamily blk) (A E : Finset (Sym2 V)),
      (∀ e ∈ A ∪ E, ¬(Sym2.map blk e).IsDiag) →
      (∀ i j, (sameBlockGraph blk ⊔ SimpleGraph.fromEdgeSet
        ((A ∪ E : Finset (Sym2 V)) : Set (Sym2 V))).Reachable i j) →
      A.card + E.card + 1 ≤ Fintype.card B →
      ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (β lam : ℝ), 0 < lam →
      ∀ D : Set ℝ, MeasurableSet D → ∀ N : ℕ,
      (∫⁻ c in boxConfig V N, retainedTreeTerm blk M lam A E R c *
        ∏ i, ENNReal.ofReal (restrictedPairDensity χ β lam D (c i))) ≤
          ENNReal.ofReal (C * N) * ∫⁻ u in {u : V → ℂ | ∀ i, ‖u i‖ ∈ D},
            ENNReal.ofReal (logDensityWeight χ β lam k u) := by
  obtain ⟨C, hC, hb⟩ := lintegral_retainedTreeTerm_positions hM k
  refine ⟨C, hC, fun V B _ _ _ _ _ hV blk R A E hinter hconn hcount χ hχ β lam hlam D hD N => ?_⟩
  let root : V := Classical.arbitrary V
  let H : (V → ℂ × ℂ) → ℝ≥0∞ := fun c => retainedTreeTerm blk M lam A E R c *
    ∏ i, ENNReal.ofReal (restrictedPairDensity χ β lam D (c i))
  let G : (V → ℂ × ℂ) → ℝ≥0∞ := fun c => (box N).indicator 1 (c root).1 * H c
  have hH : Measurable H :=
    (measurable_retainedTreeTerm blk M lam A E R).mul
      (Finset.measurable_prod _ fun i _ => ((measurable_restrictedPairDensity hχ hlam β D hD).comp
        (measurable_pi_apply i)).ennreal_ofReal)
  have hG : Measurable G :=
    (((measurable_const.indicator (measurableSet_box N)).comp
      (measurable_fst.comp (measurable_pi_apply root))).mul hH)
  have hbox : (∫⁻ c in boxConfig V N, H c) ≤ ∫⁻ c, G c := by
    rw [← lintegral_indicator (measurableSet_boxConfig N)]
    apply lintegral_mono
    intro c
    by_cases hc : c ∈ boxConfig V N
    · rw [indicator_of_mem hc]
      have hr : (c root).1 ∈ box N := ((Set.mem_univ_pi.mp hc) root).1
      simp only [G, indicator_of_mem hr, Pi.one_apply, one_mul, le_refl]
    · rw [indicator_of_notMem hc]
      exact bot_le
  refine hbox.trans ?_
  rw [lintegral_eq_lintegral_pos_vec G hG,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hDU : MeasurableSet {u : V → ℂ | ∀ i, ‖u i‖ ∈ D} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => hD.preimage (by fun_prop)
  rw [← lintegral_indicator hDU]
  apply lintegral_mono
  intro u
  let dens : ℝ≥0∞ := ∏ i, ENNReal.ofReal
    (Real.exp (β * smearedKernel χ lam (u i)) * D.indicator 1 ‖u i‖)
  have hre (x : V → ℂ) : G (ofPosVec x u) =
      ((box N).indicator (1 : ℂ → ℝ≥0∞) (x root) *
        retainedTreeTerm blk M lam A E R (ofPosVec x u)) * dens := by
    simp only [G, H]
    simp_rw [restrictedPairDensity_ofPosVec hχ]
    exact (mul_assoc _ _ _).symm
  change (∫⁻ x, G (ofPosVec x u)) ≤ _
  simp_rw [hre]
  rw [lintegral_mul_const' _ _ (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)]
  refine (mul_le_mul_left (hb V B hV blk R A E hinter hconn hcount root u lam hlam N) dens).trans_eq ?_
  by_cases hu : ∀ i, ‖u i‖ ∈ D
  · rw [indicator_of_mem (show u ∈ {u : V → ℂ | ∀ i, ‖u i‖ ∈ D} from hu)]
    have hdens : dens = ENNReal.ofReal (∏ i, Real.exp (β * smearedKernel χ lam (u i))) := by
      dsimp only [dens]
      simp only [indicator_of_mem (hu _), Pi.one_apply, mul_one]
      exact (ENNReal.ofReal_prod_of_nonneg fun _ _ => (Real.exp_pos _).le).symm
    rw [hdens, ← ENNReal.ofReal_mul' (prod_nonneg fun _ _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (mul_nonneg hC.le (Nat.cast_nonneg _))]
    congr 1
    unfold logDensityWeight
    ring
  · rw [indicator_of_notMem (show u ∉ {u : V → ℂ | ∀ i, ‖u i‖ ∈ D} from hu)]
    have hdens : dens = 0 := by
      push Not at hu
      obtain ⟨i, hi⟩ := hu
      apply prod_eq_zero (mem_univ i)
      rw [indicator_of_notMem hi, mul_zero, ENNReal.ofReal_zero]
    rw [hdens, mul_zero]

end MultipoleBKT.SmallIntegral.RouteJ

end
