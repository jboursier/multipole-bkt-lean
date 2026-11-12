/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ConfigurationMajorant
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.SpatialTree

/-!
# Integrating the retained tree majorant in the positions

See Lemma A.4. The radius allocation is independent
of the positions. The spatial integration leaves its radial factor and the
written power of the logarithm.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset SimpleGraph Limits TwoComponentCoulomb
open scoped Classical ENNReal

/-- The retained term has the same logarithmic spatial bound as its
three-family profile. The odd and even edge sets have not been interchanged. -/
theorem lintegral_retainedTreeTerm_positions {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V B : Type*) [Fintype V] [Fintype B]
      [DecidableEq V] [DecidableEq B] [Nonempty V], Fintype.card V = k + 1 →
      ∀ (blk : V → B) (R : NearTreeFamily blk) (A E : Finset (Sym2 V)),
      (∀ e ∈ A ∪ E, ¬(Sym2.map blk e).IsDiag) →
      (∀ i j, (sameBlockGraph blk ⊔ fromEdgeSet ((A ∪ E : Finset (Sym2 V)) : Set (Sym2 V))).Reachable i j) →
      A.card + E.card + 1 ≤ Fintype.card B →
      ∀ (root : V) (u : V → ℂ) (lam : ℝ), 0 < lam → ∀ N : ℕ,
      (∫⁻ x : V → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (x root) *
        retainedTreeTerm blk M lam A E R (ofPosVec x u)) ≤
          ENNReal.ofReal (C * N * (1 + Real.log (maxRho lam u / minRho lam u)) ^ k *
            radialFactor lam (ofPosVec (fun _ => 0) u)) := by
  obtain ⟨C, hC, hb⟩ := lintegral_treeProfile hM k
  refine ⟨C, hC, fun V B _ _ _ _ _ hV blk R A E hinter hconn hcount root u lam hlam N => ?_⟩
  let F := nearForest blk (fun b => (R b).val)
  let T := fromEdgeSet ((F ∪ (A ∪ E) : Finset (Sym2 V)) : Set (Sym2 V))
  obtain ⟨hT, hTE, hFAE, hAE, _⟩ := retained_tree blk (fun b => (R b).val)
    (fun b => (R b).property) A E hinter hconn hcount
  have hpart : A ∪ (E ∪ F) = T.edgeFinset := by
    rw [hTE]
    ext e
    simp only [mem_union]
    tauto
  have hAF : Disjoint A F := (Finset.disjoint_union_left.mp hFAE.symm).1
  have hEF : Disjoint E F := (Finset.disjoint_union_left.mp hFAE.symm).2
  have hArest : Disjoint A (E ∪ F) := Finset.disjoint_union_right.mpr ⟨hAE, hAF⟩
  let rad := radialFactor lam (ofPosVec (fun _ : V => 0) u)
  have hrad (x : V → ℂ) : radialFactor lam (ofPosVec x u) = rad := by
    dsimp only [rad, radialFactor]
    simp only [maxRad_ofPosVec_eq, rhoD_mk, ofPosVec_apply]
  have hrad0 : 0 ≤ rad := by
    unfold rad radialFactor
    exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
      (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam _)) _)
  have hpoint (x : V → ℂ) : retainedTreeTerm blk M lam A E R (ofPosVec x u) ≤
      ENNReal.ofReal rad * treeProfile M lam A E F (ofPosVec x u) := by
    unfold retainedTreeTerm treeProfile
    rw [hrad]
    have hp : (∏ e ∈ E, ENNReal.ofReal (normalizedEven M lam (ofPosVec x u) e)) ≤
        ∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam (ofPosVec x u) e) :=
      prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (normalizedEven_le_edgeProfile hM hlam _ e)
    have hn : (∏ e ∈ F, ENNReal.ofReal (nearE M lam (ofPosVec x u) e)) =
        ∏ e ∈ F, ENNReal.ofReal (edgeProfile false M lam (ofPosVec x u) e) := by
      simp_rw [nearE_eq_edgeProfile]
    change _ ≤ ENNReal.ofReal rad * _
    rw [show nearForest blk (fun b => (R b).val) = F from rfl, hn]
    calc
      _ ≤ jointOdd (minRad lam (ofPosVec x u)) (maxRad lam (ofPosVec x u))
          (fun e : A => (Peeling.dipoleDistOn (ofPosVec x u) e : ℂ)) *
          (ENNReal.ofReal rad * ((∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam (ofPosVec x u) e)) *
            ∏ e ∈ F, ENNReal.ofReal (edgeProfile false M lam (ofPosVec x u) e))) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ x : V → ℂ, ENNReal.ofReal rad *
        ((box N).indicator (1 : ℂ → ℝ≥0∞) (x root) * treeProfile M lam A E F (ofPosVec x u)) := by
      apply lintegral_mono
      intro x
      exact (mul_le_mul_right (hpoint x) _).trans_eq (by ring)
    _ = ENNReal.ofReal rad * ∫⁻ x : V → ℂ,
        (box N).indicator (1 : ℂ → ℝ≥0∞) (x root) * treeProfile M lam A E F (ofPosVec x u) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal rad * ENNReal.ofReal
        (C * N * (1 + Real.log (maxRho lam u / minRho lam u)) ^ k) :=
      mul_le_mul_right (hb V hV T hT A E F (by
        convert! hpart using 1
        congr 1
        exact Subsingleton.elim _ _) hArest hEF root u lam hlam N) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hrad0]
      congr 1
      ring

end MultipoleBKT.SmallIntegral.RouteJ

end
