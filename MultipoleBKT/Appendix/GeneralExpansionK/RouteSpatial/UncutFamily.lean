/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.JointTail

/-!
# The complete original family with its unbounded odd tail

See Steps 3 and 4 of
the proof of Lemma A.7. Allocate near and even squared
minima on the original tree. Keep its global odd tail until the joint profile.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

/-- The retained inverse-square original weight is the literal kept edge. -/
theorem keptWeight_eq_keptE {W : Type*} (M lam : ℝ) (c : W → ℂ × ℂ) (e : Sym2 W) :
    keptWeight (dipoleDistOn c) (farInd M lam c) e = keptE M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    unfold keptWeight keptE
    simp only [dipoleDistOn_mk,symmLift_mk]
    change (if MultipoleLinked M lam (c i) (c j) then 0 else 1) / _ =
      (if MultipoleLinked M lam (c i) (c j) then 0 else _)
    split_ifs <;> simp only [zero_div,one_div]

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Normalize the whole original family, retaining its actual global tail on
every configuration. No odd edge is cut at the radial threshold. -/
theorem uncut_family_normalized (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {lam M : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (c : ℕ → ℂ × ℂ)
    (F : OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X))
    (hnear : ∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val) →
      MultipoleLinked M lam (c i) (c j)) :
    ENNReal.ofReal (F.weight (paperDistE c) (farInd M lam c) *
      globalTail (maxRad lam (fun i : X.biUnion id => c i)) (paperDistE c) F.edges *
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
        paperEvenE M lam (fun i : X.biUnion id => c i) e) ≤
      ENNReal.ofReal (radialFactor lam (fun i : X.biUnion id => c i)) *
        treeProfile M lam (oddEdges F) (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
          (nearForest (Limits.blockOf X) (fun S => (Q S).val)) (fun i : X.biUnion id => c i) := by
  let cfg := fun i : X.biUnion id => c i
  let R := maxRad lam cfg
  let A := oddEdges F
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  have hR : 0 < R := hlam.trans_le (lam_le_maxRad lam cfg)
  have hn := ordinary_family_allocated hX hOX hpar hlam hM c F Tb hTb Q hnear
  have heq : F.weight (paperDistE c) (farInd M lam c) * globalTail R (paperDistE c) F.edges *
      (∏ e ∈ E, paperEvenE M lam cfg e) = R ^ (-2 : ℝ) *
        (R ^ 2 * F.weight (paperDistE c) (farInd M lam c) * ∏ e ∈ E, paperEvenE M lam cfg e) *
          globalTail R (paperDistE c) F.edges := by
    rw [Real.rpow_neg hR.le,Real.rpow_two]
    field_simp [hR.ne']
  rw [heq,ENNReal.ofReal_mul' (globalTail_nonneg _ _ _),ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
  refine (mul_le_mul' (mul_le_mul' le_rfl hn) le_rfl).trans ?_
  have hodd := globalTail_kept_le_jointOdd_all hM hlam hR.le cfg A
  have htail : globalTail R (paperDistE c) F.edges = globalTail R (dipoleDistOn cfg) A := by
    rw [oddFamily_globalTail F]
    congr 1
    funext e
    induction e using Sym2.ind with
    | h i j => rfl
  have hraw : (∏ e ∈ A, keptWeight (dipoleDistOn cfg) (farInd M lam cfg) e) = ∏ e ∈ A, keptE M lam cfg e := by
    simp_rw [keptWeight_eq_keptE]
  have heven : ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam cfg e) ≤
      ∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam cfg e) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => show 0 ≤ normalizedEven M lam cfg e from div_nonneg
      (add_nonneg (aSqE_nonneg cfg e) (linkE_nonneg cfg e)) (minSq_pos hlam cfg e).le)]
    exact prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (normalizedEven_le_edgeProfile hM hlam cfg e)
  have hnear' : ENNReal.ofReal (∏ e ∈ N, nearE M lam cfg e) =
      ∏ e ∈ N, ENNReal.ofReal (edgeProfile false M lam cfg e) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => nearE_nonneg M lam cfg e)]
    simp_rw [nearE_eq_edgeProfile]
  rw [htail]
  have hrad : ENNReal.ofReal (R ^ (-2 : ℝ)) * ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) =
      ENNReal.ofReal (radialFactor lam cfg) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    congr 1
    unfold radialFactor
    ring
  have hprod : (ENNReal.ofReal (R ^ (-2 : ℝ)) *
      (ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) *
        (ENNReal.ofReal (∏ e ∈ A, keptWeight (dipoleDistOn cfg) (farInd M lam cfg) e) *
          (ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam cfg e) * ENNReal.ofReal (∏ e ∈ N, nearE M lam cfg e))))) *
      ENNReal.ofReal (globalTail R (dipoleDistOn cfg) A) =
      ENNReal.ofReal (radialFactor lam cfg) *
        (ENNReal.ofReal (globalTail R (dipoleDistOn cfg) A * ∏ e ∈ A, keptE M lam cfg e) *
          (ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam cfg e) * ENNReal.ofReal (∏ e ∈ N, nearE M lam cfg e))) := by
    rw [ENNReal.ofReal_mul (globalTail_nonneg _ _ _),hraw,← hrad]
    ring
  rw [hprod]
  unfold treeProfile
  exact mul_le_mul' le_rfl (mul_le_mul' hodd (mul_le_mul' heven hnear'.le))

end MultipoleBKT.ExpansionK.RouteSpatial

end
