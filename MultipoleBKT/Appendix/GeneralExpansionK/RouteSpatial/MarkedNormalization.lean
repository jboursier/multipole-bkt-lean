/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.OrdinaryNormalization
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceMarkedRadii

/-!
# Normalization of the actual retained even mark

See (A.62) and Step 3 of the proof of Lemma A.7. The original marked kernel
keeps both endpoint squares through the two-sided radius allocation.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The full marked original family is below its normalized marked profile,
with every remaining odd, even and near factor retained. -/
theorem marked_family_normalized (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {lam M h : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (c : ℕ → ℂ × ℂ)
    (F : OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X))
    (hnear : ∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val) →
      MultipoleLinked M lam (c i) (c j))
    (hshort : ∀ e ∈ oddEdges F, dipoleDistOn (fun i : X.biUnion id => c i) e ≤ 17 * h)
    {i j : X.biUnion id}
    (hmark : s(i,j) ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset)
    (hmarkshort : dipoleDist (c i) (c j) ≤ 17 * h) :
    ENNReal.ofReal (markedEvenE lam (fun i : X.biUnion id => c i) s(i,j) *
      F.weight (paperDistE c) (farInd M lam c) *
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset.erase s(i,j),
        paperEvenE M lam (fun i : X.biUnion id => c i) e) ≤
      ENNReal.ofReal (∏ v : X.biUnion id, rhoD lam (c v) ^ 2) *
        (ENNReal.ofReal (markedProfile (rhoD lam (c i)) (rhoD lam (c j)) h (dipoleDist (c i) (c j))) *
          ((∏ e ∈ oddEdges F, ENNReal.ofReal (oddProfile (minRad lam (fun i : X.biUnion id => c i)) h
            (dipoleDistOn (fun i : X.biUnion id => c i) e))) *
            ((∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset.erase s(i,j),
              ENNReal.ofReal (edgeProfile true M lam (fun i : X.biUnion id => c i) e)) *
              ∏ e ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val),
                ENNReal.ofReal (nearE M lam (fun i : X.biUnion id => c i) e)))) := by
  let cfg := fun i : X.biUnion id => c i
  let A := oddEdges F
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  let raw := ∏ e ∈ A, keptWeight (dipoleDistOn cfg) (farInd M lam cfg) e
  let even := ∏ e ∈ E.erase s(i,j), normalizedEven M lam cfg e
  let near := ∏ e ∈ N, nearE M lam cfg e
  have hraw : 0 ≤ raw := prod_nonneg fun e _ => keptWeight_nonneg (farInd_nonneg cfg) e
  have heven : 0 ≤ even := prod_nonneg fun e _ => div_nonneg
    (add_nonneg (aSqE_nonneg cfg e) (linkE_nonneg cfg e)) (minSq_pos hlam cfg e).le
  have hnear0 : 0 ≤ near := prod_nonneg fun e _ => nearE_nonneg M lam cfg e
  have hE : (∏ e ∈ E.erase s(i,j), minSq lam cfg e) * even =
      ∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro e _
    unfold normalizedEven
    rw [mul_div_cancel₀ _ (minSq_pos hlam cfg e).ne']
    induction e using Sym2.ind with
    | h a b =>
      change (if MultipoleLinked M lam (cfg a) (cfg b) then 0 else _) +
        (if MultipoleLinked M lam (cfg a) (cfg b) then 1 else 0) =
        (if MultipoleLinked M lam (cfg a) (cfg b) then 1 else ahat (cfg a) (cfg b) ^ 2)
      split_ifs <;> ring
  have hN : (∏ e ∈ N, minSq lam cfg e) * near = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro e he
    rw [minSq_mul_nearE hlam M cfg e]
    induction e using Sym2.ind with
    | h a b => exact ite_eq_left (hnear a b he)
  have hweight : F.weight (paperDistE c) (farInd M lam c) = oddPrefactor F * raw := by
    rw [oddFamily_weight_eq]
    congr 1
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h a b => rfl
  let m := markedProfile (rhoD lam (c i)) (rhoD lam (c j)) h (dipoleDist (c i) (c j))
  have hm : 0 ≤ m := by
    unfold m markedProfile
    rw [indicator_of_mem (show dipoleDist (c i) (c j) ∈ Iic (17 * h) from hmarkshort)]
    unfold RouteCases.markedEvenKernel
    have hd := dipoleDist_nonneg (c i) (c j)
    positivity
  have hmarkrestore : markedEvenE lam cfg s(i,j) =
      (rhoD lam (c i) ^ 2 * rhoD lam (c j) ^ 2) * m := by
    change RouteCases.markedEvenKernel (rhoD lam (c i)) (rhoD lam (c j)) (dipoleDist (c i) (c j)) = _
    rw [markedProfile_restore (rhoD_pos hlam _) (rhoD_pos hlam _),
      indicator_of_mem (show dipoleDist (c i) (c j) ∈ Iic (17 * h) from hmarkshort)]
  have halloc := source_family_marked_radius_allocation hX hOX hpar
    (fun i => rhoD lam (c i)) hlam (fun _ _ => le_max_right _ _) F Tb hTb Q hmark
  have hemin (e : Sym2 (X.biUnion id)) :
      edgeMin (fun a => max a lam ^ 2) (fun i : X.biUnion id => rhoD lam (c i)) e = minSq lam cfg e := by
    induction e using Sym2.ind with
    | h a b =>
      rw [edgeMin_mk,minSq_mk,max_eq_left
        (show lam ≤ min (rhoD lam (c a)) (rhoD lam (c b)) from le_min (le_max_right _ _) (le_max_right _ _))]
  simp_rw [hemin] at halloc
  have hnorm := mul_le_mul_of_nonneg_right halloc (mul_nonneg hm (mul_nonneg hraw (mul_nonneg heven hnear0)))
  have hrestore : markedEvenE lam cfg s(i,j) * F.weight (paperDistE c) (farInd M lam c) *
      (∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e) =
      (oddPrefactor F * (rhoD lam (c i) ^ 2 * rhoD lam (c j) ^ 2) *
        (∏ e ∈ E.erase s(i,j), minSq lam cfg e) * ∏ e ∈ N, minSq lam cfg e) *
        (m * (raw * (even * near))) := by
    rw [hweight,hmarkrestore]
    calc
      _ = ((rhoD lam (c i) ^ 2 * rhoD lam (c j) ^ 2) * m) * (oddPrefactor F * raw) *
          ((∏ e ∈ E.erase s(i,j), minSq lam cfg e) * even) *
          ((∏ e ∈ N, minSq lam cfg e) * near) := by rw [hE,hN,mul_one]
      _ = _ := by ring
  have hbound := ENNReal.ofReal_le_ofReal (hrestore.trans_le hnorm)
  rw [ENNReal.ofReal_mul (prod_nonneg fun _ _ => sq_nonneg _),ENNReal.ofReal_mul hm,
    ENNReal.ofReal_mul hraw,ENNReal.ofReal_mul heven] at hbound
  have hodd : ENNReal.ofReal raw ≤ ∏ e ∈ A,
      ENNReal.ofReal (oddProfile (minRad lam cfg) h (dipoleDistOn cfg e)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => keptWeight_nonneg (farInd_nonneg cfg) e)]
    exact prod_le_prod fun e he => ENNReal.ofReal_le_ofReal (keptFar_le_oddProfile hlam hM cfg e (hshort e he))
  have he : ENNReal.ofReal even ≤ ∏ e ∈ E.erase s(i,j), ENNReal.ofReal (edgeProfile true M lam cfg e) := by
    change ENNReal.ofReal (∏ e ∈ E.erase s(i,j), normalizedEven M lam cfg e) ≤ _
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => show 0 ≤ normalizedEven M lam cfg e from
      div_nonneg (add_nonneg (aSqE_nonneg cfg e) (linkE_nonneg cfg e)) (minSq_pos hlam cfg e).le)]
    exact prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (normalizedEven_le_edgeProfile hM hlam cfg e)
  have hn : ENNReal.ofReal near = ∏ e ∈ N, ENNReal.ofReal (nearE M lam cfg e) :=
    ENNReal.ofReal_prod_of_nonneg (fun e _ => nearE_nonneg M lam cfg e)
  refine hbound.trans ?_
  rw [hn]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hodd (mul_le_mul' he le_rfl)))

end MultipoleBKT.ExpansionK.RouteSpatial

end
