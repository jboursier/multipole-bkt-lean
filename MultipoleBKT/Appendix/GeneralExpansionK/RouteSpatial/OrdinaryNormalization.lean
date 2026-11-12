/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceSum
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.ActivityTree

/-!
# Normalizing the actual ordinary component family

See Lemma A.7. Restore each allocated squared
minimum, retain the odd annulus and the actual even profile, and cancel
the extracted largest-radius square by the radius allocation.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper
open scoped Classical ENNReal

/-- The far odd weight is supported above the common smallest radius.
The short-domain hypothesis supplies exactly the upper end of its annulus. -/
theorem keptFar_le_oddProfile {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {lam M h : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M) (c : V → ℂ × ℂ)
    (e : Sym2 V) (hshort : dipoleDistOn c e ≤ 17 * h) :
    keptWeight (dipoleDistOn c) (farInd M lam c) e ≤
      oddProfile (minRad lam c) h (dipoleDistOn c e) := by
  induction e using Sym2.ind with
  | h i j =>
    by_cases hlink : MultipoleLinked M lam (c i) (c j)
    · change (if MultipoleLinked M lam (c i) (c j) then 0 else 1) / _ ≤ _
      rw [ite_eq_left hlink,zero_div]
      exact indicator_nonneg (fun _ _ => inv_nonneg.2 (sq_nonneg _)) _
    · have hd : minRad lam c < dipoleDist (c i) (c j) := by
        have hs := le_min (minRad_le lam c i) (minRad_le lam c j)
        have hs0 := (lt_min (rhoD_pos hlam (c i)) (rhoD_pos hlam (c j))).le
        exact lt_of_le_of_lt (hs.trans (le_mul_of_one_le_left hs0 hM)) (lt_of_not_ge hlink)
      change (if MultipoleLinked M lam (c i) (c j) then 0 else 1) / _ ≤ _
      rw [ite_eq_right hlink]
      unfold oddProfile
      simp only [dipoleDistOn_mk]
      rw [indicator_of_mem (show dipoleDist (c i) (c j) ∈ Ioc (minRad lam c) (17 * h) from ⟨hd,hshort⟩)]
      exact (one_div _).le

/-- The retained cutoff product splits into its three disjoint original families. -/
theorem cutTree_split {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M lam h : ℝ) (A E N : Finset (Sym2 V)) (hNA : Disjoint N (A ∪ E))
    (hAE : Disjoint A E) (c : V → ℂ × ℂ) :
    cutTree M lam h A E N c =
      (∏ e ∈ A, ENNReal.ofReal (oddProfile (minRad lam c) h (dipoleDistOn c e))) *
        ((∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam c e)) *
          ∏ e ∈ N, ENNReal.ofReal (nearE M lam c e)) := by
  unfold cutTree
  rw [prod_union hNA,prod_union hAE]
  simp_rw [cutProfile_of_config]
  have pN : (∏ e ∈ N, ENNReal.ofReal
      (if e ∈ A then oddProfile (minRad lam c) h (dipoleDistOn c e)
        else edgeProfile (e ∈ E) M lam c e)) = ∏ e ∈ N, ENNReal.ofReal (nearE M lam c e) := by
    apply prod_congr rfl
    intro e he
    have hn : e ∉ A ∪ E := fun ha => Finset.disjoint_left.1 hNA he ha
    have hnA : e ∉ A := fun ha => hn (mem_union_left _ ha)
    have hnE : e ∉ E := fun ha => hn (mem_union_right _ ha)
    rw [ite_eq_right hnA, show decide (e ∈ E) = false from decide_eq_false hnE,
      nearE_eq_edgeProfile]
  have pA : (∏ e ∈ A, ENNReal.ofReal
      (if e ∈ A then oddProfile (minRad lam c) h (dipoleDistOn c e)
        else edgeProfile (e ∈ E) M lam c e)) =
        ∏ e ∈ A, ENNReal.ofReal (oddProfile (minRad lam c) h (dipoleDistOn c e)) :=
    prod_congr rfl fun e he => by rw [ite_eq_left he]
  have pE : (∏ e ∈ E, ENNReal.ofReal
      (if e ∈ A then oddProfile (minRad lam c) h (dipoleDistOn c e)
        else edgeProfile (e ∈ E) M lam c e)) =
        ∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam c e) := by
    apply prod_congr rfl
    intro e he
    rw [ite_eq_right (fun ha => Finset.disjoint_left.1 hAE ha he),
      show decide (e ∈ E) = true from decide_eq_true he]
  rw [pN,pA,pE]
  ring

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The radius allocation before imposing any spatial cutoff on odd edges.
This form keeps the complete odd family for the omitted domain and case F. -/
theorem ordinary_family_allocated (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {lam M : ℝ}
    (hlam : 0 < lam) (_hM : 1 ≤ M) (c : ℕ → ℂ × ℂ)
    (F : RouteCases.OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X))
    (hnear : ∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val) →
      MultipoleLinked M lam (c i) (c j)) :
    ENNReal.ofReal (maxRad lam (fun i : X.biUnion id => c i) ^ 2 *
      F.weight (paperDistE c) (farInd M lam c) *
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
        paperEvenE M lam (fun i : X.biUnion id => c i) e) ≤
      ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) *
        (ENNReal.ofReal (∏ e ∈ oddEdges F,
          keptWeight (dipoleDistOn (fun i : X.biUnion id => c i)) (farInd M lam (fun i : X.biUnion id => c i)) e) *
          (ENNReal.ofReal (∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
            normalizedEven M lam (fun i : X.biUnion id => c i) e) *
            ENNReal.ofReal (∏ e ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val),
              nearE M lam (fun i : X.biUnion id => c i) e))) := by
  let cfg := fun i : X.biUnion id => c i
  let A := oddEdges F
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  let raw := ∏ e ∈ A, keptWeight (dipoleDistOn cfg) (farInd M lam cfg) e
  let even := ∏ e ∈ E, normalizedEven M lam cfg e
  let near := ∏ e ∈ N, nearE M lam cfg e
  have hraw : 0 ≤ raw := prod_nonneg fun e _ => keptWeight_nonneg (farInd_nonneg cfg) e
  have heven : 0 ≤ even := prod_nonneg fun e _ => div_nonneg
    (add_nonneg (aSqE_nonneg cfg e) (linkE_nonneg cfg e)) (minSq_pos hlam cfg e).le
  have hnear0 : 0 ≤ near := prod_nonneg fun e _ => nearE_nonneg M lam cfg e
  have hE : (∏ e ∈ E, minSq lam cfg e) * even =
      ∏ e ∈ E, paperEvenE M lam cfg e := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro e _
    unfold normalizedEven
    rw [mul_div_cancel₀ _ (minSq_pos hlam cfg e).ne']
    induction e using Sym2.ind with
    | h i j =>
      change (if MultipoleLinked M lam (cfg i) (cfg j) then 0 else _) +
        (if MultipoleLinked M lam (cfg i) (cfg j) then 1 else 0) =
        (if MultipoleLinked M lam (cfg i) (cfg j) then 1 else ahat (cfg i) (cfg j) ^ 2)
      split_ifs <;> ring
  have hN : (∏ e ∈ N, minSq lam cfg e) * near = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro e he
    rw [minSq_mul_nearE hlam M cfg e]
    induction e using Sym2.ind with
    | h i j => exact ite_eq_left (hnear i j he)
  have hweight : F.weight (paperDistE c) (farInd M lam c) = oddPrefactor F * raw := by
    rw [oddFamily_weight_eq]
    congr 1
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => rfl
  have halloc := regularized_family_radius_allocation hX hOX hpar hlam c F Tb hTb Q
  have hnorm := mul_le_mul_of_nonneg_right halloc (mul_nonneg hraw (mul_nonneg heven hnear0))
  have hrestore : maxRad lam cfg ^ 2 * F.weight (paperDistE c) (farInd M lam c) *
      (∏ e ∈ E, paperEvenE M lam cfg e) =
      (maxRad lam cfg ^ 2 * oddPrefactor F * (∏ e ∈ E, minSq lam cfg e) *
        ∏ e ∈ N, minSq lam cfg e) * (raw * (even * near)) := by
    rw [hweight]
    calc
      _ = maxRad lam cfg ^ 2 * (oddPrefactor F * raw) *
          ((∏ e ∈ E, minSq lam cfg e) * even) * ((∏ e ∈ N, minSq lam cfg e) * near) := by rw [hE,hN,mul_one]
      _ = _ := by ring
  have hbound := ENNReal.ofReal_le_ofReal (hrestore.trans_le hnorm)
  rw [ENNReal.ofReal_mul (prod_nonneg fun _ _ => sq_nonneg _),
    ENNReal.ofReal_mul hraw, ENNReal.ofReal_mul heven] at hbound
  exact hbound

/-- The complete ordinary tree weight after restoring near and even minima.
The gain's largest-radius square is cancelled before integration.
Only original graph, near-support and short-domain hypotheses occur here. -/
theorem ordinary_family_normalized (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {lam M h : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (c : ℕ → ℂ × ℂ)
    (F : RouteCases.OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X))
    (hnear : ∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val) →
      MultipoleLinked M lam (c i) (c j))
    (hshort : ∀ e ∈ oddEdges F, dipoleDistOn (fun i : X.biUnion id => c i) e ≤ 17 * h) :
    ENNReal.ofReal (maxRad lam (fun i : X.biUnion id => c i) ^ 2 *
      F.weight (paperDistE c) (farInd M lam c) *
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
        paperEvenE M lam (fun i : X.biUnion id => c i) e) ≤
      ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) *
        cutTree M lam h (oddEdges F) (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
          (nearForest (Limits.blockOf X) (fun S => (Q S).val)) (fun i : X.biUnion id => c i) := by
  let cfg := fun i : X.biUnion id => c i
  let A := oddEdges F
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  let raw := ∏ e ∈ A, keptWeight (dipoleDistOn cfg) (farInd M lam cfg) e
  let even := ∏ e ∈ E, normalizedEven M lam cfg e
  let near := ∏ e ∈ N, nearE M lam cfg e
  have hbound := ordinary_family_allocated hX hOX hpar hlam hM c F Tb hTb Q hnear
  have hodd : ENNReal.ofReal raw ≤ ∏ e ∈ A,
      ENNReal.ofReal (oddProfile (minRad lam cfg) h (dipoleDistOn cfg e)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => keptWeight_nonneg (farInd_nonneg cfg) e)]
    exact prod_le_prod fun e he => ENNReal.ofReal_le_ofReal (keptFar_le_oddProfile hlam hM cfg e (hshort e he))
  have he : ENNReal.ofReal even ≤ ∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam cfg e) := by
    change ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam cfg e) ≤ _
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => show 0 ≤ normalizedEven M lam cfg e from
      div_nonneg (add_nonneg (aSqE_nonneg cfg e) (linkE_nonneg cfg e)) (minSq_pos hlam cfg e).le)]
    exact prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (normalizedEven_le_edgeProfile hM hlam cfg e)
  have hn : ENNReal.ofReal near = ∏ e ∈ N, ENNReal.ofReal (nearE M lam cfg e) :=
    ENNReal.ofReal_prod_of_nonneg (fun e _ => nearE_nonneg M lam cfg e)
  obtain ⟨-,-,hNA,hAE,-⟩ := source_family_structure hX hOX hpar (fun i => rhoD lam (c i)) F Tb hTb Q
  refine hbound.trans ?_
  rw [cutTree_split M lam h A E N hNA hAE cfg,hn]
  exact mul_le_mul' le_rfl (mul_le_mul' hodd (mul_le_mul' he le_rfl))


end MultipoleBKT.ExpansionK.RouteSpatial

end
