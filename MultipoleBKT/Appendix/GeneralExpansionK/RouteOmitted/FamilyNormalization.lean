/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Profiles

/-!
# Normalizing the original omitted alternatives

See Lemma A.7. The quadratic minimum is kept
until allocation. The exterior even mark retains both endpoint squares.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Normalize the whole original family, retaining its actual global tail on
every configuration. No odd edge is cut at the radial threshold. -/
theorem odd_family_normalized (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {lam M H : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (hH : 0 < H) (c : ℕ → ℂ × ℂ)
    (F : OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (hRH : maxRad lam (fun i : X.biUnion id => c i) ≤ H)
    (Q : NearTreeFamily (Limits.blockOf X))
    (hnear : ∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val) →
      MultipoleLinked M lam (c i) (c j)) :
    ENNReal.ofReal (F.weight (paperDistE c) (farInd M lam c) *
      min (maxRad lam (fun i : X.biUnion id => c i) ^ 2 / H ^ 2)
        (globalTail (maxRad lam (fun i : X.biUnion id => c i)) (paperDistE c) F.edges) *
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset,
        paperEvenE M lam (fun i : X.biUnion id => c i) e) ≤
      ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) *
        omittedTree M lam H (oddEdges F) (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
          (nearForest (Limits.blockOf X) (fun S => (Q S).val)) none (fun i : X.biUnion id => c i) := by
  let cfg := fun i : X.biUnion id => c i
  let R := maxRad lam cfg
  let A := oddEdges F
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  have hR : 0 < R := hlam.trans_le (lam_le_maxRad lam cfg)
  have hn := ordinary_family_allocated hX hOX hpar hlam hM c F Tb hTb Q hnear
  have heq : F.weight (paperDistE c) (farInd M lam c) * min (R^2/H^2) (globalTail R (paperDistE c) F.edges) *
      (∏ e ∈ E, paperEvenE M lam cfg e) = (H ^ 2)⁻¹ *
        (R ^ 2 * F.weight (paperDistE c) (farInd M lam c) * ∏ e ∈ E, paperEvenE M lam cfg e) *
          globalTail H (paperDistE c) F.edges := by
    rw [quadratic_globalTail hR hH hRH]
    field_simp
  rw [heq,ENNReal.ofReal_mul' (globalTail_nonneg _ _ _),ENNReal.ofReal_mul (inv_nonneg.2 (sq_nonneg H))]
  refine (mul_le_mul' (mul_le_mul' le_rfl hn) le_rfl).trans ?_
  have hodd := globalTail_kept_le_jointOdd_all hM hlam hH.le cfg A
  have htail : globalTail H (paperDistE c) F.edges = globalTail H (dipoleDistOn cfg) A := by
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
  have hprod : (ENNReal.ofReal ((H ^ 2)⁻¹) *
      (ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) *
        (ENNReal.ofReal (∏ e ∈ A, keptWeight (dipoleDistOn cfg) (farInd M lam cfg) e) *
          (ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam cfg e) * ENNReal.ofReal (∏ e ∈ N, nearE M lam cfg e))))) *
      ENNReal.ofReal (globalTail H (dipoleDistOn cfg) A) =
      (ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i) ^ 2) * ENNReal.ofReal ((H^2)⁻¹)) *
        (ENNReal.ofReal (globalTail H (dipoleDistOn cfg) A * ∏ e ∈ A, keptE M lam cfg e) *
          (ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam cfg e) * ENNReal.ofReal (∏ e ∈ N, nearE M lam cfg e))) := by
    rw [ENNReal.ofReal_mul (globalTail_nonneg _ _ _),hraw]
    ring
  rw [hprod]
  dsimp only [omittedTree]
  rw [distanceFamily_config]
  calc
    _ ≤ (ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i)^2) * ENNReal.ofReal ((H^2)⁻¹)) *
        (jointOdd (minRad lam cfg) H (fun e : A => (dipoleDistOn cfg e : ℂ)) *
          ((∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam cfg e)) *
            ∏ e ∈ N, ENNReal.ofReal (edgeProfile false M lam cfg e))) :=
      mul_le_mul' le_rfl (mul_le_mul' hodd (mul_le_mul' heven hnear'.le))
    _ = _ := by ring

/-- The full marked original family is below its normalized marked profile,
with every remaining odd, even and near factor retained. -/
theorem even_family_normalized (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {lam M H : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (c : ℕ → ℂ × ℂ)
    (F : OddFamily hX hOX hpar (fun i => rhoD lam (c i)))
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (Q : NearTreeFamily (Limits.blockOf X))
    (hnear : ∀ i j, s(i,j) ∈ nearForest (Limits.blockOf X) (fun S => (Q S).val) →
      MultipoleLinked M lam (c i) (c j))
    {i j : X.biUnion id}
    (hmark : s(i,j) ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset)
    (hlong : H < dipoleDist (c i) (c j)) :
    ENNReal.ofReal ((rhoD lam (c i)^2 * rhoD lam (c j)^2 / dipoleDist (c i) (c j)^4) *
      F.weight (paperDistE c) (farInd M lam c) *
      globalTail (maxRad lam (fun i : X.biUnion id => c i)) (paperDistE c) F.edges *
      ∏ e ∈ (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset.erase s(i,j),
        paperEvenE M lam (fun i : X.biUnion id => c i) e) ≤
      ENNReal.ofReal (∏ v : X.biUnion id, rhoD lam (c v) ^ 2) *
        omittedTree M lam H (oddEdges F) (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
          (nearForest (Limits.blockOf X) (fun S => (Q S).val)) (some s(i,j))
          (fun i : X.biUnion id => c i) := by
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
  let m := (dipoleDist (c i) (c j)^4)⁻¹
  have hm : 0 ≤ m := inv_nonneg.2 (by positivity)
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
  have hrestore : (rhoD lam (c i)^2 * rhoD lam (c j)^2 / dipoleDist (c i) (c j)^4) *
      F.weight (paperDistE c) (farInd M lam c) *
      (∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e) =
      (oddPrefactor F * (rhoD lam (c i) ^ 2 * rhoD lam (c j) ^ 2) *
        (∏ e ∈ E.erase s(i,j), minSq lam cfg e) * ∏ e ∈ N, minSq lam cfg e) *
        (m * (raw * (even * near))) := by
    rw [hweight]
    calc
      _ = ((rhoD lam (c i)^2 * rhoD lam (c j)^2) * m) * (oddPrefactor F * raw) *
          ((∏ e ∈ E.erase s(i,j), minSq lam cfg e) * even) *
          ((∏ e ∈ N, minSq lam cfg e) * near) := by rw [hE,hN,mul_one]; rfl
      _ = _ := by ring
  have hbound := ENNReal.ofReal_le_ofReal (hrestore.trans_le hnorm)
  rw [ENNReal.ofReal_mul (prod_nonneg fun _ _ => sq_nonneg _),ENNReal.ofReal_mul hm,
    ENNReal.ofReal_mul hraw,ENNReal.ofReal_mul heven] at hbound
  let tail := globalTail (maxRad lam cfg) (paperDistE c) F.edges
  have htail0 : 0 ≤ tail := globalTail_nonneg _ _ _
  have hodd : ENNReal.ofReal tail * ENNReal.ofReal raw ≤
      jointOdd (minRad lam cfg) (maxRad lam cfg) (fun e : A => (dipoleDistOn cfg e : ℂ)) := by
    rw [← ENNReal.ofReal_mul htail0]
    have ht : tail = globalTail (maxRad lam cfg) (dipoleDistOn cfg) A := by
      dsimp only [tail]
      rw [oddFamily_globalTail F]
      congr 1
      funext e
      induction e using Sym2.ind with
      | h a b => rfl
    rw [ht]
    dsimp only [raw]
    simp_rw [keptWeight_eq_keptE]
    exact globalTail_kept_le_jointOdd_all hM hlam (hlam.trans_le (lam_le_maxRad lam cfg)).le cfg A
  have he : ENNReal.ofReal even ≤ ∏ e ∈ E.erase s(i,j), ENNReal.ofReal (edgeProfile true M lam cfg e) := by
    change ENNReal.ofReal (∏ e ∈ E.erase s(i,j), normalizedEven M lam cfg e) ≤ _
    rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => show 0 ≤ normalizedEven M lam cfg e from
      div_nonneg (add_nonneg (aSqE_nonneg cfg e) (linkE_nonneg cfg e)) (minSq_pos hlam cfg e).le)]
    exact prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (normalizedEven_le_edgeProfile hM hlam cfg e)
  have hn : ENNReal.ofReal near = ∏ e ∈ N, ENNReal.ofReal (nearE M lam cfg e) :=
    ENNReal.ofReal_prod_of_nonneg (fun e _ => nearE_nonneg M lam cfg e)
  have hlongprofile : ENNReal.ofReal m = longEvenProfile 1 1 H (dipoleDist (c i) (c j)) := by
    rw [longEvenProfile,indicator_of_mem (show dipoleDist (c i) (c j) ∈ Ioi H from hlong)]
    norm_num [m,Real.rpow_neg (dipoleDist_nonneg (c i) (c j))]
  have ht := mul_le_mul' (le_refl (ENNReal.ofReal tail)) hbound
  have hre : ENNReal.ofReal tail * (ENNReal.ofReal (∏ v : X.biUnion id, rhoD lam (c v)^2) *
      (ENNReal.ofReal m * (ENNReal.ofReal raw * (ENNReal.ofReal even * ENNReal.ofReal near)))) =
      ENNReal.ofReal (∏ v : X.biUnion id, rhoD lam (c v)^2) *
        (ENNReal.ofReal m * ((ENNReal.ofReal tail * ENNReal.ofReal raw) *
          (ENNReal.ofReal even * ENNReal.ofReal near))) := by ring
  rw [hre] at ht
  have hl : ENNReal.ofReal ((rhoD lam (c i)^2 * rhoD lam (c j)^2 / dipoleDist (c i) (c j)^4) *
      F.weight (paperDistE c) (farInd M lam c) * tail *
      (∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e)) =
      ENNReal.ofReal tail * ENNReal.ofReal ((rhoD lam (c i)^2 * rhoD lam (c j)^2 / dipoleDist (c i) (c j)^4) *
        F.weight (paperDistE c) (farInd M lam c) * ∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e) := by
    rw [← ENNReal.ofReal_mul htail0]
    congr 1
    ring
  rw [hl]
  refine ht.trans ?_
  dsimp only [omittedTree]
  rw [distanceFamily_config,dipoleDistOn_mk,← hlongprofile]
  simp_rw [← nearE_eq_edgeProfile]
  rw [hn]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' hodd (mul_le_mul' he le_rfl)))

end MultipoleBKT.ExpansionK.RouteOmitted

end
