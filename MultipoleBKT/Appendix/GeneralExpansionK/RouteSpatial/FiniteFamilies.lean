/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.FamilyProduct
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ClusterBoundary

/-!
# Fixed finite choices for the odd trees and their roots

See Lemma A.7. The graph choices do not depend on
lambda or the configuration. Their maximal-radius sectors keep the component
root condition until radius allocation.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ UpperBound.BoundedUpper
open scoped Classical

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- The graph and root data of the family before imposing a radius sector. -/
structure OddTreeChoice (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) where
  root : (Y : oddComponents X O) → Y.val.biUnion id
  tree : (Y : oddComponents X O) → SimpleGraph (Y.val.biUnion id)
  tree_spec : ∀ Y, IsRelTree Y.val (tree Y) ∧ tree Y ≤ RouteCases.sourceOddSkeleton hX hOX hpar Y

instance {hX : IsSubpartition X} {hOX : O ⊆ interPairs X} {hpar : IsParityPair X O ∅} :
    Finite (OddTreeChoice hX hOX hpar) := by
  classical
  apply Finite.of_injective (fun F : OddTreeChoice hX hOX hpar => (F.root,F.tree))
  intro F G h
  cases F
  cases G
  cases h
  rfl

noncomputable instance {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} : Fintype (OddTreeChoice hX hOX hpar) := Fintype.ofFinite _

/-- The maximal-radius sector attached to a fixed root choice. -/
def OddTreeChoice.Maximal {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} (F : OddTreeChoice hX hOX hpar) (r : ℕ → ℝ) : Prop :=
  ∀ Y (i : Y.val.biUnion id), r i ≤ r (F.root Y)

/-- Forget only the radius-sector proof in the chosen family. -/
def OddTreeChoice.ofFamily {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} (F : RouteCases.OddFamily hX hOX hpar r) :
    OddTreeChoice hX hOX hpar := ⟨F.root,F.tree,F.tree_spec⟩

/-- Restore the family on its maximal-radius sector. -/
def OddTreeChoice.toFamily {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} (F : OddTreeChoice hX hOX hpar) (r : ℕ → ℝ)
    (h : F.Maximal r) : RouteCases.OddFamily hX hOX hpar r :=
  ⟨F.root,F.tree,F.tree_spec,h⟩

/-- The actual component product belonging to one fixed choice.
The indicator is its maximal-radius sector, not a selected default tree. -/
noncomputable def OddTreeChoice.weight {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} (F : OddTreeChoice hX hOX hpar)
    (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ) : ℝ :=
  if F.Maximal r then
    ∏ Y : oddComponents X O,
      (∏ S ∈ univ.erase (MultipoleBKT.blockOf
        (RouteCases.source_odd_component_eulerian hX hOX hpar Y.property).1 (F.root Y)),
        blockRadius (RouteCases.source_odd_component_eulerian hX hOX hpar Y.property).1
          (fun i : Y.val.biUnion id => r i) S ^ 2) *
      ∏ e ∈ (F.tree Y).edgeFinset,
        keptWeight (RouteCases.componentEdge d) (RouteCases.componentEdge c) e
  else 0

/-- Every fixed-choice summand is nonnegative. -/
theorem OddTreeChoice.weight_nonneg {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} (F : OddTreeChoice hX hOX hpar)
    (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) : 0 ≤ F.weight r d c := by
  unfold weight
  split_ifs
  · exact prod_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
      (prod_nonneg fun _ _ => keptWeight_nonneg (fun _ => hc _) _)
  · exact le_rfl

/-- On its sector the fixed product is exactly the complete family product. -/
theorem OddTreeChoice.weight_eq {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} (F : OddTreeChoice hX hOX hpar) (r : ℕ → ℝ)
    (h : F.Maximal r) (d c : Sym2 ℕ → ℝ) :
    F.weight r d c = (F.toFamily r h).weight d c := by
  rw [weight,ite_eq_left h]
  rfl

/-- Each configuration-dependent family is one summand of a fixed finite sum. -/
theorem oddFamily_weight_le_sum {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ}
    (F : RouteCases.OddFamily hX hOX hpar r) (d c : Sym2 ℕ → ℝ) (hc : ∀ e, 0 ≤ c e) :
    F.weight d c ≤ ∑ Q : OddTreeChoice hX hOX hpar, Q.weight r d c := by
  have he : (OddTreeChoice.ofFamily F).weight r d c = F.weight d c := by
    rw [OddTreeChoice.weight_eq (OddTreeChoice.ofFamily F) r F.root_max]
    rfl
  rw [← he]
  exact single_le_sum (f := fun Q : OddTreeChoice hX hOX hpar => Q.weight r d c)
    (fun Q _ => Q.weight_nonneg r d c hc) (mem_univ _)

/-- The ordinary screening and bad-label alternatives, and the marked-even
alternative, summed over all original labels and marks. -/
noncomputable def paperSpatialSum (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (τ v : X.biUnion id → ℝ) (b J : Sym2 (X.biUnion id) → ℝ)
    (T : Finset (Sym2 (X.biUnion id))) (R : ℝ) : ℝ :=
  (∑ F : OddTreeChoice hX hOX hpar, F.weight r d c) *
    ((∑ i : X.biUnion id, (R ^ 2 / τ i ^ 2 + |v i|) * ∏ e ∈ T, b e) +
      ∑ i : X.biUnion id, ∑ j : X.biUnion id,
        if s(i,j) ∈ T then (τ i ^ 2)⁻¹ * J s(i,j) * ∏ e ∈ T.erase s(i,j), b e else 0)

/-- Every term of the paper spatial sum is nonnegative. -/
theorem paperSpatialSum_nonneg (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (τ v : X.biUnion id → ℝ) (b J : Sym2 (X.biUnion id) → ℝ)
    (T : Finset (Sym2 (X.biUnion id))) (R : ℝ)
    (hc : ∀ e, 0 ≤ c e) (hb : ∀ e, 0 ≤ b e) (hJ : ∀ e, 0 ≤ J e) :
    0 ≤ paperSpatialSum hX hOX hpar r d c τ v b J T R := by
  unfold paperSpatialSum
  apply mul_nonneg (sum_nonneg fun F _ => F.weight_nonneg r d c hc)
  apply add_nonneg
  · exact sum_nonneg fun _ _ => mul_nonneg
      (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (abs_nonneg _))
      (prod_nonneg fun e _ => hb e)
  · apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    split_ifs
    · exact mul_nonneg (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (hJ _))
        (prod_nonneg fun e _ => hb e)
    · exact le_rfl

/-- Internal finite-sum elimination of the existential alternatives.
No pointwise choice of a root or tree is moved across an integral. -/
theorem internal_paperPointwise_le_sum {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} {d c : Sym2 ℕ → ℝ}
    {τ v : X.biUnion id → ℝ} {b J : Sym2 (X.biUnion id) → ℝ}
    {T : Finset (Sym2 (X.biUnion id))}
    {P : RouteCases.FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)} {R C t : ℝ}
    (H : RouteCases.PaperPointwise hX hOX hpar r d c τ v b J T P R C t)
    (hC : 0 ≤ C) (hc : ∀ e, 0 ≤ c e) (hb : ∀ e, 0 ≤ b e) (hJ : ∀ e, 0 ≤ J e) :
    |t| ≤ C * paperSpatialSum hX hOX hpar r d c τ v b J T R := by
  let W := ∑ F : OddTreeChoice hX hOX hpar, F.weight r d c
  let A := ∑ i : X.biUnion id, (R ^ 2 / τ i ^ 2 + |v i|) * ∏ e ∈ T, b e
  let B := ∑ i : X.biUnion id, ∑ j : X.biUnion id,
    if s(i,j) ∈ T then (τ i ^ 2)⁻¹ * J s(i,j) * ∏ e ∈ T.erase s(i,j), b e else 0
  have hW : 0 ≤ W := sum_nonneg fun F _ => F.weight_nonneg r d c hc
  have hT : 0 ≤ ∏ e ∈ T, b e := prod_nonneg fun e _ => hb e
  have hA0 (i) : 0 ≤ (R ^ 2 / τ i ^ 2 + |v i|) * ∏ e ∈ T, b e :=
    mul_nonneg (add_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (abs_nonneg _)) hT
  have hB0 (i j : X.biUnion id) :
      0 ≤ (if s(i,j) ∈ T then (τ i ^ 2)⁻¹ * J s(i,j) * ∏ e ∈ T.erase s(i,j), b e else 0) := by
    split_ifs
    · exact mul_nonneg (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (hJ _))
        (prod_nonneg fun e _ => hb e)
    · exact le_rfl
  have hA : 0 ≤ A := sum_nonneg fun i _ => hA0 i
  have hB : 0 ≤ B := sum_nonneg fun i _ => sum_nonneg fun j _ => hB0 i j
  have hAi (i) : (R ^ 2 / τ i ^ 2 + |v i|) * (∏ e ∈ T, b e) ≤ A + B :=
    (single_le_sum (fun j _ => hA0 j) (mem_univ i)).trans (le_add_of_nonneg_right hB)
  have hBi (i j) (he : s(i,j) ∈ T) :
      (τ i ^ 2)⁻¹ * J s(i,j) * (∏ e ∈ T.erase s(i,j), b e) ≤ A + B := by
    have hs := (single_le_sum (fun l _ => hB0 i l) (mem_univ j)).trans
      (single_le_sum (fun l _ => sum_nonneg fun k _ => hB0 l k) (mem_univ i))
    rw [ite_eq_left he] at hs
    exact hs.trans (le_add_of_nonneg_left hA)
  change |t| ≤ C * (W * (A + B))
  rcases H with ⟨F,i,h⟩ | ⟨F,i,j,he,h⟩
  · have hF := oddFamily_weight_le_sum F d c hc
    have hF0 := F.weight_nonneg d c hc
    rcases h with h | ⟨-,h⟩
    · refine h.trans ?_
      calc
        _ = C * (F.weight d c * ((R ^ 2 / τ i ^ 2) * ∏ e ∈ T, b e)) := by ring
        _ ≤ C * (W * ((R ^ 2 / τ i ^ 2 + |v i|) * ∏ e ∈ T, b e)) := by gcongr; exact le_add_of_nonneg_right (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAi i) hW) hC
    · refine h.trans ?_
      calc
        _ = C * (F.weight d c * (|v i| * ∏ e ∈ T, b e)) := by ring
        _ ≤ C * (W * ((R ^ 2 / τ i ^ 2 + |v i|) * ∏ e ∈ T, b e)) := by gcongr; exact le_add_of_nonneg_left (div_nonneg (sq_nonneg _) (sq_nonneg _))
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAi i) hW) hC
  · have hF := oddFamily_weight_le_sum F d c hc
    have hF0 := F.weight_nonneg d c hc
    refine h.trans ?_
    calc
      _ = C * (F.weight d c * ((τ i ^ 2)⁻¹ * J s(i,j) * ∏ e ∈ T.erase s(i,j), b e)) := by ring
      _ ≤ C * (W * ((τ i ^ 2)⁻¹ * J s(i,j) * ∏ e ∈ T.erase s(i,j), b e)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact mul_le_mul_of_nonneg_right hF (mul_nonneg
          (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (hJ _)) (prod_nonneg fun e _ => hb e))
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hBi i j (mem_inter.1 he).1) hW) hC

end MultipoleBKT.ExpansionK.RouteSpatial

end
