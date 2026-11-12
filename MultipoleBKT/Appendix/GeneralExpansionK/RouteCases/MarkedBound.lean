/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.MarkedEar

/-!
# The marked skeleton estimate

See case D, (A.60). The prescribed base cycle supplies both endpoint radii.
The later ears supply the remaining block squares by the endpoint-score rule.
Their deleted weights are at most one. The spatial product is over the resulting
relative tree, which excludes the marked edge.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Peeling

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [DecidableEq κ]
variable {b : V → κ} {E : SimpleGraph V} {x y : V}
variable {r : V → ℝ} {ρ : κ → ℝ} {d c : Sym2 V → ℝ} {R : ℝ}
variable {P : Ear V} {Qs : List (Ear V × (V × V))}

open scoped Classical in
/-- The full product after opening the marked base cycle. This is the normalized
geometric content of (A.60). Multiplication by the odd-bond error estimate
in (A.56) supplies the inverse screening-radius square. -/
theorem marked_skeleton_product (h : MarkedEarData b E r d R x y P Qs)
    (hr : ∀ v, 0 ≤ r v) (hρ : ∀ S, 0 ≤ ρ S) (hrρ : ∀ v, r v ≤ ρ (b v))
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hR : ∀ v, r v ≤ R) :
    r x * r y * (∏ e ∈ E.edgeFinset.erase s(x, y), absWeight r d c e) ≤
      (∏ S, ρ S ^ 2) *
        ∏ e ∈ (keptGraph E ((P, (x, y)) :: Qs)).edgeFinset, keptWeight d c e := by
  classical
  let As := (P, (x, y)) :: Qs
  let L := (As.map Prod.fst).flatMap Ear.edges
  let Lt := (Qs.map Prod.fst).flatMap Ear.edges
  let Lb := (P.mid ++ [P.last]).map Peeling.edge
  have hD : IsStrictEarDecompOn b E (b x) (As.map Prod.fst) := h.decomp
  have hRem : IsRemoval As := h.isRemoval
  have hL : L = s(x, y) :: (Lb ++ Lt) := by
    simp [L, As, Lb, Lt, Ear.edges, Ear.toList, h.first_eq, Peeling.edge, List.append_assoc]
  have hnd : (Lb ++ Lt).Nodup ∧ s(x, y) ∉ Lb ++ Lt := by
    have hn := hD.nodup
    change L.Nodup at hn
    rw [hL, List.nodup_cons] at hn
    exact ⟨hn.2, hn.1⟩
  have heq : E.edgeFinset.erase s(x, y) = (Lb ++ Lt).toFinset := by
    ext e
    rw [mem_erase, mem_edgeFinset, ← hD.mem_iff]
    change (e ≠ s(x, y) ∧ e ∈ L) ↔ _
    rw [hL, List.mem_cons, List.mem_toFinset]
    exact ⟨fun he => he.2.resolve_left he.1, fun he => ⟨fun heq => hnd.2 (heq ▸ he), Or.inr he⟩⟩
  let W : Sym2 V → ℝ := fun e => if e ∈ removedEdges As then 1 else keptWeight d c e
  let Wg : Sym2 V → ℝ := fun e =>
    if e ∈ removedEdges As then peelWeight r d c R s(x, y) e else keptWeight d c e
  have hW0 : ∀ e, 0 ≤ W e := fun e => by
    dsimp [W]
    split_ifs
    · exact zero_le_one
    · exact keptWeight_nonneg hc _
  have hWg : ∀ e, Wg e ≤ W e := by
    intro e
    dsimp [Wg, W]
    split_ifs
    · exact peelWeight_le_one hr hc1 ((hr x).trans (hR x)) _ _
    · exact le_rfl
  have hWgeq : ∀ Q ∈ Qs, ∀ e ∈ Q.1.edges,
      Wg e = earWeight r d c R s(x, y) Q.2 e := by
    intro Q hQ e he
    simp only [Wg, earWeight,
      hRem.mem_removedEdges_iff hD.nodup Q (List.mem_cons_of_mem _ hQ) e he]
  have htail : (Lt.map (absWeight r d c)).prod ≤
      (((Qs.map Prod.fst).flatMap (Ear.interior b)).map fun S => ρ S ^ 2).prod *
        (Lt.map W).prod := by
    have haux := prod_absWeight_le_aux hr hd hc hR ρ hrρ Wg hD.isEarSeq.2 h.later_rule hWgeq
    refine haux.trans (mul_le_mul_of_nonneg_left ?_ ?_)
    · exact List.prod_map_le_prod_map₀ _ _ (fun e _ => by
        dsimp [Wg]; split_ifs
        · exact peelWeight_nonneg hc _ _
        · exact keptWeight_nonneg hc _) (fun e _ => hWg e)
    · exact List.prod_nonneg fun z hz => by
        obtain ⟨S, -, rfl⟩ := List.mem_map.1 hz
        exact sq_nonneg _
  have hbase : r x * r y * (Lb.map (absWeight r d c)).prod ≤
      (ρ (b x) ^ 2 * ((P.interior b).map fun S => ρ S ^ 2).prod) * (Lb.map W).prod := by
    have hP := hD.isEarSeq.1
    have hclose : b P.first.1 = b P.last.2 :=
      (mem_singleton.1 hP.startBlock_mem).trans (mem_singleton.1 hP.endBlock_mem).symm
    have hWb : ∀ e ∈ Lb, W e = keptWeight d c e := by
      intro e he
      have heP : e ∈ P.edges := by
        rw [Ear.edges, Ear.toList, List.map_cons]
        exact List.mem_cons_of_mem _ he
      have hne : e ≠ s(x, y) := fun heq => hnd.2 (List.mem_append_left _ (heq ▸ he))
      have hnRem : e ∉ removedEdges As := by
        rw [hRem.mem_removedEdges_iff hD.nodup (P, (x, y)) List.mem_cons_self e heP]
        exact hne
      exact ite_eq_right hnRem
    have hb := marked_base_cycle b P r ρ d c hr hρ hrρ hd hc hP.isChain hclose
    have hx : P.first.1 = x := congrArg Prod.fst h.first_eq
    have hy : P.first.2 = y := congrArg Prod.snd h.first_eq
    rw [hx, hy] at hb
    rw [congrArg List.prod (List.map_congr_left fun e he => hWb e he)]
    simpa only [Lb, List.map_map, Function.comp_def] using hb
  have hrad : ρ (b x) ^ 2 * ((P.interior b).map fun S => ρ S ^ 2).prod *
      (((Qs.map Prod.fst).flatMap (Ear.interior b)).map fun S => ρ S ^ 2).prod =
        ∏ S, ρ S ^ 2 := by
    obtain ⟨hi, hn, hcov⟩ := hD.isEarSeq.interiors
    rw [hD.covered_eq] at hcov
    let IL := (As.map Prod.fst).flatMap (Ear.interior b)
    have hfin : insert (b x) IL.toFinset = univ := by
      simpa only [singleton_union] using hcov.symm
    have hnot : b x ∉ IL.toFinset := fun hx => hn _ (List.mem_toFinset.1 hx) (mem_singleton_self _)
    have hh : ρ (b x) ^ 2 * (IL.map fun S => ρ S ^ 2).prod = ∏ S, ρ S ^ 2 := by
      rw [← List.prod_toFinset _ (show IL.Nodup from hi)]
      calc _ = ∏ S ∈ insert (b x) IL.toFinset, ρ S ^ 2 := (prod_insert hnot).symm
           _ = _ := by rw [hfin]
    simpa only [IL, As, List.map_cons, List.flatMap_cons, List.map_append, List.prod_append,
      mul_assoc] using hh
  have htree : (L.map W).prod =
      ∏ e ∈ (keptGraph E As).edgeFinset, keptWeight d c e := by
    have hE : E.edgeFinset = L.toFinset := by
      ext e
      rw [mem_edgeFinset, List.mem_toFinset]
      exact (hD.mem_iff e).symm
    rw [← List.prod_toFinset _ hD.nodup, ← hE]
    simp only [W]
    rw [prod_ite, prod_const_one, one_mul]
    apply prod_congr
    · ext e
      rw [mem_filter, mem_edgeFinset, mem_edgeFinset, keptGraph, edgeSet_deleteEdges]
      rfl
    · intro _ _
      rfl
  have hWmark : W s(x, y) = 1 := by simp [W, As, removedEdges, Peeling.edge]
  have hprod : (L.map W).prod = (Lb.map W).prod * (Lt.map W).prod := by
    rw [hL, List.map_cons, List.prod_cons, hWmark, one_mul, List.map_append, List.prod_append]
  rw [heq, List.prod_toFinset _ hnd.1, List.map_append, List.prod_append]
  calc r x * r y * ((Lb.map (absWeight r d c)).prod * (Lt.map (absWeight r d c)).prod)
      = (r x * r y * (Lb.map (absWeight r d c)).prod) * (Lt.map (absWeight r d c)).prod := by ring
    _ ≤ ((ρ (b x) ^ 2 * ((P.interior b).map fun S => ρ S ^ 2).prod) * (Lb.map W).prod) *
        ((((Qs.map Prod.fst).flatMap (Ear.interior b)).map fun S => ρ S ^ 2).prod * (Lt.map W).prod) :=
      mul_le_mul hbase htail
        (List.prod_nonneg fun z hz => by
          obtain ⟨e, -, rfl⟩ := List.mem_map.1 hz
          exact absWeight_nonneg hr hd hc _)
        (mul_nonneg (mul_nonneg (sq_nonneg _) (List.prod_nonneg fun z hz => by
          obtain ⟨S, -, rfl⟩ := List.mem_map.1 hz
          exact sq_nonneg _)) (List.prod_nonneg fun z hz => by
          obtain ⟨e, -, rfl⟩ := List.mem_map.1 hz
          exact hW0 e))
    _ = (∏ S, ρ S ^ 2) * (L.map W).prod := by rw [hprod, ← hrad]; ring
    _ = _ := by rw [htree]

end MultipoleBKT.ExpansionK.RouteCases

end
