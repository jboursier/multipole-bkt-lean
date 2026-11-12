/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Compensation

/-!
# Comparison costs on lifted chains

The paper: Corollary 5.34. Each parent bridge is used once. An internal block crossing
is used only by the path arriving through its heavy child.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift
open CoreForest

variable {Λ V : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype V] [DecidableEq V]
  {τ : SimpleGraph Λ} [DecidableRel τ.Adj] {a : Λ} {h : Λ → Λ} {T : SimpleGraph V}

/-- The nonroot blocks traversed by a leaf's heavy chain. -/
noncomputable def chainBlocks (l : Leaf τ a) : Finset (Nonroot a) :=
  univ.filter fun v => IsHeavyChain τ a h v.val l.val

/-- Distinct heavy chains use disjoint blocks for their internal crossings. -/
theorem chainBlocks_disjoint (hτ : τ.IsTree) {l l' : Leaf τ a} (hne : l ≠ l') :
    Disjoint (chainBlocks (h := h) l) (chainBlocks (h := h) l') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  apply hne
  apply Subtype.ext
  exact ((mem_filter.1 hv).2).eq_of_leaf (mem_filter.1 hv').2
    ((mem_leaves_iff_of_ne (T := τ) (r := a) hτ
      (mem_erase.1 l.property).1).1 (mem_erase.1 l.property).2)
    ((mem_leaves_iff_of_ne (T := τ) (r := a) hτ
      (mem_erase.1 l'.property).1).1 (mem_erase.1 l'.property).2)

namespace BlockTree

variable (D : BlockTree τ a T) (hτ : τ.IsTree)

/-- Local costs multiply over the disjoint lifted chains. This version permits
an entire block comparison to be charged as one factor `W`, rather than counting
its individual extracted-tree edges. -/
theorem transport_by_block_costs (hh : IsChildChoice τ a h) {δ : V → ℝ}
    {K : ℝ} {W : Λ → ℝ} (hK : 1 ≤ K) (hW : ∀ u, 1 ≤ W u)
    (hδ : ∀ x, 0 < δ x)
    (hbridge : ∀ v, δ (D.parentEnd v) ≤ K * δ (D.childEnd v))
    (hinside : ∀ v c : Nonroot a, IsParent τ a v c → h v = c.val →
      δ (D.childEnd v) ≤ W v * δ (D.parentEnd c)) :
    (∏ l : Leaf τ a, 1 / δ (D.start l)) ≤
      (∏ v : Nonroot a, (K * if τ.degree v = 1 then 1 else W v)) *
        ∏ S, (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card := by
  let cost : Nonroot a → ℝ := fun v => K * if τ.degree v = 1 then 1 else W v
  have hcost : ∀ v, 1 ≤ cost v := fun v => by
    dsimp [cost]
    split_ifs
    · simpa using hK
    · exact one_le_mul_of_one_le_of_one_le hK (hW v)
  have hlocal : ∀ (l : Leaf τ a) (v : Nonroot a), IsHeavyChain τ a h v l →
      δ (D.parentEnd v) ≤ (∏ c ∈ chainBlocks (h := h) l,
        if IsDesc τ a v.val c.val then cost c else 1) * δ (D.start l) := by
    intro l v hc
    have key : ∀ {u : Λ} (hu : u ≠ a), IsHeavyChain τ a h u l →
        δ (D.parentEnd ⟨u, hu⟩) ≤
          (∏ c ∈ chainBlocks (h := h) l,
            if IsDesc τ a u c.val then cost c else 1) * δ (D.start l) := by
      intro u hu hchain
      induction hchain using Relation.ReflTransGen.head_induction_on with
      | refl =>
        have hleaf : τ.degree l = 1 := (mem_leaves.1 (mem_erase.1 l.property).2)
        have heq : (∏ c ∈ chainBlocks (h := h) l,
            if IsDesc τ a l.val c.val then cost c else 1) = cost ⟨l, hu⟩ := by
          calc _ = (if IsDesc τ a l.val l.val then cost ⟨l, hu⟩ else 1) := by
                  apply Finset.prod_eq_single (⟨l, hu⟩ : Nonroot a)
                  · intro c hc hne
                    rw [ite_eq_right]
                    intro hlc
                    exact hne (Subtype.ext (hlc.antisymm ((mem_filter.1 hc).2).isDesc).symm)
                  · intro hn
                    exact (hn (mem_filter.2 ⟨mem_univ _, Relation.ReflTransGen.refl⟩)).elim
                _ = _ := ite_eq_left (IsDesc.refl _)
        rw [heq]
        simpa only [cost, hleaf, ite_true, mul_one, start] using hbridge ⟨l, hu⟩
      | @head u c huc hcl ih =>
        have hcne : c ≠ a := fun he => not_isParent_root _ (he ▸ huc.1)
        have hnleaf : τ.degree u ≠ 1 := by
          intro hl
          exact ((mem_leaves_iff_of_ne hτ hu).1 (mem_leaves.2 hl)) c huc.1
        have hcu : ¬ IsDesc τ a c u := by
          intro hd
          have := hd.dist_le
          have := huc.1.dist_lt
          omega
        have hsplit : (∏ z ∈ chainBlocks (h := h) l,
            if IsDesc τ a u z.val then cost z else 1) =
            cost ⟨u, hu⟩ * (∏ z ∈ chainBlocks (h := h) l,
              if IsDesc τ a c z.val then cost z else 1) := by
          have huMem : (⟨u, hu⟩ : Nonroot a) ∈ chainBlocks (h := h) l :=
            mem_filter.2 ⟨mem_univ _, Relation.ReflTransGen.head huc hcl⟩
          rw [← Finset.mul_prod_erase _ _ huMem, ite_eq_left (IsDesc.refl u)]
          congr 1
          rw [← Finset.mul_prod_erase _ (fun z : Nonroot a =>
            if IsDesc τ a c z.val then cost z else 1) huMem, ite_eq_right hcu, one_mul]
          apply Finset.prod_congr rfl
          intro z hz
          have hzl := ((mem_filter.1 (mem_of_mem_erase hz)).2).isDesc
          have hzu : z.val ≠ u := fun he => (ne_of_mem_erase hz) (Subtype.ext he)
          have heq : IsDesc τ a u z.val ↔ IsDesc τ a c z.val := by
            constructor
            · intro huz
              rcases IsDesc.total hτ hzl (show IsHeavyChain τ a h c l from hcl).isDesc with hzc | hcz
              · have he := hzc.eq_or_isDesc_of_isParent hτ huc.1
                rcases he with he | hzu'
                · exact he.symm ▸ IsDesc.refl c
                · exact (hzu (hzu'.antisymm huz)).elim
              · exact hcz
            · exact fun hcz => huc.1.isDesc.trans hcz
          rw [heq]
        rw [hsplit]
        calc δ (D.parentEnd ⟨u, hu⟩) ≤ K * δ (D.childEnd ⟨u, hu⟩) := hbridge _
          _ ≤ K * (W u * δ (D.parentEnd ⟨c, hcne⟩)) :=
            mul_le_mul_of_nonneg_left (hinside ⟨u, hu⟩ ⟨c, hcne⟩ huc.1 huc.2)
              (zero_le_one.trans hK)
          _ ≤ K * (W u * ((∏ z ∈ chainBlocks (h := h) l,
              if IsDesc τ a c z.val then cost z else 1) * δ (D.start l))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (ih hcne) (zero_le_one.trans (hW u)))
              (zero_le_one.trans hK)
          _ = _ := by simp only [cost, hnleaf, ite_false]; ring
    exact key v.property hc
  have hleaf : ∀ l : Leaf τ a, 1 / δ (D.start l) ≤
      (∏ v ∈ chainBlocks (h := h) l, cost v) * (1 / δ (loc (h := h) hτ D.parentEnd l)) := by
    intro l
    have hc := hlocal l (terminalChild (h := h) hτ l) (terminalChild_spec (h := h) hτ l).2.1
    have hle : (∏ v ∈ chainBlocks (h := h) l,
        if IsDesc τ a (terminalChild (h := h) hτ l).val v.val then cost v else 1) ≤
        ∏ v ∈ chainBlocks (h := h) l, cost v := by
      apply prod_le_prod₀
      · intro v _
        split_ifs
        · exact zero_le_one.trans (hcost v)
        · exact zero_le_one
      · intro v _
        split_ifs
        · exact le_rfl
        · exact hcost v
    have hc' := hc.trans (mul_le_mul_of_nonneg_right hle (hδ _).le)
    rw [mul_one_div, div_le_div_iff₀ (hδ _) (hδ _), one_mul]
    exact hc'
  have hprod : (∏ l : Leaf τ a, ∏ v ∈ chainBlocks (h := h) l, cost v) = ∏ v, cost v := by
    rw [← Finset.prod_biUnion]
    · congr 1
      ext v
      rw [mem_biUnion]
      constructor
      · intro _
        exact mem_univ _
      · intro _
        obtain ⟨l, hl, -⟩ := existsUnique_heavyLeaf hτ hh v.property
        exact ⟨⟨l, hl.1⟩, mem_univ _, mem_filter.2 ⟨mem_univ _, hl.2⟩⟩
    · intro l _ l' _ hne
      exact chainBlocks_disjoint (hτ := hτ) hne
  calc (∏ l : Leaf τ a, 1 / δ (D.start l)) ≤
      ∏ l : Leaf τ a, ((∏ v ∈ chainBlocks (h := h) l, cost v) *
        (1 / δ (loc (h := h) hτ D.parentEnd l))) :=
      prod_le_prod₀ (fun l _ => (one_div_pos.2 (hδ _)).le) fun l _ => hleaf l
    _ = _ := by rw [prod_mul_distrib, hprod, prod_attachmentFiber (h := h) hτ D.parentEnd (fun S => 1 / δ S)]

end BlockTree
end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
