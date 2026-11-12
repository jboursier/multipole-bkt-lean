/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Chains

/-!
# Multiplication of the attachment-level radius estimates

The paper: Corollary 5.34, equations (5.93) through (5.100).
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift
open CoreForest

variable {Λ V : Type*} [Fintype Λ] [DecidableEq Λ] [Fintype V] [DecidableEq V]
  {τ : SimpleGraph Λ} [DecidableRel τ.Adj] {a : Λ} {h : Λ → Λ} {T : SimpleGraph V}

namespace BlockTree
variable (D : BlockTree τ a T) (hτ : τ.IsTree)

omit [DecidableRel τ.Adj] in
/-- The product of bridge endpoint radii is the degree product on the parts. -/
theorem prod_bridge_radii {M : Type*} [CommMonoid M] (r : V → M) :
    (∏ v : Nonroot a, r (D.childEnd v) * r (D.parentEnd v)) =
      ∏ S, r S ^ D.bridgeDegree S := by
  have hp : ∀ S, (childBridges (τ := τ) D.parentEnd (D.block S) S) =
      univ.filter (fun v => D.parentEnd v = S) := by
    intro S
    ext v
    simp only [childBridges, mem_filter, mem_univ, true_and]
    exact ⟨fun hv => hv.2, fun hv => ⟨hv ▸ D.parent_block v, hv⟩⟩
  simp only [bridgeDegree, pow_add, prod_mul_distrib, hp]
  congr 1
  · symm
    have := Finset.prod_fiberwise (univ : Finset (Nonroot a)) D.childEnd (fun v => r (D.childEnd v))
    rw [← this]
    apply prod_congr rfl
    intro S _
    rw [← Finset.prod_const]
    exact prod_congr rfl fun v hv => (congrArg r (mem_filter.1 hv).2).symm
  · symm
    have := Finset.prod_fiberwise (univ : Finset (Nonroot a)) D.parentEnd (fun v => r (D.parentEnd v))
    rw [← this]
    apply prod_congr rfl
    intro S _
    rw [← Finset.prod_const]
    exact prod_congr rfl fun v hv => (congrArg r (mem_filter.1 hv).2).symm

/-- A childless nonroot block has no attachment fibers, so its one parent
radius and the radius from its retained leaf mark give a square, as in (5.93). -/
theorem compensate_leaf (hh : IsChildChoice τ a h) {r δ : V → ℝ} {R : ℝ}
    (hr : ∀ S, 0 ≤ r S) {u : Λ} (hu : u ≠ a) (hleaf : τ.degree u = 1)
    (hrR : ∀ S, D.block S = u → r S ≤ R) :
    (∏ S ∈ univ.filter (fun S => D.block S = u), r S ^ D.bridgeDegree S) * R *
      (∏ S ∈ univ.filter (fun S => D.block S = u),
        (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) ≤ R ^ 2 := by
  have hnchild := (mem_leaves_iff_of_ne hτ hu).1 (mem_leaves.2 hleaf)
  have hemp : ∀ S, childBridges (τ := τ) D.parentEnd u S = ∅ := by
    intro S
    exact eq_empty_iff_forall_notMem.2 fun c hc => hnchild c (mem_filter.1 hc).2.1
  have hf : ∀ S, D.block S = u → (attachmentFiber (h := h) hτ D.parentEnd S).card = 0 := by
    intro S hS
    rw [card_attachmentFiber hτ hh D.block D.parentEnd D.parent_block, hS, hemp]
    simp
  rw [D.prod_bridgeDegree_nonroot r hu]
  simp only [hemp, card_empty, pow_zero, prod_const_one, mul_one]
  have hd : (∏ S ∈ univ.filter (fun S => D.block S = u),
      (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) = 1 :=
    prod_eq_one fun S hS => by rw [hf S (mem_filter.1 hS).2, pow_zero]
  rw [hd, mul_one, sq]
  exact mul_le_mul_of_nonneg_right (hrR _ (D.child_block _))
    ((hr (D.childEnd ⟨u, hu⟩)).trans (hrR _ (D.child_block ⟨u, hu⟩)))

/-- A degree-two nonroot block has one parent and one heavy child. No
path stops there, so its two endpoint radii give the square in (5.93). -/
theorem compensate_degree_two (hh : IsChildChoice τ a h) {r δ : V → ℝ} {R : ℝ}
    (hr : ∀ S, 0 ≤ r S) {u : Λ} (hu : u ≠ a) (hdeg : τ.degree u = 2)
    (hrR : ∀ S, D.block S = u → r S ≤ R) :
    (∏ S ∈ univ.filter (fun S => D.block S = u), r S ^ D.bridgeDegree S) *
      (∏ S ∈ univ.filter (fun S => D.block S = u),
        (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) ≤ R ^ 2 := by
  have hcard : (children τ a u).card = 1 := by
    have hd := degree_eq (r := a) hτ u
    rw [ite_eq_right hu, hdeg] at hd
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.1 hcard
  have huc : IsParent τ a u c := mem_children.1 (hc ▸ mem_singleton_self _)
  have hheavy : h u = c := by
    have := mem_children.2 (hh u c huc)
    rwa [hc, mem_singleton] at this
  have hf : ∀ S, D.block S = u → (attachmentFiber (h := h) hτ D.parentEnd S).card = 0 := by
    intro S hS
    rw [card_attachmentFiber hτ hh D.block D.parentEnd D.parent_block, hS]
    apply Finset.card_eq_zero.2
    apply eq_empty_iff_forall_notMem.2
    intro z hz
    have hzchild := (mem_filter.1 (mem_filter.1 hz).1).2.1
    have hzc : z.val = c := by
      have := mem_children.2 hzchild
      rwa [hc, mem_singleton] at this
    exact ((mem_filter.1 hz).2.resolve_left hu) (hheavy.trans hzc.symm)
  have huc' := hh u c huc
  let H : Nonroot a := ⟨h u, fun he => not_isParent_root _ (he ▸ huc')⟩
  have hp : D.block (D.parentEnd H) = u := (D.parent_block H).unique hτ huc'
  rw [D.prod_bridgeDegree_nonroot r hu, D.prod_children_nonroot hτ hh r hu huc']
  have hprod : ∀ f : V → ℝ, (∏ S ∈ univ.filter (fun S => D.block S = u),
      f S ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) = 1 := fun f =>
    prod_eq_one fun S hS => by rw [hf S (mem_filter.1 hS).2, pow_zero]
  rw [hprod, hprod, mul_one, mul_one, sq]
  exact mul_le_mul (hrR _ (D.child_block _)) (hrR _ hp) (hr _)
    ((hr (D.childEnd ⟨u, hu⟩)).trans (hrR _ (D.child_block _)))

/-- The root has a single child bridge. Its degree product with attachment
inverse powers is exactly the ratio at the parent endpoint of that bridge. -/
theorem compensate_root_eq (hh : IsChildChoice τ a h) (ha : τ.degree a = 1)
    {r δ : V → ℝ} :
    ∃ v : Nonroot a, IsParent τ a a v ∧
      (∏ S ∈ univ.filter (fun S => D.block S = a), r S ^ D.bridgeDegree S) *
        (∏ S ∈ univ.filter (fun S => D.block S = a),
          (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) =
        r (D.parentEnd v) / δ (D.parentEnd v) := by
  have hc : (children τ a a).card = 1 := by
    have := degree_eq (r := a) hτ a
    simpa only [ite_true, add_zero, ha] using this.symm
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hc
  have hvp : IsParent τ a a v := mem_children.1 (hv ▸ mem_singleton_self _)
  have hvne : v ≠ a := fun he => not_isParent_root _ (he ▸ hvp)
  let v' : Nonroot a := ⟨v, hvne⟩
  have hp : D.block (D.parentEnd v') = a := (D.parent_block v').unique hτ hvp
  have hf : ∀ S, D.block S = a →
      (attachmentFiber (h := h) hτ D.parentEnd S).card = if D.parentEnd v' = S then 1 else 0 := by
    intro S hS
    rw [card_attachmentFiber_root hτ hh D.block D.parentEnd D.parent_block hS]
    have heq : childBridges (τ := τ) D.parentEnd a S =
        if D.parentEnd v' = S then {v'} else ∅ := by
      ext c
      simp only [childBridges, mem_filter, mem_univ, true_and]
      have hciff : IsParent τ a a c ↔ c = v' := by
        rw [← mem_children, hv, mem_singleton]
        exact ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
      rw [hciff]
      by_cases he : D.parentEnd v' = S
      · simp only [ite_eq_left he, mem_singleton]
        exact ⟨fun hc => hc.1, fun hc => ⟨hc, hc ▸ he⟩⟩
      · simp only [ite_eq_right he, notMem_empty, iff_false, not_and]
        exact fun hc => hc ▸ he
    rw [heq]
    split_ifs <;> simp
  refine ⟨v', hvp, ?_⟩
  rw [← prod_mul_distrib]
  calc _ = ∏ S ∈ univ.filter (fun S => D.block S = a),
      if D.parentEnd v' = S then r S / δ S else 1 := by
        apply prod_congr rfl
        intro S hS
        rw [D.bridgeDegree_root hτ hh (mem_filter.1 hS).2, hf S (mem_filter.1 hS).2]
        split_ifs <;> simp [div_eq_mul_inv]
    _ = _ := by rw [prod_ite_eq, ite_eq_left (show D.parentEnd v' ∈ univ.filter (fun S => D.block S = a) from mem_filter.2 ⟨mem_univ _, hp⟩)]

/-- Multiplying (5.97), the low-degree bounds in (5.93), and the
root identity. The root marked ratio is retained until this last multiplication. -/
theorem compensate_all (hh : IsChildChoice τ a h) (ha : τ.degree a = 1)
    {r δ : V → ℝ} {R : Λ → ℝ} {W : ℝ} (hr : ∀ S, 0 ≤ r S)
    (hδ : ∀ S, 0 < δ S) (hrδ : ∀ S, r S ≤ δ S) (hR : ∀ u, 0 ≤ R u)
    (hrR : ∀ S, r S ≤ R (D.block S)) (m : V) (hm : D.block m = a)
    (hinside : ∀ S, D.block S = a → δ m ≤ W * δ S) :
    (∏ v : Nonroot a, r (D.childEnd v) * r (D.parentEnd v)) *
      (∏ l : Leaf τ a, R l) *
      (∏ S, (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) *
      (r m / δ m) ≤ W * (∏ u, R u ^ 2) / δ m ^ 2 := by
  let B : Λ → ℝ := fun u =>
    (∏ S ∈ univ.filter (fun S => D.block S = u), r S ^ D.bridgeDegree S) *
      (∏ S ∈ univ.filter (fun S => D.block S = u),
        (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card)
  let L : Λ → ℝ := fun u => if u = a then r m / δ m else if τ.degree u = 1 then R u else 1
  have hB0 : ∀ u, 0 ≤ B u := fun u => mul_nonneg
    (prod_nonneg fun S _ => pow_nonneg (hr _) _)
    (prod_nonneg fun S _ => pow_nonneg (one_div_pos.2 (hδ _)).le _)
  have hL0 : ∀ u, 0 ≤ L u := fun u => by
    dsimp [L]
    split_ifs
    · exact div_nonneg (hr _) (hδ _).le
    · exact hR _
    · exact zero_le_one
  have hnonroot : ∀ u, u ≠ a → B u * L u ≤ R u ^ 2 := by
    intro u hu
    dsimp only [L]
    rw [ite_eq_right hu]
    by_cases hl : τ.degree u = 1
    · rw [ite_eq_left hl]
      have := D.compensate_leaf hτ hh (δ := δ) hr hu hl
        (fun S hS => hS ▸ hrR S)
      dsimp only [B]
      convert this using 1
      ring
    · rw [ite_eq_right hl, mul_one]
      by_cases htwo : τ.degree u = 2
      · exact D.compensate_degree_two hτ hh (δ := δ) hr hu htwo (fun S hS => hS ▸ hrR S)
      · have hdeg : 2 < τ.degree u := by
          have hd := degree_eq (r := a) hτ u
          rw [ite_eq_right hu] at hd
          omega
        have hex : ∃ c, IsParent τ a u c := by
          have hd := degree_eq (r := a) hτ u
          rw [ite_eq_right hu] at hd
          have hpos : 0 < (children τ a u).card := by omega
          obtain ⟨c, hc⟩ := Finset.card_pos.1 hpos
          exact ⟨c, mem_children.1 hc⟩
        obtain ⟨c, hc⟩ := hex
        simpa only [one_mul, one_pow, mul_one] using
          D.compensate_nonroot hτ hh (C := 1) hr hδ hu (hh u c hc)
            (fun S hS => hS ▸ hrR S) (fun S _ => by simpa using hrδ S)
  have hroot : B a * L a ≤ (W / δ m ^ 2) * R a ^ 2 := by
    obtain ⟨v, hv, heq⟩ := D.compensate_root_eq hτ hh ha (r := r) (δ := δ)
    have hp := (D.parent_block v).unique hτ hv
    change B a * (if a = a then r m / δ m else _) ≤ _
    rw [ite_eq_left rfl]
    change (_ * _) * (r m / δ m) ≤ _
    rw [heq]
    have hcomp : 1 / δ (D.parentEnd v) ≤ W / δ m := by
      rw [div_le_div_iff₀ (hδ _) (hδ _), one_mul]
      exact hinside _ hp
    calc r (D.parentEnd v) / δ (D.parentEnd v) * (r m / δ m)
        = (r (D.parentEnd v) * r m) * (1 / δ (D.parentEnd v)) / δ m := by ring
      _ ≤ (R a * R a) * (W / δ m) / δ m := by
        apply div_le_div_of_nonneg_right _ (hδ _).le
        exact mul_le_mul
          (mul_le_mul (show r (D.parentEnd v) ≤ R a by simpa only [hp] using hrR (D.parentEnd v))
            (show r m ≤ R a by simpa only [hm] using hrR m) (hr _) (hR _)) hcomp
          (one_div_pos.2 (hδ _)).le (mul_nonneg (hR _) (hR _))
      _ = _ := by ring
  have hprod : (∏ u, B u * L u) ≤ (W / δ m ^ 2) * ∏ u, R u ^ 2 := by
    have heach : ∀ u, B u * L u ≤ (if u = a then W / δ m ^ 2 else 1) * R u ^ 2 := by
      intro u
      by_cases hu : u = a
      · subst hu
        simpa using hroot
      · simpa only [hu, ite_false, one_mul] using hnonroot u hu
    calc (∏ u, B u * L u) ≤ ∏ u, ((if u = a then W / δ m ^ 2 else 1) * R u ^ 2) :=
        prod_le_prod₀ (fun u _ => mul_nonneg (hB0 u) (hL0 u)) fun u _ => heach u
      _ = _ := by rw [prod_mul_distrib, prod_ite_eq', ite_eq_left (mem_univ a)]
  have hBprod : (∏ u, B u) = (∏ v : Nonroot a, r (D.childEnd v) * r (D.parentEnd v)) *
      ∏ S, (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card := by
    dsimp only [B]
    rw [prod_mul_distrib, Finset.prod_fiberwise, Finset.prod_fiberwise, D.prod_bridge_radii]
  have hLprod : (∏ u, L u) = (r m / δ m) * ∏ l : Leaf τ a, R l := by
    rw [← Finset.mul_prod_erase univ L (mem_univ a)]
    have heq : (∏ u ∈ univ.erase a, L u) = ∏ u ∈ (leaves τ).erase a, R u := by
      simp only [L]
      rw [Finset.prod_congr rfl (fun u hu => ite_eq_right (ne_of_mem_erase hu))]
      rw [← Finset.prod_filter]
      congr 1
      ext u
      simp [leaves]
    rw [heq, Finset.prod_coe_sort]
    simp only [L, ite_eq_left rfl]
  rw [prod_mul_distrib, hBprod, hLprod] at hprod
  convert hprod using 1 <;> ring

end BlockTree
end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
