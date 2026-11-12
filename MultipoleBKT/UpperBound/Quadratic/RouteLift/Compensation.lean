/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.RouteLift.Paths
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Radius compensation at individual bridge attachments

The paper: proof of Corollary 5.34,
Step 4, equations (5.94), (5.95), (5.96), (5.97),
and (5.98). The order is transport of the leaf denominators, separation of
the parent radius, separation of the heavy child radius, and compensation of the
remaining radius powers against the attachment denominators.
-/

@[expose] public section

open Finset SimpleGraph
open scoped Classical

namespace MultipoleBKT.UpperBound.Quadratic.RouteLift

open CoreForest

variable {Λ V : Type*} [Fintype Λ] [DecidableEq Λ]
  [Fintype V] [DecidableEq V] {τ : SimpleGraph Λ} [DecidableRel τ.Adj]
  {a : Λ} {T : SimpleGraph V} {h : Λ → Λ}

namespace BlockTree

variable (D : BlockTree τ a T) (hτ : τ.IsTree) (hT : T.IsTree)

omit [Fintype V] [DecidableEq V] in
private theorem compare_walk {δ : V → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hδ : ∀ x, 0 ≤ δ x) (hedge : ∀ x y, T.Adj x y → δ y ≤ K * δ x) :
    ∀ {x y : V} (w : T.Walk x y), δ y ≤ K ^ w.length * δ x
  | _, _, .nil => by simp
  | _, _, .cons hxy w => by
    rw [Walk.length_cons, pow_succ]
    calc δ _ ≤ K ^ w.length * δ _ := compare_walk hK hδ hedge w
      _ ≤ K ^ w.length * (K * δ _) :=
        mul_le_mul_of_nonneg_left (hedge _ _ hxy) (pow_nonneg hK _)
      _ = _ := by ring

/-- The degree of a part in the bridge graph counts the incidences of parent
bridges and child bridges separately. -/
noncomputable def bridgeDegree (S : V) : ℕ :=
  ((univ : Finset (Nonroot a)).filter fun c => D.childEnd c = S).card +
    (childBridges (τ := τ) D.parentEnd (D.block S) S).card

omit [Fintype V] [DecidableRel τ.Adj] in
/-- At a part of a nonroot block there is one parent incidence precisely when
it is the endpoint of the parent bridge. This is the pair of degree identities
preceding (5.95). -/
theorem parent_incidence {u : Λ} (hu : u ≠ a) {S : V} (hS : D.block S = u) :
    ((univ : Finset (Nonroot a)).filter fun c => D.childEnd c = S).card =
      if D.childEnd ⟨u, hu⟩ = S then 1 else 0 := by
  have hset : ((univ : Finset (Nonroot a)).filter fun c => D.childEnd c = S) =
      if D.childEnd ⟨u, hu⟩ = S then {⟨u, hu⟩} else ∅ := by
    by_cases hc : D.childEnd ⟨u, hu⟩ = S
    · rw [ite_eq_left hc]
      ext c
      rw [mem_filter, mem_singleton, and_iff_right (mem_univ _)]
      constructor
      · intro he
        apply Subtype.ext
        rw [← D.child_block c, he, hS]
      · rintro rfl
        exact hc
    · rw [ite_eq_right hc]
      apply eq_empty_iff_forall_notMem.2
      intro c hc'
      have hcS := (mem_filter.1 hc').2
      have hcu : c = ⟨u, hu⟩ := Subtype.ext (by rw [← D.child_block c, hcS, hS])
      exact hc (hcu ▸ hcS)
  rw [hset]
  split_ifs <;> simp

include hτ in
omit [Fintype V] in
/-- In a nonroot leaf block the unique bridge attachment has degree one,
and every other part has degree zero. -/
theorem bridgeDegree_leaf {u : Λ} (hu : u ≠ a) (hl : τ.degree u = 1)
    {S : V} (hS : D.block S = u) :
    D.bridgeDegree S = if D.childEnd ⟨u, hu⟩ = S then 1 else 0 := by
  have hn := (mem_leaves_iff_of_ne hτ hu).1 (mem_leaves.2 hl)
  have hemp : childBridges (τ := τ) D.parentEnd u S = ∅ :=
    eq_empty_iff_forall_notMem.2 fun c hc => hn c (mem_filter.1 hc).2.1
  rw [bridgeDegree, D.parent_incidence hu hS, hS, hemp, card_empty, add_zero]

include hτ in
omit [Fintype V] in
/-- The definition of `X*` in Step 2: exactly the degree-one parts of the
nonroot leaf blocks. This identifies the leaf indexing with the printed set. -/
theorem mem_xStar_degree (S : V) : S ∈ D.xStar ↔
    D.block S ∈ (leaves τ).erase a ∧ D.bridgeDegree S = 1 := by
  constructor
  · intro hS
    obtain ⟨l, hl, -⟩ := (D.mem_xStar_iff S).1 hS
    rw [← hl, D.block_start l]
    refine ⟨l.property, ?_⟩
    rw [D.bridgeDegree_leaf hτ (mem_erase.1 l.property).1
      (mem_leaves.1 (mem_erase.1 l.property).2) (D.block_start l)]
    exact ite_eq_left rfl
  · rintro ⟨hl, hd⟩
    have he := D.bridgeDegree_leaf hτ (mem_erase.1 hl).1
      (mem_leaves.1 (mem_erase.1 hl).2) (S := S) rfl
    rw [hd] at he
    have hstart : D.childEnd ⟨D.block S, (mem_erase.1 hl).1⟩ = S := by
      by_contra hn
      rw [ite_eq_right hn] at he
      omega
    exact mem_image.2 ⟨⟨D.block S, hl⟩, mem_univ _, hstart⟩

omit [Fintype V] in
/-- Counting actual starting parts in `X*` agrees with counting their uniquely
indexing leaves. Thus the fiber identities are attachment-level identities. -/
theorem card_locPartFiber (S : V) :
    ((univ : Finset D.xStar).filter fun S' => D.locPart (h := h) hτ S' = S).card =
      (attachmentFiber (h := h) hτ D.parentEnd S).card := by
  symm
  refine Finset.card_bij
    (fun l _ => (⟨D.start l, mem_image.2 ⟨l, mem_univ _, rfl⟩⟩ : D.xStar)) ?_ ?_ ?_
  · intro l hl
    exact mem_filter.2 ⟨mem_univ _, (D.locPart_start hτ l).trans (mem_filter.1 hl).2⟩
  · intro l _ l' _ he
    exact D.start_injective (congrArg Subtype.val he)
  · intro S' hS'
    obtain ⟨l, hl, -⟩ := (D.mem_xStar_iff S').1 S'.property
    have he : (⟨D.start l, mem_image.2 ⟨l, mem_univ _, rfl⟩⟩ : D.xStar) = S' :=
      Subtype.ext hl
    refine ⟨l, mem_filter.2 ⟨mem_univ _, ?_⟩, he⟩
    have hx := (mem_filter.1 hS').2
    rw [← he, D.locPart_start] at hx
    exact hx

include hT in
/-- Equation (5.94), literally indexed by the parts `S' ∈ X*` and their
actual attachment fibers, with the sharper total-length exponent. -/
theorem transport_xStar_denominators {δ : V → ℝ} {K : ℝ} (hK : 1 ≤ K)
    (hδ : ∀ S, 0 < δ S) (hedge : ∀ S S', T.Adj S S' → δ S' ≤ K * δ S) :
    (∏ S' : D.xStar, 1 / δ S') ≤ K ^ (Fintype.card V - 1) *
      ∏ S, (1 / δ S) ^
        ((univ : Finset D.xStar).filter fun S' => D.locPart (h := h) hτ S' = S).card := by
  have hlocal : ∀ S' : D.xStar, 1 / δ S' ≤
      K ^ T.dist S' (D.locPart (h := h) hτ S') * (1 / δ (D.locPart (h := h) hτ S')) := by
    intro S'
    obtain ⟨w, -, hw⟩ := hT.connected.exists_path_of_dist S' (D.locPart (h := h) hτ S')
    have hcmp := compare_walk (zero_le_one.trans hK) (fun S => (hδ S).le) hedge w
    rw [hw] at hcmp
    rw [mul_one_div, div_le_div_iff₀ (hδ _) (hδ _), one_mul]
    exact hcmp
  have hregroup : (∏ S' : D.xStar, 1 / δ (D.locPart (h := h) hτ S')) =
      ∏ S, (1 / δ S) ^ ((univ : Finset D.xStar).filter fun S' =>
        D.locPart (h := h) hτ S' = S).card := by
    rw [← Finset.prod_fiberwise (univ : Finset D.xStar) (D.locPart (h := h) hτ)]
    apply prod_congr rfl
    intro S _
    rw [← Finset.prod_const]
    apply prod_congr rfl
    intro S' hS'
    rw [(mem_filter.1 hS').2]
  calc (∏ S' : D.xStar, 1 / δ S') ≤ ∏ S' : D.xStar,
        K ^ T.dist S' (D.locPart (h := h) hτ S') * (1 / δ (D.locPart (h := h) hτ S')) :=
      prod_le_prod₀ (fun S' _ => (one_div_pos.2 (hδ S')).le) fun S' _ => hlocal S'
    _ = K ^ (∑ S' : D.xStar, T.dist S' (D.locPart (h := h) hτ S')) *
        ∏ S, (1 / δ S) ^ ((univ : Finset D.xStar).filter fun S' =>
          D.locPart (h := h) hτ S' = S).card := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, hregroup]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hK (D.total_xStar_length_le (h := h) hτ hT))
      (prod_nonneg fun S _ => pow_nonneg (one_div_pos.2 (hδ S)).le _)

omit [Fintype V] in
/-- (5.96) at the actual set `X*`: the heavy child removes one path
precisely at the part incident to that child bridge. -/
theorem card_locPartFiber_nonroot (hh : IsChildChoice τ a h)
    {u : Λ} (hu : u ≠ a) (huc : IsParent τ a u (h u)) {S : V} (hS : D.block S = u) :
    ((univ : Finset D.xStar).filter fun S' => D.locPart (h := h) hτ S' = S).card +
      (if D.parentEnd ⟨h u, fun he => not_isParent_root _ (he ▸ huc)⟩ = S then 1 else 0) =
        (childBridges (τ := τ) D.parentEnd u S).card := by
  rw [D.card_locPartFiber hτ]
  exact card_attachmentFiber_nonroot hτ hh D.block D.parentEnd D.parent_block hu huc hS

omit [Fintype V] in
/-- (5.98) at the actual set `X*`. -/
theorem card_locPartFiber_root (hh : IsChildChoice τ a h) {S : V} (hS : D.block S = a) :
    ((univ : Finset D.xStar).filter fun S' => D.locPart (h := h) hτ S' = S).card =
      (childBridges (τ := τ) D.parentEnd a S).card := by
  rw [D.card_locPartFiber hτ]
  exact card_attachmentFiber_root hτ hh D.block D.parentEnd D.parent_block hS

omit [DecidableRel τ.Adj] in
/-- (5.95), before replacing the parent endpoint radius by the maximal radius. -/
theorem prod_bridgeDegree_nonroot {M : Type*} [CommMonoid M]
    (r : V → M) {u : Λ} (hu : u ≠ a) :
    (∏ S ∈ univ.filter (fun S => D.block S = u), r S ^ D.bridgeDegree S) =
      r (D.childEnd ⟨u, hu⟩) *
        ∏ S ∈ univ.filter (fun S => D.block S = u),
          r S ^ (childBridges (τ := τ) D.parentEnd u S).card := by
  have hdeg : ∀ S ∈ univ.filter (fun S => D.block S = u),
      r S ^ D.bridgeDegree S =
        (if D.childEnd ⟨u, hu⟩ = S then r S else 1) *
          r S ^ (childBridges (τ := τ) D.parentEnd u S).card := by
    intro S hS
    have hb := (mem_filter.1 hS).2
    rw [bridgeDegree, D.parent_incidence hu hb, hb, pow_add]
    split_ifs <;> simp
  have hmem : D.childEnd ⟨u, hu⟩ ∈ univ.filter (fun S => D.block S = u) :=
    mem_filter.2 ⟨mem_univ _, D.child_block _⟩
  rw [prod_congr rfl hdeg, prod_mul_distrib, prod_ite_eq, ite_eq_left hmem]

/-- (5.96), before bounding the heavy-child endpoint radius by the block
maximum. The heavy and parent endpoints may coincide. -/
theorem prod_children_nonroot (hh : IsChildChoice τ a h) {M : Type*} [CommMonoid M]
    (r : V → M) {u : Λ} (hu : u ≠ a) (huc : IsParent τ a u (h u)) :
    (∏ S ∈ univ.filter (fun S => D.block S = u),
      r S ^ (childBridges (τ := τ) D.parentEnd u S).card) =
      r (D.parentEnd ⟨h u, fun he => not_isParent_root _ (he ▸ huc)⟩) *
        ∏ S ∈ univ.filter (fun S => D.block S = u),
          r S ^ (attachmentFiber (h := h) hτ D.parentEnd S).card := by
  let H : Nonroot a := ⟨h u, fun he => not_isParent_root _ (he ▸ huc)⟩
  have hdeg : ∀ S ∈ univ.filter (fun S => D.block S = u),
      r S ^ (childBridges (τ := τ) D.parentEnd u S).card =
        (if D.parentEnd H = S then r S else 1) *
          r S ^ (attachmentFiber (h := h) hτ D.parentEnd S).card := by
    intro S hS
    have hb := (mem_filter.1 hS).2
    rw [← card_attachmentFiber_nonroot hτ hh D.block D.parentEnd D.parent_block hu huc hb,
      pow_add, mul_comm]
    split_ifs <;> simp
  have hHS : D.block (D.parentEnd H) = u := (D.parent_block H).unique hτ huc
  have hmem : D.parentEnd H ∈ univ.filter (fun S => D.block S = u) :=
    mem_filter.2 ⟨mem_univ _, hHS⟩
  rw [prod_congr rfl hdeg, prod_mul_distrib, prod_ite_eq, ite_eq_left hmem]

/-- Nonroot compensation (5.97): separate the parent endpoint as in
(5.95), then the heavy-child endpoint as in (5.96), then use `r_S ≤ C δ_S`.
The explicit exponent is the total number of attachment fibers in this block. -/
theorem compensate_nonroot (hh : IsChildChoice τ a h) {r δ : V → ℝ} {R C : ℝ}
    (hr : ∀ S, 0 ≤ r S) (hδ : ∀ S, 0 < δ S)
    {u : Λ} (hu : u ≠ a) (huc : IsParent τ a u (h u))
    (hrR : ∀ S, D.block S = u → r S ≤ R)
    (hrδ : ∀ S, D.block S = u → r S ≤ C * δ S) :
    (∏ S ∈ univ.filter (fun S => D.block S = u), r S ^ D.bridgeDegree S) *
      (∏ S ∈ univ.filter (fun S => D.block S = u),
        (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) ≤
      R ^ 2 * C ^ (∑ S ∈ univ.filter (fun S => D.block S = u),
        (attachmentFiber (h := h) hτ D.parentEnd S).card) := by
  let H : Nonroot a := ⟨h u, fun he => not_isParent_root _ (he ▸ huc)⟩
  have hp : D.block (D.parentEnd H) = u := (D.parent_block H).unique hτ huc
  have hR0 : 0 ≤ R := (hr (D.childEnd ⟨u, hu⟩)).trans (hrR _ (D.child_block _))
  have hends : r (D.childEnd ⟨u, hu⟩) * r (D.parentEnd H) ≤ R ^ 2 := by
    rw [sq]
    exact mul_le_mul (hrR _ (D.child_block _)) (hrR _ hp) (hr _) hR0
  have hratio : ∀ S ∈ univ.filter (fun S => D.block S = u), 0 ≤ r S / δ S ∧ r S / δ S ≤ C := by
    intro S hS
    exact ⟨div_nonneg (hr S) (hδ S).le,
      (div_le_iff₀ (hδ S)).2 (hrδ S (mem_filter.1 hS).2)⟩
  rw [D.prod_bridgeDegree_nonroot r hu, D.prod_children_nonroot hτ hh r hu huc]
  calc r (D.childEnd ⟨u, hu⟩) * (r (D.parentEnd H) *
        ∏ S ∈ univ.filter (fun S => D.block S = u),
          r S ^ (attachmentFiber (h := h) hτ D.parentEnd S).card) *
        (∏ S ∈ univ.filter (fun S => D.block S = u),
          (1 / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card)
      = (r (D.childEnd ⟨u, hu⟩) * r (D.parentEnd H)) *
          ∏ S ∈ univ.filter (fun S => D.block S = u),
            (r S / δ S) ^ (attachmentFiber (h := h) hτ D.parentEnd S).card := by
              simp only [div_eq_mul_inv, mul_pow, prod_mul_distrib, one_mul]
              ring
    _ ≤ R ^ 2 * ∏ S ∈ univ.filter (fun S => D.block S = u),
        C ^ (attachmentFiber (h := h) hτ D.parentEnd S).card := by
      exact mul_le_mul hends
        (prod_le_prod₀ (fun S hS => pow_nonneg (hratio S hS).1 _) fun S hS =>
          pow_le_pow_left₀ (hratio S hS).1 (hratio S hS).2 _)
        (prod_nonneg fun S hS => pow_nonneg (hratio S hS).1 _) (sq_nonneg _)
    _ = _ := by rw [prod_pow_eq_pow_sum]

omit [Fintype V] in
/-- At the root there is no parent incidence, so the attachment fiber has
exactly the bridge degree. This is (5.98) at the part level. -/
theorem bridgeDegree_root (hh : IsChildChoice τ a h) {S : V} (hS : D.block S = a) :
    D.bridgeDegree S = (attachmentFiber (h := h) hτ D.parentEnd S).card := by
  have hempty : ((univ : Finset (Nonroot a)).filter fun c => D.childEnd c = S) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro c hc
    have he := (mem_filter.1 hc).2
    exact c.property (by rw [← D.child_block c, he, hS])
  rw [bridgeDegree, hempty, card_empty, zero_add, hS,
    card_attachmentFiber_root hτ hh D.block D.parentEnd D.parent_block hS]

end BlockTree

end MultipoleBKT.UpperBound.Quadratic.RouteLift

end
