/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Hypertree

/-!
# Theorem 1 from the gates: grouping cluster sums by the union of the polymers

Combinatorics of the hypertree evaluation in the proof of Theorem 1 (equation (5.167) and the exponent count after it).
Throughout, `V = (V_1, …, V_n)` is a family of finite subsets of `ℕ`.

* `IsRelabelInvariant F`: `F(f(V_1), …, f(V_n)) = F(V)` for every `f` injective on `⋃ᵢ Vᵢ`.
  The connection graph, the cardinalities and hence the cluster weights are relabel invariant
  (`connectionGraph_image`).
* `sum_union_eq_sum_union_range`: for relabel invariant `F`, the sum over the families with
  union `U` equals the sum over the families with union `{0, …, |U| - 1}`.
* `sum_piFinset_range_eq_sum_choose` (eq. (5.167)): `∑_{V ⊂ [N]} F(V) = ∑_k C(N, k) T(k)` with
  `T(k)` the sum over the families with union `{0, …, k - 1}`.
* `card_biUnion_add_le` (the exponent count): if `G(V)` is connected, then
  `|⋃ᵢ Vᵢ| + n ≤ ∑ᵢ |Vᵢ| + 1`, with equality exactly for hypertrees.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace TheoremOne

variable {n : ℕ}

/-- A function of families of subsets of `ℕ` that is invariant under relabeling of the points:
`F(f(V_1), …, f(V_n)) = F(V)` for every `f` injective on `⋃ᵢ Vᵢ`. -/
def IsRelabelInvariant (F : (Fin n → Finset ℕ) → ℝ) : Prop :=
  ∀ (V : Fin n → Finset ℕ) (f : ℕ → ℕ), Set.InjOn f ↑(univ.biUnion V) →
    F (fun i => (V i).image f) = F V

theorem injOn_union_of_injOn_biUnion {V : Fin n → Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f ↑(univ.biUnion V)) (i j : Fin n) : Set.InjOn f (↑(V i) ∪ ↑(V j)) := by
  refine hf.mono ?_
  intro a ha
  simp only [Set.mem_union, mem_coe] at ha
  simp only [coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, mem_coe]
  rcases ha with ha | ha
  · exact ⟨i, ha⟩
  · exact ⟨j, ha⟩

/-- The connection graph is invariant under a relabeling injective on the union. -/
theorem connectionGraph_image {V : Fin n → Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f ↑(univ.biUnion V)) :
    connectionGraph (fun i => (V i).image f) = connectionGraph V := by
  ext i j
  simp only [connectionGraph, SimpleGraph.fromRel_adj]
  rw [← image_inter_of_injOn _ _ (injOn_union_of_injOn_biUnion hf i j),
    ← image_inter_of_injOn _ _ (injOn_union_of_injOn_biUnion hf j i)]
  simp only [image_nonempty]

theorem card_image_of_injOn_biUnion {V : Fin n → Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f ↑(univ.biUnion V)) (i : Fin n) : ((V i).image f).card = (V i).card := by
  refine card_image_of_injOn (hf.mono ?_)
  intro a ha
  simp only [coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, mem_coe]
  exact ⟨i, ha⟩

/-- Relabeling a family whose union is `U` by maps `f : U → W`, `g : W → U` inverse to each
other. -/
theorem image_image_eq_self {s U : Finset ℕ} {f g : ℕ → ℕ} (hs : s ⊆ U)
    (hgf : ∀ a ∈ U, g (f a) = a) : (s.image f).image g = s := by
  rw [image_image]
  conv_rhs => rw [← image_id (s := s)]
  exact image_congr fun a ha => hgf a (hs ha)

/-- **Relabeling the union.** For a relabel invariant `F`, the sum of `F` over the families
`V_1, …, V_n ⊂ U` with `⋃ᵢ Vᵢ = U` depends only on `|U|`. -/
theorem sum_union_eq_sum_union_of_card_eq {F : (Fin n → Finset ℕ) → ℝ}
    (hF : IsRelabelInvariant F) {U W : Finset ℕ} (hUW : U.card = W.card) :
    ∑ V ∈ (Fintype.piFinset fun _ : Fin n => U.powerset).filter (fun V => univ.biUnion V = U),
        F V =
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => W.powerset).filter (fun V => univ.biUnion V = W),
        F V := by
  classical
  let e : U ≃ W := Finset.equivOfCardEq hUW
  let f : ℕ → ℕ := fun a => if ha : a ∈ U then (e ⟨a, ha⟩ : ℕ) else a
  let g : ℕ → ℕ := fun b => if hb : b ∈ W then (e.symm ⟨b, hb⟩ : ℕ) else b
  have hfU : ∀ a ∈ U, f a ∈ W := fun a ha => by simp only [f, ha, dite_true]; exact (e _).2
  have hgW : ∀ b ∈ W, g b ∈ U := fun b hb => by simp only [g, hb, dite_true]; exact (e.symm _).2
  have hgf : ∀ a ∈ U, g (f a) = a := fun a ha => by
    simp only [f, ha, dite_true, g, (e _).2, Subtype.coe_eta, Equiv.symm_apply_apply]
  have hfg : ∀ b ∈ W, f (g b) = b := fun b hb => by
    simp only [g, hb, dite_true, f, (e.symm _).2, Subtype.coe_eta, Equiv.apply_symm_apply]
  have hfinj : Set.InjOn f ↑U := fun a ha a' ha' h => by
    rw [← hgf a ha, ← hgf a' ha', h]
  have hginj : Set.InjOn g ↑W := fun b hb b' hb' h => by
    rw [← hfg b hb, ← hfg b' hb', h]
  have himU : U.image f = W := by
    ext b
    simp only [mem_image]
    exact ⟨fun ⟨a, ha, hab⟩ => hab ▸ hfU a ha, fun hb => ⟨g b, hgW b hb, hfg b hb⟩⟩
  have himW : W.image g = U := by
    ext a
    simp only [mem_image]
    exact ⟨fun ⟨b, hb, hba⟩ => hba ▸ hgW b hb, fun ha => ⟨f a, hfU a ha, hgf a ha⟩⟩
  have hsub : ∀ {X : Finset ℕ} {V : Fin n → Finset ℕ}, univ.biUnion V = X → ∀ i, V i ⊆ X :=
    fun {_} {V} hV i => hV ▸ subset_biUnion_of_mem V (mem_univ i)
  refine Finset.sum_nbij' (fun V i => (V i).image f) (fun V i => (V i).image g) ?_ ?_ ?_ ?_ ?_
  · intro V hV
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset] at hV ⊢
    refine ⟨fun i => ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      exact hfU a (hV.1 i ha)
    · rw [← Finset.biUnion_image, hV.2, himU]
  · intro V hV
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset] at hV ⊢
    refine ⟨fun i => ?_, ?_⟩
    · intro a ha
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact hgW b (hV.1 i hb)
    · rw [← Finset.biUnion_image, hV.2, himW]
  · intro V hV
    simp only [mem_filter] at hV
    funext i
    exact image_image_eq_self (hsub hV.2 i) hgf
  · intro V hV
    simp only [mem_filter] at hV
    funext i
    exact image_image_eq_self (hsub hV.2 i) hfg
  · intro V hV
    simp only [mem_filter] at hV
    refine (hF V f ?_).symm
    rw [hV.2]
    exact hfinj

/-- The sum over the families with union `U` equals the sum over the families with union
`{0, …, |U| - 1}`. -/
theorem sum_union_eq_sum_union_range {F : (Fin n → Finset ℕ) → ℝ} (hF : IsRelabelInvariant F)
    (U : Finset ℕ) :
    ∑ V ∈ (Fintype.piFinset fun _ : Fin n => U.powerset).filter (fun V => univ.biUnion V = U),
        F V =
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (range U.card).powerset).filter
          (fun V => univ.biUnion V = range U.card), F V :=
  sum_union_eq_sum_union_of_card_eq hF (card_range _).symm

/-- **Grouping by the union** (eq. (5.167)): for a relabel invariant `F`,
`∑_{V_1, …, V_n ⊂ [N]} F(V) = ∑_{k ≤ N} C(N, k) ∑_{V : ⋃ᵢ Vᵢ = [k]} F(V)`. -/
theorem sum_piFinset_range_eq_sum_choose {F : (Fin n → Finset ℕ) → ℝ}
    (hF : IsRelabelInvariant F) (N : ℕ) :
    ∑ V ∈ Fintype.piFinset (fun _ : Fin n => (range N).powerset), F V =
      ∑ k ∈ range (N + 1), (N.choose k : ℝ) *
        ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (range k).powerset).filter
            (fun V => univ.biUnion V = range k), F V := by
  classical
  have hmaps : ∀ V ∈ Fintype.piFinset (fun _ : Fin n => (range N).powerset),
      univ.biUnion V ∈ (range N).powerset := by
    intro V hV
    rw [Fintype.mem_piFinset] at hV
    rw [mem_powerset]
    exact biUnion_subset.mpr fun i _ => mem_powerset.mp (hV i)
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ U ∈ (range N).powerset,
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (range N).powerset).filter
          (fun V => univ.biUnion V = U), F V =
        ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (range U.card).powerset).filter
          (fun V => univ.biUnion V = range U.card), F V := by
    intro U hU
    rw [← sum_union_eq_sum_union_range hF U]
    refine sum_congr ?_ fun _ _ => rfl
    ext V
    simp only [mem_filter, Fintype.mem_piFinset, mem_powerset]
    refine ⟨fun h => ⟨fun i => h.2 ▸ subset_biUnion_of_mem V (mem_univ i), h.2⟩,
      fun h => ⟨fun i => (h.1 i).trans (mem_powerset.mp hU), h.2⟩⟩
  rw [sum_congr rfl hfib]
  rw [sum_powerset_apply_card (fun k => ∑ V ∈ (Fintype.piFinset fun _ : Fin n =>
      (range k).powerset).filter (fun V => univ.biUnion V = range k), F V), card_range]
  simp only [nsmul_eq_mul]

/-- **The exponent count**: if the connection graph of `V_1, …, V_n` is
connected, then `|⋃ᵢ Vᵢ| + n ≤ ∑ᵢ |Vᵢ| + 1`. -/
theorem card_biUnion_add_le {α : Type*} [DecidableEq α] {V : Fin n → Finset α}
    (hV : (connectionGraph V).Connected) :
    (univ.biUnion V).card + n ≤ ∑ i, (V i).card + 1 := by
  classical
  have hne : ∀ a ∈ univ.biUnion V, (incidence V a).Nonempty := fun a ha => incidence_nonempty ha
  have hconn : (SimpleGraph.fromRel fun x y =>
      ∃ a ∈ univ.biUnion V, x ∈ incidence V a ∧ y ∈ incidence V a).Connected := by
    refine hV.mono fun i j hij => ?_
    obtain ⟨hne', a, hai, haj⟩ := connectionGraph_adj.mp hij
    exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne', Or.inl ⟨a, mem_biUnion.mpr ⟨i, mem_univ _, hai⟩,
      mem_incidence.mpr hai, mem_incidence.mpr haj⟩⟩
  have h := card_le_sum_card_sub_one (univ.biUnion V) (incidence V) hne hconn
  rw [Fintype.card_fin, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, ← Nat.cast_sum,
    sum_card_incidence] at h
  omega

end TheoremOne

end MultipoleBKT

end
