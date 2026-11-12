/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Majorant
public import MultipoleBKT.LowerBound.Peeling.Quadratic
public import MultipoleBKT.LowerBound.Peeling.Dipole
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteReattach.Exchange

/-!
# Eulerian reattachment sums for one group

Lemma 4.55, with block radii from Definition 4.42, the weights (4.95), and
the display defining `ḡ` immediately before (4.95).

`eulerGroupSum_reattach` applies the summed quadratic estimate to the selected
minimal skeleton. It sums the pseudoforest with its exceptional edge removed
and the unused edges. `eulerGroupSum_route_le` exchanges the original and
reattached tree sums and applies the determinant forest count (4.71).
The resulting logarithmic product measures the predecessor multiplicities.


-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity Peeling

/-! ### Block radii -/

section Radii

variable (c : ℕ → ℂ × ℂ)

/-- The block radius `r_S = max_{i ∈ S} r_i` (Definition 4.42) at the
configuration `c`, with `r_i = |x_i - y_i|` (the maximum over the empty set of these nonnegative
numbers being `0`). -/
noncomputable def blockRad (S : Finset ℕ) : ℝ :=
  ((S.sup fun i => ‖(c i).1 - (c i).2‖₊ : NNReal) : ℝ)

/-- `∏_{S ∈ Y, S ≠ Ŝ} r_S²` for a block `Ŝ` of `Y` of maximal radius (display (4.94), (4.95)): the minimum over `S ∈ Y` of `∏_{S' ∈ Y, S' ≠ S} r_{S'}²`, attained at
the blocks of maximal radius (`prodExceptMax_eq`); the empty product `1` for `Y = ∅`. -/
noncomputable def prodExceptMax (Y : Finset (Finset ℕ)) : ℝ :=
  if h : Y.Nonempty then Y.inf' h (fun S => ∏ S' ∈ Y.erase S, blockRad c S' ^ 2) else 1

variable {c}

theorem blockRad_nonneg (S : Finset ℕ) : 0 ≤ blockRad c S := NNReal.coe_nonneg _

theorem le_blockRad {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) : ‖(c i).1 - (c i).2‖ ≤ blockRad c S := by
  unfold blockRad
  have := le_sup (f := fun i => ‖(c i).1 - (c i).2‖₊) hi
  exact_mod_cast this

theorem exists_blockRad_eq {S : Finset ℕ} (hS : S.Nonempty) :
    ∃ i ∈ S, blockRad c S = ‖(c i).1 - (c i).2‖ := by
  obtain ⟨i, hi, h⟩ := exists_mem_eq_sup S hS fun i => ‖(c i).1 - (c i).2‖₊
  exact ⟨i, hi, by rw [blockRad, h, coe_nnnorm]⟩

/-- `∏_{S ∈ Y, S ≠ Ŝ} r_S²` for any block `Ŝ` of maximal radius. -/
theorem prodExceptMax_eq {Y : Finset (Finset ℕ)} {S₀ : Finset ℕ} (hS₀ : S₀ ∈ Y)
    (hmax : ∀ S ∈ Y, blockRad c S ≤ blockRad c S₀) :
    prodExceptMax c Y = ∏ S' ∈ Y.erase S₀, blockRad c S' ^ 2 := by
  classical
  rw [prodExceptMax, dite_eq_left ⟨S₀, hS₀⟩]
  refine le_antisymm (inf'_le _ hS₀) (le_inf' _ _ fun S hS => ?_)
  by_cases hSS : S = S₀
  · rw [hSS]
  have hS' : S ∈ Y.erase S₀ := mem_erase.2 ⟨hSS, hS⟩
  have hS₀' : S₀ ∈ Y.erase S := mem_erase.2 ⟨fun h => hSS h.symm, hS₀⟩
  rw [← mul_prod_erase _ _ hS', ← mul_prod_erase _ _ hS₀', erase_right_comm]
  refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun _ _ => sq_nonneg _)
  exact pow_le_pow_left₀ (blockRad_nonneg S) (hmax S hS) 2

theorem prodExceptMax_nonneg (Y : Finset (Finset ℕ)) : 0 ≤ prodExceptMax c Y := by
  rw [prodExceptMax]
  split_ifs with h
  · obtain ⟨S, hS, heq⟩ := exists_mem_eq_inf' h fun S => ∏ S' ∈ Y.erase S, blockRad c S' ^ 2
    rw [heq]
    exact prod_nonneg fun _ _ => sq_nonneg _
  · exact zero_le_one

end Radii

/-! ### The weights `ḡ` and the kept weight -/

section Weights

open scoped Classical

variable (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ)

/-- `ḡ_ij = 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R̄} max(r_i, r_j)² / max(d_ij, r_i, r_j, λ)²` (display (gbar),
Section 4.16), at the configuration `c`, with `R` in the role of `R̄_{β,λ}`. -/
noncomputable def gbar (i j : ℕ) : ℝ :=
  (if MultipoleLinked M lam (c i) (c j) then 0 else 1) *
    (if dipoleDist (c i) (c j) ≤ 17 * ε₀ * R then 1 else 0) *
    (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ^ 2 /
      max (max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖)) lam ^ 2)

/-- The weight `d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c}` of the tree edges in (4.94)–(4.96). -/
noncomputable def keptPair (p : ℕ × ℕ) : ℝ :=
  (if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1) *
    (if dipoleDist (c p.1) (c p.2) ≤ 17 * ε₀ * R then 1 else 0) / dipoleDist (c p.1) (c p.2) ^ 2

variable {M lam ε₀ R c}

theorem gbar_comm (i j : ℕ) : gbar M lam ε₀ R c i j = gbar M lam ε₀ R c j i := by
  unfold gbar
  rw [dipoleDist_comm (c j) (c i), max_comm ‖(c j).1 - (c j).2‖,
    if_congr (multipoleLinked_comm (d := c j) (e := c i)) rfl rfl]

theorem gbar_nonneg (i j : ℕ) : 0 ≤ gbar M lam ε₀ R c i j := by
  unfold gbar
  refine mul_nonneg (mul_nonneg ?_ ?_) (div_nonneg (sq_nonneg _) (sq_nonneg _))
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

theorem keptPair_nonneg (p : ℕ × ℕ) : 0 ≤ keptPair M lam ε₀ R c p := by
  unfold keptPair
  refine div_nonneg (mul_nonneg ?_ ?_) (sq_nonneg _)
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

end Weights

/-! ### Graphs on `V_Y` and their pairs -/

section Graph

variable {Y : Finset (Finset ℕ)}

theorem sym2_mk_inf_sup {V : Type*} [LinearOrder V] (e : Sym2 V) : s(e.inf, e.sup) = e := by
  induction e using Sym2.ind with
  | h a b =>
    rcases le_total a b with h | h
    · simp [inf_of_le_left h, sup_of_le_right h]
    · simp [inf_of_le_right h, sup_of_le_left h, Sym2.eq_swap]

/-- Products over the pairs of a graph, with a weight on unordered pairs agreeing with the
weight on pairs of labels. -/
theorem prod_edgesOf_eq_of {M : Type*} [CommMonoid M] (G : SimpleGraph (Y.biUnion id))
    [Fintype G.edgeSet] (f : Sym2 (Y.biUnion id) → M) (w : ℕ × ℕ → M)
    (hfw : ∀ i j : Y.biUnion id, f s(i, j) = w ((i : ℕ), (j : ℕ))) :
    ∏ p ∈ edgesOf G, w p = ∏ e ∈ G.edgeFinset, f e := by
  rw [prod_edgesOf]
  refine prod_congr rfl fun e _ => ?_
  rw [← hfw, sym2_mk_inf_sup]

theorem edgesOf_mono {U : Finset ℕ} {G G' : SimpleGraph U} (h : G ≤ G') :
    edgesOf G ⊆ edgesOf G' := fun p hp => by
  obtain ⟨h1, h2, h12, hadj⟩ := mem_edgesOf.1 hp
  exact mem_edgesOf.2 ⟨h1, h2, h12, h hadj⟩

/-- `ℰ^inter(Y)` contains the pairs of the graphs below `ℰ^inter(Y)`. -/
theorem relTrees_eq_empty_of_card_le_one (hY : IsSubpartition Y) (h : Y.card ≤ 1) :
    relTrees Y = ∅ := by
  classical
  rw [eq_empty_iff_forall_notMem]
  intro T hT
  have := (isRelConnected_iff_mem hY).1 (mem_relTrees.1 hT).1
  rw [relEdgeSets_eq_empty_of_card_le_one h] at this
  exact notMem_empty _ this

theorem relTreePairs_eq_empty_of_card_le_one (hY : IsSubpartition Y) (h : Y.card ≤ 1) :
    relTreePairs Y = ∅ := by
  rw [relTreePairs, relTrees_eq_empty_of_card_le_one hY h, image_empty]

/-- The graph-world block radius is `blockRad`. -/
theorem blockRadius_eq_blockRad (hY : IsSubpartition Y) (c : ℕ → ℂ × ℂ) (S : Y) :
    blockRadius hY (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) S = blockRad c S := by
  classical
  refine le_antisymm (sup'_le _ _ fun i hi => le_blockRad ?_) ?_
  · rw [mem_filter] at hi
    exact (blockOf_eq_iff hY).1 hi.2
  · obtain ⟨j, hj, heq⟩ := exists_blockRad_eq (c := c) (hY.1 S S.2)
    rw [heq]
    have hjV : j ∈ Y.biUnion id := subset_biUnion_of_mem S.2 hj
    refine le_sup'_of_le _ (b := ⟨j, hjV⟩) ?_ le_rfl
    exact mem_filter.2 ⟨mem_univ _, (blockOf_eq_iff hY).2 hj⟩

/-- The product of Corollary 4.47 over the blocks other than that of a vertex of maximal radius is
`prodExceptMax`. -/
theorem prod_blockRadius_erase_eq (hY : IsSubpartition Y) (c : ℕ → ℂ × ℂ)
    {v : Y.biUnion id} (hv : ∀ i : Y.biUnion id, ‖(c i).1 - (c i).2‖ ≤ ‖(c v).1 - (c v).2‖) :
    ∏ S ∈ (univ : Finset Y).erase (blockOf hY v),
        blockRadius hY (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) S ^ 2 =
      prodExceptMax c Y := by
  classical
  set S₀ := blockOf hY v
  have hmax : ∀ S ∈ Y, blockRad c S ≤ blockRad c S₀ := by
    intro S hS
    obtain ⟨j, hj, heq⟩ := exists_blockRad_eq (c := c) (hY.1 S hS)
    rw [heq]
    have hjV : j ∈ Y.biUnion id := subset_biUnion_of_mem hS hj
    exact (hv ⟨j, hjV⟩).trans (le_blockRad (mem_blockOf hY v))
  rw [prodExceptMax_eq S₀.2 hmax]
  simp_rw [blockRadius_eq_blockRad hY c]
  have hmap : ((univ : Finset Y).erase S₀).map (Function.Embedding.subtype (· ∈ Y)) =
      Y.erase S₀ := by
    ext S
    simp only [mem_map, mem_erase, mem_univ, and_true, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨S', hS', rfl⟩
      exact ⟨fun h => hS' (Subtype.ext h), S'.2⟩
    · rintro ⟨hne, hS⟩
      exact ⟨⟨S, hS⟩, fun h => hne (congrArg Subtype.val h), rfl⟩
  rw [← hmap, prod_map]
  rfl

/-- Sums over the other vertices of `V_Y` as a subtype. -/
theorem sum_erase_coe (U : Finset ℕ) (f : ℕ → ℝ) (i : U) :
    ∑ j ∈ (univ : Finset U).erase i, f j = ∑ j ∈ U.erase i, f j := by
  classical
  have hmap : ((univ : Finset U).erase i).map (Function.Embedding.subtype (· ∈ U)) =
      U.erase i := by
    ext j
    simp only [mem_map, mem_erase, mem_univ, and_true, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨j', hj', rfl⟩
      exact ⟨fun h => hj' (Subtype.ext h), j'.2⟩
    · rintro ⟨hne, hj⟩
      exact ⟨⟨j, hj⟩, fun h => hne (congrArg Subtype.val h), rfl⟩
  rw [← hmap, sum_map]
  rfl

theorem one_add_mul_self_le_four_pow (n : ℕ) : 1 + n * n ≤ 4 ^ n := by
  have h := Nat.lt_two_pow_self (n := n)
  have : n * n < 4 ^ n := by
    calc n * n < 2 ^ n * 2 ^ n := Nat.mul_lt_mul'' h h
      _ = 4 ^ n := by rw [← mul_pow]; norm_num
  omega

end Graph

/-! ### Peeling fibers and (4.103) -/

section PerGroup

open scoped Classical

variable {M lam ε₀ R C₁ : ℝ}

/-- `g_ij ≤ ḡ_ij` away from the longest edge `e₀` (the blue sentence of the proof of Lemma 4.55: on `𝓑_ij^c`, `d_ij > M λ ≥ λ`). -/
theorem peelWeight_le_gbar (hM : 1 ≤ M) (hlam : 0 < lam) {Y : Finset (Finset ℕ)}
    (c : ℕ → ℂ × ℂ) (R' : ℝ) {e₀ e : Sym2 (Y.biUnion id)} (he : e ≠ e₀) :
    peelWeight (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖)
        (dipoleDistOn fun i : Y.biUnion id => c i)
        (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) R' e₀ e ≤
      Sym2.lift ⟨fun i j : Y.biUnion id => gbar M lam ε₀ R c i j, fun i j => gbar_comm i j⟩ e := by
  induction e using Sym2.ind with
  | h i j =>
    have hd' : dipoleDistOn (fun i : Y.biUnion id => c i) s(i, j) = dipoleDist (c i) (c j) := rfl
    have hr' : radMax (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) s(i, j) =
        max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ := rfl
    have hcc' : absIndicator M lam ε₀ R (fun i : Y.biUnion id => c i) s(i, j) =
        (if MultipoleLinked M lam (c i) (c j) then 0 else 1) *
          (if dipoleDist (c i) (c j) ≤ 17 * ε₀ * R then 1 else 0) := rfl
    have hg' : (Sym2.lift ⟨fun i j : Y.biUnion id => gbar M lam ε₀ R c i j,
        fun i j => gbar_comm i j⟩) s(i, j) = gbar M lam ε₀ R c i j := rfl
    rw [hg', peelWeight, hcc', hd', hr', gbar,
      ite_eq_right (show ¬ (s(i, j) = e₀ ∧ R' ≤ dipoleDist (c i) (c j)) from fun h => he h.1)]
    by_cases hl : MultipoleLinked M lam (c i) (c j)
    · rw [ite_eq_left hl, zero_mul, zero_mul, zero_mul]
    by_cases hd : dipoleDist (c i) (c j) ≤ 17 * ε₀ * R
    swap
    · rw [ite_eq_right hd]
      simp
    rw [ite_eq_right hl, ite_eq_left hd, mul_one, one_mul, one_mul]
    set D := dipoleDist (c i) (c j)
    set m := max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖
    have hDlt : M * min (max ‖(c i).1 - (c i).2‖ lam) (max ‖(c j).1 - (c j).2‖ lam) < D :=
      not_le.1 hl
    have hmin0 : lam ≤ min (max ‖(c i).1 - (c i).2‖ lam) (max ‖(c j).1 - (c j).2‖ lam) :=
      le_min (le_max_right _ _) (le_max_right _ _)
    have hlamD : lam < D := by
      have := le_mul_of_one_le_left (hlam.le.trans hmin0) hM
      linarith
    split_ifs with hDm
    · have hmpos : 0 < m := (hlam.trans hlamD).trans hDm
      rw [max_eq_right hDm.le, max_eq_left (hlamD.trans hDm).le, div_self (pow_pos hmpos 2).ne']
    · have hmD : m ≤ D := not_lt.1 hDm
      rw [max_eq_left hmD, max_eq_left hlamD.le]

theorem edgeFinset_deleteEdges_singleton {V : Type*} [DecidableEq V] (F : SimpleGraph V)
    (e₀ : Sym2 V) [Fintype F.edgeSet] [Fintype (F.deleteEdges {e₀}).edgeSet] :
    (F.deleteEdges {e₀}).edgeFinset = F.edgeFinset.erase e₀ := by
  ext e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
    Set.mem_singleton_iff, mem_erase]
  tauto

/-- Removing the longest edge: `∏_{ij ∈ 𝓕} g_ij ≤ ∏_{ij ∈ 𝓕 ∖ {e₀}} ḡ_ij`. -/
theorem prod_peelWeight_le_prod_gbar (hM : 1 ≤ M) (hlam : 0 < lam) {Y : Finset (Finset ℕ)}
    (c : ℕ → ℂ × ℂ) {R' : ℝ} (hR' : 0 ≤ R') (F : SimpleGraph (Y.biUnion id))
    (e₀ : Sym2 (Y.biUnion id)) :
    ∏ e ∈ F.edgeFinset, peelWeight (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖)
        (dipoleDistOn fun i : Y.biUnion id => c i)
        (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) R' e₀ e ≤
      ∏ e ∈ F.edgeFinset.erase e₀,
        Sym2.lift ⟨fun i j : Y.biUnion id => gbar M lam ε₀ R c i j, fun i j => gbar_comm i j⟩ e := by
  set pw := peelWeight (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖)
    (dipoleDistOn fun i : Y.biUnion id => c i)
    (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) R' e₀
  have hpw0 : ∀ e, 0 ≤ pw e := fun e =>
    peelWeight_nonneg (absIndicator_nonneg M lam ε₀ R _) e₀ e
  have hpw1 : pw e₀ ≤ 1 := peelWeight_le_one (fun _ => norm_nonneg _)
    (absIndicator_le_one M lam ε₀ R _) hR' e₀ e₀
  have hle : ∏ e ∈ F.edgeFinset.erase e₀, pw e ≤ ∏ e ∈ F.edgeFinset.erase e₀,
      Sym2.lift ⟨fun i j : Y.biUnion id => gbar M lam ε₀ R c i j, fun i j => gbar_comm i j⟩ e :=
    prod_le_prod₀ (fun e _ => hpw0 e) fun e he =>
      peelWeight_le_gbar hM hlam c R' (ne_of_mem_erase he)
  by_cases h₀ : e₀ ∈ F.edgeFinset
  · rw [← mul_prod_erase _ _ h₀]
    exact (mul_le_of_le_one_left (prod_nonneg fun e _ => hpw0 e) hpw1).trans hle
  · rw [erase_eq_of_notMem h₀] at hle ⊢
    exact hle

/-- A graph is recovered from its deletion of `e₀` and the record of whether it contained `e₀`. -/
theorem eq_deleteEdges_sup_record {V : Type*} (F : SimpleGraph V) (e₀ : Sym2 V) :
    F = F.deleteEdges {e₀} ⊔ SimpleGraph.fromEdgeSet
      {e | (if e₀ ∈ F.edgeSet then some e₀ else none) = some e} := by
  ext u v
  simp only [SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
    Set.mem_ofPred_eq, Set.mem_singleton_iff]
  split_ifs with h
  · constructor
    · intro huv
      by_cases hs : s(u, v) = e₀
      · exact Or.inr ⟨by rw [hs], huv.ne⟩
      · exact Or.inl ⟨huv, hs⟩
    · rintro (⟨huv, -⟩ | ⟨hs, -⟩)
      · exact huv
      · rw [Option.some_inj] at hs
        rw [← SimpleGraph.mem_edgeSet, ← hs]
        exact h
  · constructor
    · intro huv
      exact Or.inl ⟨huv, fun hs => h (hs ▸ huv)⟩
    · rintro (⟨huv, -⟩ | ⟨hs, -⟩)
      · exact huv
      · exact hs.elim

theorem sum_product_mul {α γ : Type*} (s : Finset α) (t : Finset γ) (f : α → ℝ) (g : γ → ℝ) :
    ∑ q ∈ s ×ˢ t, f q.1 * g q.2 = (∑ a ∈ s, f a) * ∑ b ∈ t, g b := by
  rw [sum_product, sum_mul_sum]

theorem sum_product4 {α β γ δ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ)
    (D : Finset δ) (f₁ : α → ℝ) (f₂ : β → ℝ) (f₃ : γ → ℝ) (f₄ : δ → ℝ) :
    ∑ q ∈ A ×ˢ (B ×ˢ (C ×ˢ D)), f₁ q.1 * (f₂ q.2.1 * (f₃ q.2.2.1 * f₄ q.2.2.2)) =
      (∑ a ∈ A, f₁ a) * ((∑ b ∈ B, f₂ b) * ((∑ x ∈ C, f₃ x) * ∑ y ∈ D, f₄ y)) := by
  rw [sum_product_mul A (B ×ˢ (C ×ˢ D)) f₁ fun q => f₂ q.1 * (f₃ q.2.1 * f₄ q.2.2),
    sum_product_mul B (C ×ˢ D) f₂ fun q => f₃ q.1 * f₄ q.2, sum_product_mul C D f₃ f₄]

/-- Internal summation of the peeling fibers. The tree weight is supplied by the
quadratic estimate, either in its single-tree or its summed form. -/
private theorem eulerGroupSum_bound_of_peeling (hC₁ : 1 ≤ C₁) (hM : 1 ≤ M)
    (hlam : 0 < lam) {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    (c : ℕ → ℂ × ℂ) (κ : ℝ) (hκ : 0 ≤ κ) (B : Finset (ℕ × ℕ) → ℝ)
    (hB : ∀ T, 0 ≤ B T)
    (hquad : ∀ (E : SimpleGraph (Y.biUnion id)) (v : Y.biUnion id)
      (e₀ : Sym2 (Y.biUnion id)) (Qs), E ≤ interEdges Y →
      IsPeeling hY E (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖)
        (dipoleDistOn fun i : Y.biUnion id => c i) v e₀ Qs →
      (∏ e ∈ E.edgeFinset,
        absWeight (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) (dipoleDistOn fun i : Y.biUnion id => c i)
          (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e) ≤
        κ ^ (Y.biUnion id).card * prodExceptMax c Y * B (edgesOf (keptGraph E Qs)) *
          ∏ e ∈ (removedGraph Qs).edgeFinset,
            peelWeight (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) (dipoleDistOn fun i : Y.biUnion id => c i)
              (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) ‖(c v).1 - (c v).2‖ e₀ e) :
    eulerGroupSum C₁ (fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2)) Y ≤
      (4 * C₁ ^ 2 * κ) ^ (Y.biUnion id).card * prodExceptMax c Y *
        (∑ T ∈ relTreePairs Y, B T) *
        (∏ p ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2))) *
        ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
  set V := Y.biUnion id with hV
  set n := V.card with hn
  set z : V → ℂ × ℂ := fun i => c i with hz
  set r : V → ℝ := fun i => ‖(c i).1 - (c i).2‖ with hr_def
  set d : Sym2 V → ℝ := dipoleDistOn z with hd_def
  set cc : Sym2 V → ℝ := absIndicator M lam ε₀ R z with hcc_def
  set g : Sym2 V → ℝ :=
    Sym2.lift ⟨fun i j : V => gbar M lam ε₀ R c i j, fun i j => gbar_comm i j⟩ with hg_def
  set a : ℕ × ℕ → ℝ := fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2) with ha_def
  set P := prodExceptMax c Y with hP_def
  have hr : ∀ v, 0 ≤ r v := fun v => norm_nonneg _
  have hd : ∀ e, 0 ≤ d e := dipoleDistOn_nonneg z
  have hcc : ∀ e, 0 ≤ cc e := absIndicator_nonneg M lam ε₀ R z
  have hcc1 : ∀ e, cc e ≤ 1 := absIndicator_le_one M lam ε₀ R z
  have hg0 : ∀ e, 0 ≤ g e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact gbar_nonneg _ _
  have ha0 : ∀ p, 0 ≤ a p := fun p => absOddWeight_nonneg _ _ _ _ _ _
  have hC0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  have hP0 : 0 ≤ P := prodExceptMax_nonneg Y
  have hS₁ : 0 ≤ ∑ T ∈ relTreePairs Y, B T :=
    sum_nonneg fun T _ => hB T
  have hG0 : 0 ≤ ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) :=
    prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)
  have hQ0 : 0 ≤ ∏ p ∈ interPairs Y, Real.exp (C₁ * a p) :=
    prod_nonneg fun _ _ => (Real.exp_pos _).le
  by_cases hVne : Nonempty V
  swap
  · have hempty : relEulerianConnectedPairs Y = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro E hE
      have hE' := mem_relEdgeSets.1 (mem_relEulerianConnectedPairs.1 hE).1
      obtain ⟨p, hp⟩ := hE'.2.1
      exact hVne ⟨⟨p.1, (mem_pairsOn.1 (interPairs_subset_pairsOn (hE'.1 hp))).1⟩⟩
    rw [eulerGroupSum, hempty, sum_empty]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hP0) hS₁) hQ0) hG0
  -- a peeling of each edge set
  have hex : ∀ E, ∀ hE : E ∈ relEulerianConnectedPairs Y,
      ∃ E' v₁ e₀ Qs,
        E' = peeledSkeleton (graphOf V E)
          (Parity.lemma_4_37 hY (isRelEulerianConnected_graphOf hY hE)) ∧
        IsEulerPeeling hY (graphOf V E) E' r d v₁ e₀ Qs :=
    fun E hE => by
      have htwo := Parity.lemma_4_37 hY (isRelEulerianConnected_graphOf hY hE)
      have hs := peeledSkeleton_spec (graphOf V E) htwo
      obtain ⟨v, e, Qs, hQs⟩ := exists_isPeeling (hX := hY)
        (hs.isRelMinTwoEdgeConnected hY) r d
      exact ⟨peeledSkeleton (graphOf V E) htwo, v, e, Qs, rfl, hs, hQs⟩
  have hV0 : Nonempty V := hVne
  have : Nonempty (Sym2 V) := ⟨s(Classical.arbitrary V, Classical.arbitrary V)⟩
  choose! E' v₁ e₀ Qs hselected using hex
  have hP := fun E hE => (hselected E hE).2
  have hEsub : ∀ E ∈ relEulerianConnectedPairs Y, E ⊆ interPairs Y := fun E hE =>
    subset_interPairs_of_mem_relEulerianConnectedPairs hE
  have hEpairs : ∀ E ∈ relEulerianConnectedPairs Y, E ⊆ pairsOn V := fun E hE =>
    (hEsub E hE).trans interPairs_subset_pairsOn
  have hGle : ∀ E ∈ relEulerianConnectedPairs Y, graphOf V E ≤ interEdges Y := fun E hE =>
    (le_interEdges_iff_edgesOf_subset hY).2 (by rw [edgesOf_graphOf (hEpairs E hE)]; exact hEsub E hE)
  have hstr := fun E hE => (hP E hE).structure (hGle E hE)
  have hsubE' : ∀ E ∈ relEulerianConnectedPairs Y, edgesOf (E' E) ⊆ E := fun E hE => by
    have := edgesOf_mono (hstr E hE).2.2.1
    rwa [edgesOf_graphOf (hEpairs E hE)] at this
  -- the injection
  set Φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) × SimpleGraph V × Option (Sym2 V) × Finset (ℕ × ℕ) :=
    fun E => (edgesOf (keptGraph (E' E) (Qs E)), (removedGraph (Qs E)).deleteEdges {e₀ E},
      if e₀ E ∈ (removedGraph (Qs E)).edgeSet then some (e₀ E) else none,
      E \ edgesOf (E' E)) with hΦ
  set W := relTreePairs Y ×ˢ ((pseudoforests : Finset (SimpleGraph V)) ×ˢ
    ((univ : Finset (Option (Sym2 V))) ×ˢ (interPairs Y).powerset)) with hW
  set f₁ : Finset (ℕ × ℕ) → ℝ :=
    fun T => C₁ ^ (2 * n) * κ ^ n * P * B T with hf₁
  set f₂ : SimpleGraph V → ℝ := fun F => ∏ e ∈ F.edgeFinset, g e with hf₂
  set f₄ : Finset (ℕ × ℕ) → ℝ := fun E'' => ∏ p ∈ E'', C₁ * a p with hf₄
  set Ψ : Finset (ℕ × ℕ) × SimpleGraph V × Option (Sym2 V) × Finset (ℕ × ℕ) → ℝ :=
    fun q => f₁ q.1 * (f₂ q.2.1 * ((fun _ : Option (Sym2 V) => (1 : ℝ)) q.2.2.1 * f₄ q.2.2.2))
    with hΨ
  -- (i) the bound for one edge set
  have hone : ∀ E ∈ relEulerianConnectedPairs Y, ∏ p ∈ E, C₁ * a p ≤ Ψ (Φ E) := by
    intro E hE
    have hEP := hP E hE
    obtain ⟨hkept, hsup, hE'le, -, hcard⟩ := hstr E hE
    rw [← prod_sdiff (hsubE' E hE)]
    have h1 : ∏ p ∈ edgesOf (E' E), C₁ * a p =
        ∏ e ∈ (E' E).edgeFinset, C₁ * absWeight r d cc e :=
      prod_edgesOf_eq_of _ _ _ fun i j => by
        rw [show absWeight r d cc s(i, j) = absOddWeight M lam ε₀ R (z i) (z j) from
          absWeight_dipole M lam ε₀ R z i j]
    have hcardE' : (E' E).edgeFinset.card ≤ 2 * n := by
      rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card]
      have hnV : n = (Y.biUnion id).card := rfl
      exact hcard.trans (by omega)
    have hq := hquad (E' E) (v₁ E) (e₀ E) (Qs E) (hE'le.trans (hGle E hE)) hEP.2
    have hrem := prod_peelWeight_le_prod_gbar (ε₀ := ε₀) (R := R) hM hlam c
      (R' := r (v₁ E)) (hr _) (removedGraph (Qs E)) (e₀ E)
    have hab0 : 0 ≤ ∏ e ∈ (E' E).edgeFinset, absWeight r d cc e :=
      prod_nonneg fun e _ => absWeight_nonneg hr hd hcc e
    calc (∏ p ∈ E \ edgesOf (E' E), C₁ * a p) * ∏ p ∈ edgesOf (E' E), C₁ * a p
        = (∏ p ∈ E \ edgesOf (E' E), C₁ * a p) *
            (C₁ ^ (E' E).edgeFinset.card * ∏ e ∈ (E' E).edgeFinset, absWeight r d cc e) := by
          congr 1
          rw [h1, prod_mul_distrib, prod_const]
      _ ≤ (∏ p ∈ E \ edgesOf (E' E), C₁ * a p) *
            (C₁ ^ (2 * n) * (κ ^ n * P * B (edgesOf (keptGraph (E' E) (Qs E))) *
              ∏ e ∈ (removedGraph (Qs E)).edgeFinset.erase (e₀ E), g e)) := by
          refine mul_le_mul_of_nonneg_left ?_ (prod_nonneg fun p _ => mul_nonneg hC0 (ha0 p))
          refine mul_le_mul (pow_le_pow_right₀ hC₁ hcardE') ?_ hab0 (pow_nonneg hC0 _)
          refine hq.trans (mul_le_mul_of_nonneg_left hrem ?_)
          exact mul_nonneg (mul_nonneg (pow_nonneg hκ _) hP0) (hB _)
      _ = Ψ (Φ E) := by
          simp only [hΨ, hΦ, hf₁, hf₂, hf₄]
          rw [edgeFinset_deleteEdges_singleton]
          ring
  -- (ii) the injection lands in `W`
  have hmem : ∀ E ∈ relEulerianConnectedPairs Y, Φ E ∈ W := by
    intro E hE
    obtain ⟨hkept, -, -, -, -⟩ := hstr E hE
    have hpf := ((hP E hE).lemma_4_49 hr hd hcc hcc1).1
    refine mem_product.2 ⟨mem_image_of_mem _ (mem_relTrees.2 hkept), mem_product.2
      ⟨mem_pseudoforests.2 ((mem_pseudoforests.1 hpf).mono (SimpleGraph.deleteEdges_le _)),
        mem_product.2 ⟨mem_univ _, mem_powerset.2 (sdiff_subset.trans (hEsub E hE))⟩⟩⟩
  -- (iii) injectivity
  have hrecon : ∀ E ∈ relEulerianConnectedPairs Y, E' E =
      graphOf V (Φ E).1 ⊔ ((Φ E).2.1 ⊔ SimpleGraph.fromEdgeSet {e | (Φ E).2.2.1 = some e}) := by
    intro E hE
    obtain ⟨-, hsup, -, -, -⟩ := hstr E hE
    simp only [hΦ]
    rw [graphOf_edgesOf, ← eq_deleteEdges_sup_record, hsup]
  have hinj : Set.InjOn Φ (relEulerianConnectedPairs Y) := by
    intro E₁ hE₁ E₂ hE₂ heq
    have hE' : E' E₁ = E' E₂ := by rw [hrecon E₁ hE₁, hrecon E₂ hE₂, heq]
    have h4 : E₁ \ edgesOf (E' E₁) = E₂ \ edgesOf (E' E₂) := congrArg (fun q => q.2.2.2) heq
    rw [← sdiff_union_of_subset (hsubE' E₁ hE₁), ← sdiff_union_of_subset (hsubE' E₂ hE₂), h4, hE']
  -- (iv) nonnegativity
  have hΨ0 : ∀ q ∈ W, 0 ≤ Ψ q := fun q _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg hκ _)) hP0) (hB _))
      (mul_nonneg (prod_nonneg fun e _ => hg0 e)
        (mul_nonneg zero_le_one (prod_nonneg fun p _ => mul_nonneg hC0 (ha0 p))))
  -- the bounds on the factors
  have hF : ∑ F ∈ (pseudoforests : Finset (SimpleGraph V)), f₂ F ≤
      ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) := by
    refine (sum_pseudoforests_le g hg0).trans_eq ?_
    rw [← prod_coe_sort V]
    refine prod_congr rfl fun i _ => ?_
    rw [← sum_erase_coe V (fun j => gbar M lam ε₀ R c i j) i]
    rfl
  have hO : ∑ _o ∈ (univ : Finset (Option (Sym2 V))), (1 : ℝ) ≤ 4 ^ n := by
    rw [sum_const, card_univ, Fintype.card_option, nsmul_eq_mul, mul_one]
    have hsym : Fintype.card (Sym2 V) ≤ n * n := by
      have := Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α := V))
      rwa [Fintype.card_prod, Fintype.card_coe] at this
    have := one_add_mul_self_le_four_pow n
    have h' : Fintype.card (Sym2 V) + 1 ≤ 4 ^ n := by omega
    exact_mod_cast h'
  have hE'' : ∑ E'' ∈ (interPairs Y).powerset, f₄ E'' ≤
      ∏ p ∈ interPairs Y, Real.exp (C₁ * a p) := by
    rw [hf₄, ← prod_one_add]
    exact prod_le_prod₀ (fun p _ => by have := mul_nonneg hC0 (ha0 p); linarith)
      fun p _ => by linarith [Real.add_one_le_exp (C₁ * a p)]
  calc eulerGroupSum C₁ a Y = ∑ E ∈ relEulerianConnectedPairs Y, ∏ p ∈ E, C₁ * a p := rfl
    _ ≤ ∑ E ∈ relEulerianConnectedPairs Y, Ψ (Φ E) := sum_le_sum hone
    _ = ∑ q ∈ (relEulerianConnectedPairs Y).image Φ, Ψ q := (sum_image hinj).symm
    _ ≤ ∑ q ∈ W, Ψ q := by
        refine sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun q hq _ => hΨ0 q hq
        obtain ⟨E, hE, rfl⟩ := mem_image.1 hq
        exact hmem E hE
    _ = (∑ T ∈ relTreePairs Y, f₁ T) * ((∑ F ∈ (pseudoforests : Finset (SimpleGraph V)), f₂ F) *
          ((∑ _o ∈ (univ : Finset (Option (Sym2 V))), (1 : ℝ)) *
            ∑ E'' ∈ (interPairs Y).powerset, f₄ E'')) := by
        rw [hW]
        exact sum_product4 _ _ _ _ f₁ f₂ (fun _ => (1 : ℝ)) f₄
    _ ≤ (∑ T ∈ relTreePairs Y, f₁ T) * ((∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)) *
          (4 ^ n * ∏ p ∈ interPairs Y, Real.exp (C₁ * a p))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hF (mul_le_mul hO hE''
          (sum_nonneg fun E'' _ => prod_nonneg fun p _ => mul_nonneg hC0 (ha0 p))
          (by positivity)) (mul_nonneg (sum_nonneg fun _ _ => zero_le_one)
            (sum_nonneg fun E'' _ => prod_nonneg fun p _ => mul_nonneg hC0 (ha0 p))) hG0)
          (sum_nonneg fun T _ => mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg hκ _)) hP0)
            (hB T))
    _ = (4 * C₁ ^ 2 * κ) ^ n * P * (∑ T ∈ relTreePairs Y, B T) *
          (∏ p ∈ interPairs Y, Real.exp (C₁ * a p)) *
          ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) := by
        rw [hf₁, ← mul_sum, mul_pow, mul_pow, ← pow_mul]
        ring

/-- Sum over peeling outputs and over the unused edges, using the summed quadratic
estimate. This is (4.100) and (4.101) in the proof of Lemma 4.55.
The exceptional edge is recorded separately before the pseudoforest sum is taken. -/
theorem eulerGroupSum_reattach (hC₁ : 1 ≤ C₁) : ∃ κ : ℝ, 0 < κ ∧
    ∀ (M lam ε₀ R : ℝ), 1 ≤ M → 0 < lam →
    ∀ {Y : Finset (Finset ℕ)}, IsSubpartition Y → ∀ c : ℕ → ℂ × ℂ,
    eulerGroupSum C₁ (fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2)) Y ≤
      (4 * C₁ ^ 2 * κ) ^ (Y.biUnion id).card * prodExceptMax c Y *
        (∑ T₀ ∈ relTrees Y,
          ∑ T ∈ longAgreeingTrees Y (fun i : Y.biUnion id => dipoleLength (c i))
            (dipoleDistOn fun i : Y.biUnion id => c i) T₀,
            ∏ e ∈ T.edgeFinset, keptWeight (dipoleDistOn fun i : Y.biUnion id => c i)
              (absIndicator M lam ε₀ R fun i : Y.biUnion id => c i) e) *
        (∏ p ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2))) *
        ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
  obtain ⟨κ, hκ, hquad⟩ := quadratic_estimate_sum
  refine ⟨κ, hκ, fun M lam ε₀ R hM hlam Y hY c => ?_⟩
  let z : Y.biUnion id → ℂ × ℂ := fun i => c i
  let w : SimpleGraph (Y.biUnion id) → ℝ := fun T =>
    ∏ e ∈ T.edgeFinset, keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ R z) e
  let B : Finset (ℕ × ℕ) → ℝ := fun T₀ =>
    ∑ T ∈ longAgreeingTrees Y (fun i => dipoleLength (z i)) (dipoleDistOn z)
      (graphOf (Y.biUnion id) T₀), w T
  have hB : ∀ T₀, 0 ≤ B T₀ := fun T₀ => sum_nonneg fun T _ =>
    prod_nonneg fun e _ => keptWeight_nonneg (absIndicator_nonneg M lam ε₀ R z) e
  have hbound := eulerGroupSum_bound_of_peeling (ε₀ := ε₀) (R := R) hC₁ hM hlam hY c κ hκ.le B hB ?_
  · have hinj : Set.InjOn (edgesOf (U := Y.biUnion id)) (relTrees Y) := by
      intro T hT T' hT' h
      simpa only [graphOf_edgesOf] using congrArg (graphOf (Y.biUnion id)) h
    have hsum : (∑ T ∈ relTreePairs Y, B T) =
        ∑ T₀ ∈ relTrees Y, ∑ T ∈ longAgreeingTrees Y
          (fun i => dipoleLength (c i)) (dipoleDistOn z) T₀, w T := by
      rw [relTreePairs, sum_image hinj]
      simp only [B, graphOf_edgesOf]
      rfl
    simpa only [hsum] using hbound
  intro E v e₀ Qs hE hP
  have hq := hquad hE hP (fun _ => norm_nonneg _)
    (dipoleDistOn_nonneg z) (absIndicator_nonneg M lam ε₀ R z)
  rw [prod_blockRadius_erase_eq hY c hP.le_radius] at hq
  simpa only [B, graphOf_edgesOf, w, z, dipoleLength] using hq

/-- The group estimate (4.103), obtained by exchanging reattachment sums and
applying (4.71). See the proof of Lemma 4.55.
The logarithmic product here is the bound for predecessor multiplicities. -/
theorem eulerGroupSum_route_le (p : ℕ) (hC₁ : 1 ≤ C₁) : ∃ K : ℝ, 0 < K ∧
    ∀ (M lam ε₀ R : ℝ), 9 ≤ M → 0 < lam →
    ∀ {Y : Finset (Finset ℕ)}, IsSubpartition Y → (∀ S ∈ Y, S.card ≤ p) →
    ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      (∀ i j : Y.biUnion id, (interEdges Y).Adj i j → ¬ MultipoleLinked M lam (c i) (c j)) →
    eulerGroupSum C₁ (fun q => absOddWeight M lam ε₀ R (c q.1) (c q.2)) Y ≤
      K ^ (Y.biUnion id).card * prodExceptMax c Y *
        (∑ T ∈ relTreePairs Y, ∏ q ∈ T, keptPair M lam ε₀ R c q) *
        (∏ q ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) *
        (∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j)) *
        ∏ i ∈ Y.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2 := by
  obtain ⟨κ, hκ, hraw⟩ := eulerGroupSum_reattach hC₁
  obtain ⟨D, hD, hcount⟩ := RouteReattach.exchange_le p
  refine ⟨4 * C₁ ^ 2 * κ * D, by positivity, fun M lam ε₀ R hM hlam Y hY hp c hr hB => ?_⟩
  let z : Y.biUnion id → ℂ × ℂ := fun i => c i
  let w : SimpleGraph (Y.biUnion id) → ℝ := fun T =>
    ∏ e ∈ T.edgeFinset, keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ R z) e
  have hw : ∀ T, 0 ≤ w T := fun T =>
    prod_nonneg fun e _ => keptWeight_nonneg (absIndicator_nonneg M lam ε₀ R z) e
  have hchange := hcount hY hp (R := ε₀ * R) z hM (fun i => hr i i.2) hB w (fun T _ => hw T)
  have hinj : Set.InjOn (edgesOf (U := Y.biUnion id)) (relTrees Y) := by
    intro T hT T' hT' h
    simpa only [graphOf_edgesOf] using congrArg (graphOf (Y.biUnion id)) h
  have hsum : (∑ T ∈ relTrees Y, w T) =
      ∑ T ∈ relTreePairs Y, ∏ q ∈ T, keptPair M lam ε₀ R c q := by
    rw [relTreePairs, sum_image hinj]
    exact sum_congr rfl fun T _ => (prod_edgesOf_eq_of T _ _ (fun i j => rfl)).symm
  have hlog : (∏ i : Y.biUnion id, (1 + Real.logb M (17 * (ε₀ * R) / dipoleLength (z i))) ^ 2) =
      ∏ i ∈ Y.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2 := by
    rw [← prod_coe_sort (Y.biUnion id)]
    simp only [z, dipoleLength, mul_assoc]
  rw [hsum, hlog] at hchange
  have hraw' := hraw M lam ε₀ R (by linarith) hlam hY c
  refine hraw'.trans ?_
  have hP0 := prodExceptMax_nonneg (c := c) Y
  have hE0 : 0 ≤ ∏ q ∈ interPairs Y,
      Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2)) :=
    prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hG0 : 0 ≤ ∏ i ∈ Y.biUnion id,
      (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j) :=
    prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)
  calc
    _ ≤ (4 * C₁ ^ 2 * κ) ^ (Y.biUnion id).card * prodExceptMax c Y *
        (D ^ (Y.biUnion id).card *
          (∏ i ∈ Y.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2) *
          ∑ T ∈ relTreePairs Y, ∏ q ∈ T, keptPair M lam ε₀ R c q) *
        (∏ q ∈ interPairs Y, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) *
        ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hchange (mul_nonneg (by positivity) hP0)) hE0) hG0
    _ = _ := by rw [mul_pow]; ring

end PerGroup

end AbsoluteLower

end MultipoleBKT

end
