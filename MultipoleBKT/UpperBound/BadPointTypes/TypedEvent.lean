/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.SubConfig

/-!
# The structure of a configuration of bad points of types 1, 2, 3

The paper: proof of Lemma 5.39, on the
event `{I^1_bad = V_1, I^2_bad = V_2, I^3_bad = V_3}` with `V_1 ∪ V_2 ∪ V_3 = [n]`, for a
configuration without isosceles coincidences (Lebesgue-almost every configuration):

* `cluster_split`: every cluster lies in `V_1` or is a singleton;
  hence the complement of any set containing or avoiding `V_1` is a union of clusters
  (`clusterUnion_of_split`), which is what the sub-configurations need;
* `radius_of_not_mem` (Definition 5.2 and Remark 5.6): for `i ∉ V_1`,
  `r_i ≤ ε₀ R̄` and `τ_i^± = max(λ, r_i/4)`;
* `card_typeThree_le` ("Every `U`-component contained in `V_bad^3` meets
  `J_bad^3` and has at most `p(β)` vertices"): `|V_3| ≤ p(β) |J_bad^3|`;
* `exists_forest` and `typeThree_forest`: on the sub-configuration of `V_3`, the
  seeds `J^3_bad` and a parent map along the multipole links with a decreasing depth (the forest
  `F` of the paper).
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset TheoremTwo UpperBound

variable {n : ℕ}

/-- The near-bond relation of type 3 (Definition 5.4): `dist({x, y}, {x', y'}) ≤ M max(r, λ)`,
`r = |x - y|`. -/
def IsNear (M lam : ℝ) (a b : ℂ × ℂ) : Prop :=
  min (min ‖a.1 - b.1‖ ‖a.1 - b.2‖) (min ‖a.2 - b.1‖ ‖a.2 - b.2‖) ≤ M * max ‖a.1 - a.2‖ lam

open scoped Classical in
/-- `J^3_bad` (Definition 5.4) for `I^{1,2}_bad = B`: the labels outside `B` near some label of
`B`. -/
noncomputable def nearSet (M lam : ℝ) (d : Fin n → ℂ × ℂ) (B : Finset (Fin n)) :
    Finset (Fin n) :=
  (univ \ B).filter fun i => ∃ j ∈ B, IsNear M lam (d i) (d j)

/-! ### Clusters of a generic configuration -/

section Generic

variable {q : ℕ} {h : ℝ} {z : Fin n → ℂ} {r : Fin n → ℝ}

/-- Every cluster of a generic configuration lies in the set `V` of overcrowded labels or is a
singleton. -/
theorem cluster_split (hq : 1 ≤ q) (hh : 0 < h) (hr : ∀ i, 0 ≤ r i) (hz : NoIsosceles z)
    {V : Finset (Fin n)} (hV : ∀ i, (clusterOf q h z r i).card = q + 1 → i ∈ V) :
    ∀ p ∈ sameSignClustering q h z r univ, p.1 ⊆ V ∨ ∃ i, p.1 = {i} := by
  intro p hp
  obtain ⟨i, hi⟩ := fst_nonempty_of_mem_clustering hp
  have hcl : clusterOf q h z r i = p.1 := by
    obtain ⟨p', hp', hip', hpi', -⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
    rw [hpi', eq_of_mem_clustering _ p' hp' p hp i hip' hi]
  rcases clusterOf_cases hq hh hr hz i with ⟨hcard, -⟩ | ⟨-, hsing, -⟩
  · left
    intro j hj
    rw [← hcl] at hj
    refine hV j ?_
    rw [(clusterOf_eq_of_mem hj).1]
    exact hcard
  · exact Or.inr ⟨i, hcl ▸ hsing⟩

end Generic

section Event

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin n → ℂ × ℂ}

/-- In a generic configuration, every cluster (of both clusterings) lies in `I^1_bad` or is a
singleton. -/
theorem cluster_split_dipoles (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (hz : NoIsosceles (fun k => (d k).1)) (hz' : NoIsosceles (fun k => (d k).2)) :
    (∀ p ∈ sameSignClustering (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (d k).1)
        (dipoleLength d) univ, p.1 ⊆ badPointsTypeOne p₀ β lam ε₀ d ∨ ∃ i, p.1 = {i}) ∧
      (∀ p ∈ sameSignClustering (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (d k).2)
        (dipoleLength d) univ, p.1 ⊆ badPointsTypeOne p₀ β lam ε₀ d ∨ ∃ i, p.1 = {i}) := by
  have hr : ∀ i, 0 ≤ dipoleLength d i := fun i => norm_nonneg _
  refine ⟨cluster_split hq hh hr hz fun i hi => ?_, cluster_split hq hh hr hz' fun i hi => ?_⟩
  · rw [mem_badPointsTypeOne_iff]; exact Or.inr (Or.inl hi)
  · rw [mem_badPointsTypeOne_iff]; exact Or.inr (Or.inr hi)

/-- The complement of a set containing or avoiding `I^1_bad` is a union of clusters. -/
theorem clusterUnion_of_split (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (hz : NoIsosceles (fun k => (d k).1)) (hz' : NoIsosceles (fun k => (d k).2))
    {G : Finset (Fin n)}
    (hG : badPointsTypeOne p₀ β lam ε₀ d ⊆ G ∨ Disjoint (badPointsTypeOne p₀ β lam ε₀ d) G) :
    ClusterUnion p₀ β lam ε₀ d G := by
  obtain ⟨h1, h2⟩ := cluster_split_dipoles hq hh hz hz'
  have key : ∀ S : Finset (Fin n), (S ⊆ badPointsTypeOne p₀ β lam ε₀ d ∨ ∃ i, S = {i}) →
      S ⊆ G ∨ Disjoint S G := by
    rintro S (hS | ⟨i, rfl⟩)
    · rcases hG with hG | hG
      · exact Or.inl (hS.trans hG)
      · exact Or.inr (Finset.disjoint_of_subset_left hS hG)
    · by_cases hi : i ∈ G
      · exact Or.inl (Finset.singleton_subset_iff.2 hi)
      · exact Or.inr (Finset.disjoint_singleton_left.2 hi)
  exact ⟨fun p hp => key p.1 (h1 p hp), fun p hp => key p.1 (h2 p hp)⟩

/-- Outside `I^1_bad`, dipoles are short and both radii are `max(λ, r_i/4)`. -/
theorem radius_of_not_mem (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (hz : NoIsosceles (fun k => (d k).1)) (hz' : NoIsosceles (fun k => (d k).2)) {i : Fin n}
    (hi : i ∉ badPointsTypeOne p₀ β lam ε₀ d) :
    dipoleLength d i ≤ cutoff p₀ β lam ε₀ ∧
      radiusPlus p₀ β lam ε₀ d i = max lam (dipoleLength d i / 4) ∧
      radiusMinus p₀ β lam ε₀ d i = max lam (dipoleLength d i / 4) := by
  rw [mem_badPointsTypeOne_iff] at hi
  push Not at hi
  obtain ⟨hlong, hp, hm⟩ := hi
  have hr : ∀ i, 0 ≤ dipoleLength d i := fun i => norm_nonneg _
  have hval : ∀ z : Fin n → ℂ, NoIsosceles z →
      (clusterOf (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) z (dipoleLength d) i).card ≠
        clusterThreshold p₀ β + 1 →
      clusterRemovalValue (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) z (dipoleLength d) i =
        dipoleLength d i / 4 := by
    intro z hz hcard
    rcases clusterOf_cases hq hh hr hz i with ⟨hc, -⟩ | ⟨-, -, hv, -⟩
    · exact absurd hc hcard
    · exact hv hlong
  refine ⟨hlong, ?_, ?_⟩
  · show max lam _ = _
    rw [hval _ hz hp]
  · show max lam _ = _
    rw [hval _ hz' hm]

variable {Nₐ : ℕ} {V₁ V₂ V₃ : Finset (Fin n)}

/-- `I^3_bad` in terms of `J^3_bad`. -/
theorem typeThreeBad_eq_nearSet (Nₐ : ℕ) :
    typeThreeBad Nₐ p₀ β lam M ε₀ d =
      (univ \ (badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d)).filter
        fun i => (multipoleClassOn M lam d (univ \ badPointsTypeOne p₀ β lam ε₀ d) i ∩
          nearSet M lam d (badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d)).Nonempty := by
  rfl

section Structure

variable (h1 : badPointsTypeOne p₀ β lam ε₀ d = V₁) (h2 : typeTwoBad Nₐ p₀ β lam M ε₀ d = V₂)
  (h3 : typeThreeBad Nₐ p₀ β lam M ε₀ d = V₃)

include h1 h2 h3

theorem mem_typeThree_iff {i : Fin n} :
    i ∈ V₃ ↔ i ∉ V₁ ∪ V₂ ∧
      (multipoleClassOn M lam d (univ \ V₁) i ∩ nearSet M lam d (V₁ ∪ V₂)).Nonempty := by
  rw [← h3, typeThreeBad_eq_nearSet, h1, h2, Finset.mem_filter, Finset.mem_sdiff]
  simp only [Finset.mem_univ, true_and]

theorem classOn_subset_typeThree {i : Fin n} (hi : i ∈ V₃) :
    multipoleClassOn M lam d (univ \ V₁) i ⊆ V₃ := by
  intro j hj
  obtain ⟨hi12, hne⟩ := (mem_typeThree_iff h1 h2 h3).1 hi
  have hiU : i ∈ univ \ V₁ := Finset.mem_sdiff.2 ⟨Finset.mem_univ i, fun h => hi12
    (Finset.mem_union_left _ h)⟩
  have hjU : j ∈ univ \ V₁ := classOn_subset hiU hj
  have hcl : multipoleClassOn M lam d (univ \ V₁) j = multipoleClassOn M lam d (univ \ V₁) i :=
    classOn_eq_of_mem hj
  refine (mem_typeThree_iff h1 h2 h3).2 ⟨?_, hcl ▸ hne⟩
  intro hj12
  rcases Finset.mem_union.1 hj12 with hj1 | hj2
  · exact (Finset.mem_sdiff.1 hjU).2 hj1
  · -- type 2 is a union of classes
    have hij : i ∈ multipoleClassOn M lam d (univ \ V₁) j := by
      rw [hcl]; exact mem_classOn_self _ _
    rw [← h2] at hj2
    have := typeTwoBad_mem_of_mem_classOn Nₐ hj2 (by rw [h1]; exact hij)
    rw [h2] at this
    exact hi12 (Finset.mem_union_right _ this)

theorem card_classOn_typeThree_le {i : Fin n} (hi : i ∈ V₃) :
    (multipoleClassOn M lam d (univ \ V₁) i).card ≤ pBeta p₀ β := by
  obtain ⟨hi12, -⟩ := (mem_typeThree_iff h1 h2 h3).1 hi
  by_contra hlt
  push Not at hlt
  have hiU : i ∈ univ \ V₁ := Finset.mem_sdiff.2 ⟨Finset.mem_univ i, fun h => hi12
    (Finset.mem_union_left _ h)⟩
  have : i ∈ typeTwoBad Nₐ p₀ β lam M ε₀ d := by
    rw [mem_typeTwoBad_iff, h1]
    exact ⟨hiU, Or.inl hlt⟩
  rw [h2] at this
  exact hi12 (Finset.mem_union_right _ this)

theorem nearSet_subset_typeThree : nearSet M lam d (V₁ ∪ V₂) ⊆ V₃ := by
  classical
  intro j hj
  unfold nearSet at hj
  have hj12 : j ∉ V₁ ∪ V₂ := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hj).1).2
  exact (mem_typeThree_iff h1 h2 h3).2 ⟨hj12, ⟨j, Finset.mem_inter.2 ⟨mem_classOn_self _ _, hj⟩⟩⟩

/-- **`|V_3| ≤ p(β) |J^3_bad|`** (proof of Lemma 5.39). -/
theorem card_typeThree_le : V₃.card ≤ pBeta p₀ β * (nearSet M lam d (V₁ ∪ V₂)).card := by
  classical
  have hsub : V₃ ⊆ (nearSet M lam d (V₁ ∪ V₂)).biUnion
      fun s => multipoleClassOn M lam d (univ \ V₁) s := by
    intro i hi
    obtain ⟨-, s, hs⟩ := (mem_typeThree_iff h1 h2 h3).1 hi
    rw [Finset.mem_inter] at hs
    refine Finset.mem_biUnion.2 ⟨s, hs.2, ?_⟩
    rw [classOn_eq_of_mem hs.1]
    exact mem_classOn_self _ _
  calc V₃.card ≤ ((nearSet M lam d (V₁ ∪ V₂)).biUnion
        fun s => multipoleClassOn M lam d (univ \ V₁) s).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ nearSet M lam d (V₁ ∪ V₂), (multipoleClassOn M lam d (univ \ V₁) s).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ nearSet M lam d (V₁ ∪ V₂), pBeta p₀ β :=
        Finset.sum_le_sum fun s hs => card_classOn_typeThree_le h1 h2 h3
          (nearSet_subset_typeThree h1 h2 h3 hs)
    _ = pBeta p₀ β * (nearSet M lam d (V₁ ∪ V₂)).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

end Structure

end Event

/-! ### A forest towards a set of seeds -/

/-- **Breadth-first forest**: if every vertex can reach the set `S`, there are a parent map along
the edges and a depth decreasing along it off `S`. -/
theorem exists_forest {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hreach : ∀ a, ∃ s ∈ S, G.Reachable a s) :
    ∃ par : V → V, ∃ dep : V → ℕ, ∀ a, a ∉ S → G.Adj a (par a) ∧ dep (par a) < dep a := by
  classical
  have hP : ∀ a, ∃ k, ∃ s ∈ S, ∃ w : G.Walk a s, w.length = k := by
    intro a
    obtain ⟨s, hs, ⟨w⟩⟩ := hreach a
    exact ⟨w.length, s, hs, w, rfl⟩
  set dep : V → ℕ := fun a => Nat.find (hP a) with hdep
  have hex : ∀ a, a ∉ S → ∃ b, G.Adj a b ∧ dep b < dep a := by
    intro a ha
    obtain ⟨s, hs, w, hw⟩ := Nat.find_spec (hP a)
    cases w with
    | nil => exact absurd hs ha
    | @cons _ b _ hadj w' =>
      refine ⟨b, hadj, ?_⟩
      have hle : dep b ≤ w'.length := Nat.find_min' (hP b) ⟨s, hs, w', rfl⟩
      simp only [SimpleGraph.Walk.length_cons] at hw
      show dep b < Nat.find (hP a)
      omega
  refine ⟨fun a => if h : a ∉ S then Classical.choose (hex a h) else a, dep, fun a ha => ?_⟩
  simp only [ha, not_false_eq_true, ↓reduceDIte]
  exact Classical.choose_spec (hex a ha)

end BadPointTypes

end MultipoleBKT

end
