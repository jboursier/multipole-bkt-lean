/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.BadPoints
public import MultipoleBKT.Frozen.GoodPoints
public import MultipoleBKT.Frozen.GoodMultipoleCount
public import MultipoleBKT.Frozen.MultipoleCount
public import MultipoleBKT.Frozen.CriticalScale
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.AlphaExponent
public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 2: good points and good multipoles

Definitions 5.2, 5.3 and 5.5 and Remark 5.6 of the paper.
The component of a good point is its class in the type-one complement.
It has at most `p(β)` points, all of them good.
Counting the points of disjoint good components proves the stronger bound
`k 𝒩_k^good ≤ ε₀^{-α(β)} N λ^{2(k-1)}` used in Step 1 of the proof of Theorem 2. The existing count and profile interfaces follow from it.
The component-size sums and the long-dipole inclusion provide the other
count comparisons used in the theorem.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace TheoremTwo

/-! ### A closure principle for reachability -/

theorem mem_of_reachable_of_closed {V : Type*} {G : SimpleGraph V}
    {T : V → Prop} (hclosed : ∀ a b, T a → G.Adj a b → T b) {u v : V} (hu : T u)
    (h : G.Reachable u v) : T v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hclosed _ _ hu hadj)

/-- The minimum of the four distances between two dipoles is symmetric. -/
theorem min4_comm (d e : ℂ × ℂ) :
    min (min ‖e.1 - d.1‖ ‖e.1 - d.2‖) (min ‖e.2 - d.1‖ ‖e.2 - d.2‖) =
      min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) := by
  rw [norm_sub_rev e.1 d.1, norm_sub_rev e.1 d.2, norm_sub_rev e.2 d.1, norm_sub_rev e.2 d.2]
  rw [min_assoc, min_assoc, ← min_assoc ‖d.2 - e.1‖, min_comm ‖d.2 - e.1‖ ‖d.1 - e.2‖,
    min_assoc ‖d.1 - e.2‖]

/-- If `d ↔ e` (in either order) and `M ≥ 0`, then the distance of `d` to `e` is at most
`M max(r_d, λ)`. -/
theorem min4_le_of_linked {M lam : ℝ} (hM : 0 ≤ M) {d e : ℂ × ℂ}
    (h : MultipoleLinked M lam d e ∨ MultipoleLinked M lam e d) :
    min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) ≤
      M * max ‖d.1 - d.2‖ lam := by
  rcases h with h | h
  · exact h.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hM)
  · unfold MultipoleLinked at h
    rw [min4_comm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hM)

/-- The graph whose components (through `i ∈ U`) are the classes `[i]^U`. -/
abbrev classGraph {N : ℕ} (M lam : ℝ) (d : Fin N → ℂ × ℂ) (U : Finset (Fin N)) :
    SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun a b : Fin N => a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (d a) (d b)

/-- The graph of `↔` on all of `[N]`. -/
abbrev linkGraph {N : ℕ} (M lam : ℝ) (d : Fin N → ℂ × ℂ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun a b : Fin N => MultipoleLinked M lam (d a) (d b)

/-- `U = [N] ∖ I^1_bad`. -/
noncomputable abbrev typeOneComplement {N : ℕ} (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d

/-- The class `[i]^U`, `U = [N] ∖ I^1_bad`. -/
noncomputable abbrev goodClass {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)
    (i : Fin N) : Finset (Fin N) :=
  multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) i

section Classes

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}



theorem classGraph_le (U : Finset (Fin N)) : classGraph M lam d U ≤ linkGraph M lam d := by
  intro a b h
  rw [SimpleGraph.fromRel_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with h' | h'
  · exact Or.inl h'.2.2
  · exact Or.inr h'.2.2

theorem mem_of_classGraph_reachable {U : Finset (Fin N)} {i j : Fin N} (hi : i ∈ U)
    (h : (classGraph M lam d U).Reachable i j) : j ∈ U :=
  mem_of_reachable_of_closed (T := fun x => x ∈ U) (fun a b _ hab => by
    rw [SimpleGraph.fromRel_adj] at hab
    rcases hab.2 with h' | h'
    · exact h'.2.1
    · exact h'.1) hi h

theorem mem_classOn_iff {U : Finset (Fin N)} {i j : Fin N} :
    j ∈ multipoleClassOn M lam d U i ↔ (classGraph M lam d U).Reachable i j := by
  classical
  unfold multipoleClassOn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_classOn_self (U : Finset (Fin N)) (i : Fin N) : i ∈ multipoleClassOn M lam d U i :=
  mem_classOn_iff.mpr (SimpleGraph.Reachable.refl i)

theorem classOn_eq_of_mem {U : Finset (Fin N)} {i j : Fin N}
    (h : j ∈ multipoleClassOn M lam d U i) :
    multipoleClassOn M lam d U j = multipoleClassOn M lam d U i := by
  ext l
  rw [mem_classOn_iff, mem_classOn_iff]
  have hij := mem_classOn_iff.mp h
  exact ⟨fun hjl => hij.trans hjl, fun hil => hij.symm.trans hil⟩

/-- Membership in `I^2_bad` depends only on membership in `U` and on `|[i]^U|`. -/
theorem mem_badPointsTypeTwo_iff {i : Fin N} :
    i ∈ badPointsTypeTwo p₀ β lam M ε₀ d ↔
      i ∈ typeOneComplement p₀ β lam ε₀ d ∧
        (pBeta p₀ β < (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) i).card ∨
          ((multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) i).card ∈
              Finset.Icc 1 (pBeta p₀ β) ∧
            ε₀ ^ (-alphaExponent β) * N *
                lam ^ (2 * ((multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) i).card - 1)) <
              (((typeOneComplement p₀ β lam ε₀ d).filter fun u =>
                (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) u).card =
                  (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) i).card).card : ℝ))) := by
  classical
  set U := typeOneComplement p₀ β lam ε₀ d
  unfold badPointsTypeTwo
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · rintro (⟨hU, hp⟩ | ⟨k, hk, hmem⟩)
    · exact ⟨hU, Or.inl hp⟩
    · split_ifs at hmem with hcond
      · rw [Finset.mem_filter] at hmem
        refine ⟨hmem.1, Or.inr ⟨hmem.2 ▸ hk, ?_⟩⟩
        rw [hmem.2]
        exact hcond
      · exact absurd hmem (Finset.notMem_empty _)
  · rintro ⟨hU, hp | ⟨hk, hcond⟩⟩
    · exact Or.inl ⟨hU, hp⟩
    · refine Or.inr ⟨_, hk, ?_⟩
      rw [ite_eq_left hcond, Finset.mem_filter]
      exact ⟨hU, rfl⟩

theorem mem_badPointsTypeThree_iff {i : Fin N} :
    i ∈ badPointsTypeThree p₀ β lam M ε₀ d ↔
      i ∉ badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d ∧
        (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) i ∩
          (Finset.univ \ (badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d)).filter
            fun j => ∃ l ∈ badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d,
              min (min ‖(d j).1 - (d l).1‖ ‖(d j).1 - (d l).2‖)
                  (min ‖(d j).2 - (d l).1‖ ‖(d j).2 - (d l).2‖)
                ≤ M * max ‖(d j).1 - (d j).2‖ lam).Nonempty := by
  classical
  unfold badPointsTypeThree
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]

theorem mem_goodPoints_iff {i : Fin N} :
    i ∈ goodPoints p₀ β lam M ε₀ d ↔
      i ∉ badPointsTypeOne p₀ β lam ε₀ d ∧ i ∉ badPointsTypeTwo p₀ β lam M ε₀ d ∧
        i ∉ badPointsTypeThree p₀ β lam M ε₀ d := by
  unfold goodPoints badPoints
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
  tauto

theorem mem_typeOneComplement_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    i ∈ typeOneComplement p₀ β lam ε₀ d := by
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, (mem_goodPoints_iff.mp hi).1⟩

/-- **Remark 5.6**: the class of a good point has at most `p(β)` elements. -/
theorem card_classOn_le {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    (goodClass p₀ β lam M ε₀ d i).card ≤ pBeta p₀ β := by
  by_contra h
  push Not at h
  exact (mem_goodPoints_iff.mp hi).2.1
    (mem_badPointsTypeTwo_iff.mpr ⟨mem_typeOneComplement_of_good hi, Or.inl h⟩)

/-- **Remark 5.6**: all points of the class of a good point are good. -/
theorem good_of_mem_classOn {i j : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d)
    (hj : j ∈ goodClass p₀ β lam M ε₀ d i) : j ∈ goodPoints p₀ β lam M ε₀ d := by
  classical
  obtain ⟨hi1, hi2, hi3⟩ := mem_goodPoints_iff.mp hi
  have hiU := mem_typeOneComplement_of_good hi
  have hjU : j ∈ typeOneComplement p₀ β lam ε₀ d :=
    mem_of_classGraph_reachable hiU (mem_classOn_iff.mp hj)
  have hcls : goodClass p₀ β lam M ε₀ d j = goodClass p₀ β lam M ε₀ d i := classOn_eq_of_mem hj
  have hj1 : j ∉ badPointsTypeOne p₀ β lam ε₀ d := (Finset.mem_sdiff.mp hjU).2
  have hj2 : j ∉ badPointsTypeTwo p₀ β lam M ε₀ d := by
    intro h2
    obtain ⟨-, h⟩ := mem_badPointsTypeTwo_iff.mp h2
    apply hi2
    refine mem_badPointsTypeTwo_iff.mpr ⟨hiU, ?_⟩
    have hc : (goodClass p₀ β lam M ε₀ d j).card = (goodClass p₀ β lam M ε₀ d i).card := by
      rw [hcls]
    simp only [goodClass] at hc
    rw [hc] at h
    exact h
  refine mem_goodPoints_iff.mpr ⟨hj1, hj2, fun h3 => ?_⟩
  obtain ⟨-, hne⟩ := mem_badPointsTypeThree_iff.mp h3
  apply hi3
  refine mem_badPointsTypeThree_iff.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_union, not_or]
    exact ⟨hi1, hi2⟩
  · simp only [goodClass] at hcls
    rw [hcls] at hne
    exact hne

/-- **Remark 5.6**: for a good point `i`, the points reachable from `i` in the graph of `↔` on
`[N]` are exactly the class `[i]^U`. -/
theorem reachable_iff_mem_classOn (hM : 0 ≤ M) {i j : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    (linkGraph M lam d).Reachable i j ↔ j ∈ goodClass p₀ β lam M ε₀ d i := by
  classical
  constructor
  · intro h
    refine mem_of_reachable_of_closed (T := fun x => x ∈ goodClass p₀ β lam M ε₀ d i)
      (fun a b ha hab => ?_) (mem_classOn_self _ i) h
    have hag := good_of_mem_classOn hi ha
    obtain ⟨ha1, ha2, ha3⟩ := mem_goodPoints_iff.mp hag
    have haU := mem_typeOneComplement_of_good hag
    rw [SimpleGraph.fromRel_adj] at hab
    by_cases hbU : b ∈ typeOneComplement p₀ β lam ε₀ d
    · refine mem_classOn_iff.mpr ((mem_classOn_iff.mp ha).trans ?_)
      refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.fromRel_adj]
      refine ⟨hab.1, ?_⟩
      rcases hab.2 with h' | h'
      · exact Or.inl ⟨haU, hbU, h'⟩
      · exact Or.inr ⟨hbU, haU, h'⟩
    · exfalso
      have hb1 : b ∈ badPointsTypeOne p₀ β lam ε₀ d := by
        by_contra hb
        exact hbU (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩)
      apply ha3
      refine mem_badPointsTypeThree_iff.mpr ⟨?_, a, Finset.mem_inter.mpr
        ⟨mem_classOn_self _ a, ?_⟩⟩
      · rw [Finset.mem_union, not_or]
        exact ⟨ha1, ha2⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, b,
          Finset.mem_union_left _ hb1, min4_le_of_linked hM hab.2⟩
        rw [Finset.mem_union, not_or]
        exact ⟨ha1, ha2⟩
  · intro h
    exact (mem_classOn_iff.mp h).mono (classGraph_le _)

end Classes

/-! ### Components of the multipole graph -/

section Components

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- The matched dipoles `(x_i, y_{σ_N(i)})` of a configuration. -/
noncomputable abbrev matched (c : Fin N → ℂ × ℂ) : Fin N → ℂ × ℂ :=
  fun i => ((c i).1, (c (stableMatching c i)).2)

theorem multipoleGraph_eq (c : Fin N → ℂ × ℂ) :
    multipoleGraph M lam c = linkGraph M lam (matched c) := rfl

theorem connectedComponentMk_out {V : Type*} {G : SimpleGraph V} (C : G.ConnectedComponent) :
    G.connectedComponentMk (Quot.out C) = C :=
  Quot.out_eq C

theorem natCard_supp_eq {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableEq G.ConnectedComponent] (C : G.ConnectedComponent) :
    Nat.card C.supp = (Finset.univ.filter fun v => G.connectedComponentMk v = C).card := by
  classical
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext v
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- For a good point `i`, the multipole of `i` is the class `[i]^U`. -/
theorem supp_connectedComponentMk_eq (hM : 0 ≤ M) {c : Fin N → ℂ × ℂ} {i : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ (matched c)) :
    ((multipoleGraph M lam c).connectedComponentMk i).supp =
      ↑(goodClass p₀ β lam M ε₀ (matched c) i) := by
  ext j
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.eq, Finset.mem_coe, multipoleGraph_eq,
    ← reachable_iff_mem_classOn hM hi]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem natCard_supp_of_good (hM : 0 ≤ M) {c : Fin N → ℂ × ℂ} {i : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ (matched c)) :
    Nat.card ((multipoleGraph M lam c).connectedComponentMk i).supp =
      (goodClass p₀ β lam M ε₀ (matched c) i).card := by
  rw [supp_connectedComponentMk_eq hM hi, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem supp_subset_good (hM : 0 ≤ M) {c : Fin N → ℂ × ℂ} {i : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ (matched c)) :
    ((multipoleGraph M lam c).connectedComponentMk i).supp ⊆
      ↑(goodPoints p₀ β lam M ε₀ (matched c)) := by
  rw [supp_connectedComponentMk_eq hM hi]
  intro j hj
  exact good_of_mem_classOn hi hj

open scoped Classical in
theorem multipoleCount_eq_card (c : Fin N → ℂ × ℂ) (k : ℕ) :
    multipoleCount M lam c k =
      (Finset.univ.filter fun C : (multipoleGraph M lam c).ConnectedComponent =>
        Nat.card C.supp = k).card := by
  unfold multipoleCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open scoped Classical in
theorem goodMultipoleCount_eq_card (c : Fin N → ℂ × ℂ) (k : ℕ) :
    goodMultipoleCount p₀ β lam M ε₀ c k =
      (Finset.univ.filter fun C : (multipoleGraph M lam c).ConnectedComponent =>
        Nat.card C.supp = k ∧ C.supp ⊆ ↑(goodPoints p₀ β lam M ε₀ (matched c))).card := by
  unfold goodMultipoleCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- `𝒩_k^good ≤ 𝒩_k`. -/
theorem goodMultipoleCount_le_multipoleCount (c : Fin N → ℂ × ℂ) (k : ℕ) :
    goodMultipoleCount p₀ β lam M ε₀ c k ≤ multipoleCount M lam c k := by
  classical
  rw [goodMultipoleCount_eq_card, multipoleCount_eq_card]
  refine Finset.card_le_card fun C hC => ?_
  rw [Finset.mem_filter] at hC ⊢
  exact ⟨hC.1, hC.2.1⟩

/-- `k |s| = ∑_{a ∈ s} f a` when `f = k` on `s`. -/
theorem mul_card_eq_sum_of_forall {α : Type*} (s : Finset α) (f : α → ℕ) (k : ℕ)
    (h : ∀ a ∈ s, f a = k) : k * s.card = ∑ a ∈ s, f a := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The sizes of the multipoles add up to `N`. -/
theorem sum_natCard_supp {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] :
    ∑ C : G.ConnectedComponent, Nat.card C.supp = Fintype.card V := by
  classical
  rw [← Finset.card_univ (α := V),
    Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr ?_ fun C _ => natCard_supp_eq C
  ext C
  simp

open scoped Classical in
/-- **`∑_{k ∈ T} k 𝒩_k ≤ N`**: the multipoles are disjoint. -/
theorem sum_mul_multipoleCount_le (c : Fin N → ℂ × ℂ) (T : Finset ℕ) :
    ∑ k ∈ T, k * multipoleCount M lam c k ≤ N := by
  set G := multipoleGraph M lam c
  have h1 : ∀ k, k * multipoleCount M lam c k =
      ∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent => Nat.card C.supp = k),
        Nat.card C.supp := by
    intro k
    rw [multipoleCount_eq_card]
    exact mul_card_eq_sum_of_forall _ _ _ fun C hC => (Finset.mem_filter.mp hC).2
  simp_rw [h1]
  have h2 : ∑ k ∈ T, ∑ C ∈ Finset.univ.filter
      (fun C : G.ConnectedComponent => Nat.card C.supp = k), Nat.card C.supp =
      ∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent => Nat.card C.supp ∈ T),
        Nat.card C.supp := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter
      (fun C : G.ConnectedComponent => Nat.card C.supp ∈ T)) (t := T)
      (g := fun C => Nat.card C.supp) (fun C hC => (Finset.mem_filter.mp hC).2)]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr ?_ fun _ _ => rfl
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl; exact ⟨hk, rfl⟩
    · rintro ⟨-, h⟩; exact h
  rw [h2]
  calc ∑ C ∈ Finset.univ.filter (fun C : G.ConnectedComponent => Nat.card C.supp ∈ T),
        Nat.card C.supp ≤ ∑ C : G.ConnectedComponent, Nat.card C.supp :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = N := (sum_natCard_supp G).trans (Fintype.card_fin N)

open scoped Classical in
/-- **Remark 5.6**: the good points are covered by the good multipoles of sizes `1, …, p(β)`:
`N ≤ |I_bad| + ∑_{k=1}^{p} k 𝒩_k^good`. -/
theorem card_le_card_badPoints_add_sum (hM : 0 ≤ M) (c : Fin N → ℂ × ℂ) :
    N ≤ (badPoints p₀ β lam M ε₀ (matched c)).card +
      ∑ k ∈ Finset.Icc 1 (pBeta p₀ β), k * goodMultipoleCount p₀ β lam M ε₀ c k := by
  set G := multipoleGraph M lam c
  set good := goodPoints p₀ β lam M ε₀ (matched c)
  set Pg : G.ConnectedComponent → Prop := fun C =>
    Nat.card C.supp ∈ Finset.Icc 1 (pBeta p₀ β) ∧ C.supp ⊆ ↑good
  have hN : N = good.card + (badPoints p₀ β lam M ε₀ (matched c)).card := by
    have := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (badPoints p₀ β lam M ε₀ (matched c)))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hcover : good ⊆ (Finset.univ.filter Pg).biUnion
      (fun C => Finset.univ.filter fun v => G.connectedComponentMk v = C) := by
    intro i hi
    rw [Finset.mem_biUnion]
    refine ⟨G.connectedComponentMk i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    · rw [natCard_supp_of_good hM hi, Finset.mem_Icc]
      exact ⟨Finset.card_pos.mpr ⟨i, mem_classOn_self _ i⟩, card_classOn_le hi⟩
    · exact supp_subset_good hM hi
  have h1 : good.card ≤ ∑ C ∈ Finset.univ.filter Pg, Nat.card C.supp := by
    refine (Finset.card_le_card hcover).trans (Finset.card_biUnion_le.trans ?_)
    exact (Finset.sum_congr rfl fun C _ => (natCard_supp_eq C).symm).le
  have h2 : ∑ C ∈ Finset.univ.filter Pg, Nat.card C.supp =
      ∑ k ∈ Finset.Icc 1 (pBeta p₀ β), k * goodMultipoleCount p₀ β lam M ε₀ c k := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter Pg)
      (t := Finset.Icc 1 (pBeta p₀ β)) (g := fun C => Nat.card C.supp)
      (fun C hC => (Finset.mem_filter.mp hC).2.1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [goodMultipoleCount_eq_card,
      mul_card_eq_sum_of_forall _ _ _ fun C hC => (Finset.mem_filter.mp hC).2.1]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pg]
    constructor
    · rintro ⟨⟨-, hsub⟩, rfl⟩; exact ⟨rfl, hsub⟩
    · rintro ⟨rfl, hsub⟩; exact ⟨⟨hk, hsub⟩, rfl⟩
  omega

open scoped Classical in
/-- The good-point bound in Step 1 of the proof of Theorem 2: `k 𝒩_k^good ≤ ε₀^{-α(β)} N λ^{2(k-1)}`. -/
theorem mul_goodMultipoleCount_le (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀) (c : Fin N → ℂ × ℂ) {k : ℕ} (hk1 : 1 ≤ k)
    (hkp : k ≤ pBeta p₀ β) :
    (k : ℝ) * goodMultipoleCount p₀ β lam M ε₀ c k ≤
      ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) := by
  set G := multipoleGraph M lam c
  set d := matched c
  set good := goodPoints p₀ β lam M ε₀ d
  set U := typeOneComplement p₀ β lam ε₀ d
  set S : Finset (Fin N) := U.filter fun u => (goodClass p₀ β lam M ε₀ d u).card = k
  set Q : Finset G.ConnectedComponent :=
    Finset.univ.filter fun C => Nat.card C.supp = k ∧ C.supp ⊆ ↑good
  rw [goodMultipoleCount_eq_card]
  -- the representative of a good multipole of size `k` lies in `S`
  have hrep : ∀ C ∈ Q, Quot.out C ∈ S ∧ Quot.out C ∈ good := by
    intro C hC
    obtain ⟨-, hsize, hsub⟩ := Finset.mem_filter.mp hC
    have hmem : Quot.out C ∈ C.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact connectedComponentMk_out C
    have hg : Quot.out C ∈ good := hsub hmem
    refine ⟨Finset.mem_filter.mpr ⟨mem_typeOneComplement_of_good hg, ?_⟩, hg⟩
    rw [← natCard_supp_of_good hM hg, connectedComponentMk_out C, hsize]
  have hcard : k * Q.card ≤ S.card := by
    let F : G.ConnectedComponent → Finset (Fin N) := fun C =>
      Finset.univ.filter fun v => G.connectedComponentMk v = C
    have hsize : ∀ C ∈ Q, (F C).card = k := fun C hC =>
      (natCard_supp_eq C).symm.trans (Finset.mem_filter.mp hC).2.1
    have hdis : (Q : Set G.ConnectedComponent).PairwiseDisjoint F := by
      intro C _ C' _ hne
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      exact hne ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hv').2)
    have hsub : Q.biUnion F ⊆ S := by
      intro v hv
      obtain ⟨C, hC, hv⟩ := Finset.mem_biUnion.mp hv
      have heq := (Finset.mem_filter.mp hv).2
      have hmem : v ∈ C.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
        exact heq
      have hg := (Finset.mem_filter.mp hC).2.2 hmem
      refine Finset.mem_filter.mpr ⟨mem_typeOneComplement_of_good hg, ?_⟩
      rw [← natCard_supp_of_good hM hg, heq]
      exact (Finset.mem_filter.mp hC).2.1
    calc k * Q.card = ∑ C ∈ Q, (F C).card := by
          rw [Finset.sum_congr rfl hsize, Finset.sum_const, smul_eq_mul, mul_comm]
      _ = (Q.biUnion F).card := (Finset.card_biUnion hdis).symm
      _ ≤ S.card := Finset.card_le_card hsub
  rcases Q.eq_empty_or_nonempty with hQ | ⟨C₀, hC₀⟩
  · rw [show Finset.univ.filter (fun C : G.ConnectedComponent =>
        Nat.card C.supp = k ∧ C.supp ⊆ ↑good) = Q from rfl, hQ, Finset.card_empty,
      Nat.cast_zero, mul_zero]
    have h1 : 0 ≤ ε₀ ^ (-alphaExponent β) := Real.rpow_nonneg hε₀ _
    have h2 : 0 ≤ lam ^ (2 * (k - 1)) := by
      rw [pow_mul]; exact pow_nonneg (sq_nonneg lam) _
    positivity
  · obtain ⟨hvS, hvg⟩ := hrep C₀ hC₀
    set v := Quot.out C₀
    have hvk : (goodClass p₀ β lam M ε₀ d v).card = k := (Finset.mem_filter.mp hvS).2
    have hS : (S.card : ℝ) ≤ ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) := by
      by_contra hlt
      push Not at hlt
      have hv2 : v ∈ badPointsTypeTwo p₀ β lam M ε₀ d := by
        refine mem_badPointsTypeTwo_iff.mpr ⟨(Finset.mem_filter.mp hvS).1, Or.inr ⟨?_, ?_⟩⟩
        · rw [show (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) v).card = k
            from hvk]
          exact Finset.mem_Icc.mpr ⟨hk1, hkp⟩
        · rw [show (multipoleClassOn M lam d (typeOneComplement p₀ β lam ε₀ d) v).card = k
            from hvk]
          exact hlt
      exact (mem_goodPoints_iff.mp hvg).2.1 hv2
    have hc : ((k * Q.card : ℕ) : ℝ) ≤ S.card := Nat.cast_le.mpr hcard
    push_cast at hc
    exact hc.trans hS

/-- The existing count interface, obtained from the good-point bound. -/
theorem goodMultipoleCount_le (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀) (c : Fin N → ℂ × ℂ) {k : ℕ}
    (hk1 : 1 ≤ k) (hkp : k ≤ pBeta p₀ β) :
    (goodMultipoleCount p₀ β lam M ε₀ c k : ℝ) ≤
      ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have h := mul_goodMultipoleCount_le (lam := lam) hM hε₀ c hk1 hkp
  nlinarith [Nat.cast_nonneg (α := ℝ) (goodMultipoleCount p₀ β lam M ε₀ c k)]

/-- **`#{i : r_i ≥ R_{β,λ}} ≤ |I_bad|`** (Step 1 of the proof of Theorem 2): a dipole of length at least
`R_{β,λ} > ε₀ R̄_{β,λ}` is a bad point of type 1 (for `β ≥ 4`, `R_{β,λ} = ∞` and the set is
empty). -/
theorem ncard_le_card_badPoints (hlam : 0 < lam) (hε₀ : ε₀ < 1) (c : Fin N → ℂ × ℂ) :
    {i : Fin N | criticalScale β lam ≤
        ENNReal.ofReal ‖(c i).1 - (c (stableMatching c i)).2‖}.ncard ≤
      (badPoints p₀ β lam M ε₀ (matched c)).card := by
  classical
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard (fun i hi => ?_) (Finset.finite_toSet _)
  simp only [Set.mem_ofPred_eq] at hi
  have h1 : i ∈ badPointsTypeOne p₀ β lam ε₀ (matched c) := by
    unfold badPointsTypeOne
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    left; left
    unfold criticalScale at hi
    unfold truncationScale criticalScale
    split_ifs at hi ⊢ with h4
    · rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hlam.le _)]
      rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hi
      have hpos : 0 < lam ^ (-(β - 2) / (4 - β)) := Real.rpow_pos_of_pos hlam _
      calc ε₀ * lam ^ (-(β - 2) / (4 - β)) < 1 * lam ^ (-(β - 2) / (4 - β)) :=
            mul_lt_mul_of_pos_right hε₀ hpos
        _ = lam ^ (-(β - 2) / (4 - β)) := one_mul _
        _ ≤ _ := hi
    · exact absurd (top_le_iff.mp hi) ENNReal.ofReal_ne_top
  unfold badPoints
  exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ h1))

/-! ### The profile of good multipoles -/

theorem sum_fin_eq_sum_Icc (p : ℕ) (f : ℕ → ℕ) :
    ∑ i : Fin p, ((i : ℕ) + 1) * f ((i : ℕ) + 1) = ∑ k ∈ Finset.Icc 1 p, k * f k := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i + 1) * f (i + 1)) p,
    show Finset.Icc 1 p = Finset.Ico 1 (p + 1) from rfl, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm 1 i]

/-- `∑_{k=1}^{p} k 𝒩_k^good ≤ N`. -/
theorem sum_good_profile_le (c : Fin N → ℂ × ℂ) (p : ℕ) :
    ∑ i : Fin p, ((i : ℕ) + 1) * goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) ≤ N := by
  rw [sum_fin_eq_sum_Icc p (goodMultipoleCount p₀ β lam M ε₀ c)]
  refine le_trans (Finset.sum_le_sum fun k _ => Nat.mul_le_mul_left k
    (goodMultipoleCount_le_multipoleCount c k)) (sum_mul_multipoleCount_le c _)

/-- `∑_{k=1}^{p} k 𝒩_k ≤ N`. -/
theorem sum_profile_le (c : Fin N → ℂ × ℂ) (p : ℕ) :
    ∑ i : Fin p, ((i : ℕ) + 1) * multipoleCount M lam c ((i : ℕ) + 1) ≤ N := by
  rw [sum_fin_eq_sum_Icc p (multipoleCount M lam c)]
  exact sum_mul_multipoleCount_le c _

/-- `N ≤ |I_bad| + ∑_{k=1}^{p} k 𝒩_k^good`, in the indexing of profiles. -/
theorem le_card_badPoints_add_profile (hM : 0 ≤ M) (c : Fin N → ℂ × ℂ) :
    N ≤ (badPoints p₀ β lam M ε₀ (matched c)).card +
      ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) := by
  rw [sum_fin_eq_sum_Icc]
  exact card_le_card_badPoints_add_sum hM c

/-- (5.56) for the good profile, in the indexing of profiles. -/
theorem good_profile_le (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀) (c : Fin N → ℂ × ℂ)
    (i : Fin (pBeta p₀ β)) :
    (goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) : ℝ) ≤
      ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N := by
  have h := goodMultipoleCount_le (lam := lam) hM hε₀ c (k := (i : ℕ) + 1) (by omega) i.2
  rw [Nat.add_sub_cancel] at h
  linarith [h, show ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (i : ℕ)) =
    ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N by ring]

end Components

end TheoremTwo

end MultipoleBKT

end
