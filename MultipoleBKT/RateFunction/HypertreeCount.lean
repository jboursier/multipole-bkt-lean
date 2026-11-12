/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Hypertree
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Counting hypertrees with the weight `ω`

For a finite set `A` with `|A| = M` we prove

  `∑_{X ∈ Htrees_n(A), X_1 ∪ ⋯ ∪ X_n = A} ω(X) ≤ n^M (M + n)^n`

(`MultipoleBKT.sum_hypertreeWeight_le`). This is the hypertree count (4.151) of the proof of
Proposition 4.62, Step 3, and the combinatorial input of the convergence of the cluster series in
the rate function (proof of Theorem 2, Step 1).

As in the paper, we root the incidence tree of the hypertree. Choose a root edge `i₀` and, for
every other edge `i`, a parent vertex `π(i) ∈ X_i` shared with an edge strictly closer to `i₀`
in the connection graph; for every vertex `a`, let `ε(a)` be an edge containing `a` that is
closest to `i₀`. The incidences `(i, π(i))` and `(ε(a), a)` (`a ≠ π(i₀)`) are distinct, and
there are `n + M - 1 = ∑ᵢ |X_i|` of them, so they exhaust the incidences
(`MultipoleBKT.exists_root_of_mem_hypertrees`). Hence `X` is determined by `(π, ε)` and every
vertex `a` lies in at most `|π⁻¹(a)| + 1` edges, so `ω(X) ≤ ∏ₐ |π⁻¹(a)|!`. Summing over all pairs
`(π, ε)` gives `n^M ∑_π ∏ₐ |π⁻¹(a)|! = n^M M (M + 1) ⋯ (M + n - 1)`
(`MultipoleBKT.sum_prod_factorial_card_fiber`).
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph
open scoped Nat

section Graph

variable {V : Type*} {G : SimpleGraph V}

/-- In a connected graph, every vertex `v ≠ u` has a neighbour strictly closer to `u`. -/
theorem exists_adj_dist_lt_of_connected (hG : G.Connected) {u v : V} (hvu : v ≠ u) :
    ∃ w, G.Adj v w ∧ G.dist u w < G.dist u v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v u
  cases p with
  | nil => exact absurd rfl hvu
  | cons h q =>
    refine ⟨_, h, ?_⟩
    rw [Walk.length_cons] at hp
    rw [dist_comm (u := u), dist_comm (u := u), ← hp]
    exact Nat.lt_succ_of_le (dist_le q)

end Graph

section Rooting

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- The defining properties of `X ∈ Htrees_n(A)`. -/
theorem hypertrees_props {A : Finset α} {X : Fin n → Finset α} (hX : X ∈ hypertrees n A) :
    (∀ i, X i ⊆ A) ∧ (∀ i, 2 ≤ (X i).card) ∧ (connectionGraph X).Connected ∧
      ((univ.biUnion X).card : ℤ) + n - ∑ i, ((X i).card : ℤ) = 1 := by
  classical
  simp only [hypertrees, mem_filter, Fintype.mem_piFinset, mem_powerset] at hX
  exact ⟨hX.1, hX.2.1, hX.2.2.1, hX.2.2.2⟩

/-- A hypertree `X` with `X_1 ∪ ⋯ ∪ X_n = A` satisfies `∑ᵢ (|X_i| - 1) = |A| - 1`. -/
theorem sum_card_sub_one_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) (hU : univ.biUnion X = A) :
    ∑ i, ((X i).card - 1) = A.card - 1 := by
  obtain ⟨-, h2, -, hcount⟩ := hypertrees_props hX
  rw [hU] at hcount
  have hsum : ((∑ i, ((X i).card - 1) : ℕ) : ℤ) = ∑ i, ((X i).card : ℤ) - n := by
    rw [Nat.cast_sum]
    rw [sum_congr rfl fun i _ => Nat.cast_sub (by have := h2 i; omega : 1 ≤ (X i).card)]
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, Nat.cast_one, nsmul_eq_mul,
      mul_one]
  have hA : 1 ≤ A.card := by
    have : (1 : ℤ) ≤ A.card := by
      have : ∀ i ∈ (univ : Finset (Fin n)), (2 : ℤ) ≤ (X i).card := fun i _ => by
        exact_mod_cast h2 i
      have := sum_le_sum this
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    exact_mod_cast this
  have : ((A.card - 1 : ℕ) : ℤ) = A.card - 1 := by push_cast [Nat.cast_sub hA]; ring
  omega

/-- A hypertree `X ∈ Htrees_n(A)` with `X_1 ∪ ⋯ ∪ X_n = A` has `n + 1 ≤ |A|`. -/
theorem add_one_le_card_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) (hU : univ.biUnion X = A) : n + 1 ≤ A.card := by
  obtain ⟨-, h2, -, hcount⟩ := hypertrees_props hX
  rw [hU] at hcount
  have : ∀ i ∈ (univ : Finset (Fin n)), (2 : ℤ) ≤ (X i).card := fun i _ => by exact_mod_cast h2 i
  have := sum_le_sum this
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have : ((n : ℤ) + 1) ≤ A.card := by linarith
  exact_mod_cast this

/-- **Rooting of a hypertree.** For `X ∈ Htrees_n(A)` there are a parent vertex `π(i) ∈ X_i` of
every edge and an edge `ε(a) ∋ a` for every vertex `a ∈ ⋃ᵢ X_i` such that every incidence
`a ∈ X_i` with `a ≠ π(i)` has `i = ε(a)`. -/
theorem exists_root_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) :
    ∃ π : Fin n → α, ∃ ε : α → Fin n, (∀ i, π i ∈ X i) ∧
      (∀ a ∈ univ.biUnion X, a ∈ X (ε a)) ∧ ∀ i a, a ∈ X i → π i ≠ a → ε a = i := by
  classical
  obtain ⟨-, hcard2, hconn, hcount⟩ := hypertrees_props hX
  obtain ⟨i₀⟩ := hconn.nonempty
  set G := connectionGraph X
  set U := univ.biUnion X
  let ℓ : Fin n → ℕ := fun i => G.dist i₀ i
  obtain ⟨r, hr⟩ : (X i₀).Nonempty := card_pos.mp (by have := hcard2 i₀; omega)
  have key : ∀ i, ∃ a ∈ X i, (i = i₀ → a = r) ∧ (i ≠ i₀ → ∃ j, a ∈ X j ∧ ℓ j < ℓ i) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      exact ⟨r, hr, fun _ => rfl, fun h => absurd rfl h⟩
    · obtain ⟨j, hij, hj⟩ := exists_adj_dist_lt_of_connected hconn hi
      obtain ⟨-, a, hai, haj⟩ := connectionGraph_adj.mp hij
      exact ⟨a, hai, fun h => absurd h hi, fun _ => ⟨j, haj, hj⟩⟩
  choose π hπX hπ₀ hπ using key
  have key2 : ∀ a, ∃ i, a ∈ U → a ∈ X i ∧ ∀ i', a ∈ X i' → ℓ i ≤ ℓ i' := by
    intro a
    by_cases ha : a ∈ U
    · obtain ⟨i, hi, hmin⟩ := (incidence X a).exists_min_image ℓ (incidence_nonempty ha)
      exact ⟨i, fun _ => ⟨mem_incidence.mp hi, fun i' hi' => hmin i' (mem_incidence.mpr hi')⟩⟩
    · exact ⟨i₀, fun h => absurd h ha⟩
  choose ε hε using key2
  refine ⟨π, ε, hπX, fun a ha => (hε a ha).1, ?_⟩
  -- the incidences, and the two families of tree incidences
  let I : Finset (Σ _ : Fin n, α) := univ.sigma X
  let P : Finset (Σ _ : Fin n, α) := univ.image fun i => ⟨i, π i⟩
  let Q : Finset (Σ _ : Fin n, α) := (U.erase r).image fun a => ⟨ε a, a⟩
  have hrU : r ∈ U := mem_biUnion.mpr ⟨i₀, mem_univ _, hr⟩
  have hPI : P ⊆ I := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_image.mp hx
    exact mem_sigma.mpr ⟨mem_univ _, hπX i⟩
  have hQI : Q ⊆ I := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    exact mem_sigma.mpr ⟨mem_univ _, (hε a (mem_of_mem_erase ha)).1⟩
  have hPcard : P.card = n := by
    rw [card_image_of_injective, card_univ, Fintype.card_fin]
    intro i j h
    simp only [Sigma.mk.inj_iff] at h
    exact h.1
  have hQcard : Q.card = U.card - 1 := by
    rw [card_image_of_injective, card_erase_of_mem hrU]
    intro a b h
    simp only [Sigma.mk.inj_iff, heq_iff_eq] at h
    exact h.2
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro x hxP hxQ
    obtain ⟨i, -, rfl⟩ := mem_image.mp hxP
    obtain ⟨a, ha, h⟩ := mem_image.mp hxQ
    simp only [Sigma.mk.inj_iff, heq_iff_eq] at h
    obtain ⟨h1, rfl⟩ := h
    obtain ⟨hne, haU⟩ := mem_erase.mp ha
    by_cases hi : i = i₀
    · exact hne (hπ₀ i hi)
    · obtain ⟨j, hj, hlt⟩ := hπ i hi
      have := (hε (π i) haU).2 j hj
      rw [h1] at this
      omega
  have hIcard : I.card = U.card + n - 1 := by
    have h1 : (I.card : ℤ) = ∑ i, ((X i).card : ℤ) := by
      simp only [I, card_sigma, Nat.cast_sum]
    have h2 : 1 ≤ U.card := card_pos.mpr ⟨r, hrU⟩
    omega
  have hPQI : P ∪ Q = I := by
    refine eq_of_subset_of_card_le (union_subset hPI hQI) ?_
    rw [card_union_of_disjoint hPQ, hPcard, hQcard, hIcard]
    have h2 : 1 ≤ U.card := card_pos.mpr ⟨r, hrU⟩
    omega
  intro i a ha hne
  have hx : (⟨i, a⟩ : Σ _ : Fin n, α) ∈ P ∪ Q := by
    rw [hPQI]
    exact mem_sigma.mpr ⟨mem_univ _, ha⟩
  rcases mem_union.mp hx with hxP | hxQ
  · obtain ⟨j, -, h⟩ := mem_image.mp hxP
    simp only [Sigma.mk.inj_iff, heq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd rfl hne
  · obtain ⟨b, -, h⟩ := mem_image.mp hxQ
    simp only [Sigma.mk.inj_iff, heq_iff_eq] at h
    obtain ⟨h1, rfl⟩ := h
    exact h1

end Rooting

section FiberCount

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [Fintype β] in
private theorem card_filter_cons_eq {n : ℕ} (b : β) (π : Fin n → β) (c : β) :
    (univ.filter fun i : Fin (n + 1) => (Fin.cons b π : Fin (n + 1) → β) i = c).card =
      (univ.filter fun i => π i = c).card + if b = c then 1 else 0 := by
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

private theorem prod_factorial_cons {n : ℕ} (b : β) (π : Fin n → β) :
    ∏ c, (univ.filter fun i : Fin (n + 1) =>
        (Fin.cons b π : Fin (n + 1) → β) i = c).card.factorial =
      (∏ c, (univ.filter fun i => π i = c).card.factorial) *
        ((univ.filter fun i => π i = b).card + 1) := by
  simp_rw [card_filter_cons_eq]
  have : ∀ c, ((univ.filter fun i => π i = c).card + if b = c then 1 else 0) ! =
      (univ.filter fun i => π i = c).card.factorial *
        if b = c then (univ.filter fun i => π i = c).card + 1 else 1 := by
    intro c
    split_ifs
    · rw [Nat.factorial_succ, mul_comm]
    · rw [add_zero, mul_one]
  simp_rw [this, prod_mul_distrib, prod_ite_eq]
  simp only [mem_univ, ite_true]

/-- `∑_{π : [n] → β} ∏_b |π⁻¹(b)|! = M (M + 1) ⋯ (M + n - 1)` with `M = |β|`. -/
theorem sum_prod_factorial_card_fiber (n : ℕ) :
    ∑ π : Fin n → β, ∏ b, (univ.filter fun i => π i = b).card.factorial =
      ∏ j ∈ range n, (Fintype.card β + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type, prod_range_succ, ← ih,
      sum_mul]
    simp only [Fin.consEquiv_apply]
    simp_rw [prod_factorial_cons]
    rw [sum_comm]
    refine sum_congr rfl fun π _ => ?_
    rw [← mul_sum, sum_add_distrib, ← card_eq_sum_card_fiberwise (fun _ _ => mem_univ _),
      sum_const, card_univ, card_univ, Fintype.card_fin, smul_eq_mul, mul_one, add_comm n]

end FiberCount

section WeightBound

variable {α : Type*} [DecidableEq α] {n : ℕ}

private theorem card_incidence_le {X : Fin n → Finset α} (π : Fin n → α) (ε : α → Fin n)
    (hroot : ∀ i a, a ∈ X i → π i ≠ a → ε a = i) (a : α) :
    (univ.filter fun i => a ∈ X i).card ≤ (univ.filter fun i => π i = a).card + 1 := by
  calc (univ.filter fun i => a ∈ X i).card
      ≤ (insert (ε a) (univ.filter fun i => π i = a)).card := by
        refine card_le_card fun i hi => ?_
        rw [mem_filter] at hi
        rw [mem_insert, mem_filter]
        by_cases h : π i = a
        · exact Or.inr ⟨mem_univ _, h⟩
        · exact Or.inl (hroot i a hi.2 h).symm
    _ ≤ _ := card_insert_le _ _

/-- **The weighted hypertree count.** For a finite set `A`,
`∑_{X ∈ Htrees_n(A), X_1 ∪ ⋯ ∪ X_n = A} ω(X) ≤ n^{|A|} (|A| + n)^n`. -/
theorem sum_hypertreeWeight_le (A : Finset α) (n : ℕ) :
    ∑ X ∈ (hypertrees n A).filter (fun X => univ.biUnion X = A), hypertreeWeight X ≤
      n ^ A.card * (A.card + n) ^ n := by
  classical
  set S := (hypertrees n A).filter (fun X => univ.biUnion X = A)
  let w : (Fin n → A) × (A → Fin n) → ℕ := fun c =>
    ∏ a : A, (univ.filter fun i => c.1 i = a).card.factorial
  have hcode : ∀ X ∈ S, ∃ c : (Fin n → A) × (A → Fin n),
      (∀ i (a : A), (a : α) ∈ X i ↔ (c.1 i = a ∨ c.2 a = i)) ∧ hypertreeWeight X ≤ w c := by
    intro X hXS
    obtain ⟨hX, hU⟩ := mem_filter.mp hXS
    have hXA : ∀ i, X i ⊆ A := fun i => hU ▸ subset_biUnion_of_mem X (mem_univ i)
    obtain ⟨π, ε, hπX, hεX, hroot⟩ := exists_root_of_mem_hypertrees hX
    refine ⟨(fun i => ⟨π i, hXA i (hπX i)⟩, fun a => ε a), fun i a => ?_, ?_⟩
    · constructor
      · intro ha
        by_cases h : π i = a
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (hroot i a ha h)
      · rintro (h | h)
        · rw [← Subtype.ext_iff.mp h]
          exact hπX i
        · simp only at h
          rw [← h]
          exact hεX a (hU ▸ a.2)
    · rw [hypertreeWeight, hU, ← prod_coe_sort A]
      refine prod_le_prod fun a _ => Nat.factorial_le ?_
      have h1 := card_incidence_le π ε hroot (a : α)
      have h2 : (univ.filter fun i => π i = (a : α)).card =
          (univ.filter fun i => (⟨π i, hXA i (hπX i)⟩ : A) = a).card := by
        congr 1
        ext i
        simp only [mem_filter, mem_univ, true_and, Subtype.ext_iff]
      dsimp only
      omega
  rcases S.eq_empty_or_nonempty with hS | ⟨X₀, hX₀⟩
  · rw [hS, sum_empty]
    exact Nat.zero_le _
  have : Nonempty ((Fin n → A) × (A → Fin n)) := ⟨(hcode X₀ hX₀).choose⟩
  choose! code hcode1 hcode2 using hcode
  have hinj : Set.InjOn code (S : Set (Fin n → Finset α)) := by
    intro X hX Y hY hXY
    have hXA : ∀ i, X i ⊆ A := fun i =>
      (mem_filter.mp hX).2 ▸ subset_biUnion_of_mem X (mem_univ i)
    have hYA : ∀ i, Y i ⊆ A := fun i =>
      (mem_filter.mp hY).2 ▸ subset_biUnion_of_mem Y (mem_univ i)
    funext i
    ext a
    constructor
    · intro ha
      have h := (hcode1 X hX i ⟨a, hXA i ha⟩).mp ha
      rw [hXY] at h
      exact (hcode1 Y hY i ⟨a, hXA i ha⟩).mpr h
    · intro ha
      have h := (hcode1 Y hY i ⟨a, hYA i ha⟩).mp ha
      rw [← hXY] at h
      exact (hcode1 X hX i ⟨a, hYA i ha⟩).mpr h
  have hall : ∑ c : (Fin n → A) × (A → Fin n), w c =
      n ^ A.card * ∏ j ∈ range n, (A.card + j) := by
    rw [Fintype.sum_prod_type]
    simp only [w, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      smul_eq_mul]
    rw [← mul_sum, sum_prod_factorial_card_fiber, Fintype.card_coe]
  calc ∑ X ∈ S, hypertreeWeight X
      ≤ ∑ X ∈ S, w (code X) := sum_le_sum fun X hX => hcode2 X hX
    _ = ∑ c ∈ S.image code, w c := (sum_image hinj).symm
    _ ≤ ∑ c : (Fin n → A) × (A → Fin n), w c := sum_le_sum_of_subset (subset_univ _)
    _ = n ^ A.card * ∏ j ∈ range n, (A.card + j) := hall
    _ ≤ n ^ A.card * (A.card + n) ^ n := by
      refine Nat.mul_le_mul_left _ ?_
      calc ∏ j ∈ range n, (A.card + j) ≤ (A.card + n) ^ (range n).card :=
            prod_le_pow_card _ _ _ fun j hj => by
              have := mem_range.mp hj
              omega
        _ = (A.card + n) ^ n := by rw [card_range]

end WeightBound

end MultipoleBKT

end
