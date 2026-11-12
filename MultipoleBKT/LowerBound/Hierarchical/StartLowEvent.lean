/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.StartLowCluster
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Lemma 4.18, Steps 1–2: the multipoles of a configuration with `σ_N = Id`

The proof of Lemma 4.18, Steps 1–2
(proof of Lemma 4.18): on `{σ_N = Id}`, the multipoles are the blocks of the partition `Π_mult` into
connected components of the multipole relation on the dipoles `(x_i, y_i)`.

For `c ∈ startEvent π` (all `𝒜_ij`, every block of `π` connected, no link between blocks):

* `multipoleGraph_eq_of_stableMatching_eq_refl`: with `σ_N = Id` the frozen multipole graph is the
  graph of the multipole relation on `(x_i, y_i)`;
* `reachable_iff_of_mem_startEvent`: `i` and `j` are in the same multipole iff they are in the
  same block of `π` (`Π_mult = π`);
* `multipoleCount_eq_of_mem_startEvent`: `𝒩_k = |{S ∈ π : |S| = k}|`;
* `startEvent_subset`: if `π` has `n_k` blocks of size `k` (`k ≤ p`), then `startEvent π` lies in
  the event `𝒜 ∩ {σ_N = Id}` of (4.24), in the form of the frozen Proposition 4.62;
* `eq_of_mem_startEvent`: the events `startEvent π` of distinct partitions are disjoint.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {N p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- With `σ_N = Id`, the multipole graph is the graph of the multipole relation on the dipoles
`(x_i, y_i)`. -/
theorem multipoleGraph_eq_of_stableMatching_eq_refl {c : Fin N → ℂ × ℂ}
    (h : stableMatching c = Equiv.refl _) :
    multipoleGraph M lam c = SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j) := by
  unfold multipoleGraph
  rw [h]
  simp only [Equiv.refl_apply, Prod.mk.eta]

/-- A set closed under adjacency contains everything reachable from it. -/
theorem of_reachable_of_closed {V : Type*} {G : SimpleGraph V} {T : V → Prop}
    (hclosed : ∀ a b, T a → G.Adj a b → T b) {u v : V} (hu : T u) (h : G.Reachable u v) :
    T v := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hclosed _ _ hu hadj)

theorem stableMatching_eq_refl_of_mem_startEvent {π : Finset (Finset ℕ)} {c : Fin N → ℂ × ℂ}
    (hc : c ∈ startEvent N p₀ β lam M ε₀ π) : stableMatching c = Equiv.refl _ :=
  (stableMatching_eq_refl_iff c).2 hc.2.2.1

/-- **`Π_mult = π`**: for `c ∈ startEvent π`, two dipoles are joined by the multipole relation
iff they lie in the same block of `π`. -/
theorem reachable_iff_of_mem_startEvent {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions (Finset.range N)) {c : Fin N → ℂ × ℂ}
    (hc : c ∈ startEvent N p₀ β lam M ε₀ π) (i j : Fin N) :
    (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j)).Reachable i j ↔
      ∃ S ∈ π, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S := by
  have hπs := (mem_partitions.1 hπ).1
  obtain ⟨-, -, -, hconn, hcross⟩ := hc
  constructor
  · intro h
    obtain ⟨S, hS, hiS⟩ := exists_mem_of_mem_partitions hπ (Finset.mem_range.2 i.2)
    refine ⟨S, hS, hiS, of_reachable_of_closed (T := fun k : Fin N => (k : ℕ) ∈ S)
      (fun a b ha hab => ?_) hiS h⟩
    rw [SimpleGraph.fromRel_adj] at hab
    obtain ⟨hne, hlink⟩ := hab
    obtain ⟨S', hS', hbS'⟩ := exists_mem_of_mem_partitions hπ (Finset.mem_range.2 b.2)
    by_contra hbS
    have hSS' : S ≠ S' := fun h => hbS (h ▸ hbS')
    have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hab' with hlt | hgt
    · have hp := mem_interPairs_of hπs hS hS' hSS' (p := ((a : ℕ), (b : ℕ))) ha hbS' hlt
      refine hcross _ hp ?_
      simp only [finToLabels_apply]
      rcases hlink with h | h
      · exact h
      · exact multipoleLinked_comm.1 h
    · have hp := mem_interPairs_of hπs hS' hS hSS'.symm (p := ((b : ℕ), (a : ℕ))) hbS' ha hgt
      refine hcross _ hp ?_
      simp only [finToLabels_apply]
      rcases hlink with h | h
      · exact multipoleLinked_comm.1 h
      · exact h
  · rintro ⟨S, hS, hiS, hjS⟩
    have hSN : S ⊆ Finset.range N := subset_of_mem_partitions hπ hS
    obtain ⟨-, hreach⟩ := hconn S hS
    obtain ⟨w⟩ := hreach _ hiS _ hjS
    -- lift the walk of `edgeGraph (linkedPairs …)` to `Fin N`
    have hlift : ∀ (u v : ℕ) (w : (edgeGraph (linkedPairs M lam (finToLabels c) S)).Walk u v)
        (a b : Fin N), (a : ℕ) = u → (b : ℕ) = v →
        (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j)).Reachable a b := by
      intro u v w
      induction w with
      | nil =>
        intro a b ha hb
        rw [Fin.ext (ha.trans hb.symm)]
      | cons hadj w' ih =>
        intro a b ha hb
        rename_i x y z
        have hy : y ∈ S := (mem_of_edgeGraph_adj linkedPairs_subset hadj).2
        have hyN : y < N := Finset.mem_range.1 (hSN hy)
        refine SimpleGraph.Reachable.trans ?_ (ih ⟨y, hyN⟩ b rfl hb)
        refine SimpleGraph.Adj.reachable ?_
        rw [edgeGraph_adj] at hadj
        rw [SimpleGraph.fromRel_adj]
        refine ⟨fun h => hadj.1 (ha ▸ congrArg Fin.val h), ?_⟩
        rcases hadj.2 with h | h
        · left
          have := (mem_linkedPairs.1 h).2
          simpa [← ha, finToLabels_apply, finToLabels, hyN] using this
        · right
          have := (mem_linkedPairs.1 h).2
          simpa [← ha, finToLabels_apply, finToLabels, hyN] using this
    exact hlift _ _ w i j rfl rfl

/-- The events of distinct partitions are disjoint. -/
theorem eq_of_mem_startEvent {π π' : Finset (Finset ℕ)} (hπ : π ∈ partitions (Finset.range N))
    (hπ' : π' ∈ partitions (Finset.range N)) {c : Fin N → ℂ × ℂ}
    (hc : c ∈ startEvent N p₀ β lam M ε₀ π) (hc' : c ∈ startEvent N p₀ β lam M ε₀ π') :
    π = π' := by
  have hsame : ∀ i j : Fin N, (∃ S ∈ π, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S) ↔
      ∃ S ∈ π', (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S := fun i j =>
    (reachable_iff_of_mem_startEvent hπ hc i j).symm.trans
      (reachable_iff_of_mem_startEvent hπ' hc' i j)
  have hπs := (mem_partitions.1 hπ).1
  have hπs' := (mem_partitions.1 hπ').1
  -- every block of one partition is a block of the other
  have key : ∀ {σ τ : Finset (Finset ℕ)}, σ ∈ partitions (Finset.range N) →
      τ ∈ partitions (Finset.range N) →
      (∀ i j : Fin N, (∃ S ∈ σ, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S) ↔
        ∃ S ∈ τ, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S) → σ ⊆ τ := by
    intro σ τ hσ hτ hst S hS
    have hσs := (mem_partitions.1 hσ).1
    have hτs := (mem_partitions.1 hτ).1
    obtain ⟨a, ha⟩ := hσs.1 S hS
    have haN : a < N := Finset.mem_range.1 (subset_of_mem_partitions hσ hS ha)
    obtain ⟨T, hT, haT⟩ := exists_mem_of_mem_partitions hτ (Finset.mem_range.2 haN)
    have hST : S = T := by
      ext b
      constructor
      · intro hb
        have hbN : b < N := Finset.mem_range.1 (subset_of_mem_partitions hσ hS hb)
        obtain ⟨T', hT', haT', hbT'⟩ := (hst ⟨a, haN⟩ ⟨b, hbN⟩).1 ⟨S, hS, ha, hb⟩
        rwa [eq_of_isSubpartition hτs hT hT' haT haT']
      · intro hb
        have hbN : b < N := Finset.mem_range.1 (subset_of_mem_partitions hτ hT hb)
        obtain ⟨S', hS', haS', hbS'⟩ := (hst ⟨a, haN⟩ ⟨b, hbN⟩).2 ⟨T, hT, haT, hb⟩
        rwa [eq_of_isSubpartition hσs hS hS' ha haS']
    rw [hST]
    exact hT
  exact Finset.Subset.antisymm (key hπ hπ' hsame) (key hπ' hπ fun i j => (hsame i j).symm)

open scoped Classical in
theorem multipoleCount_eq_card' (c : Fin N → ℂ × ℂ) (k : ℕ) :
    multipoleCount M lam c k =
      (Finset.univ.filter fun C : (multipoleGraph M lam c).ConnectedComponent =>
        Nat.card C.supp = k).card := by
  unfold multipoleCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open scoped Classical in
/-- **`𝒩_k = #_k π`**: for `c ∈ startEvent π`, the number of multipoles of size `k` is the number
of blocks of `π` of size `k`. -/
theorem multipoleCount_eq_of_mem_startEvent {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions (Finset.range N)) {c : Fin N → ℂ × ℂ}
    (hc : c ∈ startEvent N p₀ β lam M ε₀ π) (k : ℕ) :
    multipoleCount M lam c k = (π.filter fun S => S.card = k).card := by
  have hπs := (mem_partitions.1 hπ).1
  set G := multipoleGraph M lam c with hG
  have hG' : G = SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j) :=
    multipoleGraph_eq_of_stableMatching_eq_refl (stableMatching_eq_refl_of_mem_startEvent hc)
  have hreach : ∀ i j : Fin N, G.Reachable i j ↔ ∃ S ∈ π, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S := by
    rw [hG']
    exact reachable_iff_of_mem_startEvent hπ hc
  have hSN : ∀ S ∈ π, S ⊆ Finset.range N := fun S hS => subset_of_mem_partitions hπ hS
  -- the support of the component of `i ∈ S` is `S`
  have hsupp : ∀ S ∈ π, ∀ i : Fin N, (i : ℕ) ∈ S →
      (G.connectedComponentMk i).supp = {j : Fin N | (j : ℕ) ∈ S} := by
    intro S hS i hi
    ext j
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨T, hT, hjT, hiT⟩ := (hreach j i).1 h
      rwa [eq_of_isSubpartition hπs hS hT hi hiT]
    · intro hj
      exact (hreach j i).2 ⟨S, hS, hj, hi⟩
  have hcard : ∀ S ∈ π, ∀ i : Fin N, (i : ℕ) ∈ S → Nat.card (G.connectedComponentMk i).supp =
      S.card := by
    intro S hS i hi
    rw [hsupp S hS i hi, Nat.card_eq_card_toFinset]
    refine Finset.card_bij (fun j _ => (j : ℕ)) (fun j hj => by simpa using hj)
      (fun a _ b _ h => Fin.ext h) fun x hx => ?_
    have hxN : x < N := Finset.mem_range.1 (hSN S hS hx)
    exact ⟨⟨x, hxN⟩, by simpa using hx, rfl⟩
  rw [multipoleCount_eq_card']
  symm
  refine Finset.card_bij (fun S hS => G.connectedComponentMk ⟨(Finset.mem_filter.1 hS).1 |>
      fun h => (hπs.1 S h).choose, Finset.mem_range.1 (hSN S (Finset.mem_filter.1 hS).1
        (hπs.1 S (Finset.mem_filter.1 hS).1).choose_spec)⟩) ?_ ?_ ?_
  · intro S hS
    rw [Finset.mem_filter] at hS ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hcard S hS.1 _ (hπs.1 S hS.1).choose_spec]
    exact hS.2
  · intro S hS S' hS' h
    rw [Finset.mem_filter] at hS hS'
    have h' := SimpleGraph.ConnectedComponent.exact h
    obtain ⟨T, hT, h1, h2⟩ := (hreach _ _).1 h'
    exact (eq_of_isSubpartition hπs hS.1 hT (hπs.1 S hS.1).choose_spec h1).trans
      (eq_of_isSubpartition hπs hS'.1 hT (hπs.1 S' hS'.1).choose_spec h2).symm
  · intro C hC
    revert hC
    refine SimpleGraph.ConnectedComponent.ind (fun i hC => ?_) C
    rw [Finset.mem_filter] at hC
    obtain ⟨S, hS, hiS⟩ := exists_mem_of_mem_partitions hπ (Finset.mem_range.2 i.2)
    refine ⟨S, Finset.mem_filter.2 ⟨hS, ?_⟩, ?_⟩
    · rw [← hcard S hS i hiS]
      exact hC.2
    · rw [SimpleGraph.ConnectedComponent.eq]
      exact (hreach _ _).2 ⟨S, hS, (hπs.1 S hS).choose_spec, hiS⟩

open scoped Classical in
/-- **Steps 1–2**: if `π` has `n_k` blocks of size `k` for `k = 1, …, p`, the event `startEvent π`
lies in `𝒜 ∩ {σ_N = Id}`, `𝒜 = {𝒩_1 = n_1, …, 𝒩_p = n_p} ∩ ⋂ᵢ {|x_i - y_{σ_N(i)}| ≤ ε₀ R̄}`
(eq. (4.24)), written as in the frozen Proposition 4.62. -/
theorem startEvent_subset {p : ℕ} {n : Fin p → ℕ} {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions (Finset.range N))
    (hprof : ∀ i : Fin p, (π.filter fun S => S.card = (i : ℕ) + 1).card = n i) :
    startEvent N p₀ β lam M ε₀ π ⊆
      ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
        {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
          ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
            ε₀ * truncationScale p₀ β lam}) ∩
      {c | stableMatching c = Equiv.refl _} := by
  intro c hc
  have hσ := stableMatching_eq_refl_of_mem_startEvent hc
  refine ⟨⟨fun i _ => hc.1 i, fun i => ?_, fun i => ?_⟩, hσ⟩
  · rw [multipoleCount_eq_of_mem_startEvent hπ hc]
    exact hprof i
  · rw [hσ, Equiv.refl_apply]
    exact hc.2.1 i

end Hierarchical

end MultipoleBKT

end
