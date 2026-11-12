/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Parity.Reduction

/-!
# Eulerian graphs with exceptional vertices (Definition 5.23) and the parity of cuts

The paper: Section 5.6, Definition 5.23, Corollary 5.24, Lemma 5.27 (1),
and the parity step in the proofs of Lemma 5.27 (2) and Corollary 5.34.

Throughout, `X` is a subpartition of `ℕ`, `V_X` is the type `X.biUnion id`, edge sets are simple
graphs on `V_X`, and the marked vertices `V₁ = V_1^∞` form a `Finset` of `V_X` (as in the parity
reduction `MultipoleBKT.Parity.integral_edgeProd_prod_add_mul_eq_sum_relEulerian`).

* `IsRelEulerianOff X V₁ E`, `relEulerianOff X V₁`: `E ∈ Eul^X(V₁)`, i.e. `E ⊆ ℰ^inter(X)` and
  `deg_E(S) + |S ∩ V₁|` is even for every `S ∈ X`; `IsRelEulerianOffConnected X V₁ E`,
  `relEulerianOffConnected X V₁`: `E ∈ Eulc^X(V₁) = Eul^X(V₁) ∩ 𝖤^X`.
* `isRelEulerianOff_empty_iff`: `Eul^X(∅) = Eul^X` (Definition 4.33).
* `coro_5_24_termwise`: Corollary 5.24 termwise (the parity reduction with vertex weights, in which
  the contributing `(E₁, V₁)` are those with `E₁ ∈ Eul^X(V₁)`). The corollary is stated for each term of `𝖪^{+,Z}_{ε₀}`, as in
  `MultipoleBKT.Parity`.
* `cutPairs E U`: the edges of `E` leaving a vertex set `U`, as ordered pairs;
  `even_sum_degree_add_card_cutPairs`: `∑_{v ∈ U} deg_E(v) + |∂U|` is even (handshake on `U`).
* `even_card_cutPairs_add_card_inter`: for `E ∈ Eul^X(V₁)` and a union `U` of blocks of `X`,
  `|∂U| + |U ∩ V₁|` is even. Hence:
  * `lemma_5_27_1`: **Lemma 5.27 (1)**, a block of degree one contains a marked vertex;
  * `odd_card_inter_of_card_cutPairs_eq_one`: a union of blocks left by exactly one edge of `E`
    contains an odd number of marked vertices (the step of Lemma 5.27 (2), and of
    Corollary 5.34, "a leaf block contains an odd number of elements of `V_1^∞`");
  * `even_card_marks`: `|V₁|` is even (Corollary 5.34).
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace CoreForest

open Parity

/-! ### Cuts and the handshake on a vertex set -/

section Cut

variable {V : Type*} [Fintype V] [DecidableEq V] (E : SimpleGraph V) [DecidableRel E.Adj]

/-- The edges of `E` with exactly one endpoint in `U`, as the ordered pairs `(a, b)` with `a ∈ U`,
`b ∉ U`, `ab ∈ E`. -/
def cutPairs (U : Finset V) : Finset (V × V) := (U ×ˢ Uᶜ).filter fun p => E.Adj p.1 p.2

variable {E}

theorem mem_cutPairs {U : Finset V} {p : V × V} :
    p ∈ cutPairs E U ↔ p.1 ∈ U ∧ p.2 ∉ U ∧ E.Adj p.1 p.2 := by
  rw [cutPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_compl, and_assoc]

/-- **Handshake on a vertex set**: `∑_{v ∈ U} deg_E(v) + |∂U|` is even (the degrees inside `U`
count each inner edge twice and each edge leaving `U` once). -/
theorem even_sum_degree_add_card_cutPairs (U : Finset V) :
    Even (∑ v ∈ U, E.degree v + (cutPairs E U).card) := by
  classical
  let EU : SimpleGraph V := E ⊓ SimpleGraph.fromRel fun a b => a ∈ U ∧ b ∈ U
  have hEU : ∀ a b, EU.Adj a b ↔ E.Adj a b ∧ a ∈ U ∧ b ∈ U := by
    intro a b
    simp only [EU, inf_adj, fromRel_adj]
    constructor
    · rintro ⟨h, -, h' | h'⟩
      · exact ⟨h, h'⟩
      · exact ⟨h, h'.2, h'.1⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, h.ne, Or.inl h'⟩
  have hdeg : ∀ v ∈ U, E.degree v = EU.degree v + (Uᶜ.filter (E.Adj v)).card := by
    intro v hv
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter,
      ← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (E.Adj v))
        (fun w => w ∈ U)]
    congr 2
    · ext w
      simp [hEU, hv, and_comm]
    · ext w
      simp [and_comm]
  have hzero : ∀ v ∉ U, EU.degree v = 0 := by
    intro v hv
    rw [← card_neighborFinset_eq_degree, Finset.card_eq_zero, neighborFinset_eq_filter,
      Finset.filter_eq_empty_iff]
    intro w _ hw
    exact hv ((hEU v w).1 hw).2.1
  have hsum : ∑ v, EU.degree v = ∑ v ∈ U, EU.degree v :=
    (Finset.sum_subset (Finset.subset_univ U) fun v _ hv => hzero v hv).symm
  have hcut : (cutPairs E U).card = ∑ v ∈ U, (Uᶜ.filter (E.Adj v)).card := by
    rw [cutPairs, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_add_distrib, ← hsum, sum_degrees_eq_twice_card_edges,
    hcut]
  rw [add_assoc]
  exact (even_two_mul _).add ⟨_, rfl⟩

end Cut

/-! ### Definition 5.23 -/

section Definitions

variable (X : Finset (Finset ℕ))

/-- `E ∈ Eul^X(V₁)`, Eulerian relative to `X` with exceptional vertices `V₁ = V_1^∞`
(Definition 5.23): `E ⊆ ℰ^inter(X)` and, for every `S ∈ X`,
`deg_E(S) + ∑_{i ∈ S} 𝟙_{i ∈ V₁}` is even. -/
def IsRelEulerianOff (V₁ : Finset (X.biUnion id)) (E : SimpleGraph (X.biUnion id)) : Prop :=
  E ≤ interEdges X ∧ ∀ S ∈ X, Even (blockDegree X E S + (blockSet X S ∩ V₁).card)

/-- `E ∈ Eulc^X(V₁) = Eul^X(V₁) ∩ 𝖤^X` (Definition 5.23): `E` is Eulerian
with exceptional vertices `V₁` and connected relative to `X`. -/
def IsRelEulerianOffConnected (V₁ : Finset (X.biUnion id)) (E : SimpleGraph (X.biUnion id)) :
    Prop :=
  IsRelEulerianOff X V₁ E ∧ IsRelConnected X E

open scoped Classical in
/-- The finite set `Eul^X(V₁)`. -/
noncomputable def relEulerianOff (V₁ : Finset (X.biUnion id)) :
    Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (IsRelEulerianOff X V₁)

open scoped Classical in
/-- The finite set `Eulc^X(V₁)`. -/
noncomputable def relEulerianOffConnected (V₁ : Finset (X.biUnion id)) :
    Finset (SimpleGraph (X.biUnion id)) :=
  (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (IsRelEulerianOffConnected X V₁)

variable {X}

theorem mem_relEulerianOff {V₁ : Finset (X.biUnion id)} {E : SimpleGraph (X.biUnion id)} :
    E ∈ relEulerianOff X V₁ ↔ IsRelEulerianOff X V₁ E := by
  simp [relEulerianOff]

theorem mem_relEulerianOffConnected {V₁ : Finset (X.biUnion id)}
    {E : SimpleGraph (X.biUnion id)} :
    E ∈ relEulerianOffConnected X V₁ ↔ IsRelEulerianOffConnected X V₁ E := by
  simp [relEulerianOffConnected]

open scoped Classical in
theorem relEulerianOffConnected_eq (V₁ : Finset (X.biUnion id)) :
    relEulerianOffConnected X V₁ = relEulerianOff X V₁ ∩ relConnected X := by
  ext E
  rw [mem_relEulerianOffConnected, Finset.mem_inter, mem_relEulerianOff, mem_relConnected]
  rfl

/-- With no exceptional vertex, `Eul^X(∅) = Eul^X` (Definition 4.33). -/
theorem isRelEulerianOff_empty_iff {E : SimpleGraph (X.biUnion id)} :
    IsRelEulerianOff X ∅ E ↔ IsRelEulerian X E := by
  simp [IsRelEulerianOff, IsRelEulerian]

end Definitions

/-! ### Corollary 5.24, termwise -/

section Reduction

variable {α : Type*} [MeasureTheory.MeasureSpace α] {σ : α → α}

open MeasureTheory

open scoped Classical in
/-- **Corollary 5.24**, termwise: expanding every
Mayer bond `f_ij = a_ij + b_ij` (odd and even parts) and every external weight
`f_{i∞} = a_{i∞} + b_{i∞}` of a term of `𝖪^{+,Z}_{ε₀}(X)`, only the pairs `(E₁, V₁)` with
`E₁ ∈ Eul^X(V₁)` contribute. This is
`MultipoleBKT.Parity.integral_edgeProd_prod_add_mul_eq_sum_relEulerian` with the contributing
pairs written through Definition 5.23. -/
theorem coro_5_24_termwise {X : Finset (Finset ℕ)} (hσ : Measurable σ)
    (hσσ : Function.Involutive σ) {P : Measure (X.biUnion id → α)}
    (hP : ∀ S ∈ X, MeasurePreserving (flipOn σ (blockSet X S)) P P)
    (E : SimpleGraph (X.biUnion id)) (hE : E ≤ interEdges X)
    {a b : X.biUnion id → X.biUnion id → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    (hb₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j (σ x) y = b i j x y)
    (hb₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j x (σ y) = b i j x y)
    (V : Finset (X.biUnion id)) {u v : X.biUnion id → α → ℝ}
    (hu : ∀ i ∈ V, ∀ x, u i (σ x) = -u i x) (hv : ∀ i ∈ V, ∀ x, v i (σ x) = v i x)
    {G : (X.biUnion id → α) → ℝ} (hG : ∀ S ∈ X, ∀ c, G (flipOn σ (blockSet X S) c) = G c)
    (hint : ∀ E₁ ≤ E, ∀ V₁ ⊆ V, Integrable (fun c => edgeProd E₁ a c * edgeProd (E \ E₁) b c *
      (∏ i ∈ V₁, u i (c i)) * (∏ i ∈ V \ V₁, v i (c i)) * G c) P) :
    ∫ c, edgeProd E (fun i j x y => a i j x y + b i j x y) c *
        (∏ i ∈ V, (u i (c i) + v i (c i))) * G c ∂P =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (· ≤ E),
        ∑ V₁ ∈ V.powerset.filter (fun V₁ => IsRelEulerianOff X V₁ E₁),
          ∫ c, edgeProd E₁ a c * edgeProd (E \ E₁) b c * (∏ i ∈ V₁, u i (c i)) *
            (∏ i ∈ V \ V₁, v i (c i)) * G c ∂P := by
  rw [integral_edgeProd_prod_add_mul_eq_sum_relEulerian hσ hσσ hP E ha₁ ha₂ hb₁ hb₂ V hu hv hG
    hint]
  refine Finset.sum_congr rfl fun E₁ hE₁ => ?_
  have hE₁X : E₁ ≤ interEdges X := (Finset.mem_filter.1 hE₁).2.trans hE
  congr 1
  ext V₁
  simp only [Finset.mem_filter, IsRelEulerianOff, hE₁X, true_and]

end Reduction

/-! ### Parity of cuts for `Eul^X(V₁)` -/

section Parity

variable {X : Finset (Finset ℕ)}

/-- If `∑_{i ∈ S} f(i)` is even for every block `S ∈ X`, the sum of `f` over a union of blocks is
even. -/
theorem even_sum_of_saturated (hX : IsSubpartition X) (f : X.biUnion id → ℕ)
    (hf : ∀ S ∈ X, Even (∑ i ∈ blockSet X S, f i)) {C : Finset (X.biUnion id)}
    (hC : ∀ i ∈ C, ∀ j : X.biUnion id, blockOf hX i = blockOf hX j → j ∈ C) :
    Even (∑ i ∈ C, f i) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := blockOf hX)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.even_sum _ fun S _ => ?_
  by_cases h : ∃ i ∈ C, blockOf hX i = S
  · obtain ⟨i₀, hi₀, hi₀S⟩ := h
    have hset : C.filter (fun i => blockOf hX i = S) = blockSet X S := by
      ext j
      rw [Finset.mem_filter, mem_blockSet, ← blockOf_eq_iff hX]
      exact ⟨fun h => h.2, fun h => ⟨hC i₀ hi₀ j (hi₀S.trans h.symm), h⟩⟩
    rw [hset]
    exact hf S S.2
  · push Not at h
    rw [Finset.filter_false_of_mem h, Finset.sum_empty]
    exact ⟨0, rfl⟩

open scoped Classical in
/-- **Parity of a cut.** For `E ∈ Eul^X(V₁)` and a union `U` of blocks of `X`, the number of edges
of `E` leaving `U` plus the number of marked vertices in `U` is even. -/
theorem even_card_cutPairs_add_card_inter (hX : IsSubpartition X)
    {V₁ : Finset (X.biUnion id)} {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E)
    {U : Finset (X.biUnion id)}
    (hU : ∀ i ∈ U, ∀ j : X.biUnion id, blockOf hX i = blockOf hX j → j ∈ U) :
    Even ((cutPairs E U).card + (U ∩ V₁).card) := by
  have h₁ : Even (∑ i ∈ U, (E.degree i + if i ∈ V₁ then 1 else 0)) := by
    refine even_sum_of_saturated hX _ (fun S hS => ?_) hU
    rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter]
    exact hE.2 S hS
  rw [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter] at h₁
  have h₂ := even_sum_degree_add_card_cutPairs (E := E) U
  have h₃ := h₁.add h₂
  have h₄ : ∑ i ∈ U, E.degree i + (U ∩ V₁).card + (∑ i ∈ U, E.degree i + (cutPairs E U).card) =
      (cutPairs E U).card + (U ∩ V₁).card + 2 * ∑ i ∈ U, E.degree i := by ring
  rw [h₄] at h₃
  exact (Nat.even_add.1 h₃).2 (even_two_mul _)

/-- **Lemma 5.27 (1)**: for `E ∈ Eul^X(V₁)`, a
block `S ∈ X` with `deg_E(S) = 1` contains a vertex of `V₁`, i.e. `S ∈ X_1^∞`. -/
theorem lemma_5_27_1 {V₁ : Finset (X.biUnion id)} {E : SimpleGraph (X.biUnion id)}
    (hE : IsRelEulerianOff X V₁ E) {S : Finset ℕ} (hS : S ∈ X) (hdeg : blockDegree X E S = 1) :
    ∃ i ∈ V₁, (i : ℕ) ∈ S := by
  have h := hE.2 S hS
  rw [hdeg] at h
  obtain ⟨i, hi⟩ : (blockSet X S ∩ V₁).Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    rw [Nat.eq_zero_of_not_pos h0] at h
    exact Nat.not_even_one h
  rw [Finset.mem_inter, mem_blockSet] at hi
  exact ⟨i, hi.2, hi.1⟩

/-- Lemma 5.27 (1) in the paper's form `S ∈ X_1^∞ = {[i]^X : i ∈ V_1^∞}`. -/
theorem lemma_5_27_1' (hX : IsSubpartition X) {V₁ : Finset (X.biUnion id)}
    {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E) {S : X}
    (hdeg : blockDegree X E S = 1) : S ∈ V₁.image (blockOf hX) := by
  obtain ⟨i, hi, hiS⟩ := lemma_5_27_1 hE S.2 hdeg
  exact Finset.mem_image.2 ⟨i, hi, (blockOf_eq_iff hX).2 hiS⟩

open scoped Classical in
/-- **A union of blocks left by exactly one edge contains an odd number of marked vertices**
(proof of Lemma 5.27 (2), Corollary 5.34). -/
theorem odd_card_inter_of_card_cutPairs_eq_one (hX : IsSubpartition X)
    {V₁ : Finset (X.biUnion id)} {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E)
    {U : Finset (X.biUnion id)}
    (hU : ∀ i ∈ U, ∀ j : X.biUnion id, blockOf hX i = blockOf hX j → j ∈ U)
    (hcut : (cutPairs E U).card = 1) : Odd (U ∩ V₁).card := by
  have h := even_card_cutPairs_add_card_inter hX hE hU
  rw [hcut] at h
  rcases Nat.even_or_odd (U ∩ V₁).card with he | ho
  · exact absurd (Nat.even_add.1 h |>.2 he) Nat.not_even_one
  · exact ho

open scoped Classical in
/-- In particular such a union of blocks contains a marked vertex. -/
theorem exists_mem_inter_of_card_cutPairs_eq_one (hX : IsSubpartition X)
    {V₁ : Finset (X.biUnion id)} {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E)
    {U : Finset (X.biUnion id)}
    (hU : ∀ i ∈ U, ∀ j : X.biUnion id, blockOf hX i = blockOf hX j → j ∈ U)
    (hcut : (cutPairs E U).card = 1) : ∃ i ∈ U, i ∈ V₁ := by
  obtain ⟨i, hi⟩ := Finset.card_pos.1 (odd_card_inter_of_card_cutPairs_eq_one hX hE hU hcut).pos
  rw [Finset.mem_inter] at hi
  exact ⟨i, hi⟩

/-- `|V_1^∞|` is even for `E ∈ Eul^X(V₁)` (Corollary 5.34). -/
theorem even_card_marks (hX : IsSubpartition X) {V₁ : Finset (X.biUnion id)}
    {E : SimpleGraph (X.biUnion id)} (hE : IsRelEulerianOff X V₁ E) : Even V₁.card := by
  classical
  have h := even_card_cutPairs_add_card_inter hX hE (U := Finset.univ)
    (fun _ _ j _ => Finset.mem_univ j)
  have hcut : cutPairs E Finset.univ = ∅ := by
    ext p
    simp [mem_cutPairs]
  rwa [hcut, Finset.card_empty, zero_add, Finset.univ_inter] at h

end Parity

end CoreForest

end MultipoleBKT

end
