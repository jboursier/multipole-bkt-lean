/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Parity.Eulerian

/-!
# Reduction to Eulerian graphs (Corollary 4.34, general form)

Corollary 4.34, equation (4.61), and the parity argument of Lemma 4.32:
 every bond `f_ij = a_ij + b_ij` of an edge set `E` is split into an odd
and an even part, the product `∏_{ij ∈ E} f_ij` is expanded over the subsets `E₁ ⊆ E` (the edges
carrying `a`), and the terms in which `E₁` is not Eulerian relative to the blocks vanish by
Lemma 4.32.

* `edgeProd_add_eq_sum`:
  `∏_{ij ∈ E} (a_ij + b_ij) = ∑_{E₁ ⊆ E} ∏_{ij ∈ E₁} a_ij ∏_{ij ∈ E ∖ E₁} b_ij`;
* `integral_edgeProd_add_mul_eq_sum` (general blocks `blk k`, `k ∈ 𝔅`) and
  `integral_edgeProd_add_mul_eq_sum_relEulerian` (the blocks of a subpartition `X`, the form of
  (4.61)): if the reference measure and the remaining factor `G` are invariant under the
  reversal of each block, `a_ij` odd and `b_ij` even in both dipoles, then
  `∫ ∏_E (a + b) G = ∑_{E₁ ⊆ E, E₁ ∈ Eul^X} ∫ ∏_{E₁} a ∏_{E ∖ E₁} b G`;
* `integral_edgeProd_prod_add_mul_eq_sum`, `integral_edgeProd_prod_add_mul_eq_sum_relEulerian`:
  the same with odd/even vertex weights `u_i + v_i` (`f_{i∞} = a_{i∞} + b_{i∞}` in Section 5); the
  contributing pairs `(E₁, V₁)` satisfy `deg_{E₁}(S) + |S ∩ V₁|` even (`Eul^X(V₁)`,
  Definition 5.23), the form of Corollary 5.24;
* `sum_sum_sdiff_eq_sum_sum`: the reindexing `(E, E₁) ↦ (E_{1}, E_{2} = E ∖ E₁)` from the sum over
  `E ∈ 𝒮`, `E₁ ⊆ E` to the sum over `E₁` and `E₂` with `E₁ ∩ E₂ = ∅`, `E₁ ∪ E₂ ∈ 𝒮`, as written
  in (4.61).

Applied to every term `(n, X₁, …, Xₙ, E₁, …, Eₙ, F)` of the activity (4.21), with
`E = E₁ ∪ ⋯ ∪ Eₙ` (on `V_X`) and `G = ∏_{ij ∈ ∪ ℰ^inter(X_l)} 𝟙_{𝓑_ij^c} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})`
times the density, this gives (4.61): the condition `E₁ ∈ Eul^X` on `E₁ ⊆ E₁ ∪ ⋯ ∪ Eₙ` says
exactly that each `E_{l,1} = E₁ ∩ E_l` is in `Eul^{X_l}`, since an edge of `E_l` only meets blocks
of `X_l` (`MultipoleBKT.Parity.isRelEulerian_iff_forall_group`). The instance for the frozen
multipole activity `𝖪^mult = 𝖪^0_∞` is in `MultipoleBKT.LowerBound.Parity.Hierarchical`. The
reduction for `𝖪^-_{ε₀}` is stated here termwise, as used in the proofs of
Propositions 4.23 and 4.27.
-/

@[expose] public section

open MeasureTheory Finset SimpleGraph

namespace MultipoleBKT

namespace Parity

/-! ### Expanding a product over the edges -/

section Expand

variable {ι α : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]

open scoped Classical

/-- The ordered pairs `(i, j)`, `i < j`, of the edges of `E`. -/
noncomputable def edgePairs (E : SimpleGraph ι) : Finset (ι × ι) :=
  Finset.univ.filter fun p => p.1 < p.2 ∧ E.Adj p.1 p.2

/-- The graph whose edges are the pairs of `t`. -/
def pairGraph (t : Finset (ι × ι)) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => (i, j) ∈ t

omit [DecidableEq ι] in
theorem mem_edgePairs {E : SimpleGraph ι} {p : ι × ι} :
    p ∈ edgePairs E ↔ p.1 < p.2 ∧ E.Adj p.1 p.2 := by
  simp [edgePairs]

omit [DecidableEq ι] in
theorem edgeProd_eq_prod_edgePairs (E : SimpleGraph ι) (f : ι → ι → α → α → ℝ) (c : ι → α) :
    edgeProd E f c = ∏ p ∈ edgePairs E, f p.1 p.2 (c p.1) (c p.2) := by
  rw [edgePairs, Finset.prod_filter, Fintype.prod_prod_type]
  rfl

omit [DecidableEq ι] in
theorem edgePairs_mono {E E' : SimpleGraph ι} (h : E ≤ E') : edgePairs E ⊆ edgePairs E' :=
  fun _ hp => mem_edgePairs.2 ⟨(mem_edgePairs.1 hp).1, h (mem_edgePairs.1 hp).2⟩

theorem edgePairs_sdiff (E E₁ : SimpleGraph ι) :
    edgePairs (E \ E₁) = edgePairs E \ edgePairs E₁ := by
  ext p
  simp only [Finset.mem_sdiff, mem_edgePairs, sdiff_adj]
  tauto

omit [DecidableEq ι] in
theorem pairGraph_edgePairs (E : SimpleGraph ι) : pairGraph (edgePairs E) = E := by
  ext i j
  simp only [pairGraph, fromRel_adj, mem_edgePairs]
  constructor
  · rintro ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩
    · exact h
    · exact h.symm
  · intro h
    refine ⟨h.ne, ?_⟩
    rcases lt_or_gt_of_ne h.ne with hij | hij
    · exact Or.inl ⟨hij, h⟩
    · exact Or.inr ⟨hij, h.symm⟩

omit [DecidableEq ι] in
theorem edgePairs_pairGraph {t : Finset (ι × ι)} (ht : ∀ p ∈ t, p.1 < p.2) :
    edgePairs (pairGraph t) = t := by
  ext p
  rw [mem_edgePairs, pairGraph, fromRel_adj]
  constructor
  · rintro ⟨hlt, -, h | h⟩
    · exact h
    · exact absurd (ht _ h) (not_lt.2 hlt.le)
  · intro h
    exact ⟨ht p h, (ht p h).ne, Or.inl h⟩

/-- **Expansion of a product of bonds**:
`∏_{ij ∈ E} (a_ij + b_ij) = ∑_{E₁ ⊆ E} ∏_{ij ∈ E₁} a_ij ∏_{ij ∈ E ∖ E₁} b_ij`. -/
theorem edgeProd_add_eq_sum (E : SimpleGraph ι) (a b : ι → ι → α → α → ℝ) (c : ι → α) :
    edgeProd E (fun i j x y => a i j x y + b i j x y) c =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph ι)).filter (· ≤ E),
        edgeProd E₁ a c * edgeProd (E \ E₁) b c := by
  rw [edgeProd_eq_prod_edgePairs, Finset.prod_add]
  refine Finset.sum_nbij' pairGraph edgePairs (fun t ht => ?_) (fun E₁ hE₁ => ?_)
    (fun t ht => ?_) (fun E₁ hE₁ => ?_) (fun t ht => ?_)
  · rw [Finset.mem_powerset] at ht
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i j hij => ?_⟩
    rw [pairGraph, fromRel_adj] at hij
    rcases hij.2 with h | h
    · exact (mem_edgePairs.1 (ht h)).2
    · exact (mem_edgePairs.1 (ht h)).2.symm
  · exact Finset.mem_powerset.2 (edgePairs_mono (Finset.mem_filter.1 hE₁).2)
  · rw [Finset.mem_powerset] at ht
    exact edgePairs_pairGraph fun p hp => (mem_edgePairs.1 (ht hp)).1
  · exact pairGraph_edgePairs E₁
  · rw [Finset.mem_powerset] at ht
    have ht' : edgePairs (pairGraph t) = t :=
      edgePairs_pairGraph fun p hp => (mem_edgePairs.1 (ht hp)).1
    rw [edgeProd_eq_prod_edgePairs, edgeProd_eq_prod_edgePairs, edgePairs_sdiff, ht']

end Expand

/-! ### Reindexing by `(E₁, E₂)` -/

section Reindex

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
/-- The reindexing of (4.61): the sum over `E ∈ 𝒮` and `E₁ ⊆ E` with `P(E₁)` of
`F(E₁, E ∖ E₁)` is the sum over `E₁` with `P(E₁)` and over `E₂` with `E₁ ∩ E₂ = ∅`,
`E₁ ∪ E₂ ∈ 𝒮` of `F(E₁, E₂)`. -/
theorem sum_sum_sdiff_eq_sum_sum {M : Type*} [AddCommMonoid M] (𝒮 : Finset (SimpleGraph V))
    (P : SimpleGraph V → Prop) (F : SimpleGraph V → SimpleGraph V → M) :
    ∑ E ∈ 𝒮, ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph V)).filter (fun E₁ => E₁ ≤ E ∧ P E₁),
        F E₁ (E \ E₁) =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph V)).filter P,
        ∑ E₂ ∈ (Finset.univ : Finset (SimpleGraph V)).filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ⊔ E₂ ∈ 𝒮), F E₁ E₂ := by
  rw [Finset.sum_comm' (t' := (Finset.univ : Finset (SimpleGraph V)).filter P)
    (s' := fun E₁ => 𝒮.filter (E₁ ≤ ·))]
  · refine Finset.sum_congr rfl fun E₁ _ => ?_
    refine Finset.sum_nbij' (fun E => E \ E₁) (fun E₂ => E₁ ⊔ E₂) (fun E hE => ?_)
      (fun E₂ hE₂ => ?_) (fun E hE => ?_) (fun E₂ hE₂ => ?_) (fun E hE => rfl)
    · rw [Finset.mem_filter] at hE ⊢
      refine ⟨Finset.mem_univ _, disjoint_sdiff_self_left.symm, ?_⟩
      rw [sup_sdiff_cancel_right hE.2]
      exact hE.1
    · rw [Finset.mem_filter] at hE₂ ⊢
      exact ⟨hE₂.2.2, le_sup_left⟩
    · rw [Finset.mem_filter] at hE
      exact sup_sdiff_cancel_right hE.2
    · rw [Finset.mem_filter] at hE₂
      exact hE₂.2.1.sup_sdiff_cancel_left
  · intro E E₁
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

end Reindex

/-! ### The parity reduction -/

section Reduction

variable {ι α : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] [MeasurableSpace α]
  {σ : α → α}

open scoped Classical

/-- **The parity reduction** (the argument of Corollary 4.34), general form. Let `P` be a measure
on configurations `ι → α` invariant under the reversal `flipOn σ (blk k)` of each block
`blk k`, `k ∈ 𝔅`; let `a_ij` be odd and `b_ij` even in both variables, and `G` invariant under
the reversal of each block. If every term is integrable, then
`∫ ∏_{ij ∈ E} (a_ij + b_ij) G dP
  = ∑_{E₁ ⊆ E Eulerian} ∫ ∏_{ij ∈ E₁} a_ij ∏_{ij ∈ E ∖ E₁} b_ij G dP`,
where `E₁` is Eulerian when `∑_{i ∈ blk k} deg_{E₁}(i)` is even for every `k ∈ 𝔅`. -/
theorem integral_edgeProd_add_mul_eq_sum {κ : Type*} (hσ : Measurable σ)
    (hσσ : Function.Involutive σ) {P : Measure (ι → α)} (𝔅 : Finset κ) (blk : κ → Finset ι)
    (hP : ∀ k ∈ 𝔅, MeasurePreserving (flipOn σ (blk k)) P P) (E : SimpleGraph ι)
    {a b : ι → ι → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    (hb₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j (σ x) y = b i j x y)
    (hb₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j x (σ y) = b i j x y)
    {G : (ι → α) → ℝ} (hG : ∀ k ∈ 𝔅, ∀ c, G (flipOn σ (blk k) c) = G c)
    (hint : ∀ E₁ ≤ E, Integrable (fun c => edgeProd E₁ a c * edgeProd (E \ E₁) b c * G c) P) :
    ∫ c, edgeProd E (fun i j x y => a i j x y + b i j x y) c * G c ∂P =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph ι)).filter
          (fun E₁ => E₁ ≤ E ∧ ∀ k ∈ 𝔅, Even (∑ i ∈ blk k, E₁.degree i)),
        ∫ c, edgeProd E₁ a c * edgeProd (E \ E₁) b c * G c ∂P := by
  simp_rw [edgeProd_add_eq_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun E₁ hE₁ => hint E₁ (Finset.mem_filter.1 hE₁).2]
  symm
  refine Finset.sum_subset (fun E₁ h => ?_) (fun E₁ h₂ h₁ => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 h).2.1⟩
  · rw [Finset.mem_filter] at h₁ h₂
    have hEul : ¬ ∀ k ∈ 𝔅, Even (∑ i ∈ blk k, E₁.degree i) := fun h => h₁ ⟨h₂.1, h₂.2, h⟩
    push Not at hEul
    obtain ⟨k, hk, hodd⟩ := hEul
    rw [Nat.not_even_iff_odd] at hodd
    have hle : E₁ ≤ E := h₂.2
    simp_rw [mul_assoc]
    refine integral_edgeProd_mul_eq_zero hσ hσσ (hP k hk)
      (fun i j hij h => ha₁ i j hij (hle h)) (fun i j hij h => ha₂ i j hij (hle h))
      (fun c => ?_) hodd
    have hsd : E \ E₁ ≤ E := sdiff_le
    rw [edgeProd_flipOn_of_even (E \ E₁) (fun i j hij h => hb₁ i j hij (hsd h))
      (fun i j hij h => hb₂ i j hij (hsd h)), hG k hk]

/-- **The parity reduction for a subpartition** (Corollary 4.34, eq. (4.61), termwise): for a
subpartition `X`, `E ⊆ ℰ^inter(X)`, a measure on configurations of `V_X` invariant under the
reversal of the dipoles of each block, `a_ij` odd and `b_ij` even in both dipoles, and `G`
invariant under these reversals,
`∫ ∏_{ij ∈ E} (a_ij + b_ij) G
  = ∑_{E₁ ⊆ E, E₁ ∈ Eul^X} ∫ ∏_{ij ∈ E₁} a_ij ∏_{ij ∈ E ∖ E₁} b_ij G`. -/
theorem integral_edgeProd_add_mul_eq_sum_relEulerian {X : Finset (Finset ℕ)} (hσ : Measurable σ)
    (hσσ : Function.Involutive σ) {P : Measure (X.biUnion id → α)}
    (hP : ∀ S ∈ X, MeasurePreserving (flipOn σ (blockSet X S)) P P)
    {E : SimpleGraph (X.biUnion id)} (hE : E ≤ interEdges X)
    {a b : X.biUnion id → X.biUnion id → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    (hb₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j (σ x) y = b i j x y)
    (hb₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j x (σ y) = b i j x y)
    {G : (X.biUnion id → α) → ℝ} (hG : ∀ S ∈ X, ∀ c, G (flipOn σ (blockSet X S) c) = G c)
    (hint : ∀ E₁ ≤ E, Integrable (fun c => edgeProd E₁ a c * edgeProd (E \ E₁) b c * G c) P) :
    ∫ c, edgeProd E (fun i j x y => a i j x y + b i j x y) c * G c ∂P =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter
          (fun E₁ => E₁ ≤ E ∧ IsRelEulerian X E₁),
        ∫ c, edgeProd E₁ a c * edgeProd (E \ E₁) b c * G c ∂P := by
  rw [integral_edgeProd_add_mul_eq_sum hσ hσσ X (blockSet X) hP E ha₁ ha₂ hb₁ hb₂ hG hint]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext E₁
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, IsRelEulerian, blockDegree_eq_sum]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h1.trans hE, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩

/-- **The parity reduction with vertex weights** (the argument of Corollary 5.24, Section 5.6),
general form: in addition to the bonds, every vertex `i ∈ V` carries a weight `u_i + v_i` with
`u_i` odd and `v_i` even (in Section 5: `f_{i∞} = a_{i∞} + b_{i∞}`, Definition 5.21). Expanding,
`∫ ∏_{ij ∈ E} (a_ij + b_ij) ∏_{i ∈ V} (u_i + v_i) G
= ∑_{E₁ ⊆ E} ∑_{V₁ ⊆ V} ∫ ∏_{E₁} a ∏_{E ∖ E₁} b ∏_{V₁} u ∏_{V ∖ V₁} v G`, and only the pairs
`(E₁, V₁)` with `∑_{i ∈ blk k} deg_{E₁}(i) + |blk k ∩ V₁|` even for every `k ∈ 𝔅` contribute. -/
theorem integral_edgeProd_prod_add_mul_eq_sum {κ : Type*} (hσ : Measurable σ)
    (hσσ : Function.Involutive σ) {P : Measure (ι → α)} (𝔅 : Finset κ) (blk : κ → Finset ι)
    (hP : ∀ k ∈ 𝔅, MeasurePreserving (flipOn σ (blk k)) P P) (E : SimpleGraph ι)
    {a b : ι → ι → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    (hb₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j (σ x) y = b i j x y)
    (hb₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j x (σ y) = b i j x y)
    (V : Finset ι) {u v : ι → α → ℝ} (hu : ∀ i ∈ V, ∀ x, u i (σ x) = -u i x)
    (hv : ∀ i ∈ V, ∀ x, v i (σ x) = v i x)
    {G : (ι → α) → ℝ} (hG : ∀ k ∈ 𝔅, ∀ c, G (flipOn σ (blk k) c) = G c)
    (hint : ∀ E₁ ≤ E, ∀ V₁ ⊆ V, Integrable (fun c => edgeProd E₁ a c * edgeProd (E \ E₁) b c *
      (∏ i ∈ V₁, u i (c i)) * (∏ i ∈ V \ V₁, v i (c i)) * G c) P) :
    ∫ c, edgeProd E (fun i j x y => a i j x y + b i j x y) c *
        (∏ i ∈ V, (u i (c i) + v i (c i))) * G c ∂P =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph ι)).filter (· ≤ E),
        ∑ V₁ ∈ V.powerset.filter
            (fun V₁ => ∀ k ∈ 𝔅, Even (∑ i ∈ blk k, E₁.degree i + (blk k ∩ V₁).card)),
          ∫ c, edgeProd E₁ a c * edgeProd (E \ E₁) b c * (∏ i ∈ V₁, u i (c i)) *
            (∏ i ∈ V \ V₁, v i (c i)) * G c ∂P := by
  have hexp : ∀ c, edgeProd E (fun i j x y => a i j x y + b i j x y) c *
      (∏ i ∈ V, (u i (c i) + v i (c i))) * G c =
      ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph ι)).filter (· ≤ E), ∑ V₁ ∈ V.powerset,
        edgeProd E₁ a c * edgeProd (E \ E₁) b c * (∏ i ∈ V₁, u i (c i)) *
          (∏ i ∈ V \ V₁, v i (c i)) * G c := by
    intro c
    rw [edgeProd_add_eq_sum, Finset.prod_add, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun E₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun V₁ _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun E₁ hE₁ => integrable_finsetSum _ fun V₁ hV₁ =>
    hint E₁ (Finset.mem_filter.1 hE₁).2 V₁ (Finset.mem_powerset.1 hV₁)]
  refine Finset.sum_congr rfl fun E₁ hE₁ => ?_
  have hle : E₁ ≤ E := (Finset.mem_filter.1 hE₁).2
  rw [integral_finsetSum _ fun V₁ hV₁ => hint E₁ hle V₁ (Finset.mem_powerset.1 hV₁)]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) (fun V₁ h₂ h₁ => ?_)
  have hcond : ¬ ∀ k ∈ 𝔅, Even (∑ i ∈ blk k, E₁.degree i + (blk k ∩ V₁).card) :=
    fun h => h₁ (Finset.mem_filter.2 ⟨h₂, h⟩)
  push Not at hcond
  obtain ⟨k, hk, hodd⟩ := hcond
  rw [Nat.not_even_iff_odd] at hodd
  have hV₁ : V₁ ⊆ V := Finset.mem_powerset.1 h₂
  have hsd : E \ E₁ ≤ E := sdiff_le
  have hre : ∀ c, edgeProd E₁ a c * edgeProd (E \ E₁) b c * (∏ i ∈ V₁, u i (c i)) *
      (∏ i ∈ V \ V₁, v i (c i)) * G c = edgeProd E₁ a c * (∏ i ∈ V₁, u i (c i)) *
        (edgeProd (E \ E₁) b c * (∏ i ∈ V \ V₁, v i (c i)) * G c) := fun c => by ring
  simp_rw [hre]
  refine integral_edgeProd_mul_prod_mul_eq_zero hσ hσσ (hP k hk)
    (fun i j hij h => ha₁ i j hij (hle h)) (fun i j hij h => ha₂ i j hij (hle h))
    (fun i hi => hu i (hV₁ hi)) (fun c => ?_) hodd
  rw [edgeProd_flipOn_of_even (E \ E₁) (fun i j hij h => hb₁ i j hij (hsd h))
    (fun i j hij h => hb₂ i j hij (hsd h)),
    prod_flipOn_of_even (V \ V₁) (fun i hi => hv i (Finset.sdiff_subset hi)), hG k hk]

/-- **The parity reduction with vertex weights for a subpartition** (Corollary 5.24, termwise):
the pairs `(E₁, V₁)` that contribute are those with `deg_{E₁}(S) + |S ∩ V₁|` even for every
`S ∈ X`, i.e. `E₁ ∈ Eul^X(V₁)` (Definition 5.23). -/
theorem integral_edgeProd_prod_add_mul_eq_sum_relEulerian {X : Finset (Finset ℕ)}
    (hσ : Measurable σ) (hσσ : Function.Involutive σ) {P : Measure (X.biUnion id → α)}
    (hP : ∀ S ∈ X, MeasurePreserving (flipOn σ (blockSet X S)) P P)
    (E : SimpleGraph (X.biUnion id)) {a b : X.biUnion id → X.biUnion id → α → α → ℝ}
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
        ∑ V₁ ∈ V.powerset.filter
            (fun V₁ => ∀ S ∈ X, Even (blockDegree X E₁ S + (blockSet X S ∩ V₁).card)),
          ∫ c, edgeProd E₁ a c * edgeProd (E \ E₁) b c * (∏ i ∈ V₁, u i (c i)) *
            (∏ i ∈ V \ V₁, v i (c i)) * G c ∂P :=
  integral_edgeProd_prod_add_mul_eq_sum hσ hσσ X (blockSet X) hP E ha₁ ha₂ hb₁ hb₂ V hu hv hG
    hint

end Reduction

end Parity

end MultipoleBKT

end
