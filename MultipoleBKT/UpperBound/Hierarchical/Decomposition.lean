/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.IntegrandBound
public import MultipoleBKT.Main.TheoremTwo.MeasurableBadPoints
public import MultipoleBKT.Main.PropFiveFortyFive.Counting

/-!
# Fixing the bad labels and the good multipoles (Steps 1–3 of Lemma 5.16)

The paper: Steps 1–3 of the proof of Lemma 5.16. On `{σ_N = Id}`, the bad labels form a set `V = I_bad` and the good multipoles
(the components of the multipole graph made of good points, `goodBlocks`) form a partition `π` of
the good labels; with the profile `𝒩_k = n_k` of the event `𝒜` (eq. (5.57)):

* `goodBlocks_mem_partitions`, `card_le_of_mem_goodBlocks`, `blockCount_goodBlocks`: `π` is a
  partition of `V_good` (read on `ℕ`) with `n_k` blocks of size `k ≤ p(β)` and none larger
  (Step 1, Remark 5.6; the paper's `Π_mult^{V_good}`, eq. (5.61));
* `card_badPoints_eq`: `|I_bad| = N - ∑_k k n_k` (Step 1: `|I_good| = 𝒩_1 + 2𝒩_2 + ⋯ + p𝒩_p`);
* `connOn_goodBlocks`, `not_linked_of_mem_interPairs_goodBlocks`: `c ∈ ⋂_{S ∈ π} 𝓑_S ∩
  ⋂_{ij ∈ ℰ^inter(π)} 𝓑_ij^c` (eq. (5.63));
* `frozenEvent V π`: the event `{σ_N = Id, I_bad = V} ∩ ⋂_{S ∈ π} 𝓑_S ∩ ⋂_{ij ∈ ℰ^inter(π)} 𝓑_ij^c`,
  measurable (`measurableSet_frozenEvent`); `mem_frozenEvent` collects the above.

The decomposition is a union of events instead of the paper's relabelling identities
(5.60)–(5.61) (which would need the exchangeability of `I_bad`, a null-set statement for
the index tie-breaking of Definition 5.1); the resulting bound sums over `V` and `π`.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBound

open Hierarchical Multipole SetPartition Parity TheoremTwo PropFiveFortyFive

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-! ### The good multipoles -/

section Blocks

open scoped Classical

/-- The labels (read in `ℕ`) of a connected component of the multipole graph. -/
noncomputable def componentLabels (M lam : ℝ) (c : Fin N → ℂ × ℂ)
    (C : (multipoleGraph M lam c).ConnectedComponent) : Finset ℕ :=
  (Finset.univ.filter fun i => (multipoleGraph M lam c).connectedComponentMk i = C).map
    Fin.valEmbedding

/-- **The good multipoles** of a configuration: the labels of the components of the multipole
graph made of good points (the paper's `Π_mult^{V_good}` on `I_bad = V_bad`, proof of Lemma 5.16). -/
noncomputable def goodBlocks (p₀ : ℕ) (β lam M ε₀ : ℝ) (c : Fin N → ℂ × ℂ) : Finset (Finset ℕ) :=
  (Finset.univ.filter fun C : (multipoleGraph M lam c).ConnectedComponent =>
      C.supp ⊆ ↑(goodPoints p₀ β lam M ε₀ (matched c))).image (componentLabels M lam c)

theorem mem_componentLabels {c : Fin N → ℂ × ℂ} {C : (multipoleGraph M lam c).ConnectedComponent}
    {n : ℕ} :
    n ∈ componentLabels M lam c C ↔
      ∃ i : Fin N, (multipoleGraph M lam c).connectedComponentMk i = C ∧ (i : ℕ) = n := by
  simp [componentLabels]

theorem card_componentLabels (c : Fin N → ℂ × ℂ) (C : (multipoleGraph M lam c).ConnectedComponent) :
    (componentLabels M lam c C).card = Nat.card C.supp := by
  rw [componentLabels, Finset.card_map, natCard_supp_eq]

theorem componentLabels_injective (c : Fin N → ℂ × ℂ) :
    Function.Injective (componentLabels M lam c) := by
  intro C C' h
  obtain ⟨v, hv⟩ : ∃ v, (multipoleGraph M lam c).connectedComponentMk v = C :=
    ⟨Quot.out C, connectedComponentMk_out C⟩
  have hmem : (v : ℕ) ∈ componentLabels M lam c C := mem_componentLabels.2 ⟨v, hv, rfl⟩
  rw [h] at hmem
  obtain ⟨w, hw, hwv⟩ := mem_componentLabels.1 hmem
  rw [← Fin.ext hwv, hw] at hv
  exact hv.symm

theorem matched_eq_of_refl {c : Fin N → ℂ × ℂ} (hσ : stableMatching c = Equiv.refl _) :
    matched c = c := by
  funext i
  simp [matched, hσ]

variable (hM : 0 ≤ M) {c : Fin N → ℂ × ℂ} (hσ : stableMatching c = Equiv.refl _)
include hM hσ

/-- The component of a good point consists of good points. -/
theorem component_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ c) :
    ((multipoleGraph M lam c).connectedComponentMk i).supp ⊆ ↑(goodPoints p₀ β lam M ε₀ (matched c)) := by
  rw [matched_eq_of_refl hσ] at *
  have := supp_subset_good (p₀ := p₀) (β := β) (ε₀ := ε₀) hM (c := c) (i := i)
    (by rw [matched_eq_of_refl hσ]; exact hi)
  rwa [matched_eq_of_refl hσ] at this

/-- **The good multipoles partition the good labels.** -/
theorem goodBlocks_mem_partitions :
    goodBlocks p₀ β lam M ε₀ c ∈
      partitions ((Finset.univ \ badPoints p₀ β lam M ε₀ c).map Fin.valEmbedding) := by
  rw [mem_partitions]
  refine ⟨⟨fun S hS => ?_, fun S hS T hT hST => ?_⟩, ?_⟩
  · obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hS
    obtain ⟨v, hv⟩ : ∃ v, (multipoleGraph M lam c).connectedComponentMk v = C :=
      ⟨Quot.out C, connectedComponentMk_out C⟩
    exact ⟨v, mem_componentLabels.2 ⟨v, hv, rfl⟩⟩
  · obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hS
    obtain ⟨C', -, rfl⟩ := Finset.mem_image.1 hT
    rw [Function.onFun, Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨i, hi, rfl⟩ := mem_componentLabels.1 hn
    obtain ⟨j, hj, hji⟩ := mem_componentLabels.1 hn'
    rw [← Fin.ext hji, hj] at hi
    exact hST (by rw [hi])
  · ext n
    simp only [mem_biUnion_id, goodBlocks, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_map, Finset.mem_sdiff, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨S, ⟨C, hC, rfl⟩, hn⟩
      obtain ⟨i, hi, rfl⟩ := mem_componentLabels.1 hn
      refine ⟨i, ?_, rfl⟩
      have hig : i ∈ goodPoints p₀ β lam M ε₀ (matched c) :=
        hC (by rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hi])
      rw [matched_eq_of_refl hσ] at hig
      exact (Finset.mem_sdiff.1 hig).2
    · rintro ⟨i, hi, rfl⟩
      have hig : i ∈ goodPoints p₀ β lam M ε₀ c := Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi⟩
      exact ⟨_, ⟨_, component_good hM hσ hig, rfl⟩, mem_componentLabels.2 ⟨i, rfl, rfl⟩⟩

omit hσ in
/-- The good multipoles have at most `p(β)` elements (Remark 5.6). -/
theorem card_le_of_mem_goodBlocks {S : Finset ℕ} (hS : S ∈ goodBlocks p₀ β lam M ε₀ c) :
    S.card ≤ pBeta p₀ β := by
  obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hS
  rw [Finset.mem_filter] at hC
  obtain ⟨v, hv⟩ : ∃ v, (multipoleGraph M lam c).connectedComponentMk v = C :=
    ⟨Quot.out C, connectedComponentMk_out C⟩
  have hvg : v ∈ goodPoints p₀ β lam M ε₀ (matched c) :=
    hC.2 (by rw [SimpleGraph.ConnectedComponent.mem_supp_iff, hv])
  rw [card_componentLabels, ← hv, natCard_supp_of_good hM hvg]
  exact card_classOn_le hvg

omit hM hσ in
/-- **The profile of the good multipoles**. -/
theorem blockCount_goodBlocks (p : ℕ) (i : Fin p) :
    blockCount p (goodBlocks p₀ β lam M ε₀ c) i =
      goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) := by
  rw [blockCount, goodMultipoleCount_eq_card, goodBlocks, Finset.filter_image,
    Finset.card_image_of_injective _ (componentLabels_injective c), Finset.filter_filter]
  congr 1
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, card_componentLabels]
  tauto

omit hM in
/-- The good multipoles are connected (`𝓑_S`). -/
theorem connOn_goodBlocks {S : Finset ℕ} (hS : S ∈ goodBlocks p₀ β lam M ε₀ c) :
    ConnOn S (linkedPairs M lam (natConfig c) S) := by
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hS
  obtain ⟨v, hv⟩ : ∃ v, (multipoleGraph M lam c).connectedComponentMk v = C :=
    ⟨Quot.out C, connectedComponentMk_out C⟩
  refine ⟨⟨v, mem_componentLabels.2 ⟨v, hv, rfl⟩⟩, fun n hn m hm => ?_⟩
  obtain ⟨i, hi, rfl⟩ := mem_componentLabels.1 hn
  obtain ⟨j, hj, rfl⟩ := mem_componentLabels.1 hm
  have hij : (multipoleGraph M lam c).Reachable i j := by
    rw [← SimpleGraph.ConnectedComponent.eq, hi, hj]
  refine (mem_of_reachable_of_closed
    (T := fun w => (multipoleGraph M lam c).connectedComponentMk w = C ∧
      (edgeGraph (linkedPairs M lam (natConfig c) (componentLabels M lam c C))).Reachable i w)
    (fun a b ha hab => ?_) ⟨hi, SimpleGraph.Reachable.refl _⟩ hij).2
  have hb : (multipoleGraph M lam c).connectedComponentMk b = C := by
    rw [← ha.1]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hab.symm
  refine ⟨hb, ha.2.trans (SimpleGraph.Adj.reachable ?_)⟩
  rw [edgeGraph_linkedPairs_adj (mem_componentLabels.2 ⟨a, ha.1, rfl⟩)
    (mem_componentLabels.2 ⟨b, hb, rfl⟩), natConfig_apply, natConfig_apply]
  rw [multipoleGraph, SimpleGraph.fromRel_adj] at hab
  have hm : ∀ k : Fin N, ((c k).1, (c (stableMatching c k)).2) = c k := fun k => by
    simp [hσ]
  simp only [hm] at hab
  exact ⟨fun h => hab.1 (Fin.ext h), hab.2⟩

omit hM in
/-- Distinct good multipoles are not linked (`𝓑_ij^c` for `ij ∈ ℰ^inter(π)`). -/
theorem not_linked_of_mem_interPairs_goodBlocks {q : ℕ × ℕ}
    (hq : q ∈ interPairs (goodBlocks p₀ β lam M ε₀ c)) :
    ¬ MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2) := by
  obtain ⟨S, hS, S', hS', hSS', h1, h2⟩ := exists_of_mem_interPairs hq
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hS
  obtain ⟨C', -, rfl⟩ := Finset.mem_image.1 hS'
  obtain ⟨i, hi, hiq⟩ := mem_componentLabels.1 h1
  obtain ⟨j, hj, hjq⟩ := mem_componentLabels.1 h2
  have h12 := (mem_pairsOn.1 (interPairs_subset_pairsOn hq)).2.2
  intro hlink
  apply hSS'
  rw [← hiq, ← hjq, natConfig_apply, natConfig_apply] at hlink
  have hadj : (multipoleGraph M lam c).Adj i j := by
    rw [multipoleGraph, SimpleGraph.fromRel_adj]
    have hm : ∀ k : Fin N, ((c k).1, (c (stableMatching c k)).2) = c k := fun k => by
      simp [hσ]
    simp only [hm]
    refine ⟨fun h => ?_, Or.inl hlink⟩
    subst h
    rw [← hiq, ← hjq] at h12
    exact lt_irrefl _ h12
  rw [← hi, ← hj, SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj]

/-- `|I_good| = ∑_{S ∈ π} |S|` and hence `|I_bad| = N - ∑_k k 𝒩_k^good`. -/
theorem card_badPoints_eq (p : ℕ) (hp : pBeta p₀ β = p) :
    (badPoints p₀ β lam M ε₀ c).card =
      N - ∑ i : Fin p, ((i : ℕ) + 1) * goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) := by
  have hπ := goodBlocks_mem_partitions (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) hM hσ
  have hsizes : ∀ S ∈ goodBlocks p₀ β lam M ε₀ c, 1 ≤ S.card ∧ S.card ≤ p := fun S hS =>
    ⟨Finset.card_pos.2 ((mem_partitions.1 hπ).1.1 S hS), hp ▸ card_le_of_mem_goodBlocks hM hS⟩
  have hsum := sum_mul_blockCount hsizes
  simp_rw [blockCount_goodBlocks] at hsum
  rw [hsum]
  have hcard : ∑ S ∈ goodBlocks p₀ β lam M ε₀ c, S.card =
      ((Finset.univ \ badPoints p₀ β lam M ε₀ c).map Fin.valEmbedding).card := by
    rw [← (mem_partitions.1 hπ).2, Finset.card_biUnion (mem_partitions.1 hπ).1.2]
    rfl
  rw [hcard, Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin]
  have := Finset.card_le_univ (badPoints p₀ β lam M ε₀ c)
  rw [Fintype.card_fin] at this
  omega

end Blocks

/-! ### The frozen event -/

section Event

/-- **The frozen event** `{σ_N = Id, I_bad = V} ∩ ⋂_{S ∈ π} 𝓑_S ∩ ⋂_{ij ∈ ℰ^inter(π)} 𝓑_ij^c`
(eqs. (5.62)–(5.64)). -/
def frozenEvent (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (π : Finset (Finset ℕ)) :
    Set (Fin N → ℂ × ℂ) :=
  {c | stableMatching c = Equiv.refl _ ∧ badPoints p₀ β lam M ε₀ c = V ∧
    (∀ S ∈ π, ConnOn S (linkedPairs M lam (natConfig c) S)) ∧
    ∀ q ∈ interPairs π, ¬ MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2)}

theorem measurable_natConfig_apply (n : ℕ) :
    Measurable fun c : Fin N → ℂ × ℂ => natConfig c n := by
  unfold natConfig
  by_cases h : n < N
  · simp only [h, dite_true]
    exact measurable_pi_apply _
  · simp only [h, dite_false]
    exact measurable_const

theorem measurableSet_linked_natConfig (q : ℕ × ℕ) :
    MeasurableSet {c : Fin N → ℂ × ℂ | MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2)} :=
  ((measurable_natConfig_apply q.1).prodMk (measurable_natConfig_apply q.2))
    (measurableSet_multipoleLinked M lam)

theorem measurableSet_connOn (S : Finset ℕ) :
    MeasurableSet {c : Fin N → ℂ × ℂ | ConnOn S (linkedPairs M lam (natConfig c) S)} := by
  classical
  have h : FiberMeasurable fun c : Fin N → ℂ × ℂ => linkedPairs M lam (natConfig c) S := by
    have := fiberMeasurable_filter (α := Fin N → ℂ × ℂ) (pairsOn S)
      (P := fun c q => MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2))
      fun q => measurableSet_linked_natConfig q
    convert this using 2 with c
    ext q
    rw [mem_linkedPairs, Finset.mem_filter]
  exact h.preimage {E | ConnOn S E}

theorem measurableSet_frozenEvent (V : Finset (Fin N)) (π : Finset (Finset ℕ)) :
    MeasurableSet (frozenEvent p₀ β lam M ε₀ V π) := by
  classical
  have h1 := measurableSet_stableMatching_eq (N := N) (Equiv.refl _)
  have h2 : MeasurableSet {c : Fin N → ℂ × ℂ | badPoints p₀ β lam M ε₀ c = V} :=
    fiberMeasurable_badPoints (d := fun c : Fin N → ℂ × ℂ => c) measurable_id p₀ β lam M ε₀ V
  have h3 : MeasurableSet {c : Fin N → ℂ × ℂ | ∀ S ∈ π, ConnOn S (linkedPairs M lam (natConfig c) S)} := by
    have : {c : Fin N → ℂ × ℂ | ∀ S ∈ π, ConnOn S (linkedPairs M lam (natConfig c) S)} =
        ⋂ S ∈ (π : Set (Finset ℕ)), {c | ConnOn S (linkedPairs M lam (natConfig c) S)} := by
      ext c; simp
    rw [this]
    exact MeasurableSet.biInter π.countable_toSet fun S _ => measurableSet_connOn S
  have h4 : MeasurableSet {c : Fin N → ℂ × ℂ |
      ∀ q ∈ interPairs π, ¬ MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2)} := by
    have : {c : Fin N → ℂ × ℂ |
        ∀ q ∈ interPairs π, ¬ MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2)} =
        ⋂ q ∈ ((interPairs π : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)),
          {c | MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2)}ᶜ := by
      ext c; simp
    rw [this]
    exact MeasurableSet.biInter (interPairs π).countable_toSet fun q _ =>
      (measurableSet_linked_natConfig q).compl
  exact h1.inter (h2.inter (h3.inter h4))

/-- **Every configuration of the event `𝒜 ∩ {σ_N = Id}` lies in a frozen event** with
`|V| = N - N'` and `π` a partition of the good labels with the profile `n`. -/
theorem mem_frozenEvent (hM : 0 ≤ M) {n : Fin (pBeta p₀ β) → ℕ} {c : Fin N → ℂ × ℂ}
    (hσ : stableMatching c = Equiv.refl _)
    (hn : ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i) :
    badPoints p₀ β lam M ε₀ c ∈ (Finset.univ : Finset (Fin N)).powersetCard
        (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) ∧
      goodBlocks p₀ β lam M ε₀ c ∈
        (partitions ((Finset.univ \ badPoints p₀ β lam M ε₀ c).map Fin.valEmbedding)).filter
          (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n) ∧
      c ∈ frozenEvent p₀ β lam M ε₀ (badPoints p₀ β lam M ε₀ c) (goodBlocks p₀ β lam M ε₀ c) := by
  refine ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, ?_⟩, Finset.mem_filter.2
    ⟨goodBlocks_mem_partitions hM hσ, fun S hS => card_le_of_mem_goodBlocks hM hS,
      funext fun i => by rw [blockCount_goodBlocks, hn]⟩,
    hσ, rfl, fun S hS => connOn_goodBlocks hσ hS,
    fun q hq => not_linked_of_mem_interPairs_goodBlocks hσ hq⟩
  rw [card_badPoints_eq hM hσ (pBeta p₀ β) rfl]
  simp_rw [hn]

end Event

end UpperBound

end MultipoleBKT

end
