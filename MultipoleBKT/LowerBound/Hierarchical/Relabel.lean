/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.StartLowSum

/-!
# Relabeling the partition in Lemma 4.18 ("the number of ways to choose `π`")

The proof of Lemma 4.18, Step 1
(proof of Lemma 4.18): the integral over `{Π_mult = π, σ_N = Id}` does not depend on the partition `π` of
a given profile. We prove the corresponding invariance of the lower bound: the cluster integral
`𝔼_{ρ^{⊗ ℕ}}[(∏_{S ∈ π} bw_S) ∏_{ij ∈ ℰ^inter(π)} (1 + u_ij)]` of Steps 4–8 takes the same value on
two partitions with the same block sizes.

* `blockWeightOf_comp`, `prod_interPairs_comp`, `clusterWeight_comp`: relabeling the dipoles by a
  permutation `τ` of the labels that is increasing on each block of `π'` turns the cluster
  integrand of `π'` into that of `π = {τ(S) : S ∈ π'}` (the pair `i < j` of a block keeps its order;
  the bond `u` between blocks is symmetric when `w` is symmetric and `M ≥ 1`);
* `measurePreserving_comp_perm`: `ρ^{⊗ ℕ}` is invariant under the relabeling;
* `exists_perm_of_profile`: two partitions of `[N]` with the same numbers of blocks of each size
  are related by such a permutation (match the blocks of equal sizes, and the points of matched
  blocks in increasing order);
* `clusterIntegralOf_eq_of_profile`: hence the cluster integrals agree.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

/-! ### Relabeling the integrand -/

section Integrand

open scoped Classical

variable (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ) (τ : Equiv.Perm ℕ)

theorem edgeGraph_linkedPairs_comp_adj (c : ℕ → ℂ × ℂ) (S : Finset ℕ) (a b : ℕ) :
    (edgeGraph (linkedPairs M lam (c ∘ τ) S)).Adj a b ↔
      (edgeGraph (linkedPairs M lam c (S.image τ))).Adj (τ a) (τ b) := by
  simp only [edgeGraph_adj, mem_linkedPairs, mem_pairsOn, Finset.mem_image, Function.comp_apply,
    τ.injective.ne_iff]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with ⟨⟨ha, hb, -⟩, hl⟩ | ⟨⟨hb, ha, -⟩, hl⟩
    · rcases lt_or_gt_of_ne (τ.injective.ne hne) with h' | h'
      · exact Or.inl ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, h'⟩, hl⟩
      · exact Or.inr ⟨⟨⟨b, hb, rfl⟩, ⟨a, ha, rfl⟩, h'⟩, multipoleLinked_comm.1 hl⟩
    · rcases lt_or_gt_of_ne (τ.injective.ne hne) with h' | h'
      · exact Or.inl ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, h'⟩, multipoleLinked_comm.1 hl⟩
      · exact Or.inr ⟨⟨⟨b, hb, rfl⟩, ⟨a, ha, rfl⟩, h'⟩, hl⟩
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rcases h with ⟨⟨⟨a', ha', ha⟩, ⟨b', hb', hb⟩, -⟩, hl⟩ | ⟨⟨⟨b', hb', hb⟩, ⟨a', ha', ha⟩, -⟩, hl⟩
    · rw [τ.injective ha] at ha'
      rw [τ.injective hb] at hb'
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inl ⟨⟨ha', hb', h'⟩, hl⟩
      · exact Or.inr ⟨⟨hb', ha', h'⟩, multipoleLinked_comm.1 hl⟩
    · rw [τ.injective ha] at ha'
      rw [τ.injective hb] at hb'
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact Or.inl ⟨⟨ha', hb', h'⟩, multipoleLinked_comm.1 hl⟩
      · exact Or.inr ⟨⟨hb', ha', h'⟩, hl⟩

/-- Connectedness of a block by the multipole relation is invariant under relabeling. -/
theorem connOn_linkedPairs_comp (c : ℕ → ℂ × ℂ) (S : Finset ℕ) :
    ConnOn S (linkedPairs M lam (c ∘ τ) S) ↔
      ConnOn (S.image τ) (linkedPairs M lam c (S.image τ)) := by
  let e : edgeGraph (linkedPairs M lam (c ∘ τ) S) ≃g edgeGraph (linkedPairs M lam c (S.image τ)) :=
    ⟨τ, fun {a b} => (edgeGraph_linkedPairs_comp_adj M lam τ c S a b).symm⟩
  unfold ConnOn
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne.image τ, fun i hi j hj => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hj
    exact (h a ha b hb).map e.toHom
  · rintro ⟨hne, h⟩
    obtain ⟨x, hx⟩ := hne
    obtain ⟨a₀, ha₀, -⟩ := Finset.mem_image.1 hx
    refine ⟨⟨a₀, ha₀⟩, fun a ha b hb => ?_⟩
    have := (h (τ a) (Finset.mem_image_of_mem τ ha) (τ b) (Finset.mem_image_of_mem τ hb)).map
      e.symm.toHom
    have he : ∀ x, e.symm.toHom (τ x) = x := fun x => τ.symm_apply_apply x
    rwa [he a, he b] at this

/-- **Relabeling a block weight**: for `τ` increasing on `S`, `bw_S(c ∘ τ) = bw_{τ(S)}(c)`. -/
theorem blockWeightOf_comp {S : Finset ℕ} (hτ : StrictMonoOn τ S) (c : ℕ → ℂ × ℂ) :
    blockWeightOf β w ψ M lam S (c ∘ τ) = blockWeightOf β w ψ M lam (S.image τ) c := by
  unfold blockWeightOf
  congr 1
  · congr 1
    · exact if_congr (connOn_linkedPairs_comp M lam τ c S) rfl rfl
    · refine Finset.prod_nbij' (fun p => (τ p.1, τ p.2)) (fun q => (τ.symm q.1, τ.symm q.2))
        (fun p hp => ?_) (fun q hq => ?_) (fun p _ => by simp) (fun q _ => by simp)
        (fun p _ => rfl)
      · obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 hp
        exact mem_pairsOn.2 ⟨Finset.mem_image_of_mem τ h1, Finset.mem_image_of_mem τ h2,
          hτ h1 h2 h12⟩
      · obtain ⟨q1, q2⟩ := q
        obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 hq
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h1
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 h2
        simp only [Equiv.symm_apply_apply]
        exact mem_pairsOn.2 ⟨ha, hb, (hτ.lt_iff_lt ha hb).1 h12⟩
  · rw [Finset.prod_image fun a _ b _ h => τ.injective h]
    rfl

/-- **Relabeling the bonds between blocks**: for a subpartition `π'`, a permutation `τ` and a
symmetric pair weight `u`, `∏_{ij ∈ ℰ^inter(π')} g(c_{τ i}, c_{τ j}) =
∏_{ij ∈ ℰ^inter(τ(π'))} g(c_i, c_j)`. -/
theorem prod_interPairs_comp {π' : Finset (Finset ℕ)} (hπ' : IsSubpartition π')
    (g : ℂ × ℂ → ℂ × ℂ → ℝ) (hg : ∀ d e, g d e = g e d) (c : ℕ → ℂ × ℂ) :
    ∏ p ∈ interPairs π', g (c (τ p.1)) (c (τ p.2)) =
      ∏ q ∈ interPairs (π'.image fun S => S.image τ), g (c q.1) (c q.2) := by
  have himg : IsSubpartition (π'.image fun S => S.image τ) := by
    refine ⟨fun T hT => ?_, fun T hT T' hT' hTT' => ?_⟩
    · obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
      exact (hπ'.1 S hS).image τ
    · rw [Finset.mem_coe, Finset.mem_image] at hT hT'
      obtain ⟨S, hS, rfl⟩ := hT
      obtain ⟨S', hS', rfl⟩ := hT'
      have hSS' : S ≠ S' := fun h => hTT' (h ▸ rfl)
      rw [Function.onFun, id, id]
      exact Finset.disjoint_image τ.injective |>.2 (hπ'.2 hS hS' hSS')
  have hmem : ∀ {π : Finset (Finset ℕ)}, IsSubpartition π → ∀ p : ℕ × ℕ,
      p ∈ interPairs π ↔ p.1 < p.2 ∧ ∃ S ∈ π, ∃ S' ∈ π, S ≠ S' ∧ p.1 ∈ S ∧ p.2 ∈ S' :=
    fun hπ p => ⟨fun hp => ⟨(mem_pairsOn.1 (interPairs_subset_pairsOn hp)).2.2,
      exists_of_mem_interPairs hp⟩,
      fun ⟨h12, S, hS, S', hS', hSS', h1, h2⟩ => mem_interPairs_of hπ hS hS' hSS' h1 h2 h12⟩
  let sort : ℕ × ℕ → ℕ × ℕ := fun p => (min p.1 p.2, max p.1 p.2)
  refine Finset.prod_nbij' (fun p => sort (τ p.1, τ p.2)) (fun q => sort (τ.symm q.1, τ.symm q.2))
    (fun p hp => ?_) (fun q hq => ?_) (fun p hp => ?_) (fun q hq => ?_) (fun p _ => ?_)
  · obtain ⟨h12, S, hS, S', hS', hSS', h1, h2⟩ := (hmem hπ' p).1 hp
    have hne : τ p.1 ≠ τ p.2 := τ.injective.ne h12.ne
    have hTT' : S.image τ ≠ S'.image τ := fun h => hSS' (Finset.image_injective τ.injective h)
    rcases lt_or_gt_of_ne hne with h | h
    · refine (hmem himg _).2 ⟨?_, S.image τ, Finset.mem_image_of_mem _ hS, S'.image τ,
        Finset.mem_image_of_mem _ hS', hTT', ?_, ?_⟩
      · simp only [sort, min_eq_left h.le, max_eq_right h.le]
        exact h
      · simp only [sort, min_eq_left h.le]
        exact Finset.mem_image_of_mem τ h1
      · simp only [sort, max_eq_right h.le]
        exact Finset.mem_image_of_mem τ h2
    · refine (hmem himg _).2 ⟨?_, S'.image τ, Finset.mem_image_of_mem _ hS', S.image τ,
        Finset.mem_image_of_mem _ hS, hTT'.symm, ?_, ?_⟩
      · simp only [sort, min_eq_right h.le, max_eq_left h.le]
        exact h
      · simp only [sort, min_eq_right h.le]
        exact Finset.mem_image_of_mem τ h2
      · simp only [sort, max_eq_left h.le]
        exact Finset.mem_image_of_mem τ h1
  · obtain ⟨h12, T, hT, T', hT', hTT', h1, h2⟩ := (hmem himg q).1 hq
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨S', hS', rfl⟩ := Finset.mem_image.1 hT'
    obtain ⟨a, ha, hqa⟩ := Finset.mem_image.1 h1
    obtain ⟨b, hb, hqb⟩ := Finset.mem_image.1 h2
    have hSS' : S ≠ S' := fun h => hTT' (h ▸ rfl)
    have hab : τ.symm q.1 = a := by rw [← hqa, Equiv.symm_apply_apply]
    have hba : τ.symm q.2 = b := by rw [← hqb, Equiv.symm_apply_apply]
    have hne : a ≠ b := fun h => (h12.ne (by rw [← hqa, ← hqb, h]))
    rw [hab, hba]
    rcases lt_or_gt_of_ne hne with h | h
    · refine (hmem hπ' _).2 ⟨?_, S, hS, S', hS', hSS', ?_, ?_⟩
      · simp only [sort, min_eq_left h.le, max_eq_right h.le]
        exact h
      · simp only [sort, min_eq_left h.le]
        exact ha
      · simp only [sort, max_eq_right h.le]
        exact hb
    · refine (hmem hπ' _).2 ⟨?_, S', hS', S, hS, hSS'.symm, ?_, ?_⟩
      · simp only [sort, min_eq_right h.le, max_eq_left h.le]
        exact h
      · simp only [sort, min_eq_right h.le]
        exact hb
      · simp only [sort, max_eq_left h.le]
        exact ha
  · have h12 := ((hmem hπ' p).1 hp).1
    rcases lt_or_gt_of_ne (τ.injective.ne h12.ne) with h | h
    · simp only [sort, min_eq_left h.le, max_eq_right h.le, Equiv.symm_apply_apply,
        min_eq_left h12.le, max_eq_right h12.le]
    · simp only [sort, min_eq_right h.le, max_eq_left h.le, Equiv.symm_apply_apply,
        min_eq_right h12.le, max_eq_left h12.le]
  · have h12 := ((hmem himg q).1 hq).1
    have hne : τ.symm q.1 ≠ τ.symm q.2 := τ.symm.injective.ne h12.ne
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [sort, min_eq_left h.le, max_eq_right h.le, Equiv.apply_symm_apply,
        min_eq_left h12.le, max_eq_right h12.le]
    · simp only [sort, min_eq_right h.le, max_eq_left h.le, Equiv.apply_symm_apply,
        min_eq_right h12.le, max_eq_left h12.le]
  · simp only [sort]
    rcases le_total (τ p.1) (τ p.2) with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hg]

/-- **Relabeling the cluster integrand**: for a subpartition `π'`, a permutation `τ` increasing on
each block of `π'` and a symmetric bond `u`, the cluster integrand of `π'` at `c ∘ τ` is that of
`τ(π') = {τ(S) : S ∈ π'}` at `c`. -/
theorem clusterWeight_comp {π' : Finset (Finset ℕ)} (hπ' : IsSubpartition π')
    (hτ : ∀ S ∈ π', StrictMonoOn τ S) (u : ℂ × ℂ → ℂ × ℂ → ℝ) (hu : ∀ d e, u d e = u e d)
    (c : ℕ → ℂ × ℂ) :
    clusterWeight (blockWeightOf β w ψ M lam) u π' (c ∘ τ) =
      clusterWeight (blockWeightOf β w ψ M lam) u (π'.image fun S => S.image τ) c := by
  unfold clusterWeight
  congr 1
  · rw [Finset.prod_image fun S _ S' _ h => Finset.image_injective τ.injective h]
    exact Finset.prod_congr rfl fun S hS => blockWeightOf_comp β w ψ M lam τ (hτ S hS) c
  · exact prod_interPairs_comp τ hπ' (fun d e => 1 + u d e) (fun d e => by rw [hu]) c

end Integrand

/-! ### Invariance of the reference measure -/

/-- `ρ^{⊗ ℕ}` is invariant under the relabeling `c ↦ c ∘ τ`. -/
theorem measurePreserving_comp_perm {ρ : Measure (ℂ × ℂ)} [IsProbabilityMeasure ρ]
    (τ : Equiv.Perm ℕ) :
    MeasurePreserving (fun c : ℕ → ℂ × ℂ => c ∘ τ) (labelField ρ) (labelField ρ) := by
  refine ⟨by fun_prop, ?_⟩
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.pi s.countable_toSet fun i _ => ht i)]
  have hset : (fun c : ℕ → ℂ × ℂ => c ∘ τ) ⁻¹' Set.pi s t =
      Set.pi (s.image τ : Set ℕ) fun j => t (τ.symm j) := by
    ext c
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Function.comp_apply,
      Finset.coe_image, Set.mem_image]
    constructor
    · rintro hc j ⟨i, hi, rfl⟩
      simpa using hc i hi
    · intro hc i hi
      simpa using hc (τ i) ⟨i, hi, rfl⟩
  rw [hset, labelField, Measure.infinitePi_pi (μ := fun _ : ℕ => ρ) (s := s.image τ)
    (t := fun j => t (τ.symm j)) fun j _ => ht _,
    Finset.prod_image fun a _ b _ h => τ.injective h]
  simp

/-! ### Ranks in a finite set -/

section Rank

/-- The rank `|{y ∈ S : y < x}|` of `x` in `S`. -/
def rankIn (S : Finset ℕ) (x : ℕ) : ℕ := (S.filter (· < x)).card

/-- The element of rank `r` of `T` (`0` if `r ≥ |T|`). -/
noncomputable def elemAt (T : Finset ℕ) (r : ℕ) : ℕ :=
  if h : r < T.card then T.orderEmbOfFin rfl ⟨r, h⟩ else 0

theorem rankIn_lt_card {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) : rankIn S x < S.card :=
  Finset.card_lt_card (Finset.filter_ssubset.2 ⟨x, hx, lt_irrefl x⟩)

theorem rankIn_strictMonoOn (S : Finset ℕ) : StrictMonoOn (rankIn S) S := by
  intro x hx y hy hxy
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨fun z hz => ?_, fun h => ?_⟩)
  · rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hxy⟩
  · have : x ∈ S.filter (· < y) := Finset.mem_filter.2 ⟨hx, hxy⟩
    rw [← h, Finset.mem_filter] at this
    exact lt_irrefl x this.2

theorem elemAt_mem {T : Finset ℕ} {r : ℕ} (hr : r < T.card) : elemAt T r ∈ T := by
  unfold elemAt
  simp only [hr, dite_true]
  exact Finset.orderEmbOfFin_mem T rfl _

theorem elemAt_lt_elemAt {T : Finset ℕ} {r r' : ℕ} (hr' : r' < T.card) (h : r < r') :
    elemAt T r < elemAt T r' := by
  unfold elemAt
  simp only [h.trans hr', hr', dite_true]
  exact (T.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.2 h)

/-- The map `x ↦ (element of `T` of the rank of `x` in `S`)`, for `|S| = |T|`. -/
noncomputable def matchRank (S T : Finset ℕ) (x : ℕ) : ℕ := elemAt T (rankIn S x)

theorem matchRank_mem {S T : Finset ℕ} (hST : S.card = T.card) {x : ℕ} (hx : x ∈ S) :
    matchRank S T x ∈ T :=
  elemAt_mem (hST ▸ rankIn_lt_card hx)

theorem matchRank_strictMonoOn {S T : Finset ℕ} (hST : S.card = T.card) :
    StrictMonoOn (matchRank S T) S := fun _ hx _ hy hxy =>
  elemAt_lt_elemAt (hST ▸ rankIn_lt_card hy) (rankIn_strictMonoOn S hx hy hxy)

theorem image_matchRank {S T : Finset ℕ} (hST : S.card = T.card) :
    S.image (matchRank S T) = T := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact matchRank_mem hST hx
  · rw [Finset.card_image_of_injOn (matchRank_strictMonoOn hST).injOn, hST]

end Rank

/-! ### Partitions with the same block sizes -/

section Profile

open scoped Classical

/-- Two partitions of `[N]` with the same profile have the same number of blocks of each size. -/
theorem card_filter_card_eq_of_profile {N p : ℕ} {n : Fin p → ℕ} {π π' : Finset (Finset ℕ)}
    (hπ : π ∈ profilePartitions N p n) (hπ' : π' ∈ profilePartitions N p n) (k : ℕ) :
    (π'.filter fun S => S.card = k).card = (π.filter fun S => S.card = k).card := by
  rw [profilePartitions, Finset.mem_filter] at hπ hπ'
  have hzero : ∀ {σ : Finset (Finset ℕ)}, σ ∈ partitions (Finset.range N) → (∀ S ∈ σ, S.card ≤ p) →
      ¬ (1 ≤ k ∧ k ≤ p) → (σ.filter fun S => S.card = k).card = 0 := by
    intro σ hσ hle hk
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro S hS hSk
    have := Finset.card_pos.2 ((mem_partitions.1 hσ).1.1 S hS)
    exact hk ⟨hSk ▸ this, hSk ▸ hle S hS⟩
  by_cases hk : 1 ≤ k ∧ k ≤ p
  · have hi : k - 1 < p := by omega
    have e : ((⟨k - 1, hi⟩ : Fin p) : ℕ) + 1 = k := by simp; omega
    have h1 := hπ.2.2 ⟨k - 1, hi⟩
    have h2 := hπ'.2.2 ⟨k - 1, hi⟩
    rw [e] at h1 h2
    rw [h1, h2]
  · rw [hzero hπ.1 hπ.2.1 hk, hzero hπ'.1 hπ'.2.1 hk]

theorem fintype_card_subtype_card_eq (s : Finset (Finset ℕ)) (k : ℕ) :
    Fintype.card {S : s // (S : Finset ℕ).card = k} = (s.filter fun S => S.card = k).card := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr ⟨fun S => ⟨S.1.1, Finset.mem_filter.2 ⟨S.1.2, S.2⟩⟩,
    fun S => ⟨⟨S.1, (Finset.mem_filter.1 S.2).1⟩, (Finset.mem_filter.1 S.2).2⟩,
    fun _ => rfl, fun _ => rfl⟩

/-- A size-preserving bijection between the blocks of two partitions with the same profile. -/
theorem exists_blockEquiv {N p : ℕ} {n : Fin p → ℕ} {π π' : Finset (Finset ℕ)}
    (hπ : π ∈ profilePartitions N p n) (hπ' : π' ∈ profilePartitions N p n) :
    ∃ σ : π' ≃ π, ∀ S, (σ S : Finset ℕ).card = (S : Finset ℕ).card := by
  have e : ∀ k, {S : π' // (S : Finset ℕ).card = k} ≃ {T : π // (T : Finset ℕ).card = k} :=
    fun k => Fintype.equivOfCardEq (by
      rw [fintype_card_subtype_card_eq, fintype_card_subtype_card_eq,
        card_filter_card_eq_of_profile hπ hπ' k])
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

/-- **Relabeling partitions of the same profile**: there is a permutation `τ` of the labels,
increasing on each block of `π'`, with `π = {τ(S) : S ∈ π'}`. -/
theorem exists_perm_of_profile {N p : ℕ} {n : Fin p → ℕ} {π π' : Finset (Finset ℕ)}
    (hπ : π ∈ profilePartitions N p n) (hπ' : π' ∈ profilePartitions N p n) :
    ∃ τ : Equiv.Perm ℕ, (∀ S ∈ π', StrictMonoOn τ S) ∧ π'.image (fun S => S.image τ) = π := by
  obtain ⟨σ, hσ⟩ := exists_blockEquiv hπ hπ'
  have hπp := (Finset.mem_filter.1 hπ).1
  have hπp' := (Finset.mem_filter.1 hπ').1
  have hπs := (mem_partitions.1 hπp).1
  have hπs' := (mem_partitions.1 hπp').1
  -- the block map, extended by `∅`
  let σ' : Finset ℕ → Finset ℕ := fun S => if h : S ∈ π' then (σ ⟨S, h⟩ : Finset ℕ) else ∅
  have hσ'mem : ∀ S ∈ π', σ' S ∈ π := fun S hS => by simp only [σ', hS, dite_true]; exact (σ _).2
  have hσ'card : ∀ S ∈ π', (σ' S).card = S.card := fun S hS => by
    simp only [σ', hS, dite_true]; exact hσ ⟨S, hS⟩
  have hσ'inj : ∀ S ∈ π', ∀ S' ∈ π', σ' S = σ' S' → S = S' := fun S hS S' hS' h => by
    simp only [σ', hS, hS', dite_true] at h
    exact congrArg Subtype.val (σ.injective (Subtype.ext h))
  have hσ'surj : ∀ T ∈ π, ∃ S ∈ π', σ' S = T := fun T hT => by
    obtain ⟨S, hS⟩ := σ.surjective ⟨T, hT⟩
    exact ⟨S.1, S.2, by simp only [σ', S.2, dite_true, hS]⟩
  -- the point map
  let g : ℕ → ℕ := fun x => if x ∈ Finset.range N then
    matchRank (SetPartition.blockOf π' x) (σ' (SetPartition.blockOf π' x)) x else x
  have hgS : ∀ S ∈ π', ∀ x ∈ S, g x = matchRank S (σ' S) x := fun S hS x hx => by
    have hxN : x ∈ Finset.range N := subset_of_mem_partitions hπp' hS hx
    simp only [g, ite_eq_left hxN, SetPartition.blockOf_eq hπs' hS hx]
  have hgN : ∀ x ∈ Finset.range N, g x ∈ Finset.range N := fun x hx => by
    obtain ⟨hB, hxB⟩ := SetPartition.blockOf_mem hπp' hx
    rw [hgS _ hB x hxB]
    exact subset_of_mem_partitions hπp (hσ'mem _ hB)
      (matchRank_mem (hσ'card _ hB).symm hxB)
  have hginjN : Set.InjOn g (Finset.range N) := by
    intro x hx y hy hxy
    obtain ⟨hBx, hxB⟩ := SetPartition.blockOf_mem hπp' (Finset.mem_coe.1 hx)
    obtain ⟨hBy, hyB⟩ := SetPartition.blockOf_mem hπp' (Finset.mem_coe.1 hy)
    rw [hgS _ hBx x hxB, hgS _ hBy y hyB] at hxy
    have hmx := matchRank_mem (hσ'card _ hBx).symm hxB
    have hmy := matchRank_mem (hσ'card _ hBy).symm hyB
    rw [hxy] at hmx
    have hT := eq_of_isSubpartition hπs (hσ'mem _ hBx) (hσ'mem _ hBy) hmx hmy
    have hB := hσ'inj _ hBx _ hBy hT
    rw [hB] at hxB hxy
    exact (matchRank_strictMonoOn (hσ'card _ hBy).symm).injOn hxB hyB hxy
  have hgsurjN : ∀ y ∈ Finset.range N, ∃ x ∈ Finset.range N, g x = y := by
    intro y hy
    have := Finset.surjOn_of_injOn_of_card_le g (s := Finset.range N) (t := Finset.range N)
      (fun x hx => hgN x hx) hginjN le_rfl hy
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, hx, hxy⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    by_cases hx : x ∈ Finset.range N
    · by_cases hy : y ∈ Finset.range N
      · exact hginjN hx hy hxy
      · have h1 := hgN x hx
        have h2 : g y = y := by simp only [g, ite_eq_right hy]
        rw [hxy, h2] at h1
        exact absurd h1 hy
    · have h2 : g x = x := by simp only [g, ite_eq_right hx]
      by_cases hy : y ∈ Finset.range N
      · have h1 := hgN y hy
        rw [← hxy, h2] at h1
        exact absurd h1 hx
      · have h3 : g y = y := by simp only [g, ite_eq_right hy]
        rw [← h2, ← h3, hxy]
  have hgsurj : Function.Surjective g := by
    intro y
    by_cases hy : y ∈ Finset.range N
    · obtain ⟨x, -, hx⟩ := hgsurjN y hy
      exact ⟨x, hx⟩
    · exact ⟨y, by simp only [g, ite_eq_right hy]⟩
  have hgbij : Function.Bijective g := ⟨hginj, hgsurj⟩
  refine ⟨Equiv.ofBijective g hgbij, fun S hS => ?_, ?_⟩
  · intro x hx y hy hxy
    show g x < g y
    rw [hgS S hS x hx, hgS S hS y hy]
    exact matchRank_strictMonoOn (hσ'card S hS).symm hx hy hxy
  · have himg : ∀ S ∈ π', S.image (Equiv.ofBijective g hgbij) = σ' S := by
      intro S hS
      rw [← image_matchRank (hσ'card S hS).symm]
      exact Finset.image_congr fun x hx => hgS S hS x hx
    rw [Finset.image_congr himg]
    ext T
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact hσ'mem S hS
    · intro hT
      exact hσ'surj T hT

end Profile

end Hierarchical

end MultipoleBKT

end
