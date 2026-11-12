/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Radii

/-!
# Geometric properties of good and bad points (Lemma 5.9 (1)–(6), Remark 5.10)

The paper: Lemma 5.9
and Remark 5.10. Notation as in
`MultipoleBKT.UpperBound.BadPoints.Radii`: `d` is a dipole configuration (the matched pairs on the
event `{σ_N = Id}`, which the proofs below do not use), `A_i = max(r_i, λ)`,
`d_{i,bad} = badDist`, `τ^{±,Z} = radiusPlusZ`, `radiusMinusZ`, `v^Z = interactionZ`. The paper's
standing assumptions are `λ ≤ ε₀ R̄` and `M > max(20, 3^{p(β)})`; the results
below use `0 < λ ≤ ε₀ R̄` and `3^{p(β)} ≤ M`. "Same multipole" is reachability in the graph of
`↔` on the dipoles (`Π_mult`).

* `lemma_5_9_1`: **(1)** `d_{i,bad} ≥ max(r_i, λ)` for good `i` (eq. (5.9)).
  Proof: if a bad `j` had
  `d_ij < A_i`, then `j` is of type 3 (type 1 or 2 would make `i` a seed of type 3); a path in the
  `U`-class of `j` to a seed `s ∈ J^3_bad` has at most `p(β) - 1` steps (the class has at most
  `p(β)` elements); along it the distance to `i` grows by a factor `< 3` per step, because a bad
  `k` with `d_ik < M A_i` has `max(r_k, λ) < d_ik / M` (`chain_step`); one more step reaches
  `I^1_bad ∪ I^2_bad` at distance `< 3^{p(β)} A_i ≤ M A_i`, making `i` a seed.
* `remark_5_10_good`: Remark 5.10 for good points: `τ_i^{+,Z} = τ_i^{-,Z} ≥ r_i / 4`.
* `lemma_5_9_2`: **(2)** `d_{j,bad} ≤ (M+2)^{p(β)-1} d_{i,bad}` for good `i, j` in the same
  multipole (eq. (5.10)), from eqs. (5.19)–(5.20) along a path of at most `p(β) - 1` steps.
* `lemma_5_9_3`, `lemma_5_9_4`: **(3)–(4)** for `i` good, `j` bad and `v^Z_{i,j,±} ≠ 0`:
  `d_{i,j}^± ≤ 2 τ_j^{±,Z}` and `max(r_i, λ) ≤ max(r_j, λ)` (eqs. (5.11), (5.12)).
* `le_six_mul_of_ballGrowthInteraction_ne_zero`: eq. (5.24) for an abstract distance function;
  `badDist_le_six_mul`: eq. (5.24), `v^Z_{ii'} ≠ 0` gives `d_{i',bad} ≤ 6 d_{i,bad}` (the paper's
  `6 max(d_{i,bad}, λ)`, with (1)); `lemma_5_9_5`: **(5)** the chain estimate
  `d_{i_K,bad} ≤ 6^{K-1} d_{i_1,bad}` (eq. (5.13)).
* `lemma_5_9_6`: **(6)** the chain estimate through multipoles,
  `d_{i_K',bad} ≤ (6 (M+2)^{p(β)-1})^K d_{i_1,bad}` (eq. (5.14)); the hypothesis `i_l ≠ i_l'` of
  the paper is not needed.

Sequences `i_1, …, i_K` are functions `ℕ → Fin N` read on `0, …, K-1` (`K = n + 1`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

open TheoremTwo

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-! ### Walks inside a finite set of vertices -/

/-- If every vertex reachable from `u` lies in `S`, a reachable `v` is joined to `u` by a walk of
length `< |S|` all of whose vertices are reachable from `u`. -/
theorem exists_walk_length_lt {V : Type*} {G : SimpleGraph V} {u v : V} (huv : G.Reachable u v)
    (S : Finset V) (hS : ∀ k, G.Reachable u k → k ∈ S) :
    ∃ w : G.Walk u v, w.length + 1 ≤ S.card ∧ ∀ k ∈ w.support, G.Reachable u k := by
  classical
  obtain ⟨w⟩ := huv
  refine ⟨w.bypass, ?_, fun k hk => ⟨w.bypass.takeUntil k hk⟩⟩
  have hnodup := (w.bypass_isPath).support_nodup
  rw [← SimpleGraph.Walk.length_support, ← List.toFinset_card_of_nodup hnodup]
  exact Finset.card_le_card fun k hk => hS k ⟨w.bypass.takeUntil k (List.mem_toFinset.mp hk)⟩

/-! ### Bad points of type 3 -/

/-- Every label of the `U`-class of a bad point of type 3 is of type 3. -/
theorem mem_badPointsTypeThree_of_mem_classOn {j k : Fin N}
    (hj : j ∈ badPointsTypeThree p₀ β lam M ε₀ d) (hk : k ∈ goodClass p₀ β lam M ε₀ d j) :
    k ∈ badPointsTypeThree p₀ β lam M ε₀ d := by
  classical
  obtain ⟨hj12, hne⟩ := mem_badPointsTypeThree_iff.mp hj
  have hj1 : j ∉ badPointsTypeOne p₀ β lam ε₀ d := fun h => hj12 (Finset.mem_union_left _ h)
  have hj2 : j ∉ badPointsTypeTwo p₀ β lam M ε₀ d := fun h => hj12 (Finset.mem_union_right _ h)
  have hjU : j ∈ typeOneComplement p₀ β lam ε₀ d := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj1⟩
  have hkU : k ∈ typeOneComplement p₀ β lam ε₀ d :=
    mem_of_classGraph_reachable hjU (mem_classOn_iff.mp hk)
  have hcls : goodClass p₀ β lam M ε₀ d k = goodClass p₀ β lam M ε₀ d j := classOn_eq_of_mem hk
  have hk1 : k ∉ badPointsTypeOne p₀ β lam ε₀ d := (Finset.mem_sdiff.mp hkU).2
  have hk2 : k ∉ badPointsTypeTwo p₀ β lam M ε₀ d := by
    intro h2
    obtain ⟨-, h⟩ := mem_badPointsTypeTwo_iff.mp h2
    apply hj2
    refine mem_badPointsTypeTwo_iff.mpr ⟨hjU, ?_⟩
    have hc : (goodClass p₀ β lam M ε₀ d k).card = (goodClass p₀ β lam M ε₀ d j).card := by
      rw [hcls]
    simp only [goodClass] at hc
    rw [hc] at h
    exact h
  refine mem_badPointsTypeThree_iff.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_union, not_or]
    exact ⟨hk1, hk2⟩
  · simp only [goodClass] at hcls
    rw [hcls]
    exact hne

/-- A bad point of type 3 has a `U`-class with at most `p(β)` elements. -/
theorem card_classOn_le_of_typeThree {j : Fin N} (hj : j ∈ badPointsTypeThree p₀ β lam M ε₀ d) :
    (goodClass p₀ β lam M ε₀ d j).card ≤ pBeta p₀ β := by
  obtain ⟨hj12, -⟩ := mem_badPointsTypeThree_iff.mp hj
  have hj1 : j ∉ badPointsTypeOne p₀ β lam ε₀ d := fun h => hj12 (Finset.mem_union_left _ h)
  have hj2 : j ∉ badPointsTypeTwo p₀ β lam M ε₀ d := fun h => hj12 (Finset.mem_union_right _ h)
  by_contra h
  push Not at h
  exact hj2 (mem_badPointsTypeTwo_iff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj1⟩,
    Or.inl h⟩)

theorem mem_badPoints_of_typeThree {j : Fin N} (hj : j ∈ badPointsTypeThree p₀ β lam M ε₀ d) :
    j ∈ badPoints p₀ β lam M ε₀ d :=
  Finset.mem_union_right _ hj

/-- A good point is at distance `> M max(r_i, λ)` from `I^1_bad ∪ I^2_bad` (otherwise it would be
in `J^3_bad`, hence of type 3). -/
theorem lt_dipoleDist_of_good_of_typeOneTwo {i l : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d)
    (hl : l ∈ badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d) :
    M * max ‖(d i).1 - (d i).2‖ lam < dipoleDist (d i) (d l) := by
  classical
  obtain ⟨hi1, hi2, hi3⟩ := mem_goodPoints_iff.mp hi
  by_contra h
  push Not at h
  apply hi3
  refine mem_badPointsTypeThree_iff.mpr ⟨?_, i, Finset.mem_inter.mpr ⟨mem_classOn_self _ i, ?_⟩⟩
  · rw [Finset.mem_union, not_or]
    exact ⟨hi1, hi2⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, l, hl, h⟩
    rw [Finset.mem_union, not_or]
    exact ⟨hi1, hi2⟩

/-! ### Lemma 5.9 (1) -/

/-- One step of the chain to a seed (proof of Lemma 5.9): if `i` is good, `k` is bad with
`d_ik < M A_i` and `d_{kk'} ≤ M max(r_k, λ)`, then `d_{ik'} < 3 d_ik`. -/
theorem chain_step (hlam : 0 < lam) (hM : 1 ≤ M) {i k k' : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hk : k ∈ badPoints p₀ β lam M ε₀ d)
    (hD : dipoleDist (d i) (d k) < M * max ‖(d i).1 - (d i).2‖ lam)
    (hkk' : dipoleDist (d k) (d k') ≤ M * max ‖(d k).1 - (d k).2‖ lam) :
    dipoleDist (d i) (d k') < 3 * dipoleDist (d i) (d k) := by
  set A := max ‖(d i).1 - (d i).2‖ lam
  set B := max ‖(d k).1 - (d k).2‖ lam
  have hsep := lt_dipoleDist_of_good_of_bad (zero_le_one.trans hM) hi hk
  have hBA : B < A := by
    by_contra h
    push Not at h
    rw [min_eq_left h] at hsep
    exact absurd (hsep.trans hD) (lt_irrefl _)
  rw [min_eq_right hBA.le] at hsep
  have hB0 : 0 ≤ B := hlam.le.trans (le_max_right _ _)
  have hrk : ‖(d k).1 - (d k).2‖ ≤ B := le_max_left _ _
  have hBM : B ≤ M * B := le_mul_of_one_le_left hB0 hM
  have htri := dipoleDist_le_add (d i) (d k) (d k')
  linarith

/-- The chain along a walk of bad points (proof of Lemma 5.9): the distance to the good point `i`
grows by a factor `< 3` per step while it stays below `M A_i`. -/
theorem chain_walk (hlam : 0 < lam) (hM : 1 ≤ M) {i : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) {U : Finset (Fin N)} :
    ∀ {u v : Fin N} (w : (classGraph M lam d U).Walk u v),
      (∀ k ∈ w.support, k ∈ badPoints p₀ β lam M ε₀ d) → ∀ c : ℝ,
      3 ^ w.length * c ≤ M * max ‖(d i).1 - (d i).2‖ lam →
      dipoleDist (d i) (d u) < c → dipoleDist (d i) (d v) < 3 ^ w.length * c := by
  intro u v w
  induction w with
  | nil => intro _ c _ hu; simpa using hu
  | @cons u u' v hadj w ih =>
    intro hbad c hc hu
    have hc0 : 0 ≤ c := (dipoleDist_nonneg _ _).trans hu.le
    have hlen : (SimpleGraph.Walk.cons hadj w).length = w.length + 1 := rfl
    rw [hlen, pow_succ] at hc ⊢
    have hukc : c ≤ 3 ^ w.length * 3 * c := by
      have : (1 : ℝ) ≤ 3 ^ w.length * 3 := by
        have := one_le_pow₀ (M₀ := ℝ) (a := 3) (by norm_num) (n := w.length)
        linarith
      nlinarith
    have hDu : dipoleDist (d i) (d u) < M * max ‖(d i).1 - (d i).2‖ lam := by linarith
    have hlink : dipoleDist (d u) (d u') ≤ M * max ‖(d u).1 - (d u).2‖ lam := by
      rw [SimpleGraph.fromRel_adj] at hadj
      have h' : MultipoleLinked M lam (d u) (d u') ∨ MultipoleLinked M lam (d u') (d u) := by
        rcases hadj.2 with h | h
        · exact Or.inl h.2.2
        · exact Or.inr h.2.2
      exact min4_le_of_linked (zero_le_one.trans hM) h'
    have hstep := chain_step hlam hM hi (hbad u (SimpleGraph.Walk.start_mem_support _)) hDu hlink
    have := ih (fun k hk => hbad k (List.mem_cons_of_mem _ hk)) (3 * c)
      (by linarith) (by linarith)
    linarith

/-- **Lemma 5.9 (1)**, eq. (5.9) (proof): for `i ∈ I_good`,
`d_{i,bad} ≥ max(r_i, λ)`. Hypotheses: `0 < λ ≤ ε₀ R̄` and `3^{p(β)} ≤ M` (the paper has
`M > max(20, 3^{p(β)})`). -/
theorem lemma_5_9_1 (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    max ‖(d i).1 - (d i).2‖ lam ≤ badDist p₀ β lam M ε₀ d i := by
  classical
  set A := max ‖(d i).1 - (d i).2‖ lam with hA
  have hA0 : 0 < A := lt_max_of_lt_right hlam
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hMA : A ≤ M * A := le_mul_of_one_le_left hA0.le hM1
  refine le_badDist ?_ fun j hj => ?_
  · have := norm_le_of_good hi
    exact max_le (by linarith) (by linarith)
  by_contra hDj
  push Not at hDj
  -- `j` is not of type 1 or 2
  have hj3 : j ∈ badPointsTypeThree p₀ β lam M ε₀ d := by
    rcases Finset.mem_union.mp hj with hj12 | hj3
    · exact absurd (lt_dipoleDist_of_good_of_typeOneTwo hi hj12) (not_lt.mpr (hDj.le.trans hMA))
    · exact hj3
  -- the seed `s` in the class of `j`
  obtain ⟨-, hne⟩ := mem_badPointsTypeThree_iff.mp hj3
  obtain ⟨s, hs⟩ := hne
  obtain ⟨hsj, hsJ⟩ := Finset.mem_inter.mp hs
  obtain ⟨-, l, hl, hsl⟩ := Finset.mem_filter.mp hsJ
  have hcard := card_classOn_le_of_typeThree hj3
  obtain ⟨w, hwlen, hwreach⟩ := exists_walk_length_lt (mem_classOn_iff.mp hsj)
    (goodClass p₀ β lam M ε₀ d j) fun k hk => mem_classOn_iff.mpr hk
  have hwbad : ∀ k ∈ w.support, k ∈ badPoints p₀ β lam M ε₀ d := fun k hk =>
    mem_badPoints_of_typeThree (mem_badPointsTypeThree_of_mem_classOn hj3
      (mem_classOn_iff.mpr (hwreach k hk)))
  -- the length bound `3^{m+1} ≤ 3^{p(β)} ≤ M`
  have hpow : (3 : ℝ) ^ (w.length + 1) ≤ M :=
    (pow_le_pow_right₀ (by norm_num) (by omega)).trans hM
  have hpow' : (3 : ℝ) ^ w.length * A ≤ M * A := by
    have : (3 : ℝ) ^ w.length ≤ 3 ^ (w.length + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    exact mul_le_mul_of_nonneg_right (this.trans hpow) hA0.le
  have hDs := chain_walk hlam hM1 hi w hwbad A hpow' hDj
  have hsbad : s ∈ badPoints p₀ β lam M ε₀ d := hwbad s (SimpleGraph.Walk.end_mem_support _)
  have hDs' : dipoleDist (d i) (d s) < M * A := hDs.trans_le hpow'
  have hDl := chain_step hlam hM1 hi hsbad hDs' hsl
  have hfinal : dipoleDist (d i) (d l) < M * A := by
    have : 3 * ((3 : ℝ) ^ w.length * A) = 3 ^ (w.length + 1) * A := by ring
    have h3 : (3 : ℝ) ^ (w.length + 1) * A ≤ M * A := mul_le_mul_of_nonneg_right hpow hA0.le
    linarith
  exact absurd (lt_dipoleDist_of_good_of_typeOneTwo hi hl) (not_lt.mpr hfinal.le)

/-- `d_{i,bad} ≥ λ > 0` for good `i`. -/
theorem lam_le_badDist (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    lam ≤ badDist p₀ β lam M ε₀ d i :=
  (le_max_right _ _).trans (lemma_5_9_1 hlam hlamh hM hi)

/-- `r_i ≤ d_{i,bad}` for good `i`. -/
theorem norm_le_badDist (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    ‖(d i).1 - (d i).2‖ ≤ badDist p₀ β lam M ε₀ d i :=
  (le_max_left _ _).trans (lemma_5_9_1 hlam hlamh hM hi)

/-- **Remark 5.10, good points**: `τ_i^{+,Z} = τ_i^{-,Z} ≥ r_i / 4`, hence
`r_i ≤ 2(τ_i^{+,Z} + τ_i^{-,Z})`. -/
theorem remark_5_10_good (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    radiusPlusZ p₀ β lam M ε₀ d i = radiusMinusZ p₀ β lam M ε₀ d i ∧
      ‖(d i).1 - (d i).2‖ / 4 ≤ radiusPlusZ p₀ β lam M ε₀ d i ∧
      ‖(d i).1 - (d i).2‖ ≤
        2 * (radiusPlusZ p₀ β lam M ε₀ d i + radiusMinusZ p₀ β lam M ε₀ d i) := by
  have h1 := norm_le_badDist hlam hlamh hM hi
  have h2 : ‖(d i).1 - (d i).2‖ / 4 ≤ radiusPlusZ p₀ β lam M ε₀ d i := by
    rw [radiusPlusZ_of_good hi]
    exact (div_le_div_of_nonneg_right h1 (by norm_num)).trans (le_max_left _ _)
  have heq := (radiusMinusZ_eq_radiusPlusZ hi).symm
  refine ⟨heq, h2, ?_⟩
  rw [← heq]
  linarith [norm_nonneg ((d i).1 - (d i).2)]

/-! ### Lemma 5.9 (2) -/

/-- Eqs. (5.19)–(5.20): if `i` is good and `i ↔ k` (either way), then
`d_{k,bad} ≤ (M + 2) d_{i,bad}`. -/
theorem badDist_le_of_linked (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i k : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d)
    (hik : MultipoleLinked M lam (d i) (d k) ∨ MultipoleLinked M lam (d k) (d i)) :
    badDist p₀ β lam M ε₀ d k ≤ (M + 2) * badDist p₀ β lam M ε₀ d i := by
  have hM0 : 0 ≤ M := zero_le_one.trans ((one_le_pow₀ (by norm_num)).trans hM)
  have h1 := badDist_le_add (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (d := d) i k
  have h2 : dipoleDist (d i) (d k) ≤ M * max ‖(d i).1 - (d i).2‖ lam := min4_le_of_linked hM0 hik
  have h3 := lemma_5_9_1 hlam hlamh hM hi
  have h4 : M * max ‖(d i).1 - (d i).2‖ lam ≤ M * badDist p₀ β lam M ε₀ d i :=
    mul_le_mul_of_nonneg_left h3 hM0
  have h5 : ‖(d i).1 - (d i).2‖ ≤ max ‖(d i).1 - (d i).2‖ lam := le_max_left _ _
  linarith

/-- **Lemma 5.9 (2)**, eq. (5.10) (proof): for good `i, j` in the
same multipole, `d_{j,bad} ≤ C d_{i,bad}` with `C = (M + 2)^{p(β) - 1}`. -/
theorem lemma_5_9_2 (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i j : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d)
    (hij : (SimpleGraph.fromRel fun a b : Fin N => MultipoleLinked M lam (d a) (d b)).Reachable
      i j) :
    badDist p₀ β lam M ε₀ d j ≤ (M + 2) ^ (pBeta p₀ β - 1) * badDist p₀ β lam M ε₀ d i := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans ((one_le_pow₀ (by norm_num)).trans hM)
  have hcap : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlamh
  obtain ⟨w, hwlen, hwreach⟩ := exists_walk_length_lt hij (goodClass p₀ β lam M ε₀ d i)
    fun k hk => (reachable_iff_mem_classOn hM0 hi).mp hk
  have hcard := card_classOn_le hi
  -- along the walk all points are good and the distance grows by at most `M + 2`
  have key : ∀ {u v : Fin N} (w : (linkGraph M lam d).Walk u v),
      (∀ k ∈ w.support, k ∈ goodPoints p₀ β lam M ε₀ d) →
      badDist p₀ β lam M ε₀ d v ≤ (M + 2) ^ w.length * badDist p₀ β lam M ε₀ d u := by
    intro u v w
    induction w with
    | nil => intro _; simp
    | @cons u u' v hadj w ih =>
      intro hgood
      have hu := hgood u (SimpleGraph.Walk.start_mem_support _)
      rw [SimpleGraph.fromRel_adj] at hadj
      have hstep := badDist_le_of_linked hlam hlamh hM hu hadj.2
      have := ih fun k hk => hgood k (List.mem_cons_of_mem _ hk)
      have hpos : 0 ≤ (M + 2) ^ w.length := by positivity
      calc badDist p₀ β lam M ε₀ d v ≤ (M + 2) ^ w.length * badDist p₀ β lam M ε₀ d u' := this
        _ ≤ (M + 2) ^ w.length * ((M + 2) * badDist p₀ β lam M ε₀ d u) :=
          mul_le_mul_of_nonneg_left hstep hpos
        _ = (M + 2) ^ (SimpleGraph.Walk.cons _ w).length * badDist p₀ β lam M ε₀ d u := by
          rw [SimpleGraph.Walk.length_cons, pow_succ]; ring
  have h := key w fun k hk => good_of_mem_classOn hi
    ((reachable_iff_mem_classOn hM0 hi).mp (hwreach k hk))
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (badDist_nonneg hcap i))
  exact pow_le_pow_right₀ (by linarith) (by omega)

/-! ### Lemma 5.9 (3)–(4) -/

/-- `p(β) ≥ 1` as soon as there is a good point. -/
theorem one_le_pBeta_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    1 ≤ pBeta p₀ β :=
  (Finset.card_pos.mpr ⟨i, mem_classOn_self _ i⟩).trans_le (card_classOn_le hi)

theorem three_le_M_of_good (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) : 3 ≤ M :=
  (le_self_pow₀ (by norm_num) (Nat.one_le_iff_ne_zero.mp (one_le_pBeta_of_good hi))).trans hM

/-- The core of eqs. (5.11)–(5.12): if `i` is good, `j` is bad, `x` is an endpoint of `j` with
radius `τ ≥ λ`, `τ ≤ max(r_j/4, λ)`, and `dist({x_i, y_i}, x) < τ_i^Z + τ`, then
`dist({x_i, y_i}, x) ≤ 2τ` and `max(r_i, λ) ≤ max(r_j, λ)`. -/
theorem geo_core (hlam : 0 < lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i j : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hj : j ∈ badPoints p₀ β lam M ε₀ d) {D τ : ℝ}
    (hDij : dipoleDist (d i) (d j) ≤ D) (hτ : lam ≤ τ)
    (hτj : τ ≤ max (‖(d j).1 - (d j).2‖ / 4) lam)
    (hD : D < radiusPlusZ p₀ β lam M ε₀ d i + τ) :
    D ≤ 2 * τ ∧ max ‖(d i).1 - (d i).2‖ lam ≤ max ‖(d j).1 - (d j).2‖ lam := by
  have hM3 := three_le_M_of_good hM hi
  have hbd := badDist_le_dipoleDist (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀)
    (d := d) i hj
  have hτi : radiusPlusZ p₀ β lam M ε₀ d i ≤ max (D / 4) lam := by
    rw [radiusPlusZ_of_good hi]
    exact max_le_max (by linarith) le_rfl
  have h2τ : D ≤ 2 * τ := by
    rcases le_total (D / 4) lam with h | h
    · rw [max_eq_right h] at hτi
      linarith
    · rw [max_eq_left h] at hτi
      linarith
  refine ⟨h2τ, ?_⟩
  by_contra hlt
  push Not at hlt
  apply not_multipoleLinked_of_good_of_bad (zero_le_three.trans hM3) hi hj
  show dipoleDist (d i) (d j) ≤ _
  rw [min_eq_right hlt.le]
  have h1 : max (‖(d j).1 - (d j).2‖ / 4) lam ≤ max ‖(d j).1 - (d j).2‖ lam :=
    max_le_max (by linarith [norm_nonneg ((d j).1 - (d j).2)]) le_rfl
  have h0 : 0 ≤ max ‖(d j).1 - (d j).2‖ lam := hlam.le.trans (le_max_right _ _)
  nlinarith

/-- **Lemma 5.9 (3)**, eq. (5.11) (proof): if `i ∈ I_good`,
`j ∈ I_bad` and `v^Z_{i,j,+} ≠ 0`, then `d_{i,j}^+ ≤ 2 τ_j^{+,Z}` and
`max(r_i, λ) ≤ max(r_j, λ)`, where `d_{i,j}^+ = dist({x_i, y_i}, x_j)`. -/
theorem lemma_5_9_3 {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i j : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d)
    (hj : j ∈ badPoints p₀ β lam M ε₀ d) (hv : interactionPlusZ χ p₀ β lam M ε₀ d i j ≠ 0) :
    min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ ≤ 2 * radiusPlusZ p₀ β lam M ε₀ d j ∧
      max ‖(d i).1 - (d i).2‖ lam ≤ max ‖(d j).1 - (d j).2‖ lam := by
  have hsupp := halfInteractionPlus_ne_zero hχ hlam (lam_le_radiusPlusZ (M := M) (ε₀ := ε₀))
    (lam_le_radiusMinusZ (M := M) (ε₀ := ε₀)) hv
  rw [radiusMinusZ_eq_radiusPlusZ hi] at hsupp
  refine geo_core hlam hM hi hj (dipoleDist_le_min_fst _ _) (lam_le_radiusPlusZ j)
    (radiusPlusZ_le_max_div hj) ?_
  rcases hsupp with h | h
  · exact (min_le_left _ _).trans_lt h
  · exact (min_le_right _ _).trans_lt h

/-- **Lemma 5.9 (4)**, eq. (5.12) (proof): if `i ∈ I_good`, `j ∈ I_bad`
and `v^Z_{i,j,-} ≠ 0`, then `d_{i,j}^- ≤ 2 τ_j^{-,Z}` and `max(r_i, λ) ≤ max(r_j, λ)`, where
`d_{i,j}^- = dist({x_i, y_i}, y_j)`. -/
theorem lemma_5_9_4 {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i j : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d)
    (hj : j ∈ badPoints p₀ β lam M ε₀ d) (hv : interactionMinusZ χ p₀ β lam M ε₀ d i j ≠ 0) :
    min ‖(d i).1 - (d j).2‖ ‖(d i).2 - (d j).2‖ ≤ 2 * radiusMinusZ p₀ β lam M ε₀ d j ∧
      max ‖(d i).1 - (d i).2‖ lam ≤ max ‖(d j).1 - (d j).2‖ lam := by
  have hsupp := halfInteractionMinus_ne_zero hχ hlam (lam_le_radiusPlusZ (M := M) (ε₀ := ε₀))
    (lam_le_radiusMinusZ (M := M) (ε₀ := ε₀)) hv
  rw [radiusMinusZ_eq_radiusPlusZ hi] at hsupp
  refine geo_core hlam hM hi hj (dipoleDist_le_min_snd _ _) (lam_le_radiusMinusZ j)
    (radiusMinusZ_le_max_div hj) ?_
  rcases hsupp with h | h
  · exact (min_le_left _ _).trans_lt h
  · exact (min_le_right _ _).trans_lt h

/-! ### Lemma 5.9 (5)–(6) -/

/-- **Eq. (5.24)**, abstract form: let `D` be a function on the labels (the paper's
`d_{·,bad}`) and `τ^± ≥ λ > 0` radii with `τ_k^+ = τ_k^- = max(D_k/4, λ)` for `k ∈ {i, i'}`. If
`r_i ≤ D_i`, `λ ≤ D_i`, `D_{i'} ≤ D_i + r_i + d_{ii'}` (eq. (5.22)) and `v'_{ii'} ≠ 0`, then
`D_{i'} ≤ 6 D_i`. (Also usable in the frozen-configuration convention of §5.3.) -/
theorem le_six_mul_of_ballGrowthInteraction_ne_zero {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (hlam : 0 < lam) {τp τm : Fin N → ℝ} (hp : ∀ k, lam ≤ τp k) (hm : ∀ k, lam ≤ τm k)
    {D : Fin N → ℝ} {i i' : Fin N} (hpi : τp i = max (D i / 4) lam)
    (hpi' : τp i' = max (D i' / 4) lam) (hmi : τm i = τp i) (hmi' : τm i' = τp i')
    (hr : ‖(d i).1 - (d i).2‖ ≤ D i) (hl : lam ≤ D i)
    (htri : D i' ≤ D i + ‖(d i).1 - (d i).2‖ + dipoleDist (d i) (d i'))
    (hv : ballGrowthInteraction χ lam τp τm d i i' ≠ 0) : D i' ≤ 6 * D i := by
  have hD := dipoleDist_lt_of_ballGrowthInteraction_ne_zero hχ hlam hp hm hv
  rw [hmi, hmi', max_self, max_self, hpi, hpi'] at hD
  have hdi0 : 0 ≤ D i := hlam.le.trans hl
  have hT : max (D i / 4) lam ≤ D i := max_le (by linarith) hl
  have hD2 : dipoleDist (d i) (d i') < 2 * D i := by
    rcases le_total (D i' / 4) lam with h | h
    · rw [max_eq_right h] at hD
      linarith
    · rw [max_eq_left h] at hD
      linarith
  linarith

/-- **Eq. (5.24)**: if `i, i'` are good and `v^Z_{ii'} ≠ 0`, then
`d_{i',bad} ≤ 6 d_{i,bad}` (the paper's `6 max(d_{i,bad}, λ)`, with (5.9)). -/
theorem badDist_le_six_mul {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i i' : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hi' : i' ∈ goodPoints p₀ β lam M ε₀ d)
    (hv : interactionZ χ p₀ β lam M ε₀ d i i' ≠ 0) :
    badDist p₀ β lam M ε₀ d i' ≤ 6 * badDist p₀ β lam M ε₀ d i := by
  rw [interactionZ_eq_ballGrowthInteraction] at hv
  exact le_six_mul_of_ballGrowthInteraction_ne_zero hχ hlam lam_le_radiusPlusZ lam_le_radiusMinusZ
    (radiusPlusZ_of_good hi) (radiusPlusZ_of_good hi') (radiusMinusZ_eq_radiusPlusZ hi)
    (radiusMinusZ_eq_radiusPlusZ hi') (norm_le_badDist hlam hlamh hM hi)
    (lam_le_badDist hlam hlamh hM hi) (badDist_le_add i i') hv

/-- **Lemma 5.9 (5)**, eq. (5.13) (proof): if `i_0, …, i_n` are good
and `v^Z_{i_0 i_1} ⋯ v^Z_{i_{n-1} i_n} ≠ 0`, then `d_{i_n,bad} ≤ 6^n d_{i_0,bad}` (the paper's
`K = n + 1`). -/
theorem lemma_5_9_5 {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (i : ℕ → Fin N) (n : ℕ) (hgood : ∀ k ≤ n, i k ∈ goodPoints p₀ β lam M ε₀ d)
    (hv : ∏ k ∈ Finset.range n, interactionZ χ p₀ β lam M ε₀ d (i k) (i (k + 1)) ≠ 0) :
    badDist p₀ β lam M ε₀ d (i n) ≤ 6 ^ n * badDist p₀ β lam M ε₀ d (i 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ] at hv
    have hv1 := left_ne_zero_of_mul hv
    have hv2 := right_ne_zero_of_mul hv
    have hstep := badDist_le_six_mul hχ hlam hlamh hM (hgood n (Nat.le_succ n))
      (hgood (n + 1) le_rfl) hv2
    have := ih (fun k hk => hgood k (hk.trans (Nat.le_succ n))) hv1
    calc badDist p₀ β lam M ε₀ d (i (n + 1)) ≤ 6 * badDist p₀ β lam M ε₀ d (i n) := hstep
      _ ≤ 6 * (6 ^ n * badDist p₀ β lam M ε₀ d (i 0)) := by linarith
      _ = 6 ^ (n + 1) * badDist p₀ β lam M ε₀ d (i 0) := by ring

/-- **Lemma 5.9 (6)**, eq. (5.14) (proof): if `i_0, …, i_n` and
`i_0', …, i_n'` are good, `i_l'` and `i_{l+1}` lie in the same multipole for `l < n`, and
`v^Z_{i_0 i_0'} ⋯ v^Z_{i_n i_n'} ≠ 0`, then `d_{i_n',bad} ≤ C^{n+1} d_{i_0,bad}` with
`C = 6 (M + 2)^{p(β) - 1}` (the paper's `K = n + 1`; its hypothesis `i_l ≠ i_l'` is not
needed). -/
theorem lemma_5_9_6 {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (i i' : ℕ → Fin N) (n : ℕ) (hgood : ∀ l ≤ n, i l ∈ goodPoints p₀ β lam M ε₀ d)
    (hgood' : ∀ l ≤ n, i' l ∈ goodPoints p₀ β lam M ε₀ d)
    (hmult : ∀ l < n, (SimpleGraph.fromRel fun a b : Fin N =>
      MultipoleLinked M lam (d a) (d b)).Reachable (i' l) (i (l + 1)))
    (hv : ∏ l ∈ Finset.range (n + 1), interactionZ χ p₀ β lam M ε₀ d (i l) (i' l) ≠ 0) :
    badDist p₀ β lam M ε₀ d (i' n) ≤
      (6 * (M + 2) ^ (pBeta p₀ β - 1)) ^ (n + 1) * badDist p₀ β lam M ε₀ d (i 0) := by
  have hM0 : 0 ≤ M := zero_le_one.trans ((one_le_pow₀ (by norm_num)).trans hM)
  have hcap : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlamh
  set C₀ := (M + 2) ^ (pBeta p₀ β - 1)
  have hC₀ : 1 ≤ C₀ := one_le_pow₀ (by linarith)
  have hv' : ∀ l ≤ n, interactionZ χ p₀ β lam M ε₀ d (i l) (i' l) ≠ 0 := fun l hl =>
    (Finset.prod_ne_zero_iff.mp hv) l (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  have hstep : ∀ l ≤ n, badDist p₀ β lam M ε₀ d (i' l) ≤ 6 * badDist p₀ β lam M ε₀ d (i l) :=
    fun l hl => badDist_le_six_mul hχ hlam hlamh hM (hgood l hl) (hgood' l hl) (hv' l hl)
  -- `d_{i_l,bad} ≤ (6 C₀)^l d_{i_0,bad}`
  have hchain : ∀ l ≤ n, badDist p₀ β lam M ε₀ d (i l) ≤
      (6 * C₀) ^ l * badDist p₀ β lam M ε₀ d (i 0) := by
    intro l
    induction l with
    | zero => intro _; simp
    | succ l ih =>
      intro hl
      have h1 := ih (Nat.le_of_succ_le hl)
      have h2 := hstep l (Nat.le_of_succ_le hl)
      have h3 := lemma_5_9_2 hlam hlamh hM (hgood' l (Nat.le_of_succ_le hl)) (hmult l hl)
      have h0 : 0 ≤ badDist p₀ β lam M ε₀ d (i' l) := badDist_nonneg hcap _
      calc badDist p₀ β lam M ε₀ d (i (l + 1)) ≤ C₀ * badDist p₀ β lam M ε₀ d (i' l) := h3
        _ ≤ C₀ * (6 * badDist p₀ β lam M ε₀ d (i l)) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
        _ ≤ C₀ * (6 * ((6 * C₀) ^ l * badDist p₀ β lam M ε₀ d (i 0))) := by
          gcongr
        _ = (6 * C₀) ^ (l + 1) * badDist p₀ β lam M ε₀ d (i 0) := by ring
  have h0 : 0 ≤ badDist p₀ β lam M ε₀ d (i 0) := badDist_nonneg hcap _
  have h6C : 6 ≤ 6 * C₀ := by linarith
  calc badDist p₀ β lam M ε₀ d (i' n) ≤ 6 * badDist p₀ β lam M ε₀ d (i n) := hstep n le_rfl
    _ ≤ 6 * ((6 * C₀) ^ n * badDist p₀ β lam M ε₀ d (i 0)) := by
      have := hchain n le_rfl
      linarith
    _ ≤ (6 * C₀) * ((6 * C₀) ^ n * badDist p₀ β lam M ε₀ d (i 0)) := by
      have : 0 ≤ (6 * C₀) ^ n * badDist p₀ β lam M ε₀ d (i 0) := by positivity
      nlinarith
    _ = (6 * C₀) ^ (n + 1) * badDist p₀ β lam M ε₀ d (i 0) := by ring

end UpperBound

end MultipoleBKT

end
