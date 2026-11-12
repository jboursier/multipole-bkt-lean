/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.PlusModel
public import MultipoleBKT.UpperBound.BadPoints.Geometry

/-!
# Geometry of a good dipole and frozen bad points (the geometric part of Proposition 5.18)

The paper: proof of Proposition 5.18 (Proposition 5.18, blue): "We first check (5.9) on the support of `𝖯_X^{+,ε₀,Z}`. Suppose
`d_{i,bad} < A := max(r_i, λ)`. The nearest bad dipole has type 3. Follow its component in
`Π_mult^{V_bad ∖ I^1_bad}` to a seed in `J^3_bad`, then to a dipole of type 1 or 2 … The final
distance is less than `3^{p(β)} A < M A`, contradicting (5.51).". It is Lemma 5.9 (1) with `I_good`
replaced by `I_good^Z` and the bad sets computed on `V_bad` from the frozen dipoles `Z`
(frozen-configuration convention).

Throughout, `V : Finset (Fin N)` is the set of bad labels, `Z : Fin N → ℂ × ℂ` the frozen
configuration (only `Z j`, `j ∈ V`, matters), the bad sets are `typeOneOn`, `typeTwoOn`,
`typeThreeOn`, `badPointsOn` of `MultipoleBKT.UpperBound.Hierarchical.BadSetOn`, and `e = (x, y)` is
a good dipole with `e ∈ I_good^Z` (`IsGoodZ`). The convention `I_bad^{V}(Z) = V` is used in the
form `V ⊆ I_bad^V(Z)`.

* `mem_typeTwoOn_iff`, `mem_typeThreeOn_iff`, `mem_typeThreeOn_of_mem_classOn`,
  `card_classOn_le_of_typeThreeOn`: the classes of the type-3 bad points computed on `V`;
* `lt_dipoleDist_of_isGoodZ`: a dipole of `I_good^Z` is not linked to a bad dipole,
  `M min(max(r_e, λ), max(r_j, λ)) < d(e, Z_j)` (Remark 5.6 (1) on the support);
* `max_le_badDistZ`: **eq. (5.9) on the support**: `max(r_e, λ) ≤ d_{e,bad}` for `e ∈ I_good^Z`
  with `r_e ≤ ε₀ R̄`;
* `div_four_le_goodRadiusZ`, `dipoleWeightZ_le`, `exp_neg_le_dipoleWeightZ`: `τ_e^Z ≥ r_e / 4`, hence
  `e^{-16|L|} 𝟙_{I_good^Z} ≤ e^{L r_e²/(τ_e^Z)²} 𝟙_{I_good^Z} ≤ e^{16|L|}` (the bound used in
  Lemma A.3 and in the singleton bounds);
* `badDistZ_le_add`, `badDistZ_le_of_linked`: eqs. (5.22), (5.19)–(5.20) for good dipoles:
  `d_{e',bad} ≤ (M + 2) d_{e,bad}` if `e ↔ e'` (the step of (5.10));
* `badDistZ_le_six_mul`: eq. (5.24): if `v^Z(e, e') ≠ 0` then `d_{e',bad} ≤ 6 d_{e,bad}` (the step of
  (5.13), (5.14)).

The hypotheses are `0 < λ ≤ ε₀ R̄` and `3^{p(β)} ≤ M` (the paper's `M > max(20, 3^{p(β)})`).
-/

@[expose] public section

open Finset
open MultipoleBKT.TheoremTwo

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-! ### The bad sets computed on `V` -/

section Classes

/-- `U_V = V ∖ I^1_V`, the set on which the multipoles of Definitions 5.3–5.4 are computed. -/
noncomputable abbrev complOn (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  V \ typeOneOn p₀ β lam ε₀ V Z

/-- The class `[j]^{Π_mult^{U_V}}`. -/
noncomputable abbrev classOnV (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (j : Fin N) : Finset (Fin N) :=
  multipoleClassOn M lam Z (complOn p₀ β lam ε₀ V Z) j

/-- Membership in `I^2_V` depends only on membership in `U_V` and on `|[i]^{U_V}|`. -/
theorem mem_typeTwoOn_iff {i : Fin N} :
    i ∈ typeTwoOn p₀ β lam M ε₀ V Z ↔
      i ∈ complOn p₀ β lam ε₀ V Z ∧
        (pBeta p₀ β < (classOnV p₀ β lam M ε₀ V Z i).card ∨
          ((classOnV p₀ β lam M ε₀ V Z i).card ∈ Finset.Icc 1 (pBeta p₀ β) ∧
            ε₀ ^ (-alphaExponent β) * N *
                lam ^ (2 * ((classOnV p₀ β lam M ε₀ V Z i).card - 1)) <
              (((complOn p₀ β lam ε₀ V Z).filter fun u =>
                (classOnV p₀ β lam M ε₀ V Z u).card =
                  (classOnV p₀ β lam M ε₀ V Z i).card).card : ℝ))) := by
  classical
  unfold typeTwoOn
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

/-- The seeds `J^3_V`. -/
noncomputable abbrev seedsOn (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) : Finset (Fin N) :=
  (V \ (typeOneOn p₀ β lam ε₀ V Z ∪ typeTwoOn p₀ β lam M ε₀ V Z)).filter fun i =>
    ∃ j ∈ typeOneOn p₀ β lam ε₀ V Z ∪ typeTwoOn p₀ β lam M ε₀ V Z,
      min (min ‖(Z i).1 - (Z j).1‖ ‖(Z i).1 - (Z j).2‖)
          (min ‖(Z i).2 - (Z j).1‖ ‖(Z i).2 - (Z j).2‖)
        ≤ M * max ‖(Z i).1 - (Z i).2‖ lam

theorem mem_typeThreeOn_iff {i : Fin N} :
    i ∈ typeThreeOn p₀ β lam M ε₀ V Z ↔
      i ∈ V \ (typeOneOn p₀ β lam ε₀ V Z ∪ typeTwoOn p₀ β lam M ε₀ V Z) ∧
        (classOnV p₀ β lam M ε₀ V Z i ∩ seedsOn p₀ β lam M ε₀ V Z).Nonempty := by
  classical
  unfold typeThreeOn
  simp only [Finset.mem_filter]

/-- Every label of the `U_V`-class of a bad point of type 3 (computed on `V`) is of type 3. -/
theorem mem_typeThreeOn_of_mem_classOn {j k : Fin N} (hj : j ∈ typeThreeOn p₀ β lam M ε₀ V Z)
    (hk : k ∈ classOnV p₀ β lam M ε₀ V Z j) : k ∈ typeThreeOn p₀ β lam M ε₀ V Z := by
  classical
  obtain ⟨hjV, hne⟩ := mem_typeThreeOn_iff.mp hj
  obtain ⟨hjV, hj12⟩ := Finset.mem_sdiff.mp hjV
  have hj1 : j ∉ typeOneOn p₀ β lam ε₀ V Z := fun h => hj12 (Finset.mem_union_left _ h)
  have hj2 : j ∉ typeTwoOn p₀ β lam M ε₀ V Z := fun h => hj12 (Finset.mem_union_right _ h)
  have hjU : j ∈ complOn p₀ β lam ε₀ V Z := Finset.mem_sdiff.mpr ⟨hjV, hj1⟩
  have hkU : k ∈ complOn p₀ β lam ε₀ V Z := mem_of_classGraph_reachable hjU (mem_classOn_iff.mp hk)
  have hcls : classOnV p₀ β lam M ε₀ V Z k = classOnV p₀ β lam M ε₀ V Z j := classOn_eq_of_mem hk
  have hk1 : k ∉ typeOneOn p₀ β lam ε₀ V Z := (Finset.mem_sdiff.mp hkU).2
  have hk2 : k ∉ typeTwoOn p₀ β lam M ε₀ V Z := by
    intro h2
    obtain ⟨-, h⟩ := mem_typeTwoOn_iff.mp h2
    apply hj2
    refine mem_typeTwoOn_iff.mpr ⟨hjU, ?_⟩
    rw [hcls] at h
    exact h
  refine mem_typeThreeOn_iff.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hkU).1, ?_⟩, ?_⟩
  · rw [Finset.mem_union, not_or]
    exact ⟨hk1, hk2⟩
  · rw [hcls]
    exact hne

/-- A bad point of type 3 (computed on `V`) has a `U_V`-class with at most `p(β)` elements. -/
theorem card_classOn_le_of_typeThreeOn {j : Fin N} (hj : j ∈ typeThreeOn p₀ β lam M ε₀ V Z) :
    (classOnV p₀ β lam M ε₀ V Z j).card ≤ pBeta p₀ β := by
  obtain ⟨hjV, -⟩ := mem_typeThreeOn_iff.mp hj
  obtain ⟨hjV, hj12⟩ := Finset.mem_sdiff.mp hjV
  have hj1 : j ∉ typeOneOn p₀ β lam ε₀ V Z := fun h => hj12 (Finset.mem_union_left _ h)
  have hj2 : j ∉ typeTwoOn p₀ β lam M ε₀ V Z := fun h => hj12 (Finset.mem_union_right _ h)
  by_contra h
  push Not at h
  exact hj2 (mem_typeTwoOn_iff.mpr ⟨Finset.mem_sdiff.mpr ⟨hjV, hj1⟩, Or.inl h⟩)

theorem mem_badPointsOn_of_typeThreeOn {j : Fin N} (hj : j ∈ typeThreeOn p₀ β lam M ε₀ V Z) :
    j ∈ badPointsOn p₀ β lam M ε₀ V Z :=
  Finset.mem_union_right _ hj

end Classes

/-! ### A good dipole and the bad points -/

section Separation

/-- `max(min(a, b), c) = min(max(a, c), max(b, c))`. -/
theorem max_min_eq_min_max (a b c : ℝ) : max (min a b) c = min (max a c) (max b c) :=
  max_min_distrib_right a b c

/-- **Remark 5.6 (1) on the support**: a dipole `e ∈ I_good^Z` is not linked to a bad dipole:
`M min(max(r_e, λ), max(r_j, λ)) < d(e, Z_j)` for `j ∈ I_bad^V(Z)`. -/
theorem lt_dipoleDist_of_isGoodZ (hM : 0 ≤ M) {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    {j : Fin N} (hj : j ∈ badPointsOn p₀ β lam M ε₀ V Z) :
    M * min (max ‖e.1 - e.2‖ lam) (max ‖(Z j).1 - (Z j).2‖ lam) < dipoleDist e (Z j) := by
  rcases Finset.mem_union.mp hj with hj12 | hj3
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_left _ _) hM) (he.1 j hj12)
  · have := he.2 j hj3
    rwa [max_min_eq_min_max] at this

/-- One step of the chain to a seed: if `e ∈ I_good^Z`, `k` is bad with `d(e, Z_k) < M A_e` and
`d(Z_k, Z_{k'}) ≤ M max(r_k, λ)`, then `d(e, Z_{k'}) < 3 d(e, Z_k)`. -/
theorem chain_step_Z (hlam : 0 < lam) (hM : 1 ≤ M) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) {k k' : Fin N} (hk : k ∈ badPointsOn p₀ β lam M ε₀ V Z)
    (hD : dipoleDist e (Z k) < M * max ‖e.1 - e.2‖ lam)
    (hkk' : dipoleDist (Z k) (Z k') ≤ M * max ‖(Z k).1 - (Z k).2‖ lam) :
    dipoleDist e (Z k') < 3 * dipoleDist e (Z k) := by
  set A := max ‖e.1 - e.2‖ lam
  set B := max ‖(Z k).1 - (Z k).2‖ lam
  have hsep := lt_dipoleDist_of_isGoodZ (zero_le_one.trans hM) he hk
  have hBA : B < A := by
    by_contra h
    push Not at h
    rw [min_eq_left h] at hsep
    exact absurd (hsep.trans hD) (lt_irrefl _)
  rw [min_eq_right hBA.le] at hsep
  have hB0 : 0 ≤ B := hlam.le.trans (le_max_right _ _)
  have hrk : ‖(Z k).1 - (Z k).2‖ ≤ B := le_max_left _ _
  have hBM : B ≤ M * B := le_mul_of_one_le_left hB0 hM
  have htri := dipoleDist_le_add e (Z k) (Z k')
  linarith

/-- The chain along a walk of bad points: the distance to `e` grows by a factor `< 3` per step
while it stays below `M A_e`. -/
theorem chain_walk_Z (hlam : 0 < lam) (hM : 1 ≤ M) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) {U : Finset (Fin N)} :
    ∀ {u v : Fin N} (w : (classGraph M lam Z U).Walk u v),
      (∀ k ∈ w.support, k ∈ badPointsOn p₀ β lam M ε₀ V Z) → ∀ c : ℝ,
      3 ^ w.length * c ≤ M * max ‖e.1 - e.2‖ lam →
      dipoleDist e (Z u) < c → dipoleDist e (Z v) < 3 ^ w.length * c := by
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
    have hDu : dipoleDist e (Z u) < M * max ‖e.1 - e.2‖ lam := by linarith
    have hlink : dipoleDist (Z u) (Z u') ≤ M * max ‖(Z u).1 - (Z u).2‖ lam := by
      rw [SimpleGraph.fromRel_adj] at hadj
      have h' : MultipoleLinked M lam (Z u) (Z u') ∨ MultipoleLinked M lam (Z u') (Z u) := by
        rcases hadj.2 with h | h
        · exact Or.inl h.2.2
        · exact Or.inr h.2.2
      exact min4_le_of_linked (zero_le_one.trans hM) h'
    have hstep := chain_step_Z hlam hM he (hbad u (SimpleGraph.Walk.start_mem_support _)) hDu hlink
    have := ih (fun k hk => hbad k (List.mem_cons_of_mem _ hk)) (3 * c)
      (by linarith) (by linarith)
    linarith

/-- **Eq. (5.9) on the support of `𝖯^{+,ε₀,Z}_X`** (proof of Proposition 5.18):
for `e ∈ I_good^Z` with `r_e ≤ ε₀ R̄`, `max(r_e, λ) ≤ d_{e,bad}`, under the frozen-configuration
convention `V ⊆ I_bad^V(Z)`, `0 < λ ≤ ε₀ R̄` and `3^{p(β)} ≤ M`. -/
theorem max_le_badDistZ (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    max ‖e.1 - e.2‖ lam ≤ badDistZ p₀ β lam ε₀ V Z e := by
  classical
  set A := max ‖e.1 - e.2‖ lam with hA
  have hA0 : 0 < A := lt_max_of_lt_right hlam
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hMA : A ≤ M * A := le_mul_of_one_le_left hA0.le hM1
  refine le_badDistZ ?_ fun j hj => ?_
  · exact max_le (by linarith) (by linarith)
  by_contra hDj
  push Not at hDj
  have hjb := hVZ hj
  -- `j` is not of type 1 or 2
  have hj3 : j ∈ typeThreeOn p₀ β lam M ε₀ V Z := by
    rcases Finset.mem_union.mp hjb with hj12 | hj3
    · exact absurd (he.1 j hj12) (not_lt.mpr (hDj.le.trans hMA))
    · exact hj3
  -- the seed `s` in the class of `j`
  obtain ⟨-, hne⟩ := mem_typeThreeOn_iff.mp hj3
  obtain ⟨s, hs⟩ := hne
  obtain ⟨hsj, hsJ⟩ := Finset.mem_inter.mp hs
  obtain ⟨-, l, hl, hsl⟩ := Finset.mem_filter.mp hsJ
  have hcard := card_classOn_le_of_typeThreeOn hj3
  obtain ⟨w, hwlen, hwreach⟩ := exists_walk_length_lt (mem_classOn_iff.mp hsj)
    (classOnV p₀ β lam M ε₀ V Z j) fun k hk => mem_classOn_iff.mpr hk
  have hwbad : ∀ k ∈ w.support, k ∈ badPointsOn p₀ β lam M ε₀ V Z := fun k hk =>
    mem_badPointsOn_of_typeThreeOn (mem_typeThreeOn_of_mem_classOn hj3
      (mem_classOn_iff.mpr (hwreach k hk)))
  have hpow : (3 : ℝ) ^ (w.length + 1) ≤ M :=
    (pow_le_pow_right₀ (by norm_num) (by omega)).trans hM
  have hpow' : (3 : ℝ) ^ w.length * A ≤ M * A := by
    have : (3 : ℝ) ^ w.length ≤ 3 ^ (w.length + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    exact mul_le_mul_of_nonneg_right (this.trans hpow) hA0.le
  have hDs := chain_walk_Z hlam hM1 he w hwbad A hpow' hDj
  have hsbad : s ∈ badPointsOn p₀ β lam M ε₀ V Z := hwbad s (SimpleGraph.Walk.end_mem_support _)
  have hDs' : dipoleDist e (Z s) < M * A := hDs.trans_le hpow'
  have hDl := chain_step_Z hlam hM1 he hsbad hDs' hsl
  have hfinal : dipoleDist e (Z l) < M * A := by
    have : 3 * ((3 : ℝ) ^ w.length * A) = 3 ^ (w.length + 1) * A := by ring
    have h3 : (3 : ℝ) ^ (w.length + 1) * A ≤ M * A := mul_le_mul_of_nonneg_right hpow hA0.le
    linarith
  exact absurd (he.1 l hl) (not_lt.mpr hfinal.le)

theorem lam_le_badDistZ (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    lam ≤ badDistZ p₀ β lam ε₀ V Z e :=
  (le_max_right _ _).trans (max_le_badDistZ hlam hlamh hM hVZ he hr)

theorem norm_le_badDistZ (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    ‖e.1 - e.2‖ ≤ badDistZ p₀ β lam ε₀ V Z e :=
  (le_max_left _ _).trans (max_le_badDistZ hlam hlamh hM hVZ he hr)

/-- `τ_e^Z ≥ r_e / 4` on the support (Remark 5.10 for `I_good^Z`). -/
theorem div_four_le_goodRadiusZ (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    ‖e.1 - e.2‖ / 4 ≤ goodRadiusZ p₀ β lam ε₀ V Z e := by
  unfold goodRadiusZ
  exact (div_le_div_of_nonneg_right (norm_le_badDistZ hlam hlamh hM hVZ he hr)
    (by norm_num)).trans (le_max_left _ _)

/-- `(r_e / τ_e^Z)² ≤ 16` on the support. -/
theorem sq_div_goodRadiusZ_le (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 ≤ 16 := by
  have hτ := goodRadiusZ_pos (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (Z := Z) hlam e
  have h4 := div_four_le_goodRadiusZ hlam hlamh hM hVZ he hr
  have h0 : 0 ≤ ‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e := div_nonneg (norm_nonneg _) hτ.le
  have h1 : ‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e ≤ 4 := by
    rw [div_le_iff₀ hτ]
    linarith
  nlinarith

open scoped Classical in
/-- The one-body weight of `𝖯^{+,ε₀,Z}` is at most `e^{16|L|}` on the dipoles with
`r_e ≤ ε₀ R̄`. -/
theorem dipoleWeightZ_le (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) (L : ℝ)
    {e : ℂ × ℂ} (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    dipoleWeightZ p₀ β lam M ε₀ L V Z e ≤ Real.exp (16 * |L|) := by
  unfold dipoleWeightZ
  split_ifs with he
  · rw [mul_one]
    refine Real.exp_le_exp.2 ?_
    have h := sq_div_goodRadiusZ_le hlam hlamh hM hVZ he hr
    have h0 := sq_nonneg (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e)
    calc L * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2
        ≤ |L| * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self L) h0
      _ ≤ |L| * 16 := mul_le_mul_of_nonneg_left h (abs_nonneg L)
      _ = 16 * |L| := by ring
  · rw [mul_zero]
    exact (Real.exp_pos _).le

open scoped Classical in
/-- On `I_good^Z` (with `r_e ≤ ε₀ R̄`), the one-body weight of `𝖯^{+,ε₀,Z}` is at least
`e^{-16|L|}`. -/
theorem exp_neg_le_dipoleWeightZ (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) (L : ℝ)
    {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    Real.exp (-(16 * |L|)) ≤ dipoleWeightZ p₀ β lam M ε₀ L V Z e := by
  unfold dipoleWeightZ
  rw [ite_eq_left he, mul_one]
  refine Real.exp_le_exp.2 ?_
  have h := sq_div_goodRadiusZ_le hlam hlamh hM hVZ he hr
  have h0 := sq_nonneg (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e)
  have : -(|L| * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2) ≤
      L * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 := by
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right (neg_abs_le L) h0
  have h2 : |L| * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 ≤ 16 * |L| := by
    have := mul_le_mul_of_nonneg_left h (abs_nonneg L)
    linarith
  linarith

end Separation

/-! ### Comparison of the distances to the bad set -/

section Compare

theorem badDistZ_nonneg (hcap : 0 ≤ ε₀ * truncationScale p₀ β lam) (e : ℂ × ℂ) :
    0 ≤ badDistZ p₀ β lam ε₀ V Z e :=
  le_badDistZ (mul_nonneg (by norm_num) hcap) fun _ _ => dipoleDist_nonneg _ _

/-- **Eq. (5.22)** for good dipoles: `d_{e',bad} ≤ d_{e,bad} + r_e + d(e, e')`. -/
theorem badDistZ_le_add (e e' : ℂ × ℂ) :
    badDistZ p₀ β lam ε₀ V Z e' ≤
      badDistZ p₀ β lam ε₀ V Z e + ‖e.1 - e.2‖ + dipoleDist e e' := by
  have hr := norm_nonneg (e.1 - e.2)
  have hd := dipoleDist_nonneg e e'
  have key : badDistZ p₀ β lam ε₀ V Z e' - ‖e.1 - e.2‖ - dipoleDist e e' ≤
      badDistZ p₀ β lam ε₀ V Z e := by
    refine le_badDistZ ?_ fun j hj => ?_
    · have := badDistZ_le_cap (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) e'
      linarith
    · have h1 := badDistZ_le_dipoleDist (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (Z := Z) e' hj
      have h2 := dipoleDist_le_add e' e (Z j)
      rw [dipoleDist_comm e' e] at h2
      linarith
  linarith

/-- **Eqs. (5.19)–(5.20)** for good dipoles: if `e ∈ I_good^Z` (with `r_e ≤ ε₀ R̄`) and
`e ↔ e'` (either way), then `d_{e',bad} ≤ (M + 2) d_{e,bad}`. -/
theorem badDistZ_le_of_linked (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e e' : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam)
    (hee' : MultipoleLinked M lam e e' ∨ MultipoleLinked M lam e' e) :
    badDistZ p₀ β lam ε₀ V Z e' ≤ (M + 2) * badDistZ p₀ β lam ε₀ V Z e := by
  have hM0 : 0 ≤ M := zero_le_one.trans ((one_le_pow₀ (by norm_num)).trans hM)
  have hcap : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlamh
  have h1 := badDistZ_le_add (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) e e'
  have h2 : dipoleDist e e' ≤ M * max ‖e.1 - e.2‖ lam := min4_le_of_linked hM0 hee'
  have h3 := max_le_badDistZ hlam hlamh hM hVZ he hr
  have h4 : M * max ‖e.1 - e.2‖ lam ≤ M * badDistZ p₀ β lam ε₀ V Z e :=
    mul_le_mul_of_nonneg_left h3 hM0
  have h5 : ‖e.1 - e.2‖ ≤ max ‖e.1 - e.2‖ lam := le_max_left _ _
  linarith

/-- The two-dipole configuration `(a, b)`. -/
abbrev pairConfig (a b : ℂ × ℂ) : Fin 2 → ℂ × ℂ := ![a, b]

/-- `v^Z(a, b) = v'_{01}` for the two-dipole configuration `(a, b)` with the radii
`τ^± = (t_a, t_b)`. -/
theorem pairInteraction_eq_ballGrowthInteraction (χ : ℂ → ℝ) (lam : ℝ) (a b : ℂ × ℂ)
    (ta tb : ℝ × ℝ) :
    pairInteraction χ lam a b ta tb =
      ballGrowthInteraction χ lam ![ta.1, tb.1] ![ta.2, tb.2] (pairConfig a b) 0 1 := by
  rw [← halfInteractionPlus_sub_halfInteractionMinus]
  rfl

/-- **Eq. (5.24)** for good dipoles: if `e ∈ I_good^Z` (with `r_e ≤ ε₀ R̄`) and `v^Z(e, e') ≠ 0`,
then `d_{e',bad} ≤ 6 d_{e,bad}`. -/
theorem badDistZ_le_six_mul {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e e' : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    (hr : ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam)
    (hv : interactionGoodZ χ p₀ β lam ε₀ V Z e e' ≠ 0) :
    badDistZ p₀ β lam ε₀ V Z e' ≤ 6 * badDistZ p₀ β lam ε₀ V Z e := by
  have hcap : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlamh
  set τ := goodRadiusZ p₀ β lam ε₀ V Z
  set D : Fin 2 → ℝ := ![badDistZ p₀ β lam ε₀ V Z e, badDistZ p₀ β lam ε₀ V Z e']
  have hv' : ballGrowthInteraction χ lam ![τ e, τ e'] ![τ e, τ e'] (pairConfig e e') 0 1 ≠ 0 := by
    have hv2 : pairInteraction χ lam e e' (τ e, τ e) (τ e', τ e') ≠ 0 := hv
    rwa [pairInteraction_eq_ballGrowthInteraction] at hv2
  have hp : ∀ k, lam ≤ (![τ e, τ e'] : Fin 2 → ℝ) k := by
    intro k
    fin_cases k
    · exact lam_le_goodRadiusZ e
    · exact lam_le_goodRadiusZ e'
  have h := le_six_mul_of_ballGrowthInteraction_ne_zero (d := pairConfig e e') (D := D) hχ hlam
    hp hp (i := 0) (i' := 1) rfl rfl rfl rfl (norm_le_badDistZ hlam hlamh hM hVZ he hr)
    (lam_le_badDistZ hlam hlamh hM hVZ he hr) (badDistZ_le_add e e') hv'
  exact h

end Compare

end BoundedUpper

end UpperBound

end MultipoleBKT

end
