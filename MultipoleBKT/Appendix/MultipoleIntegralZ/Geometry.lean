/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.FrozenData
public import MultipoleBKT.UpperBound.BadPoints.Geometry
public import MultipoleBKT.Potential.LowerError

/-!
# Geometry of a good dipole near frozen bad points

See Appendix A, standing convention: a frozen
configuration `Z = (x_j, y_j)_{j ∈ V_bad}` satisfies `I_bad^{V_bad} = V_bad`, the bad sets and radii
are computed from `Z`, and `M > max(20, 3^{p(β)})`. In the frozen model of
`MultipoleBKT.UpperBound.Hierarchical.FrozenData`, `V : Finset (Fin N)` is the set of bad labels,
`Z : Fin N → ℂ × ℂ` the configuration (only `(Z j)_{j ∈ V}` is used), `e = (x, y)` a good dipole,
`r_e = |x - y|`, `I_good^Z = IsGoodZ`, `d_{e,bad} = badDistZ`, `τ_e^Z = goodRadiusZ`, and
`v^Z = interactionGoodZ`. The hypothesis `I_bad^{V}(Z) = V` is `badPointsOn … V Z = V`.

* `separation_of_isGoodZ`: for `e ∈ I_good^Z` and every bad label `j`,
  `d_ej > M min(max(r_e, λ), max(r_j, λ))` (eq. (5.51), for the three types).
* `exists_near_of_not_isGoodZ`: if `e ∉ I_good^Z`, some bad dipole is at distance
  `≤ M max(r_e, λ)` (eq. (A.40)).
* `max_le_badDistZ`: **eq. (5.9) on the support of the frozen model**: for `e ∈ I_good^Z` with
  `r_e ≤ 4 ε₀ R̄` and `λ ≤ 4 ε₀ R̄`, `d_{e,bad} ≥ max(r_e, λ)`. This is the "geometric argument at
  the beginning of the proof of Proposition 5.18" invoked in the proofs of
  Lemma A.3 and Lemma A.6: the nearest bad dipole has type 3; its
  `U`-class has at most `p(β)` elements; along a walk in the class to a seed of `J^3_bad` the
  distance to `e` grows by a factor `< 3` per step; a final step reaches `I^1_bad ∪ I^2_bad` at
  distance `< 3^{p(β)} max(r_e, λ) ≤ M max(r_e, λ)`, contradicting `e ∈ I_good^Z`.
* `goodRadiusZ_ge`: hence `τ_e^Z ≥ max(r_e, λ)/4 ≥ r_e/4`.
* `abs_interactionGoodZ_sub_le`: eq. (A.35) for `v^Z`: `|v^Z_de - v_de| ≤
  C r_d r_e / max(τ_d^Z, τ_e^Z)²` (Lemma 3.9 (3), `lemma_3_9_3`, without separation), with `C`
  depending only on `χ`.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace MultipoleIntegralZ

open UpperBound TheoremTwo

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- `max(min(a, b), λ) = min(max(a, λ), max(b, λ))`. -/
theorem max_min_eq_min_max (a b lam : ℝ) : max (min a b) lam = min (max a lam) (max b lam) :=
  max_min_distrib_right a b lam

/-- **Separation from every bad dipole** (eq. (5.51)): for `e ∈ I_good^Z` and
`j ∈ V` (with `I_bad^V(Z) = V` and `M ≥ 0`), `d_ej > M min(max(r_e, λ), max(r_j, λ))`. -/
theorem separation_of_isGoodZ (hM : 0 ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V)
    {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e) {j : Fin N} (hj : j ∈ V) :
    M * min (max ‖e.1 - e.2‖ lam) (max ‖(Z j).1 - (Z j).2‖ lam) < dipoleDist e (Z j) := by
  rw [← hV] at hj
  rcases Finset.mem_union.1 hj with h12 | h3
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_left _ _) hM) (he.1 j h12)
  · have := he.2 j h3
    rwa [max_min_eq_min_max] at this

/-- **A dipole outside `I_good^Z` is near a bad dipole** (eq. (A.40)): if
`e ∉ I_good^Z` and `M ≥ 0`, then `d_ej ≤ M max(r_e, λ)` for some `j ∈ V`. -/
theorem exists_near_of_not_isGoodZ (hM : 0 ≤ M) {e : ℂ × ℂ}
    (he : ¬ IsGoodZ p₀ β lam M ε₀ V Z e) :
    ∃ j ∈ V, dipoleDist e (Z j) ≤ M * max ‖e.1 - e.2‖ lam := by
  unfold IsGoodZ at he
  rw [not_and_or] at he
  rcases he with h | h
  · push Not at h
    obtain ⟨j, hj, hle⟩ := h
    exact ⟨j, Finset.union_subset typeOneOn_subset typeTwoOn_subset hj, hle⟩
  · push Not at h
    obtain ⟨j, hj, hle⟩ := h
    refine ⟨j, typeThreeOn_subset hj, hle.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (max_le_max (min_le_left _ _) le_rfl) hM

/-! ### Eq. (5.9) for the frozen model -/

/-- One step of the chain (the proof of Proposition 5.18): if `e ∈ I_good^Z`, `k ∈ V` with `d_ek < M A_e` and
`d_{kk'} ≤ M max(r_k, λ)`, then `d_{ek'} < 3 d_ek`. -/
theorem chain_step_frozen (hlam : 0 < lam) (hM : 1 ≤ M)
    (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    {k : Fin N} (hk : k ∈ V) {f : ℂ × ℂ}
    (hD : dipoleDist e (Z k) < M * max ‖e.1 - e.2‖ lam)
    (hkf : dipoleDist (Z k) f ≤ M * max ‖(Z k).1 - (Z k).2‖ lam) :
    dipoleDist e f < 3 * dipoleDist e (Z k) := by
  set A := max ‖e.1 - e.2‖ lam
  set B := max ‖(Z k).1 - (Z k).2‖ lam
  have hsep := separation_of_isGoodZ (zero_le_one.trans hM) hV he hk
  have hBA : B < A := by
    by_contra h
    push Not at h
    rw [min_eq_left h] at hsep
    exact absurd (hsep.trans hD) (lt_irrefl _)
  rw [min_eq_right hBA.le] at hsep
  have hB0 : 0 ≤ B := hlam.le.trans (le_max_right _ _)
  have hrk : ‖(Z k).1 - (Z k).2‖ ≤ B := le_max_left _ _
  have hBM : B ≤ M * B := le_mul_of_one_le_left hB0 hM
  have htri := dipoleDist_le_add e (Z k) f
  linarith

/-- The chain along a walk in the class graph on `U ⊆ V` (the proof of Proposition 5.18). -/
theorem chain_walk_frozen (hlam : 0 < lam) (hM : 1 ≤ M)
    (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    {U : Finset (Fin N)} (hU : U ⊆ V) :
    ∀ {u v : Fin N} (w : (classGraph M lam Z U).Walk u v), u ∈ U → ∀ c : ℝ,
      3 ^ w.length * c ≤ M * max ‖e.1 - e.2‖ lam →
      dipoleDist e (Z u) < c → dipoleDist e (Z v) < 3 ^ w.length * c := by
  intro u v w
  induction w with
  | nil => intro _ c _ hu; simpa using hu
  | @cons u u' v hadj w ih =>
    intro huU c hc hu
    have hc0 : 0 ≤ c := (dipoleDist_nonneg _ _).trans hu.le
    have hlen : (SimpleGraph.Walk.cons hadj w).length = w.length + 1 := rfl
    rw [hlen, pow_succ] at hc ⊢
    have hukc : c ≤ 3 ^ w.length * 3 * c := by
      have : (1 : ℝ) ≤ 3 ^ w.length * 3 := by
        have := one_le_pow₀ (M₀ := ℝ) (a := 3) (by norm_num) (n := w.length)
        linarith
      nlinarith
    have hDu : dipoleDist e (Z u) < M * max ‖e.1 - e.2‖ lam := by linarith
    have hadj' := hadj
    rw [SimpleGraph.fromRel_adj] at hadj'
    have hlink : dipoleDist (Z u) (Z u') ≤ M * max ‖(Z u).1 - (Z u).2‖ lam := by
      have h' : MultipoleLinked M lam (Z u) (Z u') ∨ MultipoleLinked M lam (Z u') (Z u) := by
        rcases hadj'.2 with h | h
        · exact Or.inl h.2.2
        · exact Or.inr h.2.2
      exact min4_le_of_linked (zero_le_one.trans hM) h'
    have hu'U : u' ∈ U := by
      rcases hadj'.2 with h | h
      · exact h.2.1
      · exact h.1
    have hstep := chain_step_frozen hlam hM hV he (hU huU) hDu hlink
    have := ih hu'U (3 * c) (by linarith) (by linarith)
    linarith

/-- **Eq. (5.9) for the frozen model** (used in the proofs of Lemmas A.3 and A.6): if
`I_bad^V(Z) = V`, `3^{p(β)} ≤ M`, `0 < λ ≤ 4 ε₀ R̄`, `e ∈ I_good^Z` and `r_e ≤ 4 ε₀ R̄`, then
`d_{e,bad} ≥ max(r_e, λ)`. -/
theorem max_le_badDistZ (hlam : 0 < lam) (hlamh : lam ≤ 4 * (ε₀ * truncationScale p₀ β lam))
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ 4 * (ε₀ * truncationScale p₀ β lam)) :
    max ‖e.1 - e.2‖ lam ≤ badDistZ p₀ β lam ε₀ V Z e := by
  classical
  set A := max ‖e.1 - e.2‖ lam with hA
  have hA0 : 0 < A := lt_max_of_lt_right hlam
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hMA : A ≤ M * A := le_mul_of_one_le_left hA0.le hM1
  refine le_badDistZ (max_le hr hlamh) fun j hj => ?_
  by_contra hDj
  push Not at hDj
  -- `j` is of type 3
  have hjV := hj
  rw [← hV] at hj
  have hj3 : j ∈ typeThreeOn p₀ β lam M ε₀ V Z := by
    rcases Finset.mem_union.1 hj with hj12 | hj3
    · exact absurd (he.1 j hj12) (not_lt.2 (hDj.le.trans hMA))
    · exact hj3
  -- unfold the definition of type 3
  set I₁₂ := typeOneOn p₀ β lam ε₀ V Z ∪ typeTwoOn p₀ β lam M ε₀ V Z with hI₁₂
  set U := V \ typeOneOn p₀ β lam ε₀ V Z with hU
  have hj3' := hj3
  simp only [typeThreeOn, Finset.mem_filter] at hj3'
  obtain ⟨hjVI, hne⟩ := hj3'
  obtain ⟨s, hs⟩ := hne
  obtain ⟨hsj, hsJ⟩ := Finset.mem_inter.1 hs
  simp only [Finset.mem_filter] at hsJ
  obtain ⟨-, l, hl, hsl⟩ := hsJ
  -- the class of `j` has at most `p(β)` elements
  have hjU : j ∈ U := by
    rw [hU, Finset.mem_sdiff]
    exact ⟨hjV, fun h => (Finset.mem_sdiff.1 hjVI).2 (Finset.mem_union_left _ h)⟩
  have hcard : (multipoleClassOn M lam Z U j).card ≤ pBeta p₀ β := by
    by_contra hc
    push Not at hc
    apply (Finset.mem_sdiff.1 hjVI).2
    refine Finset.mem_union_right _ ?_
    simp only [typeTwoOn]
    exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hjU, hc⟩)
  -- a walk from `j` to the seed `s`
  obtain ⟨w, hwlen, -⟩ := exists_walk_length_lt (mem_classOn_iff.1 hsj)
    (multipoleClassOn M lam Z U j) fun k hk => mem_classOn_iff.2 hk
  have hUV : U ⊆ V := Finset.sdiff_subset
  have hpow : (3 : ℝ) ^ (w.length + 1) ≤ M :=
    (pow_le_pow_right₀ (by norm_num) (by omega)).trans hM
  have hpow' : (3 : ℝ) ^ w.length * A ≤ M * A := by
    have : (3 : ℝ) ^ w.length ≤ 3 ^ (w.length + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    exact mul_le_mul_of_nonneg_right (this.trans hpow) hA0.le
  have hDs := chain_walk_frozen hlam hM1 hV he hUV w hjU A hpow' hDj
  have hsU : s ∈ U := mem_of_classGraph_reachable hjU (mem_classOn_iff.1 hsj)
  have hDs' : dipoleDist e (Z s) < M * A := hDs.trans_le hpow'
  have hDl := chain_step_frozen hlam hM1 hV he (hUV hsU) hDs' (f := Z l) hsl
  have hfinal : dipoleDist e (Z l) < M * A := by
    have : 3 * ((3 : ℝ) ^ w.length * A) = 3 ^ (w.length + 1) * A := by ring
    have h3 : (3 : ℝ) ^ (w.length + 1) * A ≤ M * A := mul_le_mul_of_nonneg_right hpow hA0.le
    linarith
  exact absurd (he.1 l hl) (not_lt.2 hfinal.le)

/-- **`τ_e^Z ≥ max(r_e, λ)/4`** on the support of the frozen model (Remark 5.10 for good points): under the hypotheses of `max_le_badDistZ`. -/
theorem goodRadiusZ_ge (hlam : 0 < lam) (hlamh : lam ≤ 4 * (ε₀ * truncationScale p₀ β lam))
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) (hr : ‖e.1 - e.2‖ ≤ 4 * (ε₀ * truncationScale p₀ β lam)) :
    max ‖e.1 - e.2‖ lam / 4 ≤ goodRadiusZ p₀ β lam ε₀ V Z e := by
  have h := max_le_badDistZ hlam hlamh hM hV he hr
  unfold goodRadiusZ
  exact (div_le_div_of_nonneg_right h (by norm_num)).trans (le_max_left _ _)

/-! ### Eq. (A.35) for `v^Z` -/

/-- `v^Z` of two good dipoles with equal radii `(a, a)`, `(b, b)` is the ball-growth interaction
`v'_{01}` of the two-dipole configuration `![d, e]` with radii `![a, b]`. -/
theorem pairInteraction_eq_ballGrowthInteraction (χ : ℂ → ℝ) (lam : ℝ) (d e : ℂ × ℂ) (a b : ℝ) :
    pairInteraction χ lam d e (a, a) (b, b) =
      ballGrowthInteraction χ lam ![a, b] ![a, b] ![d, e] 0 1 := by
  unfold pairInteraction ballGrowthInteraction
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Eq. (A.35)** ("the bounds without separation in Lemmas 3.9 and 3.10") for the
interaction of two good dipoles: there is `C > 0` depending only on `χ` such that, for `λ > 0`,
`|v^Z_de - v_de| ≤ C r_d r_e / max(τ_d^Z, τ_e^Z)²`. -/
theorem abs_interactionGoodZ_sub_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) :
    ∃ C > 0, ∀ {N : ℕ} (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → ∀ d e : ℂ × ℂ,
        |interactionGoodZ χ p₀ β lam ε₀ V Z d e - dipoleInteraction χ lam d e| ≤
          C * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
            max (goodRadiusZ p₀ β lam ε₀ V Z d) (goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 := by
  obtain ⟨C, hC, h⟩ := lemma_3_9_3 hχ
  refine ⟨C, hC, fun p₀ β lam ε₀ V Z hlam d e => ?_⟩
  set a := goodRadiusZ p₀ β lam ε₀ V Z d
  set b := goodRadiusZ p₀ β lam ε₀ V Z e
  have ha : lam ≤ a := lam_le_goodRadiusZ d
  have hb : lam ≤ b := lam_le_goodRadiusZ e
  have := (h (N := 2) lam ![a, b] ![a, b] ![d, e] 0 1 hlam ha rfl hb rfl).1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  unfold interactionGoodZ
  rw [pairInteraction_eq_ballGrowthInteraction]
  exact this

end MultipoleIntegralZ

end MultipoleBKT

end
