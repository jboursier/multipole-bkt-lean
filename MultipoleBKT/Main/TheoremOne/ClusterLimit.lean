/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.Grouping
public import Mathlib.Analysis.SpecialFunctions.Choose

/-!
# Theorem 1 from the gates: the limit of a cluster term (only hypertrees survive)

The hypertree evaluation in the proof of Theorem 1 (the paper, eqs. (5.167) and (5.168)). Let `κ_N(j)` be activities depending only on the
size `j` of a polymer, vanishing for `j ≤ 1`, with `N^{j-1} κ_N(j) → a(j)` for `2 ≤ j ≤ p`, and
let `g` be a relabel invariant weight of families (in the application, the Ursell function of the
connection graph). Then, for fixed `n`,

  `(1/N) ∑_{V_1, …, V_n ⊂ [N], G(V) connected, |Vᵢ| ≤ p} ∏ᵢ κ_N(|Vᵢ|) g(V)
    → ∑_k (1/k!) ∑_{V ∈ Htrees_n([k]), ⋃ᵢ Vᵢ = [k]} ∏ᵢ a(|Vᵢ|) 𝟙_{|Vᵢ| ≤ p} g(V)`

(`MultipoleBKT.TheoremOne.tendsto_clusterSum`). The proof follows the paper: group the families
by their union (`MultipoleBKT.TheoremOne.sum_piFinset_range_eq_sum_choose`), use
`C(N, k) N^{-k} → 1/k!` and `∏ᵢ κ_N(|Vᵢ|) = N^{-∑ᵢ(|Vᵢ|-1)} ∏ᵢ (a(|Vᵢ|) + o(1))`; the exponent
of `N` is `|⋃ᵢ Vᵢ| + n - ∑ᵢ|Vᵢ| - 1 ≤ 0` (`MultipoleBKT.TheoremOne.card_biUnion_add_le`), with
equality exactly for hypertrees.
-/

@[expose] public section

open Finset Filter Topology Asymptotics

namespace MultipoleBKT

namespace TheoremOne

variable {n : ℕ}

/-- `C(N, k) N^{-k} → 1/k!` as `N → ∞`. -/
theorem tendsto_choose_mul_inv_pow (k : ℕ) :
    Tendsto (fun N : ℕ => (N.choose k : ℝ) * (1 / (N : ℝ)) ^ k) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
  have h : (fun N : ℕ => (N.choose k : ℝ) * (1 / (N : ℝ)) ^ k) ~[atTop]
      (fun N : ℕ => ((N : ℝ) ^ k / k.factorial) * (1 / (N : ℝ)) ^ k) :=
    (isEquivalent_choose k).mul Asymptotics.IsEquivalent.refl
  refine (Asymptotics.IsEquivalent.tendsto_nhds_iff h).mpr (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop 1] with N hN
  have : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  rw [div_mul_eq_mul_div, ← mul_pow, mul_one_div_cancel this, one_pow]

open scoped Classical in
/-- The cluster weight of a family is relabel invariant when `g` is. -/
theorem isRelabelInvariant_clusterWeight {g : (Fin n → Finset ℕ) → ℝ} (hg : IsRelabelInvariant g)
    (p : ℕ) (b : ℕ → ℝ) :
    IsRelabelInvariant (fun V : Fin n → Finset ℕ =>
      if (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p then (∏ i, b (V i).card) * g V
      else 0) := by
  intro V f hf
  simp only [connectionGraph_image hf, card_image_of_injOn_biUnion hf, hg V f hf]

/-- The Ursell function of the connection graph is relabel invariant. -/
theorem isRelabelInvariant_ursell :
    IsRelabelInvariant (fun V : Fin n → Finset ℕ => (ursell (connectionGraph V) : ℝ)) := by
  intro V f hf
  simp only [connectionGraph_image hf]

/-- The absolute value of the Ursell function of the connection graph is relabel invariant. -/
theorem isRelabelInvariant_abs_ursell :
    IsRelabelInvariant (fun V : Fin n → Finset ℕ => |(ursell (connectionGraph V) : ℝ)|) := by
  intro V f hf
  simp only [connectionGraph_image hf]

/-- For a family with union `{0, …, k - 1}`: `k ≤ ∑ᵢ |Vᵢ| ≤ n p` when `|Vᵢ| ≤ p`. -/
theorem le_mul_of_biUnion_eq_range {p k : ℕ} {V : Fin n → Finset ℕ}
    (hV : univ.biUnion V = range k) (hp : ∀ i, (V i).card ≤ p) : k ≤ n * p := by
  have h1 : (univ.biUnion V).card ≤ ∑ i, (V i).card := card_biUnion_le
  have h2 : ∑ i, (V i).card ≤ ∑ _i : Fin n, p := sum_le_sum fun i _ => hp i
  rw [hV, card_range] at h1
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
  omega

/-- Membership in `Htrees_n([k])` for a family with union `[k]`. -/
theorem mem_hypertrees_iff {k : ℕ} {V : Fin n → Finset ℕ}
    (hV : V ∈ Fintype.piFinset fun _ : Fin n => (range k).powerset)
    (hU : univ.biUnion V = range k) :
    V ∈ hypertrees n (range k) ↔ (∀ i, 2 ≤ (V i).card) ∧ (connectionGraph V).Connected ∧
      k + n = ∑ i, (V i).card + 1 := by
  classical
  simp only [hypertrees, mem_filter, hV, true_and, hU, card_range]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [← Nat.cast_sum]
  omega

/-- The algebra of the exponent count, for `N ≥ 1`. -/
theorem inv_mul_choose_mul_prod_eq {N k s d : ℕ} (hN : 1 ≤ N) (hkd : k + d = s + 1) (c P G : ℝ) :
    1 / (N : ℝ) * c * (P * G) =
      c * (1 / (N : ℝ)) ^ k * ((1 / (N : ℝ)) ^ d * (((N : ℝ) ^ s * P) * G)) := by
  have hx : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have h : (1 / (N : ℝ)) ^ k * (1 / (N : ℝ)) ^ d * (N : ℝ) ^ s = 1 / (N : ℝ) := by
    rw [← pow_add, hkd, one_div_pow, pow_succ]
    field_simp
  calc 1 / (N : ℝ) * c * (P * G)
      = c * ((1 / (N : ℝ)) ^ k * (1 / (N : ℝ)) ^ d * (N : ℝ) ^ s) * (P * G) := by rw [h]; ring
    _ = _ := by ring

open scoped Classical in
/-- The limit of one family's contribution `N⁻¹ C(N, k) w_N(V)`, for `V` with union `[k]`. -/
theorem tendsto_term {p k : ℕ} {κ : ℕ → ℕ → ℝ} {a : ℕ → ℝ} (hκ : ∀ N j, j ≤ 1 → κ N j = 0)
    (hlim : ∀ j, 2 ≤ j → j ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (j - 1) * κ N j) atTop (𝓝 (a j)))
    (g : (Fin n → Finset ℕ) → ℝ) {V : Fin n → Finset ℕ}
    (hV : V ∈ Fintype.piFinset fun _ : Fin n => (range k).powerset)
    (hU : univ.biUnion V = range k) :
    Tendsto (fun N : ℕ => 1 / (N : ℝ) * (N.choose k : ℝ) *
        (if (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p then
          (∏ i, κ N (V i).card) * g V else 0)) atTop
      (𝓝 (if V ∈ hypertrees n (range k) then 1 / (k.factorial : ℝ) *
        ((if ∀ i, (V i).card ≤ p then ∏ i, a (V i).card else 0) * g V) else 0)) := by
  classical
  have hmem := mem_hypertrees_iff hV hU
  by_cases hc : (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p
  swap
  · have hL : (if V ∈ hypertrees n (range k) then 1 / (k.factorial : ℝ) *
        ((if ∀ i, (V i).card ≤ p then ∏ i, a (V i).card else 0) * g V) else 0) = 0 := by
      split_ifs with hH hp
      · exact absurd ⟨(hmem.mp hH).2.1, hp⟩ hc
      · simp
      · rfl
    simp only [hc, ite_false, mul_zero, hL]
    exact tendsto_const_nhds
  by_cases h1 : ∃ i, (V i).card ≤ 1
  · obtain ⟨i₀, hi₀⟩ := h1
    have hH : V ∉ hypertrees n (range k) := fun hH => by
      have := (hmem.mp hH).1 i₀
      omega
    have hz : ∀ N, ∏ i, κ N (V i).card = 0 := fun N => prod_eq_zero (mem_univ i₀) (hκ N _ hi₀)
    simp only [hH, ite_false, hz, zero_mul, ite_self, mul_zero]
    exact tendsto_const_nhds
  push Not at h1
  -- all blocks have at least two elements
  set s : ℕ := ∑ i, ((V i).card - 1) with hs
  have hsum : ∑ i, (V i).card = s + n := by
    have h1' : ∀ i, (V i).card = ((V i).card - 1) + 1 := fun i => by have := h1 i; omega
    rw [sum_congr rfl fun i _ => h1' i, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  have hcount := card_biUnion_add_le hc.1
  rw [hU, card_range, hsum] at hcount
  set d : ℕ := s + 1 - k with hd
  have hkd : k + d = s + 1 := by omega
  have hHd : V ∈ hypertrees n (range k) ↔ d = 0 := by
    rw [hmem, hsum]
    constructor
    · rintro ⟨-, -, h⟩
      omega
    · intro h
      exact ⟨fun i => by have := h1 i; omega, hc.1, by omega⟩
  -- the limit
  have hlimP : Tendsto (fun N : ℕ => ∏ i, ((N : ℝ) ^ ((V i).card - 1) * κ N (V i).card)) atTop
      (𝓝 (∏ i, a (V i).card)) :=
    tendsto_finsetProd _ fun i _ => hlim _ (by have := h1 i; omega) (hc.2 i)
  have hinv : Tendsto (fun N : ℕ => (1 / (N : ℝ)) ^ d) atTop (𝓝 ((0 : ℝ) ^ d)) :=
    tendsto_one_div_atTop_nhds_zero_nat.pow d
  have htot := (tendsto_choose_mul_inv_pow k).mul (hinv.mul (hlimP.mul_const (g V)))
  have hval : (if V ∈ hypertrees n (range k) then 1 / (k.factorial : ℝ) *
      ((if ∀ i, (V i).card ≤ p then ∏ i, a (V i).card else 0) * g V) else 0) =
      1 / (k.factorial : ℝ) * ((0 : ℝ) ^ d * ((∏ i, a (V i).card) * g V)) := by
    by_cases hd0 : d = 0
    · rw [ite_eq_left (hHd.mpr hd0), ite_eq_left hc.2, hd0, pow_zero, one_mul]
    · rw [ite_eq_right (fun h => hd0 (hHd.mp h)), zero_pow hd0, zero_mul, mul_zero]
  rw [hval]
  refine htot.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [ite_eq_left hc]
  have hprod : ∏ i, ((N : ℝ) ^ ((V i).card - 1) * κ N (V i).card) =
      (N : ℝ) ^ s * ∏ i, κ N (V i).card := by
    rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  rw [hprod]
  exact (inv_mul_choose_mul_prod_eq hN hkd _ _ _).symm

open scoped Classical in
/-- **Only hypertrees survive** (eqs. (5.167)–(5.168)): the limit of
`N⁻¹ ∑_{V ⊂ [N], G(V) connected, |Vᵢ| ≤ p} ∏ᵢ κ_N(|Vᵢ|) g(V)`. -/
theorem tendsto_clusterSum (p : ℕ) {κ : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (hκ : ∀ N j, j ≤ 1 → κ N j = 0)
    (hlim : ∀ j, 2 ≤ j → j ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (j - 1) * κ N j) atTop (𝓝 (a j)))
    {g : (Fin n → Finset ℕ) → ℝ} (hg : IsRelabelInvariant g) :
    Tendsto (fun N : ℕ => 1 / (N : ℝ) *
        ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (range N).powerset).filter
            (fun V => (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p),
          (∏ i, κ N (V i).card) * g V) atTop
      (𝓝 (∑ k ∈ range (n * p + 1), 1 / (k.factorial : ℝ) *
        ∑ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
          (if ∀ i, (V i).card ≤ p then ∏ i, a (V i).card else 0) * g V)) := by
  classical
  set A : ℕ → Finset (Fin n → Finset ℕ) := fun k =>
    (Fintype.piFinset fun _ : Fin n => (range k).powerset).filter
      (fun V => univ.biUnion V = range k) with hA
  set F : ℕ → (Fin n → Finset ℕ) → ℝ := fun N V =>
    if (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p then (∏ i, κ N (V i).card) * g V
    else 0 with hF
  set L : ℕ → (Fin n → Finset ℕ) → ℝ := fun k V =>
    if V ∈ hypertrees n (range k) then 1 / (k.factorial : ℝ) *
      ((if ∀ i, (V i).card ≤ p then ∏ i, a (V i).card else 0) * g V) else 0 with hL
  -- the target as a double sum over `k` and the families with union `[k]`
  have hRHS : ∀ k, 1 / (k.factorial : ℝ) *
      ∑ V ∈ (hypertrees n (range k)).filter (fun V => univ.biUnion V = range k),
        (if ∀ i, (V i).card ≤ p then ∏ i, a (V i).card else 0) * g V =
      ∑ V ∈ A k, L k V := by
    intro k
    rw [hA, hL]
    simp only
    rw [← sum_filter, mul_sum]
    refine sum_congr ?_ fun _ _ => rfl
    ext V
    simp only [mem_filter]
    constructor
    · rintro ⟨hH, hU⟩
      have hH' := hH
      simp only [hypertrees, mem_filter] at hH'
      exact ⟨⟨hH'.1, hU⟩, hH⟩
    · rintro ⟨⟨-, hU⟩, hH⟩
      exact ⟨hH, hU⟩
  -- the cluster sum, grouped by the union
  have hvan : ∀ N k, n * p < k → ∑ V ∈ A k, F N V = 0 := by
    intro N k hk
    refine sum_eq_zero fun V hV => ?_
    simp only [hA, mem_filter] at hV
    simp only [hF]
    rw [ite_eq_right]
    rintro ⟨-, hp⟩
    have := le_mul_of_biUnion_eq_range hV.2 hp
    omega
  have hLHS : ∀ N, n * p ≤ N → 1 / (N : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (range N).powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p),
        (∏ i, κ N (V i).card) * g V =
      ∑ k ∈ range (n * p + 1), ∑ V ∈ A k, 1 / (N : ℝ) * (N.choose k : ℝ) * F N V := by
    intro N hN
    rw [sum_filter]
    have hinv : IsRelabelInvariant (F N) := isRelabelInvariant_clusterWeight hg p (κ N)
    rw [sum_piFinset_range_eq_sum_choose hinv N]
    rw [← sum_subset (range_subset_range.mpr (by omega : n * p + 1 ≤ N + 1))
      (fun k _ hk => by
        rw [mem_range, not_lt] at hk
        rw [hvan N k (by omega), mul_zero])]
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun V _ => ?_
    ring
  rw [sum_congr rfl fun k _ => hRHS k]
  refine (tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun V hV => ?_).congr'
    ((eventually_ge_atTop (n * p)).mono fun N hN => (hLHS N hN).symm)
  simp only [hA, mem_filter] at hV
  exact tendsto_term hκ hlim g hV.1 hV.2

end TheoremOne

end MultipoleBKT

end
