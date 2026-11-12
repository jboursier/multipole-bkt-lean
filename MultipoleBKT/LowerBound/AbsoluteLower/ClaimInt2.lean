/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.ClaimInt
public import MultipoleBKT.LowerBound.AbsoluteLower.EulerGroup

/-!
# Lemma 4.56, eq. (4.105): the product of the `ḡ` interactions

Lemma 4.56 (second claim,
eq. (4.105) in the proof of Lemma 4.56): on the event `𝒟`, for blocks of at most `p` labels
and `M > 20`,
`∏_{i ∈ V_X} (1 + ∑_{j ∈ V_X, j ≠ i} ḡ_ij) ≤ (C M)^{|V_X|} ∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{1/M}`.

The proof is the paper's, with dyadic sums:

* `sum_gbar_level_le` (proof of Lemma 4.56): for the neighbours `j` of `i` with `r_j ≥ r_i` and
  `s < r_j ≤ 2s`, those with `d_ij < 2s` lie in one block (`d_jk < 6s < M min(r_j, r_k)`), and those
  in a dyadic shell `2^k 2s ≤ d_ij < 2^{k+1} 2s` are counted by the packing estimate, with
  `ḡ_ij ≤ 4^{-k}`; at the level `s = R/2^{h+1}`, `R = ε₀ R̄`, this gives
  `∑_j ḡ_ij ≤ p (11 + 192 h / M²)`.
* `sum_weight_gbar_le` (proof of Lemma 4.56): with `w_j = (r_j/R)^{1/M} ≤ 2^{-h/M}`,
  `∑_{j ≠ i, r_j ≥ r_i} w_j ḡ_ij ≤ K₁ p M`, from `∑_h x^h ≤ 1/(1 - x)` and
  `∑_h h x^h ≤ x/(1 - x)²` for `x = 2^{-1/M}`, and `1/(1 - x) ≤ 2M / log 2`.
* `claim_int2` (eq. (4.105)): by symmetry `∑_i w_i (1 + ∑_{j ≠ i} ḡ_ij) ≤ (1 + 2 K₁ p) M |V_X|`,
  and the arithmetic-geometric mean inequality (`MultipoleBKT.Peeling.prod_le_prod_mul_exp`).
* **Lemma 4.56** (`lemma_4_56`): (4.104) (`MultipoleBKT.AbsoluteLower.claim_int`) and (4.105) with
  one constant.
* `sum_interPairs_absOddWeight_le`: `∑_{ij ∈ ℰ^inter(X)} a^abs_ij` is at most the sum over `i` of the
  left-hand sides of (4.104), the form in which (4.104) bounds `exp(2 C₁ ∑ a^abs)` downstream.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SetPartition Peeling Parity Multipole Hierarchical

/-! ### Bounds on `ḡ` -/

section Gbar

open scoped Classical

variable {M lam ε₀ R : ℝ} {c : ℕ → ℂ × ℂ}

theorem gbar_indicator_le_one (i j : ℕ) :
    (if MultipoleLinked M lam (c i) (c j) then (0 : ℝ) else 1) *
      (if dipoleDist (c i) (c j) ≤ 17 * ε₀ * R then 1 else 0) ≤ 1 := by
  split_ifs <;> norm_num

theorem gbar_indicator_nonneg (i j : ℕ) :
    0 ≤ (if MultipoleLinked M lam (c i) (c j) then (0 : ℝ) else 1) *
      (if dipoleDist (c i) (c j) ≤ 17 * ε₀ * R then 1 else 0) := by
  split_ifs <;> norm_num

/-- `ḡ_ij ≤ 1`. -/
theorem gbar_le_one (i j : ℕ) : gbar M lam ε₀ R c i j ≤ 1 := by
  unfold gbar
  have hq : max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ^ 2 /
      max (max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖)) lam ^ 2
      ≤ 1 :=
    div_le_one_of_le₀ (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _))
      (le_max_of_le_left (le_max_right _ _)) 2) (sq_nonneg _)
  calc _ ≤ 1 * 1 := mul_le_mul (gbar_indicator_le_one i j) hq
        (div_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one
    _ = 1 := one_mul 1

/-- `ḡ_ij ≤ max(r_i, r_j)² / d_ij²` for `d_ij > 0`. -/
theorem gbar_le_div {i j : ℕ} (hd : 0 < dipoleDist (c i) (c j)) :
    gbar M lam ε₀ R c i j ≤
      max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ^ 2 / dipoleDist (c i) (c j) ^ 2 := by
  unfold gbar
  have hq : max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ^ 2 /
      max (max (dipoleDist (c i) (c j)) (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖)) lam ^ 2
      ≤ max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ^ 2 / dipoleDist (c i) (c j) ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hd 2)
      (pow_le_pow_left₀ hd.le (le_max_of_le_left (le_max_left _ _)) 2)
  calc _ ≤ 1 * (max ‖(c i).1 - (c i).2‖ ‖(c j).1 - (c j).2‖ ^ 2 / dipoleDist (c i) (c j) ^ 2) :=
        mul_le_mul (gbar_indicator_le_one i j) hq (div_nonneg (sq_nonneg _) (sq_nonneg _))
          zero_le_one
    _ = _ := one_mul _

theorem gbar_eq_zero_of_linked {i j : ℕ} (h : MultipoleLinked M lam (c i) (c j)) :
    gbar M lam ε₀ R c i j = 0 := by
  classical
  unfold gbar
  rw [ite_eq_left h]
  ring

theorem gbar_eq_zero_of_far {i j : ℕ} (h : ¬ dipoleDist (c i) (c j) ≤ 17 * ε₀ * R) :
    gbar M lam ε₀ R c i j = 0 := by
  classical
  unfold gbar
  rw [ite_eq_right h]
  ring

end Gbar

/-! ### One dyadic level of radii -/

section Level

variable {X : Finset (Finset ℕ)} {p : ℕ} {M lam ε₀ R : ℝ} {c : ℕ → ℂ × ℂ}

/-- The algebra of one shell: from `N (M s)² ≤ p (2 (2 v 2s + 2s) + M s)²`,
`N / v² ≤ 3p (64/M² + 16/(M² v²) + 1/v²)`. -/
theorem shell_alg {N P M s v : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (hs : 0 < s) (hv : 1 ≤ v)
    (hpack : N * (M * s) ^ 2 ≤ P * (2 * (2 * v * (2 * s) + 2 * s) + M * s) ^ 2) :
    N * (1 / v ^ 2) ≤ 3 * P * (64 / M ^ 2 + 16 / M ^ 2 * (1 / v ^ 2) + 1 / v ^ 2) := by
  have hM0 : 0 < M := by linarith
  have hv0 : 0 < v := by linarith
  have h1 : N * M ^ 2 * s ^ 2 ≤ P * (8 * v + 4 + M) ^ 2 * s ^ 2 := by
    calc N * M ^ 2 * s ^ 2 = N * (M * s) ^ 2 := by ring
      _ ≤ _ := hpack
      _ = P * (8 * v + 4 + M) ^ 2 * s ^ 2 := by ring
  have h2 := le_of_mul_le_mul_right h1 (by positivity)
  have h3 : (8 * v + 4 + M) ^ 2 ≤ 3 * (64 * v ^ 2 + 16 + M ^ 2) := by
    nlinarith [sq_nonneg (8 * v - 4), sq_nonneg (8 * v - M), sq_nonneg (4 - M)]
  have h4 : N * M ^ 2 ≤ 3 * P * (64 * v ^ 2 + 16 + M ^ 2) := by
    calc N * M ^ 2 ≤ P * (8 * v + 4 + M) ^ 2 := h2
      _ ≤ P * (3 * (64 * v ^ 2 + 16 + M ^ 2)) := mul_le_mul_of_nonneg_left h3 hP
      _ = 3 * P * (64 * v ^ 2 + 16 + M ^ 2) := by ring
  have hk : 0 < 1 / (M ^ 2 * v ^ 2) := by positivity
  calc N * (1 / v ^ 2) = N * M ^ 2 * (1 / (M ^ 2 * v ^ 2)) := by field_simp
    _ ≤ 3 * P * (64 * v ^ 2 + 16 + M ^ 2) * (1 / (M ^ 2 * v ^ 2)) :=
        mul_le_mul_of_nonneg_right h4 hk.le
    _ = 3 * P * (64 / M ^ 2 + 16 / M ^ 2 * (1 / v ^ 2) + 1 / v ^ 2) := by
        field_simp

/-- **One dyadic level of radii** (proof of Lemma 4.56): for the labels `j ∈ F` with `s < r_j ≤ 2s` and
`r_i ≤ r_j`, if `17 ε₀ R ≤ 64 · 2^h s`, then `∑_{j ∈ F} ḡ_ij ≤ p (11 + 192 h / M²)`. -/
theorem sum_gbar_level_le (hX : IsSubpartition X) (hp : ∀ S ∈ X, S.card ≤ p) (hM : 20 < M)
    (hD : ∀ j ∈ X.biUnion id, ∀ k ∈ X.biUnion id, ¬ SameBlock X j k →
      ¬ MultipoleLinked M lam (c j) (c k))
    {i : ℕ} {s : ℝ} (hs : 0 < s) {h : ℕ}
    (h17 : 17 * ε₀ * R ≤ 64 * 2 ^ h * s) {F : Finset ℕ} (hF : F ⊆ X.biUnion id)
    (hF' : ∀ j ∈ F, s < ‖(c j).1 - (c j).2‖ ∧ ‖(c j).1 - (c j).2‖ ≤ 2 * s ∧
      ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖) :
    ∑ j ∈ F, gbar M lam ε₀ R c i j ≤ p * (11 + 192 * h / M ^ 2) := by
  classical
  set ρ := ‖(c i).1 - (c i).2‖ with hρdef
  have hM0 : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  rw [← sum_filter_add_sum_filter_not F fun j => dipoleDist (c i) (c j) < 2 * s]
  set N := F.filter fun j => dipoleDist (c i) (c j) < 2 * s with hN
  set Fr := F.filter fun j => ¬ dipoleDist (c i) (c j) < 2 * s with hFr
  -- the near neighbours lie in one block
  have hnear : ∑ j ∈ N, gbar M lam ε₀ R c i j ≤ p := by
    have hcard : N.card ≤ p := by
      refine card_le_of_forall_sameBlock hX hp fun j hj k hk => ?_
      rw [mem_filter] at hj hk
      by_contra hjk
      have hlt := mul_min_lt_dipoleDist hM0.le (hD j (hF hj.1) k (hF hk.1) hjk)
      have htri := dipoleDist_le_add (c i) (c j) (c k)
      obtain ⟨hj1, hj2, hj3⟩ := hF' j hj.1
      obtain ⟨hk1, -, -⟩ := hF' k hk.1
      have hmin : s ≤ min ‖(c j).1 - (c j).2‖ ‖(c k).1 - (c k).2‖ := le_min hj1.le hk1.le
      have : M * s ≤ M * min ‖(c j).1 - (c j).2‖ ‖(c k).1 - (c k).2‖ :=
        mul_le_mul_of_nonneg_left hmin hM0.le
      nlinarith
    calc ∑ j ∈ N, gbar M lam ε₀ R c i j ≤ ∑ j ∈ N, (1 : ℝ) := sum_le_sum fun j _ => gbar_le_one i j
      _ = N.card := by rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ p := by exact_mod_cast hcard
  -- the far neighbours, by dyadic shells
  have hfar : ∑ j ∈ Fr, gbar M lam ε₀ R c i j ≤
      3 * p * (64 * (h + 6) / M ^ 2 + 22 / M ^ 2 + 2) := by
    rw [← sum_filter_ne_zero]
    set G := Fr.filter fun j => gbar M lam ε₀ R c i j ≠ 0 with hG
    have hGmem : ∀ j ∈ G, j ∈ F ∧ 2 * s ≤ dipoleDist (c i) (c j) ∧
        ¬ MultipoleLinked M lam (c i) (c j) ∧ dipoleDist (c i) (c j) ≤ 17 * ε₀ * R := by
      intro j hj
      rw [hG, hFr, mem_filter, mem_filter] at hj
      refine ⟨hj.1.1, not_lt.1 hj.1.2, fun hl => hj.2 (gbar_eq_zero_of_linked hl),
        by_contra fun hd => hj.2 (gbar_eq_zero_of_far hd)⟩
    have h2s : 0 < 2 * s := by linarith
    set φ : ℕ → ℕ := fun j => level 2 (dipoleDist (c i) (c j)) (2 * s) with hφ
    have hspec : ∀ j ∈ G, (2 : ℝ) ^ φ j * (2 * s) ≤ dipoleDist (c i) (c j) ∧
        dipoleDist (c i) (c j) < 2 ^ (φ j + 1) * (2 * s) :=
      fun j hj => level_spec one_lt_two h2s (hGmem j hj).2.1
    have hterm : ∀ j ∈ G, gbar M lam ε₀ R c i j ≤ (1 / 4) ^ φ j := by
      intro j hj
      obtain ⟨hjF, hd2, -, -⟩ := hGmem j hj
      obtain ⟨hk1, -⟩ := hspec j hj
      have hdpos : 0 < dipoleDist (c i) (c j) := h2s.trans_le hd2
      obtain ⟨-, hrj, hρj⟩ := hF' j hjF
      refine (gbar_le_div hdpos).trans ?_
      rw [max_eq_right hρj]
      have hpos : 0 < (2 : ℝ) ^ φ j * (2 * s) := by positivity
      calc ‖(c j).1 - (c j).2‖ ^ 2 / dipoleDist (c i) (c j) ^ 2
          ≤ (2 * s) ^ 2 / ((2 : ℝ) ^ φ j * (2 * s)) ^ 2 :=
            div_le_div₀ (sq_nonneg _) (pow_le_pow_left₀ (norm_nonneg _) hrj 2)
              (by positivity) (pow_le_pow_left₀ hpos.le hk1 2)
        _ = (1 / 4) ^ φ j := by
            rw [one_div_pow, show ((4 : ℝ) ^ φ j) = (2 ^ φ j) ^ 2 by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num]
            field_simp
    -- the shells that occur
    have hk : ∀ k ∈ G.image φ, k ≤ h + 5 := by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hk
      obtain ⟨hk1, -⟩ := hspec j hj
      have hdR := (hGmem j hj).2.2.2
      have h1 : (2 : ℝ) ^ φ j * (2 * s) ≤ 64 * 2 ^ h * s := (hk1.trans hdR).trans h17
      have h2 : (2 : ℝ) ^ φ j ≤ 2 ^ (h + 5) := by
        rw [pow_add]
        nlinarith
      exact (pow_le_pow_iff_right₀ one_lt_two).1 h2
    -- the endpoints
    have hpt : ∀ j, ∃ z, (z = (c j).1 ∨ z = (c j).2) ∧
        ‖z - (c i).1‖ ≤ dipoleDist (c i) (c j) + ρ := fun j => exists_endpoint_near (c i) (c j)
    choose z hzend hznear using hpt
    have hclass : ∀ k ∈ G.image φ, ((G.filter fun j => φ j = k).card : ℝ) * (1 / 4) ^ k ≤
        3 * p * (64 / M ^ 2 + 16 / M ^ 2 * (1 / 4) ^ k + (1 / 4) ^ k) := by
      intro k _
      set Gk := G.filter fun j => φ j = k with hGk
      have hGkV : Gk ⊆ X.biUnion id := fun j hj => hF (hGmem j (mem_filter.1 hj).1).1
      have hpack := card_mul_sq_le_of_separated_blocks hX hp (J := Gk) hGkV z (c i).1
        (ρ := 2 * 2 ^ k * (2 * s) + 2 * s) (δ := M * s) (by positivity) (fun j hj => ?_)
        fun j hj j' hj' hjj' => ?_
      · have h := shell_alg (N := (Gk.card : ℝ)) (P := p) hP hM1 hs
          (one_le_pow₀ one_le_two : (1 : ℝ) ≤ 2 ^ k) hpack
        rw [show ((1 : ℝ) / 4) ^ k = 1 / (2 ^ k) ^ 2 by
          rw [one_div_pow, ← pow_mul, mul_comm, pow_mul]; norm_num]
        exact h
      · rw [mem_filter] at hj
        obtain ⟨-, hk2⟩ := hspec j hj.1
        rw [hj.2] at hk2
        obtain ⟨hjF, -, -, -⟩ := hGmem j hj.1
        obtain ⟨-, hrj, hρj⟩ := hF' j hjF
        calc ‖z j - (c i).1‖ ≤ dipoleDist (c i) (c j) + ρ := hznear j
          _ ≤ 2 * 2 ^ k * (2 * s) + 2 * s := by
              have : dipoleDist (c i) (c j) ≤ 2 ^ (k + 1) * (2 * s) := hk2.le
              rw [pow_succ] at this
              linarith
      · rw [mem_filter] at hj hj'
        have hlt := mul_min_lt_dipoleDist hM0.le
          (hD j (hF (hGmem j hj.1).1) j' (hF (hGmem j' hj'.1).1) hjj')
        have hdist := dipoleDist_le_norm_of_endpoints (hzend j) (hzend j')
        obtain ⟨hj1, -, -⟩ := hF' j (hGmem j hj.1).1
        obtain ⟨hj1', -, -⟩ := hF' j' (hGmem j' hj'.1).1
        have hmin : s ≤ min ‖(c j).1 - (c j).2‖ ‖(c j').1 - (c j').2‖ := le_min hj1.le hj1'.le
        calc M * s ≤ M * min ‖(c j).1 - (c j).2‖ ‖(c j').1 - (c j').2‖ :=
              mul_le_mul_of_nonneg_left hmin hM0.le
          _ ≤ dipoleDist (c j) (c j') := hlt.le
          _ ≤ ‖z j - z j'‖ := hdist
    have hcardk : ((G.image φ).card : ℝ) ≤ h + 6 := by
      have : G.image φ ⊆ range (h + 6) := fun k hk' =>
        mem_range.2 (Nat.lt_succ_of_le (hk k hk'))
      have := card_le_card this
      rw [card_range] at this
      exact_mod_cast this
    have t1 := sum_inv_pow_le (G.image φ) (q := 4) (by norm_num)
    norm_num at t1
    calc ∑ j ∈ G, gbar M lam ε₀ R c i j ≤ ∑ j ∈ G, (1 / 4 : ℝ) ^ φ j := sum_le_sum hterm
      _ = ∑ k ∈ G.image φ, (G.filter fun j => φ j = k).card • (1 / 4 : ℝ) ^ k :=
          sum_comp (fun k => (1 / 4 : ℝ) ^ k) φ
      _ ≤ ∑ k ∈ G.image φ, 3 * p * (64 / M ^ 2 + 16 / M ^ 2 * (1 / 4) ^ k + (1 / 4) ^ k) := by
          refine sum_le_sum fun k hk' => ?_
          rw [nsmul_eq_mul]
          exact hclass k hk'
      _ = 3 * p * ((G.image φ).card * (64 / M ^ 2) +
            16 / M ^ 2 * ∑ k ∈ G.image φ, (1 / 4 : ℝ) ^ k + ∑ k ∈ G.image φ, (1 / 4 : ℝ) ^ k) := by
          rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      _ ≤ 3 * p * ((h + 6) * (64 / M ^ 2) + 16 / M ^ 2 * (4 / 3) + 4 / 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have f1 := mul_le_mul_of_nonneg_right hcardk (by positivity : (0 : ℝ) ≤ 64 / M ^ 2)
          have f2 : 16 / M ^ 2 * ∑ k ∈ G.image φ, (1 / 4 : ℝ) ^ k ≤ 16 / M ^ 2 * (4 / 3) :=
            mul_le_mul_of_nonneg_left (by simpa using t1) (by positivity)
          have f3 : ∑ k ∈ G.image φ, (1 / 4 : ℝ) ^ k ≤ 4 / 3 := by simpa using t1
          exact add_le_add (add_le_add f1 f2) f3
      _ ≤ 3 * p * (64 * (h + 6) / M ^ 2 + 22 / M ^ 2 + 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hMpos : (0 : ℝ) < M ^ 2 := by positivity
          have e1 : (h + 6 : ℝ) * (64 / M ^ 2) = 64 * (h + 6) / M ^ 2 := by ring
          have e2 : 16 / M ^ 2 * (4 / 3 : ℝ) ≤ 22 / M ^ 2 := by
            rw [div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right (by norm_num) hMpos.le
          linarith
  -- the constants
  have hM2 : (400 : ℝ) ≤ M ^ 2 := by nlinarith
  have hc : 3 * p * (64 * (h + 6) / M ^ 2 + 22 / M ^ 2 + 2) ≤
      p * (10 + 192 * h / M ^ 2) := by
    have hMpos : 0 < M ^ 2 := by positivity
    have e : 3 * p * (64 * (h + 6) / M ^ 2 + 22 / M ^ 2 + 2) =
        p * (6 + 192 * h / M ^ 2) + p * (1218 / M ^ 2) := by ring
    have e2 : 1218 / M ^ 2 ≤ 4 := by
      rw [div_le_iff₀ hMpos]
      linarith
    rw [e]
    have := mul_le_mul_of_nonneg_left e2 hP
    linarith
  calc ∑ j ∈ N, gbar M lam ε₀ R c i j + ∑ j ∈ Fr, gbar M lam ε₀ R c i j
      ≤ p + p * (10 + 192 * h / M ^ 2) := add_le_add hnear (hfar.trans hc)
    _ = p * (11 + 192 * h / M ^ 2) := by ring

end Level

/-! ### The weighted sum over the larger neighbours -/

section Weighted

variable {X : Finset (Finset ℕ)} {p : ℕ} {M lam ε₀ R : ℝ} {c : ℕ → ℂ × ℂ}

/-- `1/(1 - 2^{-1/M}) ≤ 2M / log 2` for `M ≥ 1`. -/
theorem one_sub_rpow_half_inv_le {M : ℝ} (hM : 1 ≤ M) :
    0 ≤ ((1 : ℝ) / 2) ^ (1 / M) ∧ ((1 : ℝ) / 2) ^ (1 / M) < 1 ∧
      1 / (1 - ((1 : ℝ) / 2) ^ (1 / M)) ≤ 2 * M / Real.log 2 := by
  have hM0 : 0 < M := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  set y := Real.log 2 / M with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one hM0]
    linarith
  have hx : ((1 : ℝ) / 2) ^ (1 / M) = Real.exp (-y) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div 2, Real.log_inv, hy]
    ring_nf
  have hexp : Real.exp (-y) ≤ 1 - y / 2 := by
    have h1 : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
    have h2 : Real.exp (-y) = 1 / Real.exp y := by rw [Real.exp_neg, one_div]
    rw [h2, div_le_iff₀ (Real.exp_pos y)]
    nlinarith
  rw [hx]
  refine ⟨(Real.exp_pos _).le, ?_, ?_⟩
  · linarith
  · have hpos : 0 < y / 2 := by positivity
    calc 1 / (1 - Real.exp (-y)) ≤ 1 / (y / 2) :=
          one_div_le_one_div_of_le hpos (by linarith)
      _ = 2 * M / Real.log 2 := by
          rw [hy]
          field_simp

open scoped Classical in
/-- **The weighted sum over the larger neighbours** (proof of Lemma 4.56): on `𝒟`,
`∑_{j ≠ i, r_j ≥ r_i} (r_j / (ε₀ R))^{1/M} ḡ_ij ≤ p (22 / log 2 + 768 / (log 2)²) M`. -/
theorem sum_weight_gbar_le (hX : IsSubpartition X) (hp : ∀ S ∈ X, S.card ≤ p) (hM : 20 < M)
    (hD : ∀ j ∈ X.biUnion id, ∀ k ∈ X.biUnion id, ¬ SameBlock X j k →
      ¬ MultipoleLinked M lam (c j) (c k))
    (hr : ∀ j ∈ X.biUnion id, 0 < ‖(c j).1 - (c j).2‖ ∧ ‖(c j).1 - (c j).2‖ ≤ ε₀ * R)
    {i : ℕ} (hi : i ∈ X.biUnion id) :
    ∑ j ∈ ((X.biUnion id).erase i).filter
        (fun j => ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖),
        (‖(c j).1 - (c j).2‖ / (ε₀ * R)) ^ (1 / M) * gbar M lam ε₀ R c i j ≤
      p * (22 / Real.log 2 + 768 / Real.log 2 ^ 2) * M := by
  have hM0 : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set R₀ := ε₀ * R with hR₀def
  have hR₀ : 0 < R₀ := (hr i hi).1.trans_le (hr i hi).2
  set J := ((X.biUnion id).erase i).filter
    (fun j => ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖) with hJ
  have hJV : J ⊆ X.biUnion id := fun j hj => mem_of_mem_erase (mem_filter.1 hj).1
  set x := ((1 : ℝ) / 2) ^ (1 / M) with hx
  obtain ⟨hx0, hx1, hxinv⟩ := one_sub_rpow_half_inv_le hM1
  set φ : ℕ → ℕ := fun j => level 2 R₀ ‖(c j).1 - (c j).2‖ with hφ
  have hspec : ∀ j ∈ J, (2 : ℝ) ^ φ j * ‖(c j).1 - (c j).2‖ ≤ R₀ ∧
      R₀ < 2 ^ (φ j + 1) * ‖(c j).1 - (c j).2‖ :=
    fun j hj => level_spec one_lt_two (hr j (hJV hj)).1 (hr j (hJV hj)).2
  -- the weights
  have hw : ∀ j ∈ J, (‖(c j).1 - (c j).2‖ / R₀) ^ (1 / M) ≤ x ^ φ j := by
    intro j hj
    have hrj := (hr j (hJV hj)).1
    have h1 : ‖(c j).1 - (c j).2‖ / R₀ ≤ ((1 : ℝ) / 2) ^ φ j := by
      rw [div_le_iff₀ hR₀, one_div_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity),
        mul_comm]
      exact (hspec j hj).1
    calc (‖(c j).1 - (c j).2‖ / R₀) ^ (1 / M) ≤ (((1 : ℝ) / 2) ^ φ j) ^ (1 / M) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = x ^ φ j := by
          rw [hx, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num), mul_comm]
  -- one level
  have hlevel : ∀ h ∈ J.image φ, ∑ j ∈ J.filter (fun j => φ j = h), gbar M lam ε₀ R c i j ≤
      p * (11 + 192 * h / M ^ 2) := by
    intro h _
    set s := R₀ / 2 ^ (h + 1) with hs
    have hs0 : 0 < s := by positivity
    refine sum_gbar_level_le hX hp hM hD hs0 (h := h) ?_
      (fun j hj => hJV (mem_filter.1 hj).1) fun j hj => ?_
    · rw [hs, pow_succ]
      field_simp
      have e : 17 * ε₀ * R = 17 * R₀ := by rw [hR₀def]; ring
      linarith
    · rw [mem_filter] at hj
      obtain ⟨h1, h2⟩ := hspec j hj.1
      rw [hj.2] at h1 h2
      have hρj := (mem_filter.1 hj.1).2
      refine ⟨?_, ?_, hρj⟩
      · rw [hs, div_lt_iff₀ (by positivity), mul_comm]
        exact h2
      · rw [hs, pow_succ]
        rw [show 2 * (R₀ / (2 ^ h * 2)) = R₀ / 2 ^ h by field_simp, le_div_iff₀ (by positivity),
          mul_comm]
        exact h1
  -- summing the levels
  have hS1 : ∑ h ∈ J.image φ, x ^ h ≤ 1 / (1 - x) := by
    have hsum := summable_geometric_of_lt_one hx0 hx1
    refine (hsum.sum_le_tsum _ fun _ _ => by positivity).trans_eq ?_
    rw [tsum_geometric_of_lt_one hx0 hx1]
    exact (one_div _).symm
  have hS2 : ∑ h ∈ J.image φ, (h : ℝ) * x ^ h ≤ (1 / (1 - x)) ^ 2 := by
    refine (sum_mul_pow_le _ hx0 hx1).trans ?_
    rw [div_pow, one_pow]
    exact div_le_div_of_nonneg_right hx1.le (sq_nonneg _)
  have hsx : 0 < 1 - x := by linarith
  calc ∑ j ∈ J, (‖(c j).1 - (c j).2‖ / R₀) ^ (1 / M) * gbar M lam ε₀ R c i j
      ≤ ∑ j ∈ J, x ^ φ j * gbar M lam ε₀ R c i j :=
        sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hw j hj) (gbar_nonneg _ _)
    _ = ∑ h ∈ J.image φ, x ^ h * ∑ j ∈ J.filter (fun j => φ j = h), gbar M lam ε₀ R c i j := by
        rw [← sum_fiberwise_of_maps_to (s := J) (t := J.image φ) (g := φ)
          fun j hj => mem_image_of_mem _ hj]
        refine sum_congr rfl fun h _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun j hj => ?_
        rw [(mem_filter.1 hj).2]
    _ ≤ ∑ h ∈ J.image φ, x ^ h * (p * (11 + 192 * h / M ^ 2)) :=
        sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (hlevel h hh) (by positivity)
    _ = p * (11 * ∑ h ∈ J.image φ, x ^ h + 192 / M ^ 2 * ∑ h ∈ J.image φ, (h : ℝ) * x ^ h) := by
        simp only [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun h _ => ?_
        ring
    _ ≤ p * (11 * (2 * M / Real.log 2) + 192 / M ^ 2 * (2 * M / Real.log 2) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hP
        · exact mul_le_mul_of_nonneg_left (hS1.trans hxinv) (by norm_num)
        · refine mul_le_mul_of_nonneg_left (hS2.trans ?_) (by positivity)
          exact pow_le_pow_left₀ (by positivity) hxinv 2
    _ = p * (22 * M / Real.log 2 + 768 / Real.log 2 ^ 2) := by
        field_simp
        ring
    _ ≤ p * (22 / Real.log 2 + 768 / Real.log 2 ^ 2) * M := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hP
        have : 768 / Real.log 2 ^ 2 ≤ 768 / Real.log 2 ^ 2 * M :=
          le_mul_of_one_le_right (by positivity) hM1
        have e : 22 * M / Real.log 2 = 22 / Real.log 2 * M := by ring
        rw [e, add_mul]
        linarith

end Weighted

/-! ### Eq. (4.105) -/

section Product

open scoped Classical

/-- **Eq. (4.105)** (Lemma 4.56, second claim, (4.105) in the proof of Lemma 4.56): there is `C > 0` depending only on `p` such that for `M > 20`, every
subpartition `X` with blocks of at most `p` labels and every configuration in the event
`𝒟 = ⋂_{i ∈ V_X} {0 < r_i ≤ ε₀ R̄} ∩ ⋂_{ij ∈ ℰ^inter(X)} 𝓑_ij^c`,
`∏_{i ∈ V_X} (1 + ∑_{j ∈ V_X, j ≠ i} ḡ_ij) ≤ (C M)^{|V_X|} ∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{1/M}`, with `R` in
the role of `R̄_{β,λ}`. Here `C = 1 + 2p (22 / log 2 + 768 / (log 2)²)`. -/
theorem claim_int2 (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ {M : ℝ}, 20 < M → ∀ (lam ε₀ R : ℝ)
    {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ p) → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
        ¬ MultipoleLinked M lam (c i) (c j)) →
      ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) ≤
        (C * M) ^ (X.biUnion id).card *
          ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (1 / M) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set K₁ := 22 / Real.log 2 + 768 / Real.log 2 ^ 2 with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  refine ⟨1 + 2 * p * K₁, by positivity, fun {M} hM lam ε₀ R X hX hp c hr hD => ?_⟩
  have hM0 : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  set V := X.biUnion id with hV
  set C := 1 + 2 * p * K₁ with hC
  have hC0 : 0 < C := by positivity
  rcases V.eq_empty_or_nonempty with hVe | ⟨i₀, hi₀⟩
  · rw [hVe]
    simp
  set R₀ := ε₀ * R with hR₀def
  have hR₀ : 0 < R₀ := (hr i₀ hi₀).1.trans_le (hr i₀ hi₀).2
  set r : ℕ → ℝ := fun i => ‖(c i).1 - (c i).2‖ with hr_def
  set w : ℕ → ℝ := fun i => (r i / R₀) ^ (1 / M) with hw_def
  set g : ℕ → ℕ → ℝ := fun i j => gbar M lam ε₀ R c i j with hg_def
  set S : ℕ → ℝ := fun i => ∑ j ∈ V.erase i, g i j with hS_def
  have hw0 : ∀ i ∈ V, 0 < w i := fun i hi =>
    Real.rpow_pos_of_pos (div_pos (hr i hi).1 hR₀) _
  have hw1 : ∀ i ∈ V, w i ≤ 1 := fun i hi =>
    Real.rpow_le_one (div_nonneg (hr i hi).1.le hR₀.le)
      ((div_le_one hR₀).2 (hr i hi).2) (by positivity)
  have hwmono : ∀ i ∈ V, ∀ j ∈ V, r i ≤ r j → w i ≤ w j := fun i hi j hj h =>
    Real.rpow_le_rpow (div_nonneg (hr i hi).1.le hR₀.le) (div_le_div_of_nonneg_right h hR₀.le)
      (by positivity)
  have hS0 : ∀ i, 0 ≤ S i := fun i => sum_nonneg fun j _ => gbar_nonneg _ _
  -- the per-`i` bound
  have hper : ∀ i ∈ V, ∑ j ∈ V.erase i, (if r i ≤ r j then w j * g i j else 0) ≤ p * K₁ * M := by
    intro i hi
    rw [← sum_filter]
    exact sum_weight_gbar_le hX hp hM hD hr hi
  -- symmetrization
  have hsplit : ∀ i ∈ V, w i * S i ≤ ∑ j ∈ V.erase i, (if r i ≤ r j then w j * g i j else 0) +
      ∑ j ∈ V.erase i, (if r j < r i then w i * g i j else 0) := by
    intro i hi
    rw [hS_def, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun j hj => ?_
    have hjV : j ∈ V := mem_of_mem_erase hj
    have hg0 : 0 ≤ g i j := gbar_nonneg _ _
    split_ifs with h1 h2 h2
    · linarith
    · rw [add_zero]
      exact mul_le_mul_of_nonneg_right (hwmono i hi j hjV h1) hg0
    · rw [zero_add]
    · exact absurd (not_le.1 h1) h2
  have hswap : ∑ i ∈ V, ∑ j ∈ V.erase i, (if r j < r i then w i * g i j else 0) ≤
      ∑ i ∈ V, ∑ j ∈ V.erase i, (if r i ≤ r j then w j * g i j else 0) := by
    rw [sum_comm' (t' := V) (s' := fun y => V.erase y) fun x y => by
      simp only [mem_erase]
      tauto]
    refine sum_le_sum fun a _ => sum_le_sum fun b _ => ?_
    split_ifs with h1 h2
    · rw [hg_def]
      simp only
      rw [gbar_comm]
    · exact absurd h1.le h2
    · exact mul_nonneg (hw0 b (mem_of_mem_erase ‹b ∈ V.erase a›)).le (gbar_nonneg _ _)
    · exact le_rfl
  have hsym : ∑ i ∈ V, w i * S i ≤ 2 * (V.card * (p * K₁ * M)) := by
    calc ∑ i ∈ V, w i * S i ≤ ∑ i ∈ V, (∑ j ∈ V.erase i, (if r i ≤ r j then w j * g i j else 0) +
          ∑ j ∈ V.erase i, (if r j < r i then w i * g i j else 0)) := sum_le_sum hsplit
      _ ≤ 2 * ∑ i ∈ V, ∑ j ∈ V.erase i, (if r i ≤ r j then w j * g i j else 0) := by
          rw [sum_add_distrib]
          linarith
      _ ≤ 2 * ∑ i ∈ V, p * K₁ * M := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum hper) (by norm_num)
      _ = 2 * (V.card * (p * K₁ * M)) := by rw [sum_const, nsmul_eq_mul]
  have htotal : ∑ i ∈ V, w i * (1 + S i) ≤ V.card * (C * M) := by
    have h1 : ∑ i ∈ V, w i ≤ V.card := by
      calc ∑ i ∈ V, w i ≤ ∑ i ∈ V, (1 : ℝ) := sum_le_sum hw1
        _ = V.card := by rw [sum_const, nsmul_eq_mul, mul_one]
    have hn : (V.card : ℝ) ≤ V.card * M := le_mul_of_one_le_right (Nat.cast_nonneg _) hM1
    calc ∑ i ∈ V, w i * (1 + S i) = ∑ i ∈ V, w i + ∑ i ∈ V, w i * S i := by
          rw [← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          ring
      _ ≤ V.card + 2 * (V.card * (p * K₁ * M)) := add_le_add h1 hsym
      _ ≤ V.card * M + 2 * (V.card * (p * K₁ * M)) := by linarith
      _ = V.card * (C * M) := by rw [hC]; ring
  -- the arithmetic-geometric mean inequality
  have hamgm := prod_le_prod_mul_exp V (fun i => 1 + S i) (fun i => C * M / w i)
    (fun i _ => by have := hS0 i; linarith) fun i hi => div_pos (by positivity) (hw0 i hi)
  have hexp : Real.exp (∑ i ∈ V, ((1 + S i) / (C * M / w i) - 1)) ≤ 1 := by
    refine (Real.exp_le_exp.2 ?_).trans_eq Real.exp_zero
    have e : ∑ i ∈ V, ((1 + S i) / (C * M / w i) - 1) =
        (∑ i ∈ V, w i * (1 + S i)) / (C * M) - V.card := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_div]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      have := (hw0 i hi).ne'
      field_simp
    rw [e, sub_nonpos, div_le_iff₀ (by positivity)]
    exact htotal
  have hprod : ∏ i ∈ V, C * M / w i = (C * M) ^ V.card * ∏ i ∈ V, (R₀ / r i) ^ (1 / M) := by
    rw [prod_div_distrib, prod_const, div_eq_mul_inv, ← prod_inv_distrib]
    congr 1
    refine prod_congr rfl fun i hi => ?_
    rw [hw_def]
    simp only
    rw [← Real.inv_rpow (div_nonneg (hr i hi).1.le hR₀.le), inv_div]
  calc ∏ i ∈ V, (1 + S i) ≤ (∏ i ∈ V, C * M / w i) *
        Real.exp (∑ i ∈ V, ((1 + S i) / (C * M / w i) - 1)) := hamgm
    _ ≤ (∏ i ∈ V, C * M / w i) * 1 :=
        mul_le_mul_of_nonneg_left hexp (prod_nonneg fun i hi => (div_pos (by positivity)
          (hw0 i hi)).le)
    _ = (C * M) ^ V.card * ∏ i ∈ V, (R₀ / r i) ^ (1 / M) := by rw [mul_one, hprod]

end Product

/-! ### From the pairs of `ℰ^inter(X)` to the larger neighbours -/

section Bridge

open scoped Classical

/-- `∑_{ij ∈ ℰ^inter(X)} a^abs_ij ≤ ∑_{i ∈ V_X} ∑_{j : ij ∈ ℰ^inter(X)} a^abs_ij 𝟙_{r_j ≥ r_i}`: each
inter-block pair is counted at its endpoint of smaller radius (the bookkeeping by which (4.104)
controls `exp(2 C₁ ∑_{ij ∈ ℰ^inter(X)} a^abs_ij)` in the proof of Lemma 4.57). -/
theorem sum_interPairs_absOddWeight_le (X : Finset (Finset ℕ)) (M lam ε₀ R : ℝ)
    (c : ℕ → ℂ × ℂ) :
    ∑ p ∈ interPairs X, absOddWeight M lam ε₀ R (c p.1) (c p.2) ≤
      ∑ i ∈ X.biUnion id, ∑ j ∈ (X.biUnion id).filter (fun j => ¬ SameBlock X i j),
        absOddWeight M lam ε₀ R (c i) (c j) *
          (if ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ then 1 else 0) := by
  set V := X.biUnion id with hV
  set a : ℕ → ℕ → ℝ := fun i j => absOddWeight M lam ε₀ R (c i) (c j) with ha
  set f : ℕ × ℕ → ℝ := fun q => a q.1 q.2 *
    (if ‖(c q.1).1 - (c q.1).2‖ ≤ ‖(c q.2).1 - (c q.2).2‖ then 1 else 0) with hf
  have ha0 : ∀ i j, 0 ≤ a i j := fun i j => absOddWeight_nonneg _ _ _ _ _ _
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (ha0 _ _) (by split_ifs <;> norm_num)
  set W := (V ×ˢ V).filter fun q => ¬ SameBlock X q.1 q.2 with hW
  set A := interPairs X with hA
  set B := A.image Prod.swap with hB
  have hAW : A ⊆ W := by
    intro q hq
    have h12 := interPairs_subset_pairsOn_biUnion X hq
    refine mem_filter.2 ⟨mem_product.2 h12, ?_⟩
    rintro ⟨S, hS, h1, h2⟩
    exact (mem_interPairs.1 hq).2 ⟨S, hS, mem_pairsOn.2 ⟨h1, h2,
      (mem_pairsOn.1 (interPairs_subset_pairsOn hq)).2.2⟩⟩
  have hBW : B ⊆ W := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := mem_image.1 hq
    have := mem_filter.1 (hAW hq')
    refine mem_filter.2 ⟨mem_product.2 ⟨(mem_product.1 this.1).2, (mem_product.1 this.1).1⟩, ?_⟩
    rintro ⟨S, hS, h1, h2⟩
    exact this.2 ⟨S, hS, h2, h1⟩
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro q hqA hqB
    obtain ⟨q', hq', rfl⟩ := mem_image.1 hqB
    have h1 := (mem_pairsOn.1 (interPairs_subset_pairsOn hqA)).2.2
    have h2 := (mem_pairsOn.1 (interPairs_subset_pairsOn hq')).2.2
    simp only [Prod.fst_swap, Prod.snd_swap] at h1
    omega
  have hRHS : ∑ i ∈ V, ∑ j ∈ V.filter (fun j => ¬ SameBlock X i j), f (i, j) =
      ∑ q ∈ W, f q := by
    rw [hW, sum_filter, sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_filter]
  have hsplit : ∀ p ∈ A, a p.1 p.2 ≤ f p + f p.swap := by
    intro p _
    simp only [hf, Prod.fst_swap, Prod.snd_swap]
    have hsym : a p.2 p.1 = a p.1 p.2 := absOddWeight_comm _ _
    rw [hsym]
    split_ifs with h1 h2 h2 <;> linarith [ha0 p.1 p.2]
  calc ∑ p ∈ A, a p.1 p.2 ≤ ∑ p ∈ A, (f p + f p.swap) := sum_le_sum hsplit
    _ = ∑ q ∈ A, f q + ∑ q ∈ B, f q := by
        rw [sum_add_distrib, sum_image fun q _ q' _ h => Prod.swap_injective h]
    _ = ∑ q ∈ A ∪ B, f q := (sum_union hAB).symm
    _ ≤ ∑ q ∈ W, f q :=
        sum_le_sum_of_subset_of_nonneg (union_subset hAW hBW) fun q _ _ => hf0 q
    _ = _ := hRHS.symm

end Bridge

/-! ### Lemma 4.56 -/

section Lemma

open scoped Classical

/-- **Lemma 4.56** (Lemma 4.56, control of the interactions, Lemma 4.56): let `p ∈ ℕ`. There is `C > 0` depending only on `p` such that for `M > 20`, every
subpartition `X` with blocks of at most `p` labels (for `p = p(β)`, Definition 2.8) and every
configuration in the event `𝒟 = ⋂_{i ∈ V_X} {0 < r_i ≤ ε₀ R̄} ∩ ⋂_{ij ∈ ℰ^inter(X)} 𝓑_ij^c`:

* (4.104) for every `i ∈ V_X`,
  `∑_{j : ij ∈ ℰ^inter(X)} a^abs_ij 𝟙_{r_j ≥ r_i} ≤ (C/M) (log(17 ε₀ R̄ / r_i) + 1)`;
* (4.105) `∏_{i ∈ V_X} (1 + ∑_{j ∈ V_X, j ≠ i} ḡ_ij) ≤ (C M)^{|V_X|} ∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{1/M}`,

with `R` in the role of `R̄_{β,λ}` (the statement holds for every `λ`). -/
theorem lemma_4_56 (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ {M : ℝ}, 20 < M → ∀ (lam ε₀ R : ℝ)
    {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ p) → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
        ¬ MultipoleLinked M lam (c i) (c j)) →
      (∀ i ∈ X.biUnion id,
        ∑ j ∈ (X.biUnion id).filter (fun j => ¬ SameBlock X i j),
            absOddWeight M lam ε₀ R (c i) (c j) *
              (if ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ then 1 else 0) ≤
          C / M * (Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1)) ∧
      ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) ≤
        (C * M) ^ (X.biUnion id).card *
          ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (1 / M) := by
  obtain ⟨C₁, hC₁, h1⟩ := claim_int p
  obtain ⟨C₂, hC₂, h2⟩ := claim_int2 p
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun {M} hM lam ε₀ R X hX hp c hr hD => ⟨?_, ?_⟩⟩
  · intro i hi
    have hM0 : 0 < M := by linarith
    obtain ⟨hρ, hρR⟩ := hr i hi
    have hlog : 0 ≤ Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1 := by
      have : 1 ≤ 17 * ε₀ * R / ‖(c i).1 - (c i).2‖ := by
        rw [le_div_iff₀ hρ]
        linarith
      linarith [Real.log_nonneg this]
    refine (h1 hM lam ε₀ R hX hp c hr hD i hi).trans ?_
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_max_left _ _) hM0.le) hlog
  · have hM0 : 0 < M := by linarith
    refine (h2 hM lam ε₀ R hX hp c hr hD).trans (mul_le_mul_of_nonneg_right ?_
      (prod_nonneg fun i _ => Real.rpow_nonneg (div_nonneg (by
        have := hr i ‹_›
        linarith [this.1, this.2]) (norm_nonneg _)) _))
    exact pow_le_pow_left₀ (mul_nonneg hC₂.le hM0.le)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hM0.le) _

end Lemma

end AbsoluteLower

end MultipoleBKT

end
