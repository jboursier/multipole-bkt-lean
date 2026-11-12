/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Dyadic

/-!
# Lemma 4.56, eq. (4.104): the interactions with larger dipoles

Lemma 4.56:
on the event `𝒟 = ⋂_{i ∈ V_X} {0 < r_i ≤ ε₀ R̄} ∩ ⋂_{ij ∈ ℰ^inter(X)} 𝓑_ij^c`, for blocks of at most
`p` labels and `M > 20`,
`∑_{j : ij ∈ ℰ^inter(X)} a^abs_ij 𝟙_{r_j ≥ r_i} ≤ (C/M) (log(17 ε₀ R̄ / r_i) + 1)` (eq. (4.104)).

The paper's dyadic integrals (proof of Lemma 4.56) are replaced by dyadic sums:

* `sum_close_le` (the sum `A₂` of (4.107), eq. (4.112)): the neighbours with `M r_i ≤ d_ij ≤ r_j`
  in one dyadic shell `2^b M r_i ≤ d_ij < 2^{b+1} M r_i` are pairwise linked, hence in one block
  (proof of Lemma 4.56), so `A₂ ≤ ∑_b p r_i / (2^b M r_i) ≤ 2p/M`;
* `sum_far_le` (the sum `A₁` of (4.106), eqs. (4.109)–(4.111)): the neighbours with
  `max(r_j, M r_i) < d_ij` are grouped by the dyadic levels `2^a r_i ≤ r_j < 2^{a+1} r_i` and
  `2^b M r_i ≤ d_ij < 2^{b+1} M r_i`; in each class, endpoints of dipoles of distinct blocks are
  `M 2^a r_i`-separated, which bounds the class by the packing estimate (4.110)
  (`card_mul_sq_le_of_separated_blocks`); summing the resulting geometric series gives
  `A₁ ≤ 6p (32 (B + 1)/M² + 16/M⁴ + 8/M)` with `B = ⌊log₂(17 ε₀ R̄ / r_i)⌋`.
* `claim_int` (eq. (4.104)), with `C = p (192 / log 2 + 308) + 1`.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SetPartition Peeling Parity

section Close

variable {X : Finset (Finset ℕ)} {p : ℕ} {M lam : ℝ} {c : ℕ → ℂ × ℂ}

/-- **The close range** (the sum `A₂` of (4.107), eq. (4.112) in the proof of Lemma 4.56): for labels `j`
with `M r_i ≤ d_ij ≤ r_j`, `∑_j r_i / d_ij ≤ 2p/M`. -/
theorem sum_close_le (hX : IsSubpartition X) (hp : ∀ S ∈ X, S.card ≤ p) (hM : 5 ≤ M)
    (hD : ∀ j ∈ X.biUnion id, ∀ k ∈ X.biUnion id, ¬ SameBlock X j k →
      ¬ MultipoleLinked M lam (c j) (c k))
    {i : ℕ} (hρ : 0 < ‖(c i).1 - (c i).2‖) {J : Finset ℕ} (hJ : J ⊆ X.biUnion id)
    (hJ' : ∀ j ∈ J, dipoleDist (c i) (c j) ≤ ‖(c j).1 - (c j).2‖ ∧
      M * ‖(c i).1 - (c i).2‖ ≤ dipoleDist (c i) (c j)) :
    ∑ j ∈ J, ‖(c i).1 - (c i).2‖ / dipoleDist (c i) (c j) ≤ 2 * p / M := by
  classical
  set ρ := ‖(c i).1 - (c i).2‖ with hρdef
  have hM0 : 0 < M := by linarith
  have hMρ : 0 < M * ρ := mul_pos hM0 hρ
  set φ : ℕ → ℕ := fun j => level 2 (dipoleDist (c i) (c j)) (M * ρ) with hφ
  have hspec : ∀ j ∈ J, (2 : ℝ) ^ φ j * (M * ρ) ≤ dipoleDist (c i) (c j) ∧
      dipoleDist (c i) (c j) < 2 ^ (φ j + 1) * (M * ρ) :=
    fun j hj => level_spec one_lt_two hMρ (hJ' j hj).2
  have hterm : ∀ j ∈ J, ρ / dipoleDist (c i) (c j) ≤ 1 / M * (1 / 2) ^ φ j := by
    intro j hj
    have hpos : 0 < (2 : ℝ) ^ φ j * (M * ρ) := by positivity
    calc ρ / dipoleDist (c i) (c j) ≤ ρ / ((2 : ℝ) ^ φ j * (M * ρ)) :=
          div_le_div_of_nonneg_left hρ.le hpos (hspec j hj).1
      _ = 1 / M * (1 / 2) ^ φ j := by
          rw [one_div_pow]
          field_simp
  have hcount : ∀ b ∈ J.image φ, ((J.filter fun j => φ j = b).card : ℝ) ≤ p := by
    intro b _
    refine Nat.cast_le.2 (card_le_of_forall_sameBlock hX hp fun j hj k hk => ?_)
    rw [mem_filter] at hj hk
    by_contra hjk
    have hlt := mul_min_lt_dipoleDist hM0.le (hD j (hJ hj.1) k (hJ hk.1) hjk)
    have htri := dipoleDist_le_add (c i) (c j) (c k)
    obtain ⟨hj1, hj2⟩ := hspec j hj.1
    obtain ⟨hk1, hk2⟩ := hspec k hk.1
    rw [hj.2] at hj1 hj2
    rw [hk.2] at hk1 hk2
    set t := (2 : ℝ) ^ b * ρ with ht
    have ht0 : 0 < t := by positivity
    have h2b : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ one_le_two
    have hρt : ρ ≤ t := le_mul_of_one_le_left hρ.le h2b
    have hmin : t * M ≤ min ‖(c j).1 - (c j).2‖ ‖(c k).1 - (c k).2‖ := by
      refine le_min ?_ ?_
      · calc t * M = 2 ^ b * (M * ρ) := by rw [ht]; ring
          _ ≤ _ := hj1.trans (hJ' j hj.1).1
      · calc t * M = 2 ^ b * (M * ρ) := by rw [ht]; ring
          _ ≤ _ := hk1.trans (hJ' k hk.1).1
    have hj2' : dipoleDist (c i) (c j) < 2 * t * M := by
      calc dipoleDist (c i) (c j) < 2 ^ (b + 1) * (M * ρ) := hj2
        _ = 2 * t * M := by rw [ht, pow_succ]; ring
    have hk2' : dipoleDist (c i) (c k) < 2 * t * M := by
      calc dipoleDist (c i) (c k) < 2 ^ (b + 1) * (M * ρ) := hk2
        _ = 2 * t * M := by rw [ht, pow_succ]; ring
    have hM2 : 4 * M + 1 ≤ M * M := by nlinarith
    have h1 : M * (t * M) ≤ M * min ‖(c j).1 - (c j).2‖ ‖(c k).1 - (c k).2‖ :=
      mul_le_mul_of_nonneg_left hmin hM0.le
    have h2 : t * (4 * M + 1) ≤ t * (M * M) := mul_le_mul_of_nonneg_left hM2 ht0.le
    nlinarith
  calc ∑ j ∈ J, ρ / dipoleDist (c i) (c j)
      ≤ ∑ j ∈ J, 1 / M * (1 / 2) ^ φ j := sum_le_sum hterm
    _ = ∑ b ∈ J.image φ, (J.filter fun j => φ j = b).card • (1 / M * (1 / 2) ^ b) :=
        sum_comp (fun b => 1 / M * (1 / 2 : ℝ) ^ b) φ
    _ ≤ ∑ b ∈ J.image φ, (p : ℝ) * (1 / M * (1 / 2) ^ b) := by
        refine sum_le_sum fun b hb => ?_
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcount b hb) (by positivity)
    _ = p / M * ∑ b ∈ J.image φ, (1 / 2 : ℝ) ^ b := by
        rw [mul_sum]
        refine sum_congr rfl fun b _ => ?_
        ring
    _ ≤ p / M * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := sum_inv_pow_le (J.image φ) (q := 2) one_lt_two
        norm_num at this ⊢
        exact this
    _ = 2 * p / M := by ring

end Close

section Far

variable {X : Finset (Finset ℕ)} {p : ℕ} {M lam : ℝ} {c : ℕ → ℂ × ℂ}

/-- The algebra of one dyadic class: from the packing bound
`N (M u ρ)² ≤ p (2 (2 v M ρ + ρ) + M u ρ)²`, the class contributes
`N · 2u/(M² v²) ≤ 6p (16/(M² u) + 4/(M⁴ u v²) + u/(M² v²))`. -/
theorem fiber_alg {N P M ρ u v : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hpack : N * (M * u * ρ) ^ 2 ≤ P * (2 * (2 * v * M * ρ + ρ) + M * u * ρ) ^ 2) :
    N * (2 * u / (M ^ 2 * v ^ 2)) ≤
      6 * P * (16 / (M ^ 2 * u) + 4 / (M ^ 4 * u * v ^ 2) + u / (M ^ 2 * v ^ 2)) := by
  have hM0 : 0 < M := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hpack' : N * (M * u) ^ 2 ≤ 3 * P * (16 * v ^ 2 * M ^ 2 + 4 + M ^ 2 * u ^ 2) := by
    have h1 : N * (M * u) ^ 2 * ρ ^ 2 ≤ P * (4 * v * M + 2 + M * u) ^ 2 * ρ ^ 2 := by
      calc N * (M * u) ^ 2 * ρ ^ 2 = N * (M * u * ρ) ^ 2 := by ring
        _ ≤ P * (2 * (2 * v * M * ρ + ρ) + M * u * ρ) ^ 2 := hpack
        _ = P * (4 * v * M + 2 + M * u) ^ 2 * ρ ^ 2 := by ring
    have h2 := le_of_mul_le_mul_right h1 (by positivity)
    have h3 : (4 * v * M + 2 + M * u) ^ 2 ≤ 3 * (16 * v ^ 2 * M ^ 2 + 4 + M ^ 2 * u ^ 2) := by
      nlinarith [sq_nonneg (4 * v * M - 2), sq_nonneg (4 * v * M - M * u), sq_nonneg (2 - M * u)]
    calc N * (M * u) ^ 2 ≤ P * (4 * v * M + 2 + M * u) ^ 2 := h2
      _ ≤ P * (3 * (16 * v ^ 2 * M ^ 2 + 4 + M ^ 2 * u ^ 2)) := mul_le_mul_of_nonneg_left h3 hP
      _ = 3 * P * (16 * v ^ 2 * M ^ 2 + 4 + M ^ 2 * u ^ 2) := by ring
  have hk : 0 < 2 / (M ^ 4 * u * v ^ 2) := by positivity
  calc N * (2 * u / (M ^ 2 * v ^ 2)) = N * (M * u) ^ 2 * (2 / (M ^ 4 * u * v ^ 2)) := by
        field_simp
    _ ≤ 3 * P * (16 * v ^ 2 * M ^ 2 + 4 + M ^ 2 * u ^ 2) * (2 / (M ^ 4 * u * v ^ 2)) :=
        mul_le_mul_of_nonneg_right hpack' hk.le
    _ = 6 * P * (16 / (M ^ 2 * u) + 4 / (M ^ 4 * u * v ^ 2) + u / (M ^ 2 * v ^ 2)) := by
        field_simp
        ring

/-- **The far range** (the sum `A₁` of (4.106), eqs. (4.109)–(4.111) in the proof of Lemma 4.56): for labels
`j` with `r_i ≤ r_j < d_ij`, `M r_i ≤ d_ij ≤ R'`,
`∑_j r_i r_j / d_ij² ≤ 6p (32 (B + 1)/M² + 16/M⁴ + 8/M)`, `B = ⌊log₂(R'/r_i)⌋`. -/
theorem sum_far_le (hX : IsSubpartition X) (hp : ∀ S ∈ X, S.card ≤ p) (hM : 1 ≤ M)
    (hD : ∀ j ∈ X.biUnion id, ∀ k ∈ X.biUnion id, ¬ SameBlock X j k →
      ¬ MultipoleLinked M lam (c j) (c k))
    {i : ℕ} (hρ : 0 < ‖(c i).1 - (c i).2‖) {R' : ℝ} {J : Finset ℕ} (hJ : J ⊆ X.biUnion id)
    (hJ' : ∀ j ∈ J, ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ ∧
      ‖(c j).1 - (c j).2‖ < dipoleDist (c i) (c j) ∧
      M * ‖(c i).1 - (c i).2‖ ≤ dipoleDist (c i) (c j) ∧ dipoleDist (c i) (c j) ≤ R') :
    ∑ j ∈ J, ‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖ / dipoleDist (c i) (c j) ^ 2 ≤
      6 * p * (32 * (⌊Real.logb 2 (R' / ‖(c i).1 - (c i).2‖)⌋₊ + 1) / M ^ 2 + 16 / M ^ 4 +
        8 / M) := by
  classical
  set ρ := ‖(c i).1 - (c i).2‖ with hρdef
  set r : ℕ → ℝ := fun j => ‖(c j).1 - (c j).2‖ with hr
  set d : ℕ → ℝ := fun j => dipoleDist (c i) (c j) with hd
  set B := ⌊Real.logb 2 (R' / ρ)⌋₊ with hB
  have hM0 : 0 < M := by linarith
  have hMρ : 0 < M * ρ := mul_pos hM0 hρ
  set φ : ℕ → ℕ × ℕ := fun j => (level 2 (r j) ρ, level 2 (d j) (M * ρ)) with hφ
  have hsa : ∀ j ∈ J, (2 : ℝ) ^ (φ j).1 * ρ ≤ r j ∧ r j < 2 ^ ((φ j).1 + 1) * ρ :=
    fun j hj => level_spec one_lt_two hρ (hJ' j hj).1
  have hsb : ∀ j ∈ J, (2 : ℝ) ^ (φ j).2 * (M * ρ) ≤ d j ∧ d j < 2 ^ ((φ j).2 + 1) * (M * ρ) :=
    fun j hj => level_spec one_lt_two hMρ (hJ' j hj).2.2.1
  set w : ℕ × ℕ → ℝ := fun q => 2 * 2 ^ q.1 / (M ^ 2 * (2 ^ q.2) ^ 2) with hw
  have hterm : ∀ j ∈ J, ρ * r j / d j ^ 2 ≤ w (φ j) := by
    intro j hj
    obtain ⟨ha1, ha2⟩ := hsa j hj
    obtain ⟨hb1, -⟩ := hsb j hj
    have hpos : 0 < (2 : ℝ) ^ (φ j).2 * (M * ρ) := by positivity
    have hdpos : 0 < d j := hpos.trans_le hb1
    calc ρ * r j / d j ^ 2 ≤ ρ * (2 ^ ((φ j).1 + 1) * ρ) / ((2 : ℝ) ^ (φ j).2 * (M * ρ)) ^ 2 := by
          refine div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha2.le hρ.le)
            (by positivity) (pow_le_pow_left₀ hpos.le hb1 2)
      _ = w (φ j) := by
          simp only [hw]
          rw [pow_succ]
          field_simp
  -- the endpoints of the dipoles
  have hpt : ∀ j, ∃ z, (z = (c j).1 ∨ z = (c j).2) ∧ ‖z - (c i).1‖ ≤ d j + ρ :=
    fun j => exists_endpoint_near (c i) (c j)
  choose z hzend hznear using hpt
  set g : ℕ × ℕ → ℝ := fun q => 6 * p * (16 / M ^ 2 * (1 / 2) ^ q.1 +
    4 / M ^ 4 * (1 / 2) ^ q.1 * (1 / 4) ^ q.2 + 1 / M ^ 2 * 2 ^ q.1 * (1 / 4) ^ q.2) with hg
  -- the bound of one class
  have hclass : ∀ q ∈ J.image φ, ((J.filter fun j => φ j = q).card : ℝ) * w q ≤ g q := by
    intro q _
    set F := J.filter fun j => φ j = q with hF
    have hpack := card_mul_sq_le_of_separated_blocks hX hp (J := F)
      ((filter_subset _ _).trans hJ) z (c i).1 (ρ := 2 * 2 ^ q.2 * M * ρ + ρ)
      (δ := M * 2 ^ q.1 * ρ) (by positivity) (fun j hj => ?_) fun j hj k hk hjk => ?_
    · have h := fiber_alg (N := (F.card : ℝ)) (P := p) (Nat.cast_nonneg _) hM hρ
        (one_le_pow₀ one_le_two : (1 : ℝ) ≤ 2 ^ q.1) (one_le_pow₀ one_le_two : (1 : ℝ) ≤ 2 ^ q.2)
        (by simpa [mul_comm, mul_assoc, mul_left_comm] using hpack)
      calc (F.card : ℝ) * w q = (F.card : ℝ) * (2 * 2 ^ q.1 / (M ^ 2 * (2 ^ q.2) ^ 2)) := rfl
        _ ≤ _ := h
        _ = g q := by
            simp only [hg]
            rw [one_div_pow, one_div_pow, show ((4 : ℝ) ^ q.2) = (2 ^ q.2) ^ 2 by
              rw [← pow_mul, mul_comm, pow_mul]; norm_num]
            field_simp
    · rw [mem_filter] at hj
      obtain ⟨-, hb2⟩ := hsb j hj.1
      rw [hj.2] at hb2
      calc ‖z j - (c i).1‖ ≤ d j + ρ := hznear j
        _ ≤ 2 * 2 ^ q.2 * M * ρ + ρ := by
            have : d j ≤ 2 ^ (q.2 + 1) * (M * ρ) := hb2.le
            rw [pow_succ] at this
            linarith
    · rw [mem_filter] at hj hk
      have hlt := mul_min_lt_dipoleDist hM0.le (hD j (hJ hj.1) k (hJ hk.1) hjk)
      have hdist := dipoleDist_le_norm_of_endpoints (hzend j) (hzend k)
      obtain ⟨ha1, -⟩ := hsa j hj.1
      obtain ⟨ka1, -⟩ := hsa k hk.1
      rw [hj.2] at ha1
      rw [hk.2] at ka1
      have hmin : 2 ^ q.1 * ρ ≤ min (r j) (r k) := le_min ha1 ka1
      calc M * 2 ^ q.1 * ρ = M * (2 ^ q.1 * ρ) := by ring
        _ ≤ M * min (r j) (r k) := mul_le_mul_of_nonneg_left hmin hM0.le
        _ ≤ dipoleDist (c j) (c k) := hlt.le
        _ ≤ ‖z j - z k‖ := hdist
  -- the classes `(a, b)` that occur
  have hT : ∀ q ∈ J.image φ, q.2 ≤ B ∧ (2 : ℝ) ^ q.1 < 2 ^ (q.2 + 1) * M := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hq
    obtain ⟨ha1, -⟩ := hsa j hj
    obtain ⟨hb1, hb2⟩ := hsb j hj
    obtain ⟨-, hrd, -, hdR⟩ := hJ' j hj
    refine ⟨?_, ?_⟩
    · have hle : (2 : ℝ) ^ (φ j).2 ≤ R' / ρ := by
        rw [le_div_iff₀ hρ]
        calc (2 : ℝ) ^ (φ j).2 * ρ ≤ 2 ^ (φ j).2 * (M * ρ) :=
              mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hρ.le hM) (by positivity)
          _ ≤ d j := hb1
          _ ≤ R' := hdR
      have hR'ρ : 0 < R' / ρ := lt_of_lt_of_le (by positivity) hle
      refine Nat.le_floor ?_
      rw [Real.le_logb_iff_rpow_le one_lt_two hR'ρ, Real.rpow_natCast]
      exact hle
    · have : (2 : ℝ) ^ (φ j).1 * ρ < 2 ^ ((φ j).2 + 1) * M * ρ := by
        calc (2 : ℝ) ^ (φ j).1 * ρ ≤ r j := ha1
          _ < d j := hrd
          _ < 2 ^ ((φ j).2 + 1) * (M * ρ) := hb2
          _ = 2 ^ ((φ j).2 + 1) * M * ρ := by ring
      exact lt_of_mul_lt_mul_right this hρ.le
  -- summing the classes
  have hsumT : ∑ q ∈ J.image φ, g q ≤
      6 * p * (32 * (B + 1) / M ^ 2 + 16 / M ^ 4 + 8 / M) := by
    rw [sum_eq_sum_fiberwise_snd]
    have hinner : ∀ b ∈ (J.image φ).image Prod.snd,
        ∑ a ∈ ((J.image φ).filter fun q => q.2 = b).image Prod.fst, g (a, b) ≤
          6 * p * (32 / M ^ 2 + 8 / M ^ 4 * (1 / 4) ^ b + 4 / M * (1 / 2) ^ b) := by
      intro b _
      set Ab := ((J.image φ).filter fun q => q.2 = b).image Prod.fst with hAb
      have hAb_lt : ∀ a ∈ Ab, (2 : ℝ) ^ a < 2 ^ (b + 1) * M := by
        intro a ha
        obtain ⟨q, hq, rfl⟩ := mem_image.1 ha
        rw [mem_filter] at hq
        have := (hT q hq.1).2
        rwa [hq.2] at this
      have s1 := sum_inv_pow_le Ab (q := 2) one_lt_two
      have s2 := sum_two_pow_le_of_lt Ab (Y := 2 ^ (b + 1) * M) (by positivity) hAb_lt
      norm_num at s1
      simp only [hg]
      rw [← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_mul, ← mul_sum,
        ← sum_mul, ← mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hq4 : (0 : ℝ) ≤ (1 / 4) ^ b := by positivity
      have h24 : (2 : ℝ) ^ (b + 1) * (1 / 4) ^ b = 2 * (1 / 2) ^ b := by
        rw [pow_succ, mul_comm (2 ^ b) 2, mul_assoc, ← mul_pow]
        norm_num
      have e1 : 16 / M ^ 2 * ∑ a ∈ Ab, (1 / 2 : ℝ) ^ a ≤ 32 / M ^ 2 := by
        calc 16 / M ^ 2 * ∑ a ∈ Ab, (1 / 2 : ℝ) ^ a ≤ 16 / M ^ 2 * 2 :=
              mul_le_mul_of_nonneg_left (by simpa using s1) (by positivity)
          _ = 32 / M ^ 2 := by ring
      have e2 : 4 / M ^ 4 * (∑ a ∈ Ab, (1 / 2 : ℝ) ^ a) * (1 / 4) ^ b ≤
          8 / M ^ 4 * (1 / 4) ^ b := by
        calc 4 / M ^ 4 * (∑ a ∈ Ab, (1 / 2 : ℝ) ^ a) * (1 / 4) ^ b
            ≤ 4 / M ^ 4 * 2 * (1 / 4) ^ b :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (by simpa using s1) (by positivity)) hq4
          _ = 8 / M ^ 4 * (1 / 4) ^ b := by ring
      have e3 : 1 / M ^ 2 * (∑ a ∈ Ab, (2 : ℝ) ^ a) * (1 / 4) ^ b ≤ 4 / M * (1 / 2) ^ b := by
        calc 1 / M ^ 2 * (∑ a ∈ Ab, (2 : ℝ) ^ a) * (1 / 4) ^ b
            ≤ 1 / M ^ 2 * (2 * (2 ^ (b + 1) * M)) * (1 / 4) ^ b := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left s2 (by positivity)) hq4
          _ = 2 / M * ((2 : ℝ) ^ (b + 1) * (1 / 4) ^ b) := by
              field_simp
          _ = 4 / M * (1 / 2) ^ b := by
              rw [h24]
              ring
      linarith
    have hcardB : (((J.image φ).image Prod.snd).card : ℝ) ≤ B + 1 := by
      have : (J.image φ).image Prod.snd ⊆ range (B + 1) := fun b hb => by
        obtain ⟨q, hq, rfl⟩ := mem_image.1 hb
        exact mem_range.2 (Nat.lt_succ_of_le (hT q hq).1)
      have := card_le_card this
      rw [card_range] at this
      exact_mod_cast this
    have t1 := sum_inv_pow_le ((J.image φ).image Prod.snd) (q := 4) (by norm_num)
    have t2 := sum_inv_pow_le ((J.image φ).image Prod.snd) (q := 2) one_lt_two
    norm_num at t1 t2
    refine (sum_le_sum hinner).trans ?_
    rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
      ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have f1 : ((((J.image φ).image Prod.snd).card : ℝ)) * (32 / M ^ 2) ≤
        (B + 1) * (32 / M ^ 2) := mul_le_mul_of_nonneg_right hcardB (by positivity)
    have f2 : 8 / M ^ 4 * ∑ b ∈ (J.image φ).image Prod.snd, (1 / 4 : ℝ) ^ b ≤ 8 / M ^ 4 * 2 :=
      mul_le_mul_of_nonneg_left (by simpa using t1.trans (by norm_num)) (by positivity)
    have f3 : 4 / M * ∑ b ∈ (J.image φ).image Prod.snd, (1 / 2 : ℝ) ^ b ≤ 4 / M * 2 :=
      mul_le_mul_of_nonneg_left (by simpa using t2) (by positivity)
    calc _ ≤ (B + 1) * (32 / M ^ 2) + 8 / M ^ 4 * 2 + 4 / M * 2 :=
          add_le_add (add_le_add f1 f2) f3
      _ = 32 * (B + 1) / M ^ 2 + 16 / M ^ 4 + 8 / M := by ring
  calc ∑ j ∈ J, ρ * r j / d j ^ 2 ≤ ∑ j ∈ J, w (φ j) := sum_le_sum hterm
    _ = ∑ q ∈ J.image φ, (J.filter fun j => φ j = q).card • w q := sum_comp w φ
    _ ≤ ∑ q ∈ J.image φ, g q := by
        refine sum_le_sum fun q hq => ?_
        rw [nsmul_eq_mul]
        exact hclass q hq
    _ ≤ _ := hsumT

end Far

/-! ### Eq. (4.104) -/

section Claim

/-- The exact form of `a^abs_ij` on `𝓑_ij^c ∩ {d_ij ≤ 17 ε₀ R}`. -/
theorem absOddWeight_eq {M lam ε₀ R : ℝ} {d e : ℂ × ℂ} (hl : ¬ MultipoleLinked M lam d e)
    (hd : dipoleDist d e ≤ 17 * ε₀ * R) :
    absOddWeight M lam ε₀ R d e = ‖d.1 - d.2‖ * ‖e.1 - e.2‖ /
      (dipoleDist d e * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) := by
  classical
  unfold Parity.absOddWeight
  rw [ite_eq_right hl, ite_eq_left hd, mul_one, mul_one]

open scoped Classical in
/-- **Eq. (4.104)** (Lemma 4.56, first claim, Lemma 4.56):
there is `C > 0` depending only on `p` such that for `M > 20`, every subpartition `X` with blocks of
at most `p` labels and every configuration in the event
`𝒟 = ⋂_{i ∈ V_X} {0 < r_i ≤ ε₀ R̄} ∩ ⋂_{ij ∈ ℰ^inter(X)} 𝓑_ij^c`, for every `i ∈ V_X`,
`∑_{j : ij ∈ ℰ^inter(X)} a^abs_ij 𝟙_{r_j ≥ r_i} ≤ (C/M) (log(17 ε₀ R̄ / r_i) + 1)`, with `R` in the
role of `R̄_{β,λ}`. Here `C = p (192 / log 2 + 338) + 1`. -/
theorem claim_int (p : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ {M : ℝ}, 20 < M → ∀ (lam ε₀ R : ℝ)
    {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ p) → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
        ¬ MultipoleLinked M lam (c i) (c j)) →
      ∀ i ∈ X.biUnion id,
        ∑ j ∈ (X.biUnion id).filter (fun j => ¬ SameBlock X i j),
            absOddWeight M lam ε₀ R (c i) (c j) *
              (if ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ then 1 else 0) ≤
          C / M * (Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1) := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨p * (192 / Real.log 2 + 338) + 1, by positivity,
    fun {M} hM lam ε₀ R X hX hp c hr hD i hi => ?_⟩
  have hM1 : 1 ≤ M := by linarith
  have hM5 : 5 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  set ρ := ‖(c i).1 - (c i).2‖ with hρdef
  obtain ⟨hρ, hρR⟩ := hr i hi
  set R' := 17 * ε₀ * R with hR'
  have hR'ρ : 17 * ρ ≤ R' := by rw [hR']; linarith
  set J := (X.biUnion id).filter fun j => ¬ SameBlock X i j with hJ
  have hJV : J ⊆ X.biUnion id := filter_subset _ _
  set f : ℕ → ℝ := fun j => absOddWeight M lam ε₀ R (c i) (c j) *
    (if ρ ≤ ‖(c j).1 - (c j).2‖ then 1 else 0) with hf
  -- the properties of the terms that do not vanish
  have hprop : ∀ j ∈ J, f j ≠ 0 → ρ ≤ ‖(c j).1 - (c j).2‖ ∧
      ¬ MultipoleLinked M lam (c i) (c j) ∧ dipoleDist (c i) (c j) ≤ R' := by
    intro j hj hfj
    have hρj : ρ ≤ ‖(c j).1 - (c j).2‖ := by
      by_contra h
      exact hfj (by simp only [hf]; rw [ite_eq_right h, mul_zero])
    have hjV := hJV hj
    have hl := hD i hi j hjV (mem_filter.1 hj).2
    refine ⟨hρj, hl, ?_⟩
    by_contra h
    refine hfj ?_
    simp only [hf, Parity.absOddWeight]
    rw [ite_eq_right hl, ite_eq_right h]
    ring
  have hMρ : ∀ j ∈ J, f j ≠ 0 → M * ρ ≤ dipoleDist (c i) (c j) := by
    intro j hj hfj
    obtain ⟨hρj, hl, -⟩ := hprop j hj hfj
    have := mul_min_lt_dipoleDist hM0.le hl
    rw [min_eq_left hρj] at this
    exact this.le
  -- split according to `d_ij ≤ r_j`
  rw [← sum_filter_add_sum_filter_not J fun j => dipoleDist (c i) (c j) ≤ ‖(c j).1 - (c j).2‖]
  set J₂ := (J.filter fun j => dipoleDist (c i) (c j) ≤ ‖(c j).1 - (c j).2‖).filter
    fun j => f j ≠ 0 with hJ₂
  set J₁ := (J.filter fun j => ¬ dipoleDist (c i) (c j) ≤ ‖(c j).1 - (c j).2‖).filter
    fun j => f j ≠ 0 with hJ₁
  rw [← sum_filter_ne_zero, ← sum_filter_ne_zero (s := J.filter fun j => ¬ _)]
  change ∑ j ∈ J₂, f j + ∑ j ∈ J₁, f j ≤ _
  -- the close range
  have hclose : ∑ j ∈ J₂, f j ≤ 2 * p / M := by
    have hJ₂V : J₂ ⊆ X.biUnion id := fun j hj => hJV (mem_filter.1 (mem_filter.1 hj).1).1
    have hmem : ∀ j ∈ J₂, j ∈ J ∧ dipoleDist (c i) (c j) ≤ ‖(c j).1 - (c j).2‖ ∧ f j ≠ 0 :=
      fun j hj => ⟨(mem_filter.1 (mem_filter.1 hj).1).1, (mem_filter.1 (mem_filter.1 hj).1).2,
        (mem_filter.1 hj).2⟩
    refine (sum_le_sum fun j hj => ?_).trans (sum_close_le hX hp hM5 hD hρ hJ₂V
      fun j hj => ⟨(hmem j hj).2.1, hMρ j (hmem j hj).1 (hmem j hj).2.2⟩)
    obtain ⟨hjJ, hdr, hfj⟩ := hmem j hj
    obtain ⟨hρj, hl, hdR⟩ := hprop j hjJ hfj
    have hdpos : 0 < dipoleDist (c i) (c j) :=
      lt_of_lt_of_le (mul_pos hM0 hρ) (hMρ j hjJ hfj)
    have hrpos : 0 < ‖(c j).1 - (c j).2‖ := hdpos.trans_le hdr
    simp only [hf]
    rw [ite_eq_left hρj, mul_one, absOddWeight_eq hl hdR, max_eq_right hρj, max_eq_right hdr]
    exact le_of_eq (by field_simp)
  -- the far range
  have hfar : ∑ j ∈ J₁, f j ≤ 6 * p * (32 * (⌊Real.logb 2 (R' / ρ)⌋₊ + 1) / M ^ 2 +
      16 / M ^ 4 + 8 / M) := by
    have hJ₁V : J₁ ⊆ X.biUnion id := fun j hj => hJV (mem_filter.1 (mem_filter.1 hj).1).1
    have hmem : ∀ j ∈ J₁, j ∈ J ∧ ¬ dipoleDist (c i) (c j) ≤ ‖(c j).1 - (c j).2‖ ∧ f j ≠ 0 :=
      fun j hj => ⟨(mem_filter.1 (mem_filter.1 hj).1).1, (mem_filter.1 (mem_filter.1 hj).1).2,
        (mem_filter.1 hj).2⟩
    refine (sum_le_sum fun j hj => ?_).trans (sum_far_le hX hp hM1 hD hρ hJ₁V fun j hj =>
      ⟨(hprop j (hmem j hj).1 (hmem j hj).2.2).1, not_le.1 (hmem j hj).2.1,
        hMρ j (hmem j hj).1 (hmem j hj).2.2, (hprop j (hmem j hj).1 (hmem j hj).2.2).2.2⟩)
    obtain ⟨hjJ, hdr, hfj⟩ := hmem j hj
    obtain ⟨hρj, hl, hdR⟩ := hprop j hjJ hfj
    have hrd : ‖(c j).1 - (c j).2‖ < dipoleDist (c i) (c j) := not_le.1 hdr
    simp only [hf]
    rw [ite_eq_left hρj, mul_one, absOddWeight_eq hl hdR,
      max_eq_left (max_le (hρj.trans hrd.le) hrd.le), sq]
  -- the constants
  have hRρ : 1 ≤ R' / ρ := by rw [le_div_iff₀ hρ]; linarith
  have hL0 : 0 ≤ Real.log (R' / ρ) := Real.log_nonneg hRρ
  have hB : (⌊Real.logb 2 (R' / ρ)⌋₊ : ℝ) ≤ Real.log (R' / ρ) / Real.log 2 :=
    Nat.floor_le (Real.logb_nonneg one_lt_two hRρ)
  set B : ℝ := (⌊Real.logb 2 (R' / ρ)⌋₊ : ℝ) with hBdef
  set L := Real.log (R' / ρ) with hLdef
  have hB0 : 0 ≤ B := Nat.cast_nonneg _
  have hP : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have hM2 : 1 / M ^ 2 ≤ 1 / M := one_div_le_one_div_of_le hM0 (le_self_pow₀ hM1 two_ne_zero)
  have hM4 : 1 / M ^ 4 ≤ 1 / M :=
    one_div_le_one_div_of_le hM0 (le_self_pow₀ hM1 (by norm_num))
  have hsum : ∑ j ∈ J₂, f j + ∑ j ∈ J₁, f j ≤ p * (192 * B + 338) * (1 / M) := by
    have e1 : 32 * (B + 1) / M ^ 2 ≤ 32 * (B + 1) * (1 / M) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hM2 (by positivity)
    have e2 : 16 / M ^ 4 ≤ 16 * (1 / M) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hM4 (by norm_num)
    have e3 : 6 * p * (32 * (B + 1) / M ^ 2 + 16 / M ^ 4 + 8 / M) ≤
        6 * p * (32 * (B + 1) * (1 / M) + 16 * (1 / M) + 8 * (1 / M)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [show (8 : ℝ) / M = 8 * (1 / M) by ring]
      linarith
    have e4 : 2 * p / M = 2 * p * (1 / M) := by ring
    calc ∑ j ∈ J₂, f j + ∑ j ∈ J₁, f j
        ≤ 2 * p / M + 6 * p * (32 * (B + 1) / M ^ 2 + 16 / M ^ 4 + 8 / M) :=
          add_le_add hclose hfar
      _ ≤ 2 * p * (1 / M) + 6 * p * (32 * (B + 1) * (1 / M) + 16 * (1 / M) + 8 * (1 / M)) := by
          rw [e4]
          linarith
      _ = p * (192 * B + 338) * (1 / M) := by ring
  refine hsum.trans ?_
  rw [div_eq_mul_one_div (p * (192 / Real.log 2 + 338) + 1) M]
  have hM' : 0 < 1 / M := by positivity
  have hBL : 192 * B ≤ 192 / Real.log 2 * L := by
    calc 192 * B ≤ 192 * (L / Real.log 2) := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 192 / Real.log 2 * L := by ring
  have hkey : p * (192 * B + 338) ≤ (p * (192 / Real.log 2 + 338) + 1) * (L + 1) := by
    have h1 : p * (192 * B + 338) ≤ p * (192 / Real.log 2 * L + 338) :=
      mul_le_mul_of_nonneg_left (by linarith) hP
    have hc : 0 ≤ 192 / Real.log 2 := by positivity
    nlinarith [mul_nonneg hP (mul_nonneg hc hL0), mul_nonneg hP hL0]
  calc p * (192 * B + 338) * (1 / M) ≤ (p * (192 / Real.log 2 + 338) + 1) * (L + 1) * (1 / M) :=
        mul_le_mul_of_nonneg_right hkey hM'.le
    _ = (p * (192 / Real.log 2 + 338) + 1) * (1 / M) * (L + 1) := by ring

end Claim

end AbsoluteLower

end MultipoleBKT

end
