/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Radii

/-!
# Packing of bad charges with large radii (Lemma 5.9 (7))

The paper: Lemma 5.9 (7), eqs. (5.15), (5.16) (proof of Lemma 5.9). For a bad point `i` the radius `τ_i^{+,Z} = max(τ_i^{+,raw}, λ)` is built from the
removal value of `x_i` in the `q(β)`-clustering of the positive charges (Definition 5.1).

* `card_le_of_pairwise_le`: the core: a set of bad points whose charges `x_i` are
  pairwise within distance `t` and whose radii satisfy `τ_i^{+,Z} ≥ t`, `τ_i^{+,Z} > λ` has at
  most `q(β)` elements. If it had `q(β) + 1`, the point `i₀` of smallest radius `τ` would, at
  the scale `s = (τ + λ)/2 < τ`, see `q(β)` balls still present and meeting `B(x_{i₀}, s)`
  (`|x_{i₀} - x_j| ≤ t ≤ τ < 2s`), which the clustering excludes before the removal of `i₀`
  (`card_lt_of_lt_clusterRemovalValue`,
  with the bound `q(β)` in place of the paper's `q(β) + 1`).
* `card_filter_clusterRadius_le`: the bound for the radii of any `q`-clustering on any set of
  labels (used in the frozen-configuration convention of §5.3).
* `lemma_5_9_7_plus`, `lemma_5_9_7_minus`: eqs. (5.15), (5.16): for every `A`, `t ≥ 0` and `z`,
  `|{i ∈ I_bad : x_i ∈ B(z, A t), τ_i^{+,Z} ≥ t, τ_i^{+,Z} > λ}| ≤ q(β) (2⌈2A⌉ + 1)²`
  (`packingConstant`), and the same for `y_i` and `τ^{-,Z}`. The ball `B(z, A t)` is covered by
  the `(2⌈2A⌉ + 1)²` squares of side `t/2` of a grid centred at `z` (closed ball; the paper's
  covering reduction, which also covers `t = 0`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- The packing constant `q (2⌈2A⌉ + 1)²` of eqs. (5.15)–(5.16). -/
noncomputable def packingConstant (q : ℕ) (A : ℝ) : ℕ :=
  q * (2 * ⌈2 * A⌉₊ + 1) ^ 2

/-! ### The core: one ball of diameter `t` -/

/-- The core of eq. (5.15) for a general charge vector: if `0 < λ`, every member of `S` has
`max(removal value, λ) ≥ t` and `> λ`, and the charges of `S` are pairwise within distance `t`,
then `|S| ≤ q`. -/
theorem card_le_of_pairwise_le_aux {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ} (hlam : 0 < lam)
    {t : ℝ} (S : Finset (Fin N))
    (hS : ∀ a ∈ S, t ≤ max (clusterRemovalValue q h z r a) lam ∧
      lam < max (clusterRemovalValue q h z r a) lam)
    (hdist : ∀ a ∈ S, ∀ b ∈ S, ‖z a - z b‖ ≤ t) : S.card ≤ q := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set ρ : Fin N → ℝ := fun a => max (clusterRemovalValue q h z r a) lam
  obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image ρ hne
  have hρ : ∀ a ∈ S, ρ a = clusterRemovalValue q h z r a := fun a ha => by
    have := (hS a ha).2
    simp only [ρ] at this ⊢
    rcases le_total lam (clusterRemovalValue q h z r a) with h1 | h1
    · exact max_eq_left h1
    · rw [max_eq_right h1] at this
      exact absurd this (lt_irrefl _)
  set τ := ρ i₀
  set s := (τ + lam) / 2
  have hτlam : lam < τ := (hS i₀ hi₀).2
  have hs0 : 0 ≤ s := by simp only [s]; linarith
  have hsτ : s < clusterRemovalValue q h z r i₀ := by
    rw [← hρ i₀ hi₀]
    simp only [s]
    linarith
  have hcard := card_lt_of_lt_clusterRemovalValue hs0 hsτ
  have hsub : S.erase i₀ ⊆ Finset.univ.filter fun j => j ≠ i₀ ∧ ‖z i₀ - z j‖ ≤ 2 * s ∧
      s < clusterRemovalValue q h z r j := by
    intro j hj
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, ?_, ?_⟩
    · have h1 := hdist i₀ hi₀ j hjS
      have h2 := (hS i₀ hi₀).1
      simp only [s]
      linarith
    · rw [← hρ j hjS]
      have h1 := hmin j hjS
      simp only [s]
      linarith
  have h2 := (Finset.card_le_card hsub).trans_lt hcard
  rw [Finset.card_erase_of_mem hi₀] at h2
  omega

/-- **The core of eq. (5.15)**: if `0 < λ`, `S ⊆ I_bad`, the charges `x_i`,
`i ∈ S`, are pairwise within distance `t`, and `τ_i^{+,Z} ≥ t`, `τ_i^{+,Z} > λ` for `i ∈ S`, then
`|S| ≤ q(β)`. -/
theorem card_le_of_pairwise_le_plus (hlam : 0 < lam) {t : ℝ} (S : Finset (Fin N))
    (hSbad : S ⊆ badPoints p₀ β lam M ε₀ d)
    (hS : ∀ a ∈ S, t ≤ radiusPlusZ p₀ β lam M ε₀ d a ∧ lam < radiusPlusZ p₀ β lam M ε₀ d a)
    (hdist : ∀ a ∈ S, ∀ b ∈ S, ‖(d a).1 - (d b).1‖ ≤ t) : S.card ≤ clusterThreshold p₀ β :=
  card_le_of_pairwise_le_aux (z := fun k => (d k).1) hlam S
    (fun a ha => by rw [← radiusPlusZ_of_bad (hSbad ha)]; exact hS a ha) hdist

/-- **The core of eq. (5.16)**: the same for the negative charges `y_i` and `τ^{-,Z}`. -/
theorem card_le_of_pairwise_le_minus (hlam : 0 < lam) {t : ℝ} (S : Finset (Fin N))
    (hSbad : S ⊆ badPoints p₀ β lam M ε₀ d)
    (hS : ∀ a ∈ S, t ≤ radiusMinusZ p₀ β lam M ε₀ d a ∧ lam < radiusMinusZ p₀ β lam M ε₀ d a)
    (hdist : ∀ a ∈ S, ∀ b ∈ S, ‖(d a).2 - (d b).2‖ ≤ t) : S.card ≤ clusterThreshold p₀ β :=
  card_le_of_pairwise_le_aux (z := fun k => (d k).2) hlam S
    (fun a ha => by rw [← radiusMinusZ_of_bad (hSbad ha)]; exact hS a ha) hdist

/-! ### Covering a ball by squares -/

/-- The grid cell of `w` relative to `z`, with squares of side `t/2`. -/
noncomputable def gridCell (z : ℂ) (t : ℝ) (w : ℂ) : ℤ × ℤ :=
  (⌊(w - z).re / (t / 2)⌋, ⌊(w - z).im / (t / 2)⌋)

theorem norm_sub_lt_of_gridCell_eq {z : ℂ} {t : ℝ} (ht : 0 < t) {a b : ℂ}
    (h : gridCell z t a = gridCell z t b) : ‖a - b‖ < t := by
  have ht2 : 0 < t / 2 := by linarith
  simp only [gridCell, Prod.mk.injEq] at h
  have hre := Int.abs_sub_lt_one_of_floor_eq_floor h.1
  have him := Int.abs_sub_lt_one_of_floor_eq_floor h.2
  rw [← sub_div, abs_div, abs_of_pos ht2, div_lt_one ht2] at hre him
  have e1 : (a - z).re - (b - z).re = (a - b).re := by simp
  have e2 : (a - z).im - (b - z).im = (a - b).im := by simp
  rw [e1] at hre
  rw [e2] at him
  calc ‖a - b‖ ≤ |(a - b).re| + |(a - b).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < t / 2 + t / 2 := add_lt_add hre him
    _ = t := by ring

theorem gridCell_mem {z : ℂ} {t A : ℝ} (ht : 0 < t) {w : ℂ} (hw : ‖w - z‖ ≤ A * t) :
    gridCell z t w ∈ (Finset.Icc (-(⌈2 * A⌉₊ : ℤ)) ⌈2 * A⌉₊) ×ˢ
      (Finset.Icc (-(⌈2 * A⌉₊ : ℤ)) ⌈2 * A⌉₊) := by
  have ht2 : 0 < t / 2 := by linarith
  have hK : 2 * A ≤ (⌈2 * A⌉₊ : ℝ) := Nat.le_ceil _
  have hbound : ∀ u : ℝ, |u| ≤ ‖w - z‖ →
      ⌊u / (t / 2)⌋ ∈ Finset.Icc (-(⌈2 * A⌉₊ : ℤ)) ⌈2 * A⌉₊ := by
    intro u hu
    have h1 : |u / (t / 2)| ≤ 2 * A := by
      rw [abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
      linarith
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      push_cast
      linarith [neg_abs_le (u / (t / 2))]
    · have := Int.floor_le (u / (t / 2))
      have h2 : ((⌊u / (t / 2)⌋ : ℤ) : ℝ) ≤ (⌈2 * A⌉₊ : ℝ) := by
        linarith [le_abs_self (u / (t / 2))]
      exact_mod_cast h2
  exact Finset.mem_product.mpr ⟨hbound _ (Complex.abs_re_le_norm _),
    hbound _ (Complex.abs_im_le_norm _)⟩

theorem card_grid (K : ℕ) :
    ((Finset.Icc (-(K : ℤ)) K) ×ˢ (Finset.Icc (-(K : ℤ)) K)).card = (2 * K + 1) ^ 2 := by
  rw [Finset.card_product, Int.card_Icc, sq]
  have : ((K : ℤ) + 1 - -(K : ℤ)).toNat = 2 * K + 1 := by omega
  rw [this]

/-- Covering: a set of points of `B(z, A t)` in which every subset of pairwise distance `≤ t`
has at most `q` elements has at most `q (2⌈2A⌉ + 1)²` elements. -/
theorem card_le_packingConstant {q : ℕ} {t A : ℝ} (ht : 0 ≤ t) {z : ℂ} (x : Fin N → ℂ)
    (T : Finset (Fin N)) (hT : ∀ a ∈ T, ‖x a - z‖ ≤ A * t)
    (hcore : ∀ S ⊆ T, (∀ a ∈ S, ∀ b ∈ S, ‖x a - x b‖ ≤ t) → S.card ≤ q) :
    T.card ≤ packingConstant q A := by
  classical
  rcases ht.eq_or_lt with rfl | ht
  · -- all points equal `z`
    refine (hcore T le_rfl fun a ha b hb => ?_).trans ?_
    · have ha' := hT a ha
      have hb' := hT b hb
      rw [mul_zero, norm_le_zero_iff, sub_eq_zero] at ha' hb'
      rw [ha', hb', sub_self, norm_zero]
    · unfold packingConstant
      exact Nat.le_mul_of_pos_right _ (by positivity)
  · have h := Finset.card_le_mul_card_image_of_maps_to (f := fun a => gridCell z t (x a))
      (t := (Finset.Icc (-(⌈2 * A⌉₊ : ℤ)) ⌈2 * A⌉₊) ×ˢ (Finset.Icc (-(⌈2 * A⌉₊ : ℤ)) ⌈2 * A⌉₊))
      (fun a ha => gridCell_mem ht (hT a ha)) q fun b _ => hcore _ (Finset.filter_subset _ _)
        fun a ha a' ha' => by
          rw [Finset.mem_filter] at ha ha'
          exact (norm_sub_lt_of_gridCell_eq ht (ha.2.trans ha'.2.symm)).le
    rw [card_grid] at h
    exact h

/-! ### Lemma 5.9 (7) -/

/-- **Eq. (5.15) for the radii of any `q`-clustering**, on any set `S` of labels: for `0 < λ`,
every `A`, `t ≥ 0` and `w`, at most `q (2⌈2A⌉ + 1)²` labels `k ∈ S` have `|z_k - w| ≤ A t`,
`τ_k ≥ t` and `τ_k > λ`, where `τ_k = max(λ, removal value)` (`clusterRadius`). This form also
covers the frozen-configuration convention of §5.3, where the radii are computed from
the bad dipoles alone. -/
theorem card_filter_clusterRadius_le {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ}
    (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) (A : ℝ) (w : ℂ) (S : Finset (Fin N)) :
    (S.filter fun k => ‖z k - w‖ ≤ A * t ∧ t ≤ clusterRadius q h lam z r k ∧
      lam < clusterRadius q h lam z r k).card ≤ packingConstant q A := by
  refine card_le_packingConstant ht z _ (fun a ha => (Finset.mem_filter.mp ha).2.1)
    fun S' hS' hdist => card_le_of_pairwise_le_aux (h := h) (r := r) hlam S' (fun a ha => ?_) hdist
  have := (Finset.mem_filter.mp (hS' ha)).2.2
  rw [clusterRadius, max_comm] at this
  exact this

/-- **Lemma 5.9 (7)**, eq. (5.15) (proof): for `0 < λ`, every `A`,
`t ≥ 0` and `z ∈ ℂ`,
`|{i ∈ I_bad : x_i ∈ B(z, A t), τ_i^{+,Z} ≥ t, τ_i^{+,Z} > λ}| ≤ q(β) (2⌈2A⌉ + 1)²`
(a constant depending on `q(β)` and `A` only). -/
theorem lemma_5_9_7_plus (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) (A : ℝ) (z : ℂ) :
    ((badPoints p₀ β lam M ε₀ d).filter fun i => ‖(d i).1 - z‖ ≤ A * t ∧
      t ≤ radiusPlusZ p₀ β lam M ε₀ d i ∧ lam < radiusPlusZ p₀ β lam M ε₀ d i).card ≤
      packingConstant (clusterThreshold p₀ β) A := by
  refine card_le_packingConstant ht (fun k => (d k).1) _
    (fun a ha => (Finset.mem_filter.mp ha).2.1) fun S hS hdist => ?_
  refine card_le_of_pairwise_le_plus hlam S (fun a ha => (Finset.mem_filter.mp (hS ha)).1)
    (fun a ha => (Finset.mem_filter.mp (hS ha)).2.2) hdist

/-- **Lemma 5.9 (7)**, eq. (5.16) (proof): the same for the negative
charges `y_i` and the radii `τ^{-,Z}`. -/
theorem lemma_5_9_7_minus (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) (A : ℝ) (z : ℂ) :
    ((badPoints p₀ β lam M ε₀ d).filter fun i => ‖(d i).2 - z‖ ≤ A * t ∧
      t ≤ radiusMinusZ p₀ β lam M ε₀ d i ∧ lam < radiusMinusZ p₀ β lam M ε₀ d i).card ≤
      packingConstant (clusterThreshold p₀ β) A := by
  refine card_le_packingConstant ht (fun k => (d k).2) _
    (fun a ha => (Finset.mem_filter.mp ha).2.1) fun S hS hdist => ?_
  refine card_le_of_pairwise_le_minus hlam S (fun a ha => (Finset.mem_filter.mp (hS ha)).1)
    (fun a ha => (Finset.mem_filter.mp (hS ha)).2.2) hdist

end UpperBound

end MultipoleBKT

end
