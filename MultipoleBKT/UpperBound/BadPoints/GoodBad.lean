/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Geometry
public import MultipoleBKT.UpperBound.BadPoints.Packing
public import MultipoleBKT.UpperBound.BadPoints.Decay

/-!
# Control of good–bad interactions (Lemma 5.11)

The paper: Lemma 5.11. Split into the two charge signs. For each nonzero positive
half-interaction use (5.11), the good–bad separation and the equal-radius
translation estimate to obtain (5.28). Represent the reciprocal distances
by continuous shells `t < d⁺ < 2t`, exchange the finite sum and the integral,
then bound the counting function with (5.15). Integrating `t⁻²` gives
(5.31). Exchange positive and negative charges for the other half.

The exported statements retain their stronger versions without matching or
distinct-length assumptions. `sum_abs_halfInteractionPlus_le` is the abstract
packing-integral estimate used by `lemma_5_11` and the frozen-data consumers.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

variable {χ : ℂ → ℝ}

/-- The abstract form of eqs. (5.28)–(5.31): for `τ_i^+ = τ_i^-`, `D ≥ max(r_i, λ)`, a packing
bound `P` for the charges `x_k`, `k ∈ T`, and the support properties of `v'_{i,j,+}`
(`d^+ ≤ 2τ_j^+`, `d^+ ≥ D`, `τ_j^+ > λ` whenever `v'_{i,j,+} ≠ 0`),
`Σ_{j ∈ T} |v'_{i,j,+}| ≤ C P r_i / D` with `C` depending only on `χ`. -/
theorem sum_abs_halfInteractionPlus_le (hχ : IsMollifier χ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ {N : ℕ} (lam : ℝ) (d : Fin N → ℂ × ℂ) (τp τm : Fin N → ℝ) (T : Finset (Fin N)) (i : Fin N)
      (P : ℕ) (D : ℝ), 0 < lam → (∀ k, lam ≤ τp k) → τp i = τm i →
      ‖(d i).1 - (d i).2‖ ≤ D → lam ≤ D →
      (∀ t : ℝ, 0 ≤ t → ∀ z : ℂ,
        (T.filter fun k => ‖(d k).1 - z‖ ≤ 8 * t ∧ t ≤ τp k ∧ lam < τp k).card ≤ P) →
      (∀ j ∈ T, halfInteractionPlus χ lam τp τm d i j ≠ 0 →
        min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ ≤ 2 * τp j ∧
        D ≤ min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ ∧ lam < τp j) →
      ∑ j ∈ T, |halfInteractionPlus χ lam τp τm d i j| ≤
        C * P * (‖(d i).1 - (d i).2‖ / D) := by
  classical
  obtain ⟨Cχ, hCχ, h37⟩ := lemma_3_7_3 hχ
  obtain ⟨Mχ, hMχ⟩ := hχ.exists_bound
  set S := Real.sqrt (Real.pi * Mχ)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨4 * (Cχ + 2 * S), by positivity, ?_⟩
  intro N lam d τp τm T i P D hlam hp heq hrD hlamD hpack hsupp
  have hD : 0 < D := hlam.trans_le hlamD
  set r := ‖(d i).1 - (d i).2‖
  have hr0 : 0 ≤ r := norm_nonneg _
  set v := fun j => halfInteractionPlus χ lam τp τm d i j
  set e := fun j => min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖
  set T' := T.filter fun j => |v j| ≠ 0
  have hsum : ∑ j ∈ T, |v j| = ∑ j ∈ T', |v j| := (Finset.sum_filter_ne_zero _).symm
  have hT' : ∀ j ∈ T', e j ≤ 2 * τp j ∧ D ≤ e j ∧ lam < τp j := fun j hj => by
    obtain ⟨hjT, hj0⟩ := Finset.mem_filter.mp hj
    exact hsupp j hjT (abs_ne_zero.mp hj0)
  -- the bound on each term
  have hterm : ∀ j ∈ T', |v j| ≤ (Cχ + 2 * S) * (r / D) * (D / e j) := by
    intro j hj
    obtain ⟨he2, hDe, hlt⟩ := hT' j hj
    have he0 : 0 < e j := hD.trans_le hDe
    have hτ0 : 0 < τp j := hlam.trans hlt
    have hmax : max (e j) lam = e j := max_eq_left (hlamD.trans hDe)
    have h1 := (h37 lam hlam (d i) (d j)).1 (hrD.trans hDe)
    rw [hmax] at h1
    have h2 := abs_halfInteractionPlus_sub_le_of_eq (lam := lam) hχ hMχ d
      (hlam.trans_le (hp i)) hτ0 heq
    have h3 : S / τp j ≤ 2 * S / e j := by
      rw [div_le_div_iff₀ hτ0 he0]
      nlinarith
    have h4 : S / τp j * r ≤ 2 * S / e j * r := mul_le_mul_of_nonneg_right h3 hr0
    have h5 : |v j| ≤ Cχ * r / e j + 2 * S / e j * r := by
      have := abs_add_le (smearedKernel χ lam ((d i).1 - (d j).1) -
        smearedKernel χ lam ((d i).2 - (d j).1)) (v j - (smearedKernel χ lam ((d i).1 - (d j).1) -
          smearedKernel χ lam ((d i).2 - (d j).1)))
      rw [add_sub_cancel] at this
      linarith
    calc |v j| ≤ Cχ * r / e j + 2 * S / e j * r := h5
      _ = (Cχ + 2 * S) * (r / D) * (D / e j) := by field_simp
  -- (5.30): exchange the finite sum and the continuous scale integral
  have hdy := sum_div_le_of_continuous_count T' e hD (fun j hj => (hT' j hj).2.1) (2 * P)
    fun t ht => card_continuous_shell_le (T := T') (τp := τp) (f := e)
      (fun s hs z => (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.filter_subset _ _))).trans (hpack s hs z))
      (fun j hj => ⟨le_rfl, (hT' j hj).1, (hT' j hj).2.2⟩) ht
  have hrD0 : 0 ≤ r / D := div_nonneg hr0 hD.le
  have hCS : 0 ≤ Cχ + 2 * S := by positivity
  rw [hsum]
  calc ∑ j ∈ T', |v j| ≤ ∑ j ∈ T', (Cχ + 2 * S) * (r / D) * (D / e j) := Finset.sum_le_sum hterm
    _ = (Cχ + 2 * S) * (r / D) * ∑ j ∈ T', D / e j := by rw [Finset.mul_sum]
    _ ≤ (Cχ + 2 * S) * (r / D) * (2 * ((2 * P : ℕ) : ℝ)) := by gcongr
    _ = 4 * (Cχ + 2 * S) * P * (r / D) := by push_cast; ring

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {N : ℕ} {d : Fin N → ℂ × ℂ}

/-- For good `i`, bad `j` and `v^Z_{i,j,+} ≠ 0`: the support properties used in Lemma 5.11. -/
theorem support_plus_of_good_of_bad (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i j : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hj : j ∈ badPoints p₀ β lam M ε₀ d)
    (hv : interactionPlusZ χ p₀ β lam M ε₀ d i j ≠ 0) :
    min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ ≤ 2 * radiusPlusZ p₀ β lam M ε₀ d j ∧
      badDist p₀ β lam M ε₀ d i ≤ min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ ∧
      lam < radiusPlusZ p₀ β lam M ε₀ d j := by
  have h3 := (lemma_5_9_3 hχ hlam hM hi hj hv).1
  have hDe : dipoleDist (d i) (d j) ≤ min ‖(d i).1 - (d j).1‖ ‖(d i).2 - (d j).1‖ :=
    dipoleDist_le_min_fst _ _
  refine ⟨h3, (badDist_le_dipoleDist i hj).trans hDe, ?_⟩
  have hM3 := three_le_M_of_good hM hi
  have hsep := lt_dipoleDist_of_good_of_bad (zero_le_three.trans hM3) hi hj
  have hmin : lam ≤ min (max ‖(d i).1 - (d i).2‖ lam) (max ‖(d j).1 - (d j).2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  have : 3 * lam ≤ M * min (max ‖(d i).1 - (d i).2‖ lam) (max ‖(d j).1 - (d j).2‖ lam) :=
    mul_le_mul hM3 hmin hlam.le (zero_le_three.trans hM3)
  linarith

/-- For good `i`, bad `j` and `v^Z_{i,j,-} ≠ 0`: the support properties used in Lemma 5.11. -/
theorem support_minus_of_good_of_bad (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {i j : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hj : j ∈ badPoints p₀ β lam M ε₀ d)
    (hv : interactionMinusZ χ p₀ β lam M ε₀ d i j ≠ 0) :
    min ‖(d i).1 - (d j).2‖ ‖(d i).2 - (d j).2‖ ≤ 2 * radiusMinusZ p₀ β lam M ε₀ d j ∧
      badDist p₀ β lam M ε₀ d i ≤ min ‖(d i).1 - (d j).2‖ ‖(d i).2 - (d j).2‖ ∧
      lam < radiusMinusZ p₀ β lam M ε₀ d j := by
  have h3 := (lemma_5_9_4 hχ hlam hM hi hj hv).1
  have hDe : dipoleDist (d i) (d j) ≤ min ‖(d i).1 - (d j).2‖ ‖(d i).2 - (d j).2‖ :=
    dipoleDist_le_min_snd _ _
  refine ⟨h3, (badDist_le_dipoleDist i hj).trans hDe, ?_⟩
  have hM3 := three_le_M_of_good hM hi
  have hsep := lt_dipoleDist_of_good_of_bad (zero_le_three.trans hM3) hi hj
  have hmin : lam ≤ min (max ‖(d i).1 - (d i).2‖ lam) (max ‖(d j).1 - (d j).2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  have : 3 * lam ≤ M * min (max ‖(d i).1 - (d i).2‖ lam) (max ‖(d j).1 - (d j).2‖ lam) :=
    mul_le_mul hM3 hmin hlam.le (zero_le_three.trans hM3)
  linarith

/-- **Lemma 5.11** (Lemma 5.11, (5.26)): there is `C > 0`
depending only on `χ` and `q(β)` such that for every dipole configuration `d`, `0 < λ ≤ ε₀ R̄`,
`M ≥ 3^{p(β)}` and every good `i`, `Σ_{j ∈ I_bad} |v^Z_ij| ≤ C r_i / d_{i,bad}`. -/
theorem lemma_5_11 (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} (lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ i ∈ goodPoints p₀ β lam M ε₀ d,
        ∑ j ∈ badPoints p₀ β lam M ε₀ d, |interactionZ χ p₀ β lam M ε₀ d i j| ≤
          C * ‖(d i).1 - (d i).2‖ / badDist p₀ β lam M ε₀ d i := by
  obtain ⟨C₀, hC₀, habs⟩ := sum_abs_halfInteractionPlus_le hχ
  set P := packingConstant (clusterThreshold p₀ β) 8
  refine ⟨2 * C₀ * P + 1, by positivity, ?_⟩
  intro N lam M ε₀ d hlam hlamh hM i hi
  set B := badPoints p₀ β lam M ε₀ d
  set D := badDist p₀ β lam M ε₀ d i
  set τp := radiusPlusZ p₀ β lam M ε₀ d
  set τm := radiusMinusZ p₀ β lam M ε₀ d
  have hrD := norm_le_badDist hlam hlamh hM hi
  have hlamD := lam_le_badDist hlam hlamh hM hi
  have hD : 0 < D := hlam.trans_le hlamD
  -- the `+` part
  have hplus : ∑ j ∈ B, |interactionPlusZ χ p₀ β lam M ε₀ d i j| ≤
      C₀ * P * (‖(d i).1 - (d i).2‖ / D) :=
    habs lam d τp τm B i P D hlam lam_le_radiusPlusZ (radiusMinusZ_eq_radiusPlusZ hi).symm hrD
      hlamD (fun t ht z => lemma_5_9_7_plus hlam ht 8 z)
      fun j hj hv => support_plus_of_good_of_bad hχ hlam hM hi hj hv
  -- the `-` part, through the exchanged configuration
  have hminus : ∑ j ∈ B, |interactionMinusZ χ p₀ β lam M ε₀ d i j| ≤
      C₀ * P * (‖(d i).1 - (d i).2‖ / D) := by
    have hswap : ∀ j, |interactionMinusZ χ p₀ β lam M ε₀ d i j| =
        |halfInteractionPlus χ lam τm τp (swapConfig d) i j| := fun j => by
      rw [interactionMinusZ, halfInteractionMinus_eq_neg_swap, abs_neg]
    simp only [hswap]
    have h := habs lam (swapConfig d) τm τp B i P D hlam lam_le_radiusMinusZ
      (radiusMinusZ_eq_radiusPlusZ hi) (by rw [norm_swapConfig]; exact hrD) hlamD
      (fun t ht z => lemma_5_9_7_minus hlam ht 8 z) fun j hj hv => by
        have hv' : interactionMinusZ χ p₀ β lam M ε₀ d i j ≠ 0 := by
          rw [interactionMinusZ, halfInteractionMinus_eq_neg_swap]
          exact neg_ne_zero.mpr hv
        obtain ⟨h1, h2, h3⟩ := support_minus_of_good_of_bad hχ hlam hM hi hj hv'
        simp only [swapConfig]
        rw [min_comm]
        exact ⟨h1, h2, h3⟩
    rwa [norm_swapConfig] at h
  have hsplit : ∑ j ∈ B, |interactionZ χ p₀ β lam M ε₀ d i j| ≤
      ∑ j ∈ B, |interactionPlusZ χ p₀ β lam M ε₀ d i j| +
        ∑ j ∈ B, |interactionMinusZ χ p₀ β lam M ε₀ d i j| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => abs_sub _ _
  have hr : 0 ≤ ‖(d i).1 - (d i).2‖ / D := div_nonneg (norm_nonneg _) hD.le
  rw [mul_div_assoc]
  nlinarith

end UpperBound

end MultipoleBKT

end
