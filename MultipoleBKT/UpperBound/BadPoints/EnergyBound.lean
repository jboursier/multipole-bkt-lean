/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Geometry

/-!
# The energy lower bound with good dipoles and bad radii

The paper: (5.50).
Take `I₁ = I_good ∪ {i ∈ I_bad : r_i/4 < λ}` and the complementary bad set `I₂`.
Check the length condition on `I₁` using Remark 5.10 for good points and the
identities `τ_i^± = λ` for short bad points. Check equal radii on `I₁` and the
reverse length condition on `I₂`, then apply Proposition 3.3.

Split the sums over good and short bad points. Absorb the short bad dipoles
using their quadratic error bounded by `16`, the kernel bound at scale `λ`,
and the `κ` term. This gives `eq_b1`, with `eq_b1'` writing its coefficient
as `L/β`. The external statements also cover parameters outside the paper's
range. Only that additional range uses the stronger `energy_ge_ballGrowth`.
-/

@[expose] public section

open Finset
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

namespace UpperBound

variable {N : ℕ}

/-- `Σ_{i ≠ j} f_ij = 2 Σ_{i<j} f_ij` for a symmetric `f`. -/
theorem sum_ne_eq_two_mul_sum_lt (f : Fin N → Fin N → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j with i ≠ j, f i j = 2 * ∑ i, ∑ j with i < j, f i j := by
  have hsplit : ∀ i, ∑ j with i ≠ j, f i j = ∑ j with i < j, f i j + ∑ j with j < i, f i j := by
    intro i
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      exact ⟨fun h => h.lt_or_gt.imp id id, fun h => h.elim ne_of_lt ne_of_gt⟩
    · rw [Finset.disjoint_filter]
      intro j _ h1 h2
      exact absurd (h1.trans h2) (lt_irrefl _)
  have hswap : ∑ i, ∑ j with j < i, f i j = ∑ i, ∑ j with i < j, f i j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.filter fun i => j < i)]
    · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hf i j
    · intro i j
      simp
  simp only [hsplit, Finset.sum_add_distrib, hswap]
  ring

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- The written `I₁` length condition before Proposition 3.3, the paper. Good dipoles use Remark 5.10.
Short bad dipoles have both radii equal to `λ` and length less than `4λ`. -/
theorem badPoints_I₁_length (hlam : 0 < lam)
    (hscale : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) :
    ∀ i ∈ goodPoints p₀ β lam M ε₀ d ∪
      (badPoints p₀ β lam M ε₀ d).filter (fun i => ‖(d i).1 - (d i).2‖ / 4 < lam),
      ‖(d i).1 - (d i).2‖ ≤
        2 * (radiusPlusZ p₀ β lam M ε₀ d i + radiusMinusZ p₀ β lam M ε₀ d i) := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (remark_5_10_good hlam hscale hM hi).2.2
  · obtain ⟨hib, hr⟩ := Finset.mem_filter.mp hi
    rw [radiusPlusZ_eq_lam_of_bad hib hr, radiusMinusZ_eq_lam_of_bad hib hr]
    linarith

/-- **Eq. (5.50)** : there is `L₀ > 0` depending only on `χ` such that for every
dipole configuration `d` and `0 < λ`,
`F_λ(d) ≥ -Σ_{I_good} g_λ(x_i - y_i) - ½ Σ_{I_bad} (g(τ_i^{+,Z}) + g(τ_i^{-,Z})) + Σ_{i<j} v^Z_ij
  - L₀ Σ_{I_good} (|x_i - y_i| / τ_i^{+,Z})² - L₀ |I_bad|`.
(The paper's `L/β`, with `L` depending on `β` and `χ`, is `L₀`. See `eq_b1'`.) -/
theorem eq_b1 (hχ : IsMollifier χ) : ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (d : Fin N → ℂ × ℂ), 0 < lam →
    -(∑ i ∈ goodPoints p₀ β lam M ε₀ d, smearedKernel χ lam ((d i).1 - (d i).2)) -
        (1 / 2) * ∑ i ∈ badPoints p₀ β lam M ε₀ d,
          (logKernel (radiusPlusZ p₀ β lam M ε₀ d i) + logKernel (radiusMinusZ p₀ β lam M ε₀ d i)) +
        ∑ i, ∑ j with i < j, interactionZ χ p₀ β lam M ε₀ d i j -
        L₀ * ∑ i ∈ goodPoints p₀ β lam M ε₀ d,
          (‖(d i).1 - (d i).2‖ / radiusPlusZ p₀ β lam M ε₀ d i) ^ 2 -
        L₀ * (badPoints p₀ β lam M ε₀ d).card ≤
      energy χ lam d := by
  classical
  obtain ⟨Mχ, hMχ⟩ := hχ.exists_bound
  have hMχ0 : 0 ≤ Mχ := hχ.nonneg_of_le hMχ
  set cχ := ∫ y, logKernel y ∂smearedCharge χ 0 1
  obtain ⟨Cprop, hCprop, hprop⟩ := prop_3_3 hχ
  set C := max (3 * (Real.pi * Mχ)) Cprop
  have hC0 : 0 ≤ C := by positivity
  refine ⟨|cχ| + 16 * C + |kappa χ| + C + 1, by positivity, ?_⟩
  intro N p₀ β lam M ε₀ d hlam
  set G := goodPoints p₀ β lam M ε₀ d
  set B := badPoints p₀ β lam M ε₀ d
  set τp := radiusPlusZ p₀ β lam M ε₀ d
  set τm := radiusMinusZ p₀ β lam M ε₀ d
  set L₀ := |cχ| + 16 * C + |kappa χ| + C + 1
  set B₁ := B.filter fun i => ‖(d i).1 - (d i).2‖ / 4 < lam
  set B₂ := B.filter fun i => ¬ ‖(d i).1 - (d i).2‖ / 4 < lam
  have hGB : Disjoint G B := Finset.disjoint_left.mpr fun i hi => not_mem_badPoints_of_good hi
  have hB : B₁ ∪ B₂ = B := Finset.filter_union_filter_not_eq _ _
  have hB12 : Disjoint B₁ B₂ := Finset.disjoint_filter_filter_not _ _ _
  have hGB₁ : Disjoint G B₁ := hGB.mono_right (Finset.filter_subset _ _)
  have hGB₂ : Disjoint G B₂ := hGB.mono_right (Finset.filter_subset _ _)
  have hdisj : Disjoint (G ∪ B₁) B₂ := Finset.disjoint_union_left.mpr ⟨hGB₂, hB12⟩
  have hunion : (G ∪ B₁) ∪ B₂ = Finset.univ := by
    rw [Finset.union_assoc, hB]
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hi : i ∈ B
    · exact Or.inr hi
    · exact Or.inl (mem_goodPoints_of_not_bad hi)
  have hτB₁ : ∀ i ∈ B₁, τp i = lam ∧ τm i = lam := fun i hi => by
    obtain ⟨hiB, hr⟩ := Finset.mem_filter.mp hi
    exact ⟨radiusPlusZ_eq_lam_of_bad hiB hr, radiusMinusZ_eq_lam_of_bad hiB hr⟩
  have hI₁ : ∀ i ∈ G ∪ B₁, τp i = τm i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (radiusMinusZ_eq_radiusPlusZ hi).symm
    · rw [(hτB₁ i hi).1, (hτB₁ i hi).2]
  have hI₂ : ∀ i ∈ B₂, 2 * (τp i + τm i) ≤ ‖(d i).1 - (d i).2‖ := by
    intro i hi
    obtain ⟨hiB, hr⟩ := Finset.mem_filter.mp hi
    exact two_mul_add_le_of_bad hiB (not_lt.mp hr)
  have hP : -(∑ i ∈ G ∪ B₁, smearedKernel χ lam ((d i).1 - (d i).2)) -
      (1 / 2) * ∑ i ∈ B₂, (logKernel (τp i) + logKernel (τm i) + 2 * kappa χ) +
      (1 / 2) * ∑ i, ∑ j with i ≠ j, ballGrowthInteraction χ lam τp τm d i j -
      C * ∑ i ∈ G ∪ B₁, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 ≤ energy χ lam d := by
    have hs0 : 0 ≤ ∑ i ∈ G ∪ B₁, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    by_cases hsource : stableMatching d = Equiv.refl _ ∧
        lam ≤ ε₀ * truncationScale p₀ β lam ∧ (3 : ℝ) ^ pBeta p₀ β ≤ M
    · -- On the paper's range, check both `I₁` assumptions before Proposition 3.3.
      have hlength := badPoints_I₁_length (d := d) hlam hsource.2.1 hsource.2.2
      have hbound := hprop N lam d τp τm (G ∪ B₁) B₂ hlam hsource.1
        lam_le_radiusPlusZ lam_le_radiusMinusZ hdisj hunion
        (fun i hi => ⟨hlength i hi, hI₁ i hi⟩) hI₂
      have hCC : Cprop ≤ C := le_max_right _ _
      nlinarith
    · -- The external statement also covers parameters outside that range.
      have hbound := energy_ge_ballGrowth hχ hMχ hlam d (τp := τp) (τm := τm)
        lam_le_radiusPlusZ lam_le_radiusMinusZ hdisj hunion hI₁ hI₂
      have hCC : 3 * (Real.pi * Mχ) ≤ C := le_max_left _ _
      nlinarith

  -- the interaction term
  have hv : (1 / 2) * ∑ i, ∑ j with i ≠ j, ballGrowthInteraction χ lam τp τm d i j =
      ∑ i, ∑ j with i < j, interactionZ χ p₀ β lam M ε₀ d i j := by
    rw [sum_ne_eq_two_mul_sum_lt _ (ballGrowthInteraction_comm hχ τp τm d)]
    simp only [interactionZ_eq_ballGrowthInteraction]
    ring
  -- splitting the sums over `I₁ = G ∪ B₁` and `I_bad = B₁ ∪ B₂`
  have hs1 : ∑ i ∈ G ∪ B₁, smearedKernel χ lam ((d i).1 - (d i).2) =
      ∑ i ∈ G, smearedKernel χ lam ((d i).1 - (d i).2) +
        ∑ i ∈ B₁, smearedKernel χ lam ((d i).1 - (d i).2) := Finset.sum_union hGB₁
  have hs2 : ∑ i ∈ G ∪ B₁, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 =
      ∑ i ∈ G, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 +
        ∑ i ∈ B₁, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 := Finset.sum_union hGB₁
  have hs3 : ∑ i ∈ B, (logKernel (τp i) + logKernel (τm i)) =
      ∑ i ∈ B₁, (logKernel (τp i) + logKernel (τm i)) +
        ∑ i ∈ B₂, (logKernel (τp i) + logKernel (τm i)) := by
    rw [← hB, Finset.sum_union hB12]
  have hcard : (B.card : ℝ) = B₁.card + B₂.card := by
    rw [← hB, Finset.card_union_of_disjoint hB12]
    push_cast
    ring
  have hs4 : ∑ i ∈ B₂, (logKernel (τp i) + logKernel (τm i) + 2 * kappa χ) =
      ∑ i ∈ B₂, (logKernel (τp i) + logKernel (τm i)) + 2 * kappa χ * B₂.card := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  -- the absorbed terms: bad points with `r_i / 4 < λ`
  have hB₁bound : ∀ i ∈ B₁, smearedKernel χ lam ((d i).1 - (d i).2) +
      C * (‖(d i).1 - (d i).2‖ / τp i) ^ 2 ≤
        (1 / 2) * (logKernel (τp i) + logKernel (τm i)) + L₀ := by
    intro i hi
    obtain ⟨hp, hm⟩ := hτB₁ i hi
    have hr := (Finset.mem_filter.mp hi).2
    rw [hp, hm]
    have h1 : smearedKernel χ lam ((d i).1 - (d i).2) ≤ logKernel (lam : ℂ) + cχ :=
      smearedKernel_le hχ hlam _
    have h2 : (‖(d i).1 - (d i).2‖ / lam) ^ 2 ≤ 16 := by
      have h0 : 0 ≤ ‖(d i).1 - (d i).2‖ / lam := div_nonneg (norm_nonneg _) hlam.le
      have h4 : ‖(d i).1 - (d i).2‖ / lam ≤ 4 := by
        rw [div_le_iff₀ hlam]
        linarith
      nlinarith
    have h3 : C * (‖(d i).1 - (d i).2‖ / lam) ^ 2 ≤ C * 16 := mul_le_mul_of_nonneg_left h2 hC0
    have h4 : cχ ≤ |cχ| := le_abs_self _
    have h5 : 0 ≤ |kappa χ| := abs_nonneg _
    simp only [L₀]
    linarith
  have hB₁sum : ∑ i ∈ B₁, smearedKernel χ lam ((d i).1 - (d i).2) +
      C * ∑ i ∈ B₁, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 ≤
        (1 / 2) * ∑ i ∈ B₁, (logKernel (τp i) + logKernel (τm i)) + L₀ * B₁.card := by
    have := Finset.sum_le_sum hB₁bound
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.mul_sum] at this
    linarith
  have hG : C * ∑ i ∈ G, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 ≤
      L₀ * ∑ i ∈ G, (‖(d i).1 - (d i).2‖ / τp i) ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have : 0 ≤ |cχ| + 16 * C + |kappa χ| + 1 := by positivity
    simp only [L₀]
    linarith
  have hκ : 2 * kappa χ * B₂.card ≤ 2 * (L₀ * B₂.card) := by
    have h0 : (0 : ℝ) ≤ B₂.card := Nat.cast_nonneg _
    have hk : kappa χ ≤ L₀ := by
      have := le_abs_self (kappa χ)
      have : 0 ≤ |cχ| + 16 * C + C + 1 := by positivity
      simp only [L₀]
      linarith
    nlinarith
  rw [hv, hs1, hs2, hs4] at hP
  rw [hs3, hcard]
  nlinarith

/-- **Eq. (5.50)** in the paper's form (the paper (5.50)): for every `β > 0` there is `L > 0` (here
`L = β L₀`, depending on `β` and `χ`) such that
`F_λ ≥ -Σ_{I_good} g_λ(x_i - y_i) - ½ Σ_{I_bad} (g(τ_i^{+,Z}) + g(τ_i^{-,Z})) + Σ_{i<j} v^Z_ij
  - (L/β) Σ_{I_good} (|x_i - y_i| / τ_i^{+,Z})² - (L/β) |I_bad|`. -/
theorem eq_b1' (hχ : IsMollifier χ) (β : ℝ) (hβ : 0 < β) : ∃ L : ℝ, 0 < L ∧
    ∀ {N : ℕ} (p₀ : ℕ) (lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
    -(∑ i ∈ goodPoints p₀ β lam M ε₀ d, smearedKernel χ lam ((d i).1 - (d i).2)) -
        (1 / 2) * ∑ i ∈ badPoints p₀ β lam M ε₀ d,
          (logKernel (radiusPlusZ p₀ β lam M ε₀ d i) + logKernel (radiusMinusZ p₀ β lam M ε₀ d i)) +
        ∑ i, ∑ j with i < j, interactionZ χ p₀ β lam M ε₀ d i j -
        L / β * ∑ i ∈ goodPoints p₀ β lam M ε₀ d,
          (‖(d i).1 - (d i).2‖ / radiusPlusZ p₀ β lam M ε₀ d i) ^ 2 -
        L / β * (badPoints p₀ β lam M ε₀ d).card ≤
      energy χ lam d := by
  obtain ⟨L₀, hL₀, h⟩ := eq_b1 hχ
  refine ⟨β * L₀, mul_pos hβ hL₀, fun p₀ lam M ε₀ d hlam => ?_⟩
  rw [mul_div_cancel_left₀ _ hβ.ne']
  exact h p₀ β lam M ε₀ d hlam

end UpperBound

end MultipoleBKT

end
