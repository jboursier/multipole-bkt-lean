/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ExpE11

/-!
# Lemma 4.18, Steps 3 and 8: the energy upper bound and the change of reference measure

The proof of Lemma 4.18, Step 3
(proof of Lemma 4.18, eq. (4.31)) and the normalization of Step 8 (proof of Lemma 4.18).

* `finToLabels c`: a configuration `c : Fin N → ℂ × ℂ` read on all labels (`0` beyond `N`);
  `measurePreserving_finRestrict`: `ρ^{⊗ ℕ}` restricted to the labels `< N` is `ρ^{⊗ N}`, so
  `𝔼_{ρ^{⊗ N}}[g(c)] = 𝔼_{ρ^{⊗ ℕ}}[g]` for `g` depending on the labels `< N`
  (`integral_pi_fin_eq_integral_labelField`).
* `sum_erase_eq_two_mul_sum_pairsOn`: `∑_i ∑_{j ≠ i} f_ij = 2 ∑_{i<j} f_ij` for `f` symmetric.
* `exp_neg_mul_energy_ge` (**Step 3**): by (3.53), on the configurations with all dipole lengths
  at most `ε₀ R̄` (and `λ ≤ ε₀ R̄`, `β ≥ 0`, `L ≥ β/64`),
  `e^{-β F_λ} ≥ ∏ᵢ e^{β g_λ(x_i - y_i)} e^{-L |x_i - y_i|² / (ε₀ R̄)²} ∏_{i<j} e^{-β ṽ_ij}`.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

/-! ### Configurations of `N` dipoles read on all labels -/

/-- A configuration of the labels `0, …, N - 1` read on all labels (`0` beyond `N`). -/
def finToLabels {N : ℕ} (c : Fin N → ℂ × ℂ) : ℕ → ℂ × ℂ :=
  fun i => if h : i < N then c ⟨i, h⟩ else 0

theorem finToLabels_apply {N : ℕ} (c : Fin N → ℂ × ℂ) (i : Fin N) : finToLabels c i = c i := by
  simp [finToLabels]

theorem measurable_finToLabels (N : ℕ) : Measurable (finToLabels (N := N)) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i < N
  · simp only [finToLabels, h, dite_true]
    exact measurable_pi_apply _
  · simp only [finToLabels, h, dite_false]
    exact measurable_const

theorem finToLabels_restrict {N : ℕ} {g : (ℕ → ℂ × ℂ) → ℝ}
    (hdep : DependsOn g (Finset.range N : Set ℕ)) (c : ℕ → ℂ × ℂ) :
    g (finToLabels fun i : Fin N => c i) = g c :=
  hdep fun i hi => by
    have : i < N := Finset.mem_range.1 (Finset.mem_coe.1 hi)
    simp [finToLabels, this]

variable {ρ : Measure (ℂ × ℂ)}

/-- `ρ^{⊗ ℕ}` restricted to the labels `< N` is `ρ^{⊗ N}`. -/
theorem measurePreserving_finRestrict [IsProbabilityMeasure ρ] (N : ℕ) :
    MeasurePreserving (fun c : ℕ → ℂ × ℂ => fun i : Fin N => c i) (labelField ρ)
      (Measure.pi fun _ : Fin N => ρ) := by
  refine ⟨by fun_prop, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hset : (fun c : ℕ → ℂ × ℂ => fun i : Fin N => c i) ⁻¹' Set.univ.pi s =
      Set.pi (Finset.range N : Set ℕ) fun n => if h : n < N then s ⟨n, h⟩ else Set.univ := by
    ext c
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, Finset.coe_range,
      Set.mem_Iio]
    constructor
    · intro hc n hn
      simp only [hn, dite_true]
      exact hc ⟨n, hn⟩
    · intro hc i
      have := hc i i.2
      simpa [i.2] using this
  rw [hset, labelField, Measure.infinitePi_pi (μ := fun _ : ℕ => ρ) (s := Finset.range N)
    (t := fun n => if h : n < N then s ⟨n, h⟩ else Set.univ) fun n _ => by
    by_cases h : n < N
    · simp only [h, dite_true]
      exact hs _
    · simp only [h, dite_false]
      exact MeasurableSet.univ]
  rw [← Fin.prod_univ_eq_prod_range (fun n => ρ (if h : n < N then s ⟨n, h⟩ else Set.univ))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [i.2]

/-- **Transfer.** For `g` depending only on the labels `< N`,
`𝔼_{ρ^{⊗ N}}[g(c)] = 𝔼_{ρ^{⊗ ℕ}}[g]`. -/
theorem integral_pi_fin_eq_integral_labelField [IsProbabilityMeasure ρ] {N : ℕ}
    {g : (ℕ → ℂ × ℂ) → ℝ} (hg : Measurable g) (hdep : DependsOn g (Finset.range N : Set ℕ)) :
    ∫ c : Fin N → ℂ × ℂ, g (finToLabels c) ∂Measure.pi (fun _ => ρ) = ∫ c, g c ∂labelField ρ := by
  have hmp := measurePreserving_finRestrict (ρ := ρ) N
  rw [← hmp.map_eq, integral_map (f := fun c => g (finToLabels c)) hmp.measurable.aemeasurable
    (hg.comp (measurable_finToLabels N)).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun c => finToLabels_restrict hdep c)

/-! ### Step 3: the energy upper bound (3.53) -/

/-- A double sum over `Fin N` of a function of the labels is a double sum over `range N`. -/
theorem sum_fin_sum_fin_eq {N : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, f i j = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, f i j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, f i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Fin.sum_univ_eq_sum_range (f i) N

/-- `∑_{i<j} f_ij = ∑_{p ∈ pairsOn (range N)} f_p`. -/
theorem sum_fin_lt_eq_sum_pairsOn {N : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ i : Fin N, ∑ j : Fin N, (if i < j then f i j else 0) =
      ∑ p ∈ pairsOn (Finset.range N), f p.1 p.2 := by
  have h : ∀ i j : Fin N, (if i < j then f i j else 0) =
      if (i : ℕ) < (j : ℕ) then f i j else 0 := fun i j => by
    simp only [Fin.lt_def]
  simp_rw [h]
  rw [sum_fin_sum_fin_eq (fun i j => if i < j then f i j else 0), pairsOn, Finset.sum_filter,
    Finset.sum_product]

/-- `∑_i ∑_{j ≠ i} f_ij = 2 ∑_{i<j} f_ij` for `f` symmetric. -/
theorem sum_erase_eq_two_mul_sum_pairsOn {N : ℕ} (f : ℕ → ℕ → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, f i j =
      2 * ∑ p ∈ pairsOn (Finset.range N), f p.1 p.2 := by
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, f i j =
      ∑ j : Fin N, ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
    intro i
    rw [← Finset.filter_ne', Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, hij.ne', not_lt.2 hij.le]
    · simp
    · simp [hji, hji.ne, not_lt.2 hji.le]
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if j < i then f i j else 0) =
      ∑ i : Fin N, ∑ j : Fin N, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  simp_rw [h1, Finset.sum_add_distrib]
  rw [h2, ← two_mul, sum_fin_lt_eq_sum_pairsOn]

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam ε₀ L : ℝ}

/-- **Step 3 of Lemma 4.18** (eq. (4.31), from (3.53)): if `λ > 0`, `λ ≤ ε₀ R̄`, `β ≥ 0`,
`L ≥ β/64` and every dipole has length at most `ε₀ R̄`, then
`e^{-β F_λ} ≥ ∏ᵢ e^{β g_λ(x_i - y_i)} e^{-L |x_i - y_i|²/(ε₀ R̄)²} ∏_{i<j} e^{-β ṽ_ij}`. -/
theorem exp_neg_mul_energy_ge (hχ : IsMollifier χ) (c : Fin N → ℂ × ℂ) (hlam : 0 < lam)
    (hβ : 0 ≤ β) (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hL : β / 64 ≤ L)
    (hc : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    (∏ n ∈ Finset.range N, (Real.exp (β * smearedKernel χ lam
        ((finToLabels c n).1 - (finToLabels c n).2)) *
        gaussianWeight p₀ β lam ε₀ L (finToLabels c n))) *
      ∏ p ∈ pairsOn (Finset.range N), Real.exp (-β * upperBoundInteraction χ lam ε₀
        (truncationScale p₀ β lam) (finToLabels c p.1) (finToLabels c p.2)) ≤
    Real.exp (-β * energy χ lam c) := by
  set R := truncationScale p₀ β lam with hR
  have hb2 := eq_b2 hχ c hlam hlamR hc
  -- the interaction sum
  have hsym : ∀ i j : ℕ, upperBoundInteraction χ lam ε₀ R (finToLabels c i) (finToLabels c j) =
      upperBoundInteraction χ lam ε₀ R (finToLabels c j) (finToLabels c i) := fun i j =>
    screenedInteraction_comm χ lam _ _ _
  have hv : 1 / 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, upperBoundInteraction χ lam ε₀ R (c i) (c j) =
      ∑ p ∈ pairsOn (Finset.range N),
        upperBoundInteraction χ lam ε₀ R (finToLabels c p.1) (finToLabels c p.2) := by
    have := sum_erase_eq_two_mul_sum_pairsOn (N := N)
      (fun i j => upperBoundInteraction χ lam ε₀ R (finToLabels c i) (finToLabels c j)) hsym
    simp only [finToLabels_apply] at this
    rw [this]
    ring
  have hg : ∑ i, smearedKernel χ lam ((c i).1 - (c i).2) =
      ∑ n ∈ Finset.range N, smearedKernel χ lam ((finToLabels c n).1 - (finToLabels c n).2) := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => smearedKernel χ lam
      ((finToLabels c n).1 - (finToLabels c n).2)) N]
    simp only [finToLabels_apply]
  have hr : ∑ i, ‖(c i).1 - (c i).2‖ ^ 2 / (ε₀ * R) ^ 2 =
      ∑ n ∈ Finset.range N, ‖(finToLabels c n).1 - (finToLabels c n).2‖ ^ 2 / (ε₀ * R) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun n =>
      ‖(finToLabels c n).1 - (finToLabels c n).2‖ ^ 2 / (ε₀ * R) ^ 2) N]
    simp only [finToLabels_apply]
  rw [hv, hg, hr] at hb2
  have hr0 : 0 ≤ ∑ n ∈ Finset.range N,
      ‖(finToLabels c n).1 - (finToLabels c n).2‖ ^ 2 / (ε₀ * R) ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  simp only [gaussianWeight, ← Real.exp_add]
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, ← hR]
  have h1 : β * (1 / 64 * ∑ n ∈ Finset.range N,
      ‖(finToLabels c n).1 - (finToLabels c n).2‖ ^ 2 / (ε₀ * R) ^ 2) ≤
      L * ∑ n ∈ Finset.range N, ‖(finToLabels c n).1 - (finToLabels c n).2‖ ^ 2 / (ε₀ * R) ^ 2 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hr0
  nlinarith [mul_le_mul_of_nonneg_left hb2 hβ]

end Hierarchical

end MultipoleBKT

end
