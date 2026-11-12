/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Convexity
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Compact

/-!
# The interior minimizer of the rate function

The proof follows Steps 1 and 4 of the proof of Theorem 2, including (5.157).
Compactness gives existence. If a minimizer has a zero coordinate, moving mass
from a positive coordinate changes the rate by `t log t + O(t) < 0`.
Thus every minimizer has positive coordinates. Strict convexity from the full
Hessian on positive coordinates then gives uniqueness.

Stationarity along `e_i - (i+1) e_0` eliminates the Lagrange multiplier and gives
`γ*_i = 𝗆(i+1)/(i+1)! · (γ*_0)^{i+1} · e^{-D}`, with `|D| ≤ (i+2) ‖Dh‖`.
The resulting coordinate bounds are `C''⁻¹ λ^{2i} ≤ γ*_i ≤ C'' λ^{2i}` for `i ≥ 1`.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real Set Filter Topology
open scoped Nat

variable {p : ℕ}

section Simplex

theorem isCompact_unitBox : IsCompact (unitBox p) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem isClosed_simplex (x : ℝ) : IsClosed (simplex p x) := by
  have : simplex p x = unitBox p ∩ {γ | ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * γ i = 1 - x} := by
    ext γ
    simp only [simplex, Set.mem_inter_iff, mem_unitBox]
    rfl
  rw [this]
  exact isCompact_unitBox.isClosed.inter (isClosed_eq
    (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
    continuous_const)

theorem isCompact_simplex (x : ℝ) : IsCompact (simplex p x) :=
  isCompact_unitBox.of_isClosed_subset (isClosed_simplex x) (simplex_subset_unitBox x)

/-- `(1 - x, 0, …, 0) ∈ Δ_{p,x}` for `x ∈ [0,1]`. -/
theorem single_mem_simplex (hp : 1 ≤ p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Pi.single (⟨0, hp⟩ : Fin p) (1 - x) ∈ simplex p x := by
  refine ⟨fun i => ?_, ?_⟩
  · by_cases h : i = ⟨0, hp⟩
    · subst h
      simp only [Pi.single_eq_same, Set.mem_Icc]
      constructor <;> linarith [hx.1, hx.2]
    · simp [h]
  · rw [Finset.sum_eq_single (⟨0, hp⟩ : Fin p)]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h

theorem simplex_nonempty (hp : 1 ≤ p) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (simplex p x).Nonempty :=
  ⟨_, single_mem_simplex hp hx⟩

end Simplex

section Entropy

/-- `a log a - b log b ≤ (b - a)(-log b)` for `0 < a ≤ b`. -/
private theorem mul_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a * Real.log a - b * Real.log b ≤ (b - a) * (-Real.log b) := by
  have h1 : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have h2 : a * Real.log a ≤ a * Real.log b := mul_le_mul_of_nonneg_left h1 ha.le
  have h3 : (b - a) * (-Real.log b) = a * Real.log b - b * Real.log b := by ring
  linarith

end Entropy

section Analysis

variable {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- Lipschitz bound for the cluster part: `|h(y) - h(x)| ≤ B ‖y - x‖` on `rateDomain p`, with
`B = 16 K² 2^p λ²`. -/
theorem abs_rateCluster_sub_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {x y : Fin p → ℝ}
    (hx : x ∈ rateDomain p) (hy : y ∈ rateDomain p) :
    |rateCluster p kmult y - rateCluster p kmult x| ≤
      16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * ‖y - x‖ := by
  obtain ⟨-, hall⟩ := rateCluster_smooth_of_small hk hlam hsmall
  rw [← Real.norm_eq_abs]
  exact convex_rateDomain.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hall z hz).1.differentiableAt) (fun z hz => (hall z hz).2.2.2.1) hx hy

/-- **Interiority** of the minimizer (proof of Theorem 2, Step 1): all
coordinates of a minimizer of `ℐ` on `Δ_{p,0}` are positive. -/
theorem pos_of_isMinOn_rateFunction (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ simplex p 0)
    (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) (j : Fin p) : 0 < γ j := by
  set B := 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2
  have hB0 : 0 ≤ B := by positivity
  by_contra hj
  have hj0 : γ j = 0 := le_antisymm (not_lt.mp hj) (hγ.1 j).1
  obtain ⟨l, hl⟩ : ∃ l, 0 < γ l := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have h0 : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * γ i = 0 :=
      sum_eq_zero fun i _ => by rw [le_antisymm (h i) (hγ.1 i).1, mul_zero]
    rw [hγ.2] at h0
    norm_num at h0
  have hlj : l ≠ j := fun h => by rw [h, hj0] at hl; exact lt_irrefl _ hl
  have hl1 : γ l ≤ 1 := (hγ.1 l).2
  set r : ℝ := ((j : ℕ) + 1) / ((l : ℕ) + 1) with hr_def
  have hr : 0 < r := by positivity
  set v : Fin p → ℝ := Pi.single j 1 - r • Pi.single l 1 with hv_def
  have hvj : v j = 1 := by simp [hv_def, hlj.symm]
  have hvl : v l = -r := by simp [hv_def, hlj]
  have hvk : ∀ k, k ≠ j ∧ k ≠ l → v k = 0 := by
    intro k hk
    simp [hv_def, hk.1, hk.2]
  have hvnorm : ‖v‖ ≤ 1 + r := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    by_cases hkj : k = j
    · rw [hkj, hvj]; norm_num; exact hr.le
    · by_cases hkl : k = l
      · rw [hkl, hvl, abs_neg, abs_of_pos hr]; linarith
      · rw [hvk k ⟨hkj, hkl⟩, abs_zero]; positivity
  have hvsum : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * v k = 0 := by
    rw [Fintype.sum_eq_add j l hlj.symm fun k hk => by rw [hvk k hk, mul_zero], hvj, hvl,
      hr_def]
    field_simp
    ring
  -- the constants of the estimate
  set Lj := Real.log ((j : ℕ) + 1).factorial - 1 - Real.log (msf ((j : ℕ) + 1))
  set Ll := Real.log ((l : ℕ) + 1).factorial - 1 - Real.log (msf ((l : ℕ) + 1))
  set K₁ := |Lj| + r * (|Ll| + -Real.log (γ l)) + B * (1 + r)
  have hlogl : 0 ≤ -Real.log (γ l) := by
    have := Real.log_nonpos hl.le hl1
    linarith
  set t : ℝ := min (min 1 (γ l / (2 * r))) (Real.exp (-K₁ - 1))
  have ht0 : 0 < t := lt_min (lt_min one_pos (by positivity)) (Real.exp_pos _)
  have ht1 : t ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have htr : r * t ≤ γ l / 2 := by
    have : t ≤ γ l / (2 * r) := (min_le_left _ _).trans (min_le_right _ _)
    calc r * t ≤ r * (γ l / (2 * r)) := mul_le_mul_of_nonneg_left this hr.le
      _ = γ l / 2 := by field_simp
  have hlogt : Real.log t ≤ -K₁ - 1 := by
    have : t ≤ Real.exp (-K₁ - 1) := min_le_right _ _
    calc Real.log t ≤ Real.log (Real.exp (-K₁ - 1)) := Real.log_le_log ht0 this
      _ = -K₁ - 1 := Real.log_exp _
  have hrt0 : 0 ≤ r * t := by positivity
  -- the perturbed point
  set η : Fin p → ℝ := γ + t • v with hη_def
  have hηk : ∀ k, η k = γ k + t * v k := fun k => by simp [hη_def]
  have hηj : η j = t := by rw [hηk, hj0, hvj, mul_one, zero_add]
  have hηl : η l = γ l - r * t := by rw [hηk, hvl]; ring
  have hηmem : η ∈ simplex p 0 := by
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hkj : k = j
      · rw [hkj, hηj]; exact ⟨ht0.le, ht1⟩
      · by_cases hkl : k = l
        · rw [hkl, hηl]; constructor <;> linarith
        · rw [hηk, hvk k ⟨hkj, hkl⟩, mul_zero, add_zero]; exact hγ.1 k
    · have : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * η k =
          ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * γ k + t * ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * v k := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [hηk]
        ring
      rw [this, hγ.2, hvsum, mul_zero, add_zero]
  -- the variation of `ℐ`
  have hdiff := rateFunction_sub_eq msf kmult γ η
  have hsum : ∑ k, (rateEntTerm msf k (η k) - rateEntTerm msf k (γ k)) =
      (rateEntTerm msf j (η j) - rateEntTerm msf j (γ j)) +
        (rateEntTerm msf l (η l) - rateEntTerm msf l (γ l)) := by
    refine Fintype.sum_eq_add j l hlj.symm fun k hk => ?_
    rw [hηk, hvk k hk, mul_zero, add_zero, sub_self]
  have hj' : rateEntTerm msf j (η j) - rateEntTerm msf j (γ j) = t * Real.log t + Lj * t := by
    rw [hηj, hj0, rateEntTerm, rateEntTerm]
    simp only [Real.log_zero, zero_mul]
    ring
  have hl' : rateEntTerm msf l (η l) - rateEntTerm msf l (γ l) ≤
      r * t * (|Ll| + -Real.log (γ l)) := by
    have ha : 0 < γ l - r * t := by linarith
    have h1 := mul_log_sub_le ha (by linarith : γ l - r * t ≤ γ l)
    have h2 : rateEntTerm msf l (η l) - rateEntTerm msf l (γ l) =
        ((γ l - r * t) * Real.log (γ l - r * t) - γ l * Real.log (γ l)) - r * t * Ll := by
      rw [hηl, rateEntTerm, rateEntTerm]
      ring
    rw [h2]
    have h3 : -(r * t * Ll) ≤ r * t * |Ll| := by
      have := neg_abs_le Ll
      have hrt : 0 ≤ r * t := by positivity
      nlinarith
    have h4 : (γ l - (γ l - r * t)) * -Real.log (γ l) = r * t * -Real.log (γ l) := by ring
    linarith
  have hH : rateCluster p kmult η - rateCluster p kmult γ ≤ B * t * (1 + r) := by
    have hγD := unitBox_subset_rateDomain (simplex_subset_unitBox 0 hγ)
    have hηD := unitBox_subset_rateDomain (simplex_subset_unitBox 0 hηmem)
    have h := abs_rateCluster_sub_le hk hlam hsmall hγD hηD
    have hn : ‖η - γ‖ = t * ‖v‖ := by
      rw [hη_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    rw [hn] at h
    have := (le_abs_self _).trans h
    calc rateCluster p kmult η - rateCluster p kmult γ ≤ B * (t * ‖v‖) := this
      _ ≤ B * (t * (1 + r)) := by gcongr
      _ = B * t * (1 + r) := by ring
  have hlt : rateFunction p msf kmult η - rateFunction p msf kmult γ < 0 := by
    rw [hdiff, hsum, hj']
    have hLj : Lj * t ≤ |Lj| * t := mul_le_mul_of_nonneg_right (le_abs_self _) ht0.le
    have htlog : t * Real.log t ≤ t * (-K₁ - 1) := mul_le_mul_of_nonneg_left hlogt ht0.le
    have hK : t * (-K₁ - 1) + |Lj| * t + r * t * (|Ll| + -Real.log (γ l)) + B * t * (1 + r) =
        -t := by
      simp only [K₁]
      ring
    linarith
  have := isMinOn_iff.mp hmin η hηmem
  linarith

/-- Existence and uniqueness of the minimizer of `ℐ` on `Δ_{p,0}`. -/
theorem existsUnique_isMinOn_rateFunction (hp : 1 ≤ p) (hk : KmultBound p kmult C lam)
    (hlam : 0 ≤ lam) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4)
    (hB : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 < 1) :
    ∃! γ, γ ∈ simplex p 0 ∧ IsMinOn (rateFunction p msf kmult) (simplex p 0) γ := by
  have hcont := (continuousOn_rateFunction (msf := msf) hk hlam hsmall).mono
    ((simplex_subset_unitBox 0).trans unitBox_subset_rateDomain)
  obtain ⟨γ, hγ, hmin⟩ := (isCompact_simplex 0).exists_isMinOn
    (simplex_nonempty hp ⟨le_rfl, zero_le_one⟩) hcont
  refine ⟨γ, ⟨hγ, hmin⟩, fun η hη => ?_⟩
  have hposγ := pos_of_isMinOn_rateFunction hk hlam hsmall hγ hmin
  have hposη := pos_of_isMinOn_rateFunction hk hlam hsmall hη.1 hη.2
  have hsc := strictConvexOn_rateFunction_positive (msf := msf) hk hlam hsmall hB
  have hsc' := hsc.subset (s := simplex p 0 ∩ (unitBox p ∩ {z | ∀ i, 0 < z i}))
    inter_subset_right ((convex_simplex 0).inter hsc.1)
  exact hsc'.eq_of_isMinOn (isMinOn_iff.mpr (fun z hz => hη.2 hz.1))
    (isMinOn_iff.mpr (fun z hz => hmin hz.1))
    ⟨hη.1, simplex_subset_unitBox 0 hη.1, hposη⟩ ⟨hγ, simplex_subset_unitBox 0 hγ, hposγ⟩

/-- Coordinates of a minimizer are `< 1` when `p ≥ 2` and all coordinates are positive. -/
private theorem lt_one_of_pos {γ : Fin p → ℝ} (hγ : γ ∈ simplex p 0) (hpos : ∀ k, 0 < γ k)
    {a b : Fin p} (hab : a ≠ b) (k : Fin p) : γ k < 1 := by
  obtain ⟨k', hk'⟩ : ∃ k', k' ≠ k := by
    by_cases h : a = k
    · exact ⟨b, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨a, h⟩
  have h1 : ∑ x ∈ ({k, k'} : Finset (Fin p)), ((x : ℕ) + 1 : ℝ) * γ x ≤
      ∑ x : Fin p, ((x : ℕ) + 1 : ℝ) * γ x :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ =>
      mul_nonneg (by positivity) (hpos x).le
  rw [sum_pair hk'.symm, hγ.2, sub_zero] at h1
  have h2 : 0 < ((k' : ℕ) + 1 : ℝ) * γ k' := mul_pos (by positivity) (hpos k')
  have h3 : γ k ≤ ((k : ℕ) + 1 : ℝ) * γ k := by
    have : (1 : ℝ) ≤ (k : ℕ) + 1 := by linarith [(Nat.cast_nonneg (k : ℕ) : (0 : ℝ) ≤ (k : ℕ))]
    nlinarith [hpos k]
  linarith

/-- **Stationarity** of an interior minimizer along `e_i - (i+1) e_0` (the paper's Lagrange
condition): `log i'! + log γᵢ - log 𝗆(i') - (i+1)(log γ₀ - log 𝗆(1)) + D = 0` with
`i' = i + 1` and `|D| ≤ (i+2) B`. -/
theorem stationary_of_isMinOn (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ simplex p 0)
    (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) (hpos : ∀ k, 0 < γ k)
    (e0 i : Fin p) (he0 : (e0 : ℕ) = 0) (hi : 1 ≤ (i : ℕ)) :
    ∃ D : ℝ, |D| ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * ((i : ℕ) + 2) ∧
      (Real.log ((i : ℕ) + 1).factorial + Real.log (γ i) - Real.log (msf ((i : ℕ) + 1))) -
        ((i : ℕ) + 1) * (Real.log (γ e0) - Real.log (msf 1)) + D = 0 := by
  set B := 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2
  obtain ⟨-, hall⟩ := rateCluster_smooth_of_small hk hlam hsmall
  have hie0 : i ≠ e0 := fun h => by rw [h, he0] at hi; omega
  set c : ℝ := (i : ℕ) + 1 with hc_def
  set v : Fin p → ℝ := Pi.single i 1 - c • Pi.single e0 1 with hv_def
  have hvi : v i = 1 := by simp [hv_def, hie0]
  have hv0 : v e0 = -c := by simp [hv_def, hie0.symm]
  have hvk : ∀ k, k ≠ i ∧ k ≠ e0 → v k = 0 := by
    intro k hk
    simp [hv_def, hk.1, hk.2]
  have hvsum : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * v k = 0 := by
    rw [Fintype.sum_eq_add i e0 hie0 fun k hk => by rw [hvk k hk, mul_zero], hvi, hv0, he0,
      hc_def]
    push_cast
    ring
  have hvnorm : ‖v‖ ≤ (i : ℕ) + 2 := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
    rw [Real.norm_eq_abs]
    by_cases hki : k = i
    · rw [hki, hvi, abs_one]
      linarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ (i : ℕ))]
    · by_cases hk0 : k = e0
      · rw [hk0, hv0, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < c), hc_def]
        linarith
      · rw [hvk k ⟨hki, hk0⟩, abs_zero]
        positivity
  -- the path stays in the simplex near `t = 0`
  have hlt1 : ∀ k, γ k < 1 := lt_one_of_pos hγ hpos hie0
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), γ + t • v ∈ simplex p 0 := by
    have hcoord : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ k, γ k + t * v k ∈ Ioo (0 : ℝ) 1 := by
      refine Filter.eventually_all.mpr fun k => ?_
      have hcont : ContinuousAt (fun t : ℝ => γ k + t * v k) 0 :=
        (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
      refine hcont.eventually_mem (isOpen_Ioo.mem_nhds ?_)
      simp only [zero_mul, add_zero]
      exact ⟨hpos k, hlt1 k⟩
    filter_upwards [hcoord] with t ht
    refine ⟨fun k => ?_, ?_⟩
    · have := ht k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact Ioo_subset_Icc_self this
    · have : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * (γ + t • v) k =
          ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * γ k + t * ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * v k := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [this, hγ.2, hvsum, mul_zero, add_zero]
  have hlocmin : IsLocalMin (fun t : ℝ => rateFunction p msf kmult (γ + t • v)) 0 := by
    filter_upwards [hev] with t ht
    simp only [zero_smul, add_zero]
    exact isMinOn_iff.mp hmin _ ht
  -- the derivative at `0`
  set g' : Fin p → ℝ := fun k =>
    Real.log ((k : ℕ) + 1).factorial + Real.log (γ k) - Real.log (msf ((k : ℕ) + 1))
  have hγD : γ ∈ rateDomain p := unitBox_subset_rateDomain (simplex_subset_unitBox 0 hγ)
  have hderiv : HasDerivAt (fun t : ℝ => rateFunction p msf kmult (γ + t • v))
      (∑ k, g' k * v k + fderiv ℝ (rateCluster p kmult) γ v) 0 := by
    have hent : HasDerivAt (fun t : ℝ => ∑ k, rateEntTerm msf k (γ k + t * v k))
        (∑ k, g' k * v k) 0 := by
      have := HasDerivAt.sum (u := univ) (A := fun k (t : ℝ) => rateEntTerm msf k (γ k + t * v k))
        (A' := fun k => g' k * v k) (x := 0) fun k _ => by
          have hin : HasDerivAt (fun t : ℝ => γ k + t * v k) (v k) 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v k)).const_add (γ k)
          exact (hasDerivAt_rateEntTerm msf k (hpos k)).comp_of_eq 0 hin (by simp)
      convert this using 1
      funext t
      simp only [Finset.sum_apply]
    have hH : HasDerivAt (fun t : ℝ => rateCluster p kmult (γ + t • v))
        (fderiv ℝ (rateCluster p kmult) γ v) 0 := by
      have hin : HasDerivAt (fun t : ℝ => γ + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add γ
      exact (hall γ hγD).1.comp_hasDerivAt_of_eq 0 hin (by simp)
    have hfun : (fun t : ℝ => rateFunction p msf kmult (γ + t • v)) =
        fun t => (∑ k, rateEntTerm msf k (γ k + t * v k) + 1) +
          rateCluster p kmult (γ + t • v) := by
      funext t
      rw [rateFunction_eq_ent]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact (hent.add_const 1).add hH
  have hzero := hlocmin.hasDerivAt_eq_zero hderiv
  have hsum2 : ∑ k, g' k * v k = g' i - c * g' e0 := by
    rw [Fintype.sum_eq_add i e0 hie0 fun k hk => by rw [hvk k hk, mul_zero], hvi, hv0]
    ring
  refine ⟨fderiv ℝ (rateCluster p kmult) γ v, ?_, ?_⟩
  · rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (rateCluster p kmult) γ v‖ ≤ ‖fderiv ℝ (rateCluster p kmult) γ‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * ((i : ℕ) + 2) := by
          gcongr
          exact (hall γ hγD).2.2.2.1
  · rw [hsum2] at hzero
    have he0' : g' e0 = Real.log (γ e0) - Real.log (msf 1) := by
      simp only [g', he0, zero_add, Nat.factorial_one, Nat.cast_one, Real.log_one]
    rw [he0'] at hzero
    simpa [g', hc_def] using hzero


/-- The hypothesis (2.47) on the coefficients `𝗆`, for one value of `λ`, with a uniform
constant `C`, together with `𝗆(1) = 1`. -/
def MsfBound (p : ℕ) (msf : ℕ → ℝ) (C lam : ℝ) : Prop :=
  msf 1 = 1 ∧ ∀ k : ℕ, 2 ≤ k → k ≤ p →
    C⁻¹ * lam ^ (2 * (k - 1)) ≤ msf k ∧ msf k ≤ C * lam ^ (2 * (k - 1))

/-- The two-sided form of stationarity: `log γᵢ = log 𝗆(i+1) - log (i+1)! + (i+1) log γ₀ - D`. -/
private theorem log_eq_of_isMinOn (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (hmsf1 : msf 1 = 1) {γ : Fin p → ℝ}
    (hγ : γ ∈ simplex p 0) (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ)
    (hpos : ∀ k, 0 < γ k) (e0 i : Fin p) (he0 : (e0 : ℕ) = 0) (hi : 1 ≤ (i : ℕ)) :
    ∃ D : ℝ, |D| ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * ((i : ℕ) + 2) ∧
      Real.log (γ i) = Real.log (msf ((i : ℕ) + 1)) - Real.log ((i : ℕ) + 1).factorial +
        ((i : ℕ) + 1) * Real.log (γ e0) - D := by
  obtain ⟨D, hD, h⟩ := stationary_of_isMinOn hk hlam hsmall hγ hmin hpos e0 i he0 hi
  refine ⟨D, hD, ?_⟩
  rw [hmsf1, Real.log_one, sub_zero] at h
  linarith

/-- **Upper bound** on the coordinates of the minimizer: `γ*ᵢ ≤ e C λ^{2i}` for `1 ≤ i`. -/
theorem minimizer_le (hk : KmultBound p kmult C lam) (hlam : 0 < lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (hC : 0 < C)
    (hmsf : MsfBound p msf C lam)
    (hBp : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * (p + 1) ≤ 1) {γ : Fin p → ℝ}
    (hγ : γ ∈ simplex p 0) (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ)
    (i : Fin p) (hi : 1 ≤ (i : ℕ)) :
    γ i ≤ C * Real.exp 1 * lam ^ (2 * (i : ℕ)) := by
  have hp : 0 < p := Nat.zero_lt_of_lt i.2
  have hpos := pos_of_isMinOn_rateFunction hk hlam.le hsmall hγ hmin
  set e0 : Fin p := ⟨0, hp⟩
  obtain ⟨D, hD, hlog⟩ := log_eq_of_isMinOn hk hlam.le hsmall hmsf.1 hγ hmin hpos e0 i rfl hi
  have hm := hmsf.2 ((i : ℕ) + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hm
  have hmpos : 0 < msf ((i : ℕ) + 1) :=
    lt_of_lt_of_le (by positivity) hm.1
  have hD1 : |D| ≤ 1 := by
    refine hD.trans (le_trans ?_ hBp)
    have : ((i : ℕ) : ℝ) + 2 ≤ p + 1 := by
      have := i.2
      have : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast this
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hfact : 0 ≤ Real.log ((i : ℕ) + 1).factorial :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hlog0 : Real.log (γ e0) ≤ 0 := Real.log_nonpos (hpos e0).le (hγ.1 e0).2
  have hle : Real.log (γ i) ≤ Real.log (msf ((i : ℕ) + 1)) + 1 := by
    have h1 : ((i : ℕ) + 1 : ℝ) * Real.log (γ e0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog0
    have h2 := neg_abs_le D
    linarith
  calc γ i = Real.exp (Real.log (γ i)) := (Real.exp_log (hpos i)).symm
    _ ≤ Real.exp (Real.log (msf ((i : ℕ) + 1)) + 1) := Real.exp_le_exp.mpr hle
    _ = msf ((i : ℕ) + 1) * Real.exp 1 := by rw [Real.exp_add, Real.exp_log hmpos]
    _ ≤ C * lam ^ (2 * (i : ℕ)) * Real.exp 1 := by gcongr; exact hm.2
    _ = C * Real.exp 1 * lam ^ (2 * (i : ℕ)) := by ring

/-- The `0`-th coordinate of the minimizer is at least `1/2`. -/
theorem half_le_minimizer_zero (hk : KmultBound p kmult C lam) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (hC : 0 < C)
    (hmsf : MsfBound p msf C lam)
    (hBp : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * (p + 1) ≤ 1)
    (hsmall2 : (p : ℝ) ^ 2 * (C * Real.exp 1) * lam ^ 2 ≤ 1 / 2) {γ : Fin p → ℝ}
    (hγ : γ ∈ simplex p 0) (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ)
    (e0 : Fin p) (he0 : (e0 : ℕ) = 0) : 1 / 2 ≤ γ e0 := by
  have hsum := hγ.2
  rw [← add_sum_erase _ _ (mem_univ e0), he0, sub_zero] at hsum
  have hbound : ∀ k ∈ univ.erase e0, ((k : ℕ) + 1 : ℝ) * γ k ≤ p * (C * Real.exp 1) * lam ^ 2 := by
    intro k hkmem
    have hk1 : 1 ≤ (k : ℕ) := by
      have := ne_of_mem_erase hkmem
      have : (k : ℕ) ≠ 0 := fun h => this (Fin.ext (h.trans he0.symm))
      omega
    have h1 := minimizer_le hk hlam hsmall hC hmsf hBp hγ hmin k hk1
    have h2 : lam ^ (2 * (k : ℕ)) ≤ lam ^ 2 :=
      pow_le_pow_of_le_one hlam.le hlam1 (by omega)
    have h3 : ((k : ℕ) + 1 : ℝ) ≤ p := by
      have := k.2
      exact_mod_cast this
    have h4 : 0 ≤ γ k := (hγ.1 k).1
    calc ((k : ℕ) + 1 : ℝ) * γ k ≤ p * (C * Real.exp 1 * lam ^ (2 * (k : ℕ))) :=
          mul_le_mul h3 h1 h4 (by positivity)
      _ ≤ p * (C * Real.exp 1 * lam ^ 2) := by gcongr
      _ = p * (C * Real.exp 1) * lam ^ 2 := by ring
  have hS := sum_le_sum hbound
  rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
  have hp1 : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hS' : ((p - 1 : ℕ) : ℝ) * (p * (C * Real.exp 1) * lam ^ 2) ≤
      (p : ℝ) ^ 2 * (C * Real.exp 1) * lam ^ 2 := by
    have : 0 ≤ (p : ℝ) * (C * Real.exp 1) * lam ^ 2 := by positivity
    calc ((p - 1 : ℕ) : ℝ) * (p * (C * Real.exp 1) * lam ^ 2)
        ≤ (p : ℝ) * (p * (C * Real.exp 1) * lam ^ 2) := mul_le_mul_of_nonneg_right hp1 this
      _ = (p : ℝ) ^ 2 * (C * Real.exp 1) * lam ^ 2 := by ring
  simp only [Nat.cast_zero, zero_add, one_mul] at hsum
  linarith

/-- **Lower bound** on the coordinates of the minimizer:
`γ*ᵢ ≥ (e C p! 2^p)⁻¹ λ^{2i}` for `1 ≤ i`. -/
theorem le_minimizer (hk : KmultBound p kmult C lam) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) (hC : 0 < C)
    (hmsf : MsfBound p msf C lam)
    (hBp : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * (p + 1) ≤ 1)
    (hsmall2 : (p : ℝ) ^ 2 * (C * Real.exp 1) * lam ^ 2 ≤ 1 / 2) {γ : Fin p → ℝ}
    (hγ : γ ∈ simplex p 0) (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ)
    (i : Fin p) (hi : 1 ≤ (i : ℕ)) :
    (C * Real.exp 1 * ((p ! : ℝ) * 2 ^ p))⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γ i := by
  have hp : 0 < p := Nat.zero_lt_of_lt i.2
  have hpos := pos_of_isMinOn_rateFunction hk hlam.le hsmall hγ hmin
  set e0 : Fin p := ⟨0, hp⟩
  obtain ⟨D, hD, hlog⟩ := log_eq_of_isMinOn hk hlam.le hsmall hmsf.1 hγ hmin hpos e0 i rfl hi
  have hm := hmsf.2 ((i : ℕ) + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hm
  have hmpos : 0 < msf ((i : ℕ) + 1) := lt_of_lt_of_le (by positivity) hm.1
  have hD1 : |D| ≤ 1 := by
    refine hD.trans (le_trans ?_ hBp)
    have : ((i : ℕ) : ℝ) + 2 ≤ p + 1 := by
      have := i.2
      have : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast this
      linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hhalf := half_le_minimizer_zero hk hlam hlam1 hsmall hC hmsf hBp hsmall2 hγ hmin e0 rfl
  have hfact : Real.log ((i : ℕ) + 1).factorial ≤ Real.log (p !) := by
    refine Real.log_le_log (by exact_mod_cast Nat.factorial_pos _) ?_
    exact_mod_cast Nat.factorial_le (by omega)
  have hlog0 : -Real.log 2 ≤ Real.log (γ e0) := by
    have : Real.log (1 / 2) ≤ Real.log (γ e0) := Real.log_le_log (by norm_num) hhalf
    rwa [one_div, Real.log_inv] at this
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hge : Real.log (msf ((i : ℕ) + 1)) - Real.log (p !) - p * Real.log 2 - 1 ≤
      Real.log (γ i) := by
    have h1 : -((p : ℝ) * Real.log 2) ≤ ((i : ℕ) + 1 : ℝ) * Real.log (γ e0) := by
      have hip : ((i : ℕ) + 1 : ℝ) ≤ p := by exact_mod_cast i.2
      have := mul_le_mul_of_nonneg_left hlog0 (by positivity : (0 : ℝ) ≤ (i : ℕ) + 1)
      nlinarith
    have h2 := le_abs_self D
    linarith
  have hpf : (0 : ℝ) < p ! := by exact_mod_cast Nat.factorial_pos p
  have hexp : Real.exp (Real.log (msf ((i : ℕ) + 1)) - Real.log (p !) - p * Real.log 2 - 1) =
      msf ((i : ℕ) + 1) / ((p ! : ℝ) * 2 ^ p * Real.exp 1) := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_sub, Real.exp_log hmpos, Real.exp_log hpf,
      ← Real.rpow_natCast 2 p, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      mul_comm (Real.log 2)]
    field_simp
  calc (C * Real.exp 1 * ((p ! : ℝ) * 2 ^ p))⁻¹ * lam ^ (2 * (i : ℕ))
      = C⁻¹ * lam ^ (2 * (i : ℕ)) / ((p ! : ℝ) * 2 ^ p * Real.exp 1) := by
        field_simp
    _ ≤ msf ((i : ℕ) + 1) / ((p ! : ℝ) * 2 ^ p * Real.exp 1) := by gcongr; exact hm.1
    _ = Real.exp (Real.log (msf ((i : ℕ) + 1)) - Real.log (p !) - p * Real.log 2 - 1) :=
        hexp.symm
    _ ≤ Real.exp (Real.log (γ i)) := Real.exp_le_exp.mpr hge
    _ = γ i := Real.exp_log (hpos i)


end Analysis

section Packaged

/-- An elementary smallness criterion: if `0 ≤ X ≤ A`, `1 ≤ A` and `0 ≤ λ ≤ 1/(2A)`, then
`X λ² ≤ 1/2`. -/
theorem mul_sq_le_half_of_le {X A lam : ℝ} (hX : 0 ≤ X) (hXA : X ≤ A) (hA : 1 ≤ A)
    (hlam : 0 ≤ lam) (hlamA : lam ≤ 1 / (2 * A)) : X * lam ^ 2 ≤ 1 / 2 := by
  have hA0 : 0 < A := by linarith
  have hlam1 : lam ≤ 1 := by
    refine hlamA.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have h1 : lam ^ 2 ≤ lam := by nlinarith
  have h2 : X * lam ≤ X * (1 / (2 * A)) := mul_le_mul_of_nonneg_left hlamA hX
  have h3 : X * (1 / (2 * A)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  calc X * lam ^ 2 ≤ X * lam := mul_le_mul_of_nonneg_left h1 hX
    _ ≤ 1 / 2 := h2.trans h3

/-- **Minimizer bounds** (Steps 1 and 4 of the proof of Theorem 2). For
`p ≥ 1` and `C > 0` there are `λ₀ > 0` and `C'' > 0` such that for `0 < λ < λ₀` and
coefficients `𝗆`, `𝗄^mult` satisfying (2.47), (2.48) with constant `C` and `𝗆(1) = 1`: `ℐ` is
strictly convex on `Δ_{p,0}`, has a unique minimizer there, and every minimizer `γ*` has
positive coordinates with `C''⁻¹ λ^{2(k-1)} ≤ γ*_k ≤ C'' λ^{2(k-1)}` for `2 ≤ k ≤ p`
(`γ* i = γ*_{i+1}`). -/
theorem rateFunction_minimizer (p : ℕ) (hp : 1 ≤ p) {C : ℝ} (hC : 0 < C) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ C'' : ℝ, 0 < C'' ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ), MsfBound p msf C lam →
        KmultBound p kmult C lam →
        StrictConvexOn ℝ (simplex p 0) (rateFunction p msf kmult) ∧
        (∃! γ, γ ∈ simplex p 0 ∧ IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) ∧
        ∀ γ ∈ simplex p 0, IsMinOn (rateFunction p msf kmult) (simplex p 0) γ →
          (∀ i, 0 < γ i) ∧ ∀ i : Fin p, 1 ≤ (i : ℕ) →
            C''⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γ i ∧ γ i ≤ C'' * lam ^ (2 * (i : ℕ)) := by
  set K₂ := 16 * rateSeriesConst p C ^ 2 * 2 ^ p
  have hK₂ : 0 ≤ K₂ := by positivity
  set A := (p + 1 : ℝ) * K₂ + (p : ℝ) ^ 2 * (C * Real.exp 1) + 1
  have hA1 : 1 ≤ A := by
    have : 0 ≤ (p + 1 : ℝ) * K₂ + (p : ℝ) ^ 2 * (C * Real.exp 1) := by positivity
    linarith
  have hA0 : 0 < A := by linarith
  refine ⟨min (rateSeriesLam₀ p C) (1 / (2 * A)), lt_min (rateSeriesLam₀_pos p C)
    (by positivity), C * Real.exp 1 * ((p ! : ℝ) * 2 ^ p), by positivity, ?_⟩
  intro lam hlam hlam₀ msf kmult hmsf hk
  have hlam₀1 : lam < rateSeriesLam₀ p C := lt_of_lt_of_le hlam₀ (min_le_left _ _)
  have hlam₀2 : lam ≤ 1 / (2 * A) := (lt_of_lt_of_le hlam₀ (min_le_right _ _)).le
  have hsmall := rateSeriesConst_mul_sq_le p C hlam.le hlam₀1
  have hlam1 : lam ≤ 1 := by
    refine hlam₀2.trans ?_
    rw [div_le_one (by positivity)]
    linarith
  have hBp : K₂ * lam ^ 2 * (p + 1) ≤ 1 := by
    have := mul_sq_le_half_of_le (X := (p + 1 : ℝ) * K₂) (by positivity)
      (by have : 0 ≤ (p : ℝ) ^ 2 * (C * Real.exp 1) := by positivity
          linarith) hA1 hlam.le hlam₀2
    nlinarith
  have hB : K₂ * lam ^ 2 < 1 := by
    have hp1 : (1 : ℝ) ≤ p + 1 := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
    have : K₂ * lam ^ 2 ≤ K₂ * lam ^ 2 * (p + 1) :=
      le_mul_of_one_le_right (by positivity) hp1
    have := mul_sq_le_half_of_le (X := (p + 1 : ℝ) * K₂) (by positivity)
      (by have : 0 ≤ (p : ℝ) ^ 2 * (C * Real.exp 1) := by positivity
          linarith) hA1 hlam.le hlam₀2
    nlinarith
  have hsmall2 : (p : ℝ) ^ 2 * (C * Real.exp 1) * lam ^ 2 ≤ 1 / 2 :=
    mul_sq_le_half_of_le (by positivity)
      (by have : 0 ≤ (p + 1 : ℝ) * K₂ := by positivity
          linarith) hA1 hlam.le hlam₀2
  refine ⟨strictConvexOn_rateFunction_simplex hk hlam.le hsmall hB 0,
    existsUnique_isMinOn_rateFunction hp hk hlam.le hsmall hB, fun γ hγ hmin => ?_⟩
  refine ⟨pos_of_isMinOn_rateFunction hk hlam.le hsmall hγ hmin, fun i hi => ⟨?_, ?_⟩⟩
  · exact le_minimizer hk hlam hlam1 hsmall hC hmsf hBp hsmall2 hγ hmin i hi
  · have h := minimizer_le hk hlam hsmall hC hmsf hBp hγ hmin i hi
    have h1 : (1 : ℝ) ≤ (p ! : ℝ) * 2 ^ p := by
      have : (1 : ℝ) ≤ p ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero p)
      have : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
      nlinarith
    calc γ i ≤ C * Real.exp 1 * lam ^ (2 * (i : ℕ)) := h
      _ ≤ C * Real.exp 1 * ((p ! : ℝ) * 2 ^ p) * lam ^ (2 * (i : ℕ)) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) h1) (by positivity)

end Packaged

end MultipoleBKT

end
