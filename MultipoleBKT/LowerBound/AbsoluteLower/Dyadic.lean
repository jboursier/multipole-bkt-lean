/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Packing
public import MultipoleBKT.LowerBound.Peeling.TreeCount
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Dyadic sums and the geometry of separated dipoles

Tools for the proof of Lemma 4.56.

* Geometric sums over finite sets of exponents: `sum_two_pow_le_of_lt` (`∑_{a ∈ S} 2^a ≤ 2Y`
  when every `2^a < Y`), `sum_inv_pow_le` (`∑_{a ∈ S} q^{-a} ≤ q/(q - 1)`) and
  `sum_mul_pow_le` (`∑_{h ∈ S} h x^h ≤ x/(1 - x)²`).
* `sum_le_sum_fiberwise_snd`: a sum over a finite set of pairs `(a, b)` grouped by `b`.
* Dipoles: `exists_endpoint_near` (an endpoint of `e` within `dist(d, e) + |d|` of the first point
  of `d`), `dipoleDist_le_norm_of_endpoints`, `mul_min_lt_dipoleDist` (on `𝓑^c`,
  `d_ij > M min(r_i, r_j)`) and `multipoleLinked_of_le` (conversely `d_ij ≤ M min(r_i, r_j)` links
  the dipoles).
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SetPartition Peeling

/-! ### Geometric sums -/

section Sums

/-- `∑_{a ∈ S} 2^a ≤ 2Y` when `2^a < Y` for every `a ∈ S` (and `Y ≥ 0`). -/
theorem sum_two_pow_le_of_lt (S : Finset ℕ) {Y : ℝ} (hY : 0 ≤ Y)
    (h : ∀ a ∈ S, (2 : ℝ) ^ a < Y) : ∑ a ∈ S, (2 : ℝ) ^ a ≤ 2 * Y := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [sum_empty]
    linarith
  set m := S.max' hS
  have hsub : S ⊆ range (m + 1) := fun a ha => mem_range.2 (Nat.lt_succ_of_le (le_max' S a ha))
  have hgeom : ∑ a ∈ range (m + 1), (2 : ℝ) ^ a = 2 ^ (m + 1) - 1 := by
    rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  have hm := h m (max'_mem S hS)
  calc ∑ a ∈ S, (2 : ℝ) ^ a ≤ ∑ a ∈ range (m + 1), (2 : ℝ) ^ a :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = 2 ^ (m + 1) - 1 := hgeom
    _ ≤ 2 * Y := by rw [pow_succ]; linarith

/-- `∑_{a ∈ S} (1/q)^a ≤ q / (q - 1)` for `q > 1`. -/
theorem sum_inv_pow_le (S : Finset ℕ) {q : ℝ} (hq : 1 < q) :
    ∑ a ∈ S, (1 / q) ^ a ≤ q / (q - 1) := by
  have h0 : 0 ≤ 1 / q := by positivity
  have h1 : 1 / q < 1 := by rw [div_lt_one (by linarith)]; exact hq
  have hsum := summable_geometric_of_lt_one h0 h1
  refine (hsum.sum_le_tsum S fun _ _ => by positivity).trans_eq ?_
  rw [tsum_geometric_of_lt_one h0 h1]
  field_simp

/-- `∑_{h ∈ S} h x^h ≤ x / (1 - x)²` for `0 ≤ x < 1`. -/
theorem sum_mul_pow_le (S : Finset ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∑ h ∈ S, (h : ℝ) * x ^ h ≤ x / (1 - x) ^ 2 := by
  have hnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1
  have hsum : Summable fun n : ℕ => (n : ℝ) * x ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  refine (hsum.sum_le_tsum S fun _ _ => by positivity).trans_eq ?_
  exact tsum_coe_mul_geometric_of_norm_lt_one hnorm

/-- A sum over a finite set of pairs, grouped by the second coordinate. -/
theorem sum_eq_sum_fiberwise_snd (T : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℝ) :
    ∑ q ∈ T, g q = ∑ b ∈ T.image Prod.snd, ∑ a ∈ (T.filter fun q => q.2 = b).image Prod.fst,
      g (a, b) := by
  rw [← sum_fiberwise_of_maps_to (s := T) (t := T.image Prod.snd) (g := Prod.snd)
    fun q hq => mem_image_of_mem _ hq]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_image]
  · refine sum_congr rfl fun q hq => ?_
    rw [← (mem_filter.1 hq).2]
  · intro q hq q' hq' h
    exact Prod.ext h ((mem_filter.1 hq).2.trans (mem_filter.1 hq').2.symm)

end Sums

/-! ### Dipoles -/

section Dipoles

variable {M lam : ℝ} {d e : ℂ × ℂ}

/-- Some endpoint `b` of the dipole `e` satisfies `|b - x| ≤ dist(d, e) + |x - y|` for
`d = (x, y)`. -/
theorem exists_endpoint_near (d e : ℂ × ℂ) :
    ∃ b, (b = e.1 ∨ b = e.2) ∧ ‖b - d.1‖ ≤ dipoleDist d e + ‖d.1 - d.2‖ := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_dipoleDist_eq d e
  refine ⟨b, hb, ?_⟩
  have hab : ‖a - d.1‖ ≤ ‖d.1 - d.2‖ := by
    rcases ha with rfl | rfl
    · simp
    · rw [norm_sub_rev]
  calc ‖b - d.1‖ = ‖(b - a) + (a - d.1)‖ := by congr 1; ring
    _ ≤ ‖b - a‖ + ‖a - d.1‖ := norm_add_le _ _
    _ ≤ dipoleDist d e + ‖d.1 - d.2‖ := by rw [norm_sub_rev, ← h]; linarith

/-- The distance of two dipoles is at most the distance of any two of their endpoints. -/
theorem dipoleDist_le_norm_of_endpoints {a b : ℂ} (ha : a = d.1 ∨ a = d.2)
    (hb : b = e.1 ∨ b = e.2) : dipoleDist d e ≤ ‖a - b‖ :=
  dipoleDist_le ha hb

/-- On `𝓑_ij^c`, `d_ij > M min(r_i, r_j)`. -/
theorem mul_min_lt_dipoleDist (hM : 0 ≤ M) (h : ¬ MultipoleLinked M lam d e) :
    M * min ‖d.1 - d.2‖ ‖e.1 - e.2‖ < dipoleDist d e :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_left (min_le_min (le_max_left _ _) (le_max_left _ _)) hM)
    (not_le.1 h)

/-- `d_ij ≤ M min(r_i, r_j)` implies `𝓑_ij`. -/
theorem multipoleLinked_of_le (hM : 0 ≤ M)
    (h : dipoleDist d e ≤ M * min ‖d.1 - d.2‖ ‖e.1 - e.2‖) : MultipoleLinked M lam d e :=
  h.trans (mul_le_mul_of_nonneg_left (min_le_min (le_max_left _ _) (le_max_left _ _)) hM)

/-- The triangle inequality through a dipole:
`dist(D', D'') ≤ dist(D, D') + |D| + dist(D, D'')`. -/
theorem dipoleDist_le_add (d e e' : ℂ × ℂ) :
    dipoleDist e e' ≤ dipoleDist d e + ‖d.1 - d.2‖ + dipoleDist d e' :=
  dipoleDist_le_add_length d e e'

end Dipoles

end AbsoluteLower

end MultipoleBKT

end
