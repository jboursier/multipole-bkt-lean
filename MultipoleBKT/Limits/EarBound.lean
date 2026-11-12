/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Tail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The bound along one ear

See (A.30).

`ear_bound_endpoints` is the displayed two-endpoint inequality, proved by
bounding the endpoint maxima by the endpoint radii and using the reciprocal
arithmetic inequality. `ear_bound_exceptional` deletes one specified edge.
The forest proof uses this only in the ear containing the global longest edge.
The endpoints need not differ and the ear may have two edges.

`oddWeight` is the distributed-tail weight used by the multigraph
majorants.

-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open Finset

/-- The odd-edge weight `ω(t) = t^{-2} min(1, R/t)^{2θ}`. -/
noncomputable def oddWeight (R θ t : ℝ) : ℝ := (t ^ 2)⁻¹ * min 1 (R / t) ^ (2 * θ)

/-- `∏_{j=1}^h s_{j-1} s_j = s₀ s_h ∏_{0<j<h} s_j²` for `h ≥ 1`. -/
theorem prod_consecutive (s : ℕ → ℝ) {h : ℕ} (hh : 1 ≤ h) :
    ∏ j ∈ Icc 1 h, (s (j - 1) * s j) = s 0 * s h * ∏ j ∈ Ioo 0 h, s j ^ 2 := by
  induction h, hh using Nat.le_induction with
  | base =>
    have : Ioo 0 1 = (∅ : Finset ℕ) := by ext j; simp only [mem_Ioo, notMem_empty, iff_false]; omega
    simp [this]
  | succ n hn ih =>
    have hI : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    rw [hI, prod_insert (by simp), ih, Nat.add_sub_cancel]
    have : Ioo 0 (n + 1) = insert n (Ioo 0 n) := by
      ext j
      simp only [mem_Ioo, mem_insert]
      omega
    rw [this, prod_insert (by simp)]
    ring

/-- Bounds before opening an ear. The first uses all distance maxima, and the
second uses the two endpoint radii in the first and last maxima. -/
private theorem ear_bound_numerators {h : ℕ} (hh : 2 ≤ h) (s d a : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hd : ∀ j ∈ Icc 1 h, 0 < d j) (ha0 : ∀ j ∈ Icc 1 h, 0 ≤ a j)
    (ha : ∀ j ∈ Icc 1 h, a j ≤ s (j - 1) * s j / (d j * max (d j) (max (s (j - 1)) (s j)))) :
    (∏ j ∈ Icc 1 h, a j) * (∏ j ∈ Icc 1 h, d j ^ 2) ≤
      (∏ j ∈ Ioo 0 h, s j ^ 2) * (s 0 * s h) ∧
    (∏ j ∈ Icc 1 h, a j) * (∏ j ∈ Icc 1 h, d j ^ 2) ≤
      (∏ j ∈ Ioo 0 h, s j ^ 2) * (d 1 * d h) := by
  set M : ℕ → ℝ := fun j => max (d j) (max (s (j - 1)) (s j)) with hM
  have hMd : ∀ j, d j ≤ M j := fun j => le_max_left _ _
  have hdpos : ∀ j ∈ Icc 1 h, 0 < d j * M j := fun j hj =>
    mul_pos (hd j hj) ((hd j hj).trans_le (hMd j))
  set Sint := ∏ j ∈ Ioo 0 h, s j ^ 2 with hSint
  set D2 := ∏ j ∈ Icc 1 h, d j ^ 2 with hD2
  have hD20 : 0 < D2 := prod_pos fun j hj => pow_pos (hd j hj) 2
  set DM := ∏ j ∈ Icc 1 h, (d j * M j) with hDM
  have hDM0 : 0 < DM := prod_pos hdpos
  -- step 1: `P ≤ s₀ s_h Sint / ∏ (d_j M_j)`
  have h1 : ∏ j ∈ Icc 1 h, a j ≤ s 0 * s h * Sint / DM := by
    calc ∏ j ∈ Icc 1 h, a j ≤ ∏ j ∈ Icc 1 h, (s (j - 1) * s j / (d j * M j)) :=
          prod_le_prod₀ ha0 ha
      _ = s 0 * s h * Sint / DM := by
          rw [prod_div_distrib, prod_consecutive s (by omega)]
  -- step 2a: `∏ d_j² ≤ ∏ d_j M_j`
  have h2a : D2 ≤ DM := prod_le_prod₀ (fun j hj => sq_nonneg _) fun j hj => by
    rw [sq]; exact mul_le_mul_of_nonneg_left (hMd j) (hd j hj).le
  -- step 2b: `s₀ s_h ∏ d_j² ≤ d₁ d_h ∏ d_j M_j`
  have h1h : (1 : ℕ) ≠ h := by omega
  have hmem1 : 1 ∈ Icc 1 h := by simp; omega
  have hmemh : h ∈ (Icc 1 h).erase 1 := by simp; omega
  have h2b : s 0 * s h * D2 ≤ d 1 * d h * DM := by
    have e1 : ∀ f : ℕ → ℝ, ∏ j ∈ Icc 1 h, f j = f 1 * (f h * ∏ j ∈ ((Icc 1 h).erase 1).erase h, f j) := by
      intro f
      rw [← mul_prod_erase _ _ hmem1, ← mul_prod_erase _ _ hmemh]
    rw [hD2, hDM, e1, e1]
    have hrest : ∏ j ∈ ((Icc 1 h).erase 1).erase h, d j ^ 2 ≤
        ∏ j ∈ ((Icc 1 h).erase 1).erase h, (d j * M j) :=
      prod_le_prod₀ (fun j _ => sq_nonneg _) fun j hj => by
        have hj' : j ∈ Icc 1 h := mem_of_mem_erase (mem_of_mem_erase hj)
        rw [sq]; exact mul_le_mul_of_nonneg_left (hMd j) (hd j hj').le
    have hM1 : s 0 ≤ M 1 := (le_max_left _ _).trans (le_max_right _ _)
    have hMh : s h ≤ M h := (le_max_right _ _).trans (le_max_right _ _)
    have hd1 := hd 1 hmem1
    have hdh := hd h (mem_of_mem_erase hmemh)
    have hr0 : 0 ≤ ∏ j ∈ ((Icc 1 h).erase 1).erase h, d j ^ 2 := prod_nonneg fun j _ => sq_nonneg _
    have hs0' := hs 0
    have hsh' := hs h
    calc s 0 * s h * (d 1 ^ 2 * (d h ^ 2 * ∏ j ∈ ((Icc 1 h).erase 1).erase h, d j ^ 2))
        = d 1 * d h * ((d 1 * s 0) * ((d h * s h) *
            ∏ j ∈ ((Icc 1 h).erase 1).erase h, d j ^ 2)) := by ring
      _ ≤ d 1 * d h * ((d 1 * M 1) * ((d h * M h) *
            ∏ j ∈ ((Icc 1 h).erase 1).erase h, (d j * M j))) := by gcongr
  have hP : (∏ j ∈ Icc 1 h, a j) * DM ≤ s 0 * s h * Sint := (le_div_iff₀ hDM0).1 h1
  constructor
  · calc (∏ j ∈ Icc 1 h, a j) * D2 ≤ (∏ j ∈ Icc 1 h, a j) * DM :=
          mul_le_mul_of_nonneg_left h2a (prod_nonneg ha0)
      _ ≤ Sint * (s 0 * s h) := by simpa only [mul_assoc, mul_left_comm, mul_comm] using hP
  · apply (mul_le_mul_iff_left₀ hDM0).1
    calc ((∏ j ∈ Icc 1 h, a j) * D2) * DM = ((∏ j ∈ Icc 1 h, a j) * DM) * D2 := by ring
      _ ≤ (s 0 * s h * Sint) * D2 := mul_le_mul_of_nonneg_right hP hD20.le
      _ = Sint * (s 0 * s h * D2) := by ring
      _ ≤ Sint * (d 1 * d h * DM) := mul_le_mul_of_nonneg_left h2b (by positivity)
      _ = (Sint * (d 1 * d h)) * DM := by ring

/-- The paper's two-endpoint arithmetic inequality on an ear.
See the proof of (A.30).
The endpoints may agree, and `h = 2` is included. -/
theorem ear_bound_endpoints {h : ℕ} (hh : 2 ≤ h) (s d a : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hd : ∀ j ∈ Icc 1 h, 0 < d j) (ha0 : ∀ j ∈ Icc 1 h, 0 ≤ a j)
    (ha : ∀ j ∈ Icc 1 h, a j ≤ s (j - 1) * s j / (d j * max (d j) (max (s (j - 1)) (s j)))) :
    ∏ j ∈ Icc 1 h, a j ≤ (1 / 2 : ℝ) * (∏ j ∈ Ioo 0 h, s j ^ 2) *
      ((∏ j ∈ (Icc 1 h).erase 1, (d j ^ 2)⁻¹) + ∏ j ∈ (Icc 1 h).erase h, (d j ^ 2)⁻¹) := by
  have hb := (ear_bound_numerators hh s d a hs hd ha0 ha).2
  have hD : 0 < ∏ j ∈ Icc 1 h, d j ^ 2 := prod_pos fun j hj => pow_pos (hd j hj) 2
  have herase : ∀ i ∈ Icc 1 h, ∏ j ∈ (Icc 1 h).erase i, (d j ^ 2)⁻¹ =
      d i ^ 2 / ∏ j ∈ Icc 1 h, d j ^ 2 := by
    intro i hi
    rw [← mul_prod_erase _ _ hi, prod_inv_distrib]
    have hi0 : d i ^ 2 ≠ 0 := (pow_pos (hd i hi) 2).ne'
    field_simp [ne_of_gt (hd i hi)]
  rw [herase 1 (by simp; omega), herase h (by simp; omega)]
  rw [← add_div, ← mul_div_assoc]
  apply (le_div_iff₀ hD).2
  have hS : 0 ≤ ∏ j ∈ Ioo 0 h, s j ^ 2 := prod_nonneg fun j _ => sq_nonneg _
  have hAM : d 1 * d h ≤ (d 1 ^ 2 + d h ^ 2) / 2 := by nlinarith [sq_nonneg (d 1 - d h)]
  calc (∏ j ∈ Icc 1 h, a j) * (∏ j ∈ Icc 1 h, d j ^ 2)
      ≤ (∏ j ∈ Ioo 0 h, s j ^ 2) * (d 1 * d h) := hb
    _ ≤ (∏ j ∈ Ioo 0 h, s j ^ 2) * ((d 1 ^ 2 + d h ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left hAM hS
    _ = _ := by field_simp

/-- In the exceptional ear, delete the specified edge and retain its quadratic
factor. The forest proof applies this only to the longest edge of the whole ear
family, and only in the large-distance case.
See (A.30). -/
theorem ear_bound_exceptional {h : ℕ} (hh : 2 ≤ h) (s d a : ℕ → ℝ)
    (hs : ∀ j, 0 < s j) {R : ℝ} (hs0 : s 0 ≤ R) (hsh : s h ≤ R)
    (hd : ∀ j ∈ Icc 1 h, 0 < d j) (ha0 : ∀ j ∈ Icc 1 h, 0 ≤ a j)
    (ha : ∀ j ∈ Icc 1 h,
      a j ≤ s (j - 1) * s j / (d j * max (d j) (max (s (j - 1)) (s j))))
    {jx : ℕ} (hjx : jx ∈ Icc 1 h) :
    ∏ j ∈ Icc 1 h, a j ≤ (∏ j ∈ Ioo 0 h, s j ^ 2) *
      (R ^ 2 / d jx ^ 2) * ∏ j ∈ (Icc 1 h).erase jx, (d j ^ 2)⁻¹ := by
  have hb := (ear_bound_numerators hh s d a hs hd ha0 ha).1
  have hD : 0 < ∏ j ∈ Icc 1 h, d j ^ 2 := prod_pos fun j hj => pow_pos (hd j hj) 2
  have hR : 0 ≤ R := (hs 0).le.trans hs0
  have hends : s 0 * s h ≤ R ^ 2 := by
    simpa only [sq] using mul_le_mul hs0 hsh (hs h).le hR
  have hbound : ∏ j ∈ Icc 1 h, a j ≤
      (∏ j ∈ Ioo 0 h, s j ^ 2) * R ^ 2 / ∏ j ∈ Icc 1 h, d j ^ 2 :=
    (le_div_iff₀ hD).2 (hb.trans
      (mul_le_mul_of_nonneg_left hends (prod_nonneg fun j _ => sq_nonneg _)))
  refine hbound.trans_eq ?_
  rw [← mul_prod_erase _ _ hjx, prod_inv_distrib]
  ring



end Limits

end MultipoleBKT

end
