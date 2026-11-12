/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Event
public import MultipoleBKT.Appendix.MultipoleIntegral.LowerGeometry

/-!
# The paper's chain inside the lower event

See Lemma A.3. Positive endpoints are spaced by `9λ/2`, negative endpoints
are shifted by `3λ/2`, and all non-root balls have radius `λ/16`.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral.RouteChain

open MeasureTheory Set Finset
open TwoComponentCoulomb (box)

variable {ι : Type*} {k N : ℕ} {lam M : ℝ} {σ : ι ≃ Fin k} {root : ι}

/-- The positive endpoint centre, measured from the positive root. -/
noncomputable def centre (lam : ℝ) (σ : ι ≃ Fin k) (X : ℂ) (i : ι) : ℂ :=
  X + ((9 / 2 * (σ i : ℕ) * lam : ℝ) : ℂ)

/-- The exact small-ball chain specified in the paper. -/
def Chain (N : ℕ) (lam : ℝ) (σ : ι ≃ Fin k) (root : ι) (c : ι → ℂ × ℂ) : Prop :=
  (c root).1 ∈ innerBox N (5 * k * lam) ∧
    (∀ i, i ≠ root → ‖(c i).1 - centre lam σ (c root).1 i‖ < lam / 16) ∧
    ∀ i, ‖(c i).2 - (centre lam σ (c root).1 i + ((3 * lam / 2 : ℝ) : ℂ))‖ < lam / 16

variable {c : ι → ℂ × ℂ}

/-- The root also satisfies the positive-endpoint error estimate. -/
theorem Chain.fst_error (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) (i : ι) :
    ‖(c i).1 - centre lam σ (c root).1 i‖ < lam / 16 := by
  by_cases hi : i = root
  · subst hi
    simp only [centre, hroot, Nat.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero, add_zero,
      sub_self, norm_zero]
    positivity
  · exact hc.2.1 i hi

/-- Two endpoint errors perturb their distance by at most their sum. -/
theorem distance_error {a b z w : ℂ} {ε : ℝ} (ha : ‖a - z‖ < ε) (hb : ‖b - w‖ < ε) :
    |‖a - b‖ - ‖z - w‖| < 2 * ε := by
  have he : (a - b) - (z - w) = (a - z) - (b - w) := by ring
  have hn := abs_norm_sub_norm_le (a - b) (z - w)
  rw [he] at hn
  exact hn.trans_lt ((norm_sub_le _ _).trans_lt (by linarith))

/-- Distances between centres on the real axis. -/
theorem centre_distance (hlam : 0 < lam) (X : ℂ) (i j : ι) (a b : ℝ) :
    ‖(centre lam σ X i + ((a * lam : ℝ) : ℂ)) -
        (centre lam σ X j + ((b * lam : ℝ) : ℂ))‖ =
      |9 / 2 * ((σ i : ℕ) - (σ j : ℕ) : ℝ) + a - b| * lam := by
  have he : (centre lam σ X i + ((a * lam : ℝ) : ℂ)) -
        (centre lam σ X j + ((b * lam : ℝ) : ℂ)) =
      (((9 / 2 * ((σ i : ℕ) - (σ j : ℕ) : ℝ) + a - b) * lam : ℝ) : ℂ) := by
    simp only [centre]
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hlam]

/-- All four cross distances exceed `2λ`, even for neighbouring dipoles. -/
theorem Chain.cross_bounds (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) {i j : ι} (hij : i ≠ j) :
    2 * lam < dipoleDist (c i) (c j) := by
  have hn : (σ i : ℕ) ≠ (σ j : ℕ) := fun h => hij (σ.injective (Fin.ext h))
  have hgap : (1 : ℝ) ≤ |((σ i : ℕ) : ℝ) - ((σ j : ℕ) : ℝ)| := by
    rcases Nat.lt_or_gt_of_ne hn with h | h
    · have hh : ((σ i : ℕ) : ℝ) + 1 ≤ (σ j : ℕ) := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have hh : ((σ j : ℕ) : ℝ) + 1 ≤ (σ i : ℕ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
  have key (a b : ℂ) (u v : ℝ) (hu : 0 ≤ u ∧ u ≤ 3 / 2) (hv : 0 ≤ v ∧ v ≤ 3 / 2)
      (ha : ‖a - (centre lam σ (c root).1 i + ((u * lam : ℝ) : ℂ))‖ < lam / 16)
      (hb : ‖b - (centre lam σ (c root).1 j + ((v * lam : ℝ) : ℂ))‖ < lam / 16) :
      2 * lam < ‖a - b‖ := by
    have hd := distance_error ha hb
    rw [centre_distance hlam] at hd
    have htri := abs_sub_abs_le_abs_sub (9 / 2 * (((σ i : ℕ) : ℝ) - (σ j : ℕ))) (v - u)
    have huv : |v - u| ≤ 3 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 2)] at htri
    have hcent : 3 ≤ |9 / 2 * (((σ i : ℕ) : ℝ) - (σ j : ℕ)) + u - v| := by
      have he : 9 / 2 * (((σ i : ℕ) : ℝ) - (σ j : ℕ)) - (v - u) =
          9 / 2 * (((σ i : ℕ) : ℝ) - (σ j : ℕ)) + u - v := by ring
      rw [he] at htri
      linarith [le_abs_self (|9 / 2 * (((σ i : ℕ) : ℝ) - (σ j : ℕ))| - |v - u|)]
    have := (abs_lt.mp hd).1
    nlinarith
  have hx (l : ι) : ‖(c l).1 - (centre lam σ (c root).1 l + (((0 : ℝ) * lam : ℝ) : ℂ))‖ < lam / 16 := by
    simpa using hc.fst_error hlam hroot l
  have hy (l : ι) : ‖(c l).2 - (centre lam σ (c root).1 l + (((3 / 2 : ℝ) * lam : ℝ) : ℂ))‖ < lam / 16 := by
    simpa only [show (3 / 2 : ℝ) * lam = 3 * lam / 2 by ring] using hc.2.2 l
  unfold dipoleDist
  exact lt_min (lt_min (key _ _ 0 0 (by norm_num) (by norm_num) (hx i) (hx j))
    (key _ _ 0 (3/2) (by norm_num) (by norm_num) (hx i) (hy j)))
    (lt_min (key _ _ (3/2) 0 (by norm_num) (by norm_num) (hy i) (hx j))
      (key _ _ (3/2) (3/2) (by norm_num) (by norm_num) (hy i) (hy j)))

/-- Each dipole has radius strictly between `λ` and `2λ`. -/
theorem Chain.radii (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) (i : ι) :
    lam < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ < 2 * lam := by
  have h := distance_error (hc.fst_error hlam hroot i) (hc.2.2 i)
  have he : centre lam σ (c root).1 i -
      (centre lam σ (c root).1 i + ((3 * lam / 2 : ℝ) : ℂ)) = -((3 * lam / 2 : ℝ) : ℂ) := by ring
  rw [he, norm_neg, norm_real_of_nonneg (by positivity)] at h
  exact ⟨by linarith [(abs_lt.mp h).1], by linarith [(abs_lt.mp h).2]⟩

/-- The specified chain belongs to `𝒞`. -/
theorem Chain.event (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) : Event lam σ c := by
  refine ⟨hc.radii hlam hroot, fun i j hij => ⟨hc.cross_bounds hlam hroot (fun h => by
    rw [h] at hij; omega), ?_⟩⟩
  have h := distance_error (hc.2.2 i) (hc.fst_error hlam hroot j)
  have hj : ((σ j : ℕ) : ℝ) = (σ i : ℕ) + 1 := by exact_mod_cast hij
  have he : (centre lam σ (c root).1 i + ((3 * lam / 2 : ℝ) : ℂ)) -
      centre lam σ (c root).1 j = ((-3 * lam : ℝ) : ℂ) := by
    simp only [centre]
    rw [hj]
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_of_neg (by linarith : -3 * lam < 0)] at h
  have hd : dipoleDist (c i) (c j) ≤ ‖(c i).2 - (c j).1‖ :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith [(abs_lt.mp h).2]

/-- The chain satisfies all stable-pair constraints. -/
theorem Chain.stable (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) {i j : ι} (hij : i ≠ j) : IsStableDipolePair (c i) (c j) := by
  have hd := hc.cross_bounds hlam hroot hij
  have hr := (hc.radii hlam hroot i).2
  apply isStableDipolePair_of_lt
  · exact (min_le_left _ _).trans_lt (hr.trans (hd.trans_le ((min_le_left _ _).trans (min_le_right _ _))))
  · rw [norm_sub_rev (c j).1 (c i).2]
    exact (min_le_left _ _).trans_lt (hr.trans (hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))))

/-- Consecutive chain dipoles are linked for `M ≥ 4`. -/
theorem Chain.linked (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) (hM : 4 ≤ M) {i j : ι}
    (hij : (σ j : ℕ) = σ i + 1) : MultipoleLinked M lam (c i) (c j) := by
  have hd := ((hc.event hlam hroot).2 i j hij).2
  change dipoleDist (c i) (c j) ≤ _
  have hm : lam ≤ min (max ‖(c i).1 - (c i).2‖ lam) (max ‖(c j).1 - (c j).2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  nlinarith

/-- All endpoints of the chain lie in the box. -/
theorem Chain.mem_box (hc : Chain N lam σ root c) (hlam : 0 < lam)
    (hroot : (σ root : ℕ) = 0) (i : ι) : c i ∈ box N ×ˢ box N := by
  have hY := hc.1
  simp only [innerBox, Complex.mem_reProdIm, Set.mem_Icc] at hY
  have hb := ball_subset_box hY.1.1 (by linarith [hY.1.2]) hY.2.1 (by linarith [hY.2.2])
  have hi : ((σ i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast (σ i).2
  have hx := hc.fst_error hlam hroot i
  have hy := hc.2.2 i
  have hz : ‖centre lam σ (c root).1 i - (c root).1‖ = 9 / 2 * (σ i : ℕ) * lam := by
    simp only [centre, add_sub_cancel_left]
    exact norm_real_of_nonneg (by positivity)
  have hz' : ‖(centre lam σ (c root).1 i + ((3 * lam / 2 : ℝ) : ℂ)) - (c root).1‖ =
      (9 / 2 * (σ i : ℕ) + 3 / 2) * lam := by
    have he : (centre lam σ (c root).1 i + ((3 * lam / 2 : ℝ) : ℂ)) - (c root).1 =
        (((9 / 2 * (σ i : ℕ) + 3 / 2) * lam : ℝ) : ℂ) := by
      simp only [centre]; push_cast; ring
    rw [he, norm_real_of_nonneg (by positivity)]
  constructor
  · apply hb
    rw [Metric.mem_ball, dist_eq_norm]
    have := norm_sub_le_norm_sub_add_norm_sub (c i).1 (centre lam σ (c root).1 i) (c root).1
    rw [hz] at this
    nlinarith
  · apply hb
    rw [Metric.mem_ball, dist_eq_norm]
    have := norm_sub_le_norm_sub_add_norm_sub (c i).2
      (centre lam σ (c root).1 i + ((3 * lam / 2 : ℝ) : ℂ)) (c root).1
    rw [hz'] at this
    nlinarith

end MultipoleBKT.MultipoleIntegral.RouteChain

end
