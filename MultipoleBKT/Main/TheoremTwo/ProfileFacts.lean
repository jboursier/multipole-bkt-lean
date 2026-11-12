/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.Simplex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Theorem 2: profiles and entropy inequalities

Elementary steps in the proof of Theorem 2.
The floor profile and its compensating first coordinate are constructed in Steps 1 and 3. `exists_profile_sharp` bounds the rounding by
`D_p/N`, and `exists_profile` exports the `p²/N` bound.
Step 3 uses the segment from `z` to `max(z, γ)`.
The tangent-line entropy inequality supports the rate comparison in Step 3.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace TheoremTwo

/-! ### The entropy tangent inequality

The relative entropy is used to prove the tangent bound in Step 3 of the proof of Theorem 2.
-/

/-- The relative entropy density `a log(a/b) - a + b` (with `0 log 0 = 0`). -/
noncomputable def relEnt (a b : ℝ) : ℝ :=
  a * (Real.log a - Real.log b) - a + b

theorem relEnt_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ relEnt a b := by
  unfold relEnt
  rcases ha.eq_or_lt with rfl | ha'
  · simp [hb.le]
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos ha' hb)
    rw [Real.log_div ha'.ne' hb.ne', inv_div] at h
    have : a * (1 - b / a) = a - b := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h ha'.le]

/-- The tangent-line inequality for `s ↦ s (A + log s)` at `η > 0`:
`η (A + log η) - u (A + log u) ≤ (A + 1 + log η)(η - u)` for `u ≥ 0`. -/
theorem entropy_sub_le_tangent {A u η : ℝ} (hu : 0 ≤ u) (hη : 0 < η) :
    η * (A + Real.log η) - u * (A + Real.log u) ≤ (A + 1 + Real.log η) * (η - u) := by
  have h := relEnt_nonneg hu hη
  unfold relEnt at h
  nlinarith [h]

/-! ### Profiles -/

/-- `n/N ∈ Δ_{p,x}` with `x = 1 - ∑ i n_i / N ∈ [0,1]`. -/
theorem profile_mem_simplex {p N : ℕ} (hN : 1 ≤ N) {n : Fin p → ℕ}
    (hn : ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N) :
    (fun i => (n i : ℝ) / N) ∈
        simplex p (1 - (∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) / N) ∧
      1 - ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) : ℝ) ≤ N := by exact_mod_cast hn
  refine ⟨⟨fun i => ⟨by positivity, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [div_le_one hN0]
    have h1 : n i ≤ ((i : ℕ) + 1) * n i := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have h2 : ((i : ℕ) + 1) * n i ≤ ∑ j : Fin p, ((j : ℕ) + 1) * n j :=
      Finset.single_le_sum (f := fun j : Fin p => ((j : ℕ) + 1) * n j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    exact_mod_cast h1.trans (h2.trans hn)
  · rw [sub_sub_cancel]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · rw [sub_nonneg, div_le_one hN0]
    exact hS
  · have : 0 ≤ ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) : ℝ) / N := by positivity
    linarith

/-- Sum of the profile weights. For `p ≥ 1` this is the paper's
`D_p = 1 + ∑_{i=2}^p i` in Step 3 of the proof of Theorem 2. -/
noncomputable def roundingRadius (p : ℕ) : ℝ := ∑ i : Fin p, ((i : ℕ) + 1 : ℝ)

theorem one_le_roundingRadius {p : ℕ} (hp : 1 ≤ p) : 1 ≤ roundingRadius p := by
  have h := Finset.single_le_sum (f := fun i : Fin p => ((i : ℕ) + 1 : ℝ))
    (by intro i _; positivity) (Finset.mem_univ (⟨0, hp⟩ : Fin p))
  simpa [roundingRadius] using h

theorem roundingRadius_le_sq (p : ℕ) : roundingRadius p ≤ (p : ℝ) ^ 2 := by
  calc roundingRadius p ≤ ∑ _i : Fin p, (p : ℝ) := Finset.sum_le_sum fun i _ => by
          exact_mod_cast i.2
    _ = (p : ℝ) ^ 2 := by simp [pow_two]

/-- **Profiles near a point of `Δ_{p,0}`** in Steps 1 and 3 of the proof of Theorem 2. -/
theorem exists_profile_sharp {p : ℕ} (hp : 1 ≤ p) {η : Fin p → ℝ} (hη : η ∈ simplex p 0) {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ n : Fin p → ℕ, ∑ i : Fin p, ((i : ℕ) + 1) * n i = N ∧
      (∀ i : Fin p, 1 ≤ (i : ℕ) → (n i : ℝ) ≤ N * η i) ∧
      ∀ i : Fin p, |(n i : ℝ) / N - η i| ≤ roundingRadius p / N := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set e0 : Fin p := ⟨0, hp⟩
  set m : Fin p → ℕ := fun i => ⌊(N : ℝ) * η i⌋₊
  have hηnn : ∀ i, 0 ≤ η i := fun i => (hη.1 i).1
  have hm_le : ∀ i, (m i : ℝ) ≤ N * η i := fun i => Nat.floor_le (by have := hηnn i; positivity)
  have hm_gt : ∀ i, (N : ℝ) * η i - 1 < m i := fun i => by
    have := Nat.lt_floor_add_one ((N : ℝ) * η i); linarith
  set S : ℕ := ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1) * m i
  have hsplit : ∀ f : Fin p → ℝ, ∑ i : Fin p, f i = f e0 + ∑ i ∈ Finset.univ.erase e0, f i :=
    fun f => (Finset.add_sum_erase _ _ (Finset.mem_univ e0)).symm
  have hηsum : η e0 + ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * η i = 1 := by
    have h := hη.2
    rw [hsplit] at h
    simpa [e0] using h
  have hSreal : (S : ℝ) ≤ N * ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * η i := by
    simp only [S]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hm_le i
    nlinarith [this]
  have hSN : S ≤ N := by
    have : (S : ℝ) ≤ N := by
      have h0 := hηnn e0
      nlinarith [hSreal, hηsum]
    exact_mod_cast this
  set n : Fin p → ℕ := fun i => if i = e0 then N - S else m i
  have hn0 : n e0 = N - S := by simp [n]
  have hni : ∀ i, i ≠ e0 → n i = m i := fun i hi => by simp [n, hi]
  have hi1 : ∀ i : Fin p, i ≠ e0 ↔ 1 ≤ (i : ℕ) := fun i => by
    constructor
    · intro h; by_contra h'; exact h (Fin.ext (by simp [e0]; omega))
    · intro h h'; rw [h'] at h; simp [e0] at h
  refine ⟨n, ?_, fun i hi => ?_, fun i => ?_⟩
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e0), hn0]
    have : ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1) * n i = S :=
      Finset.sum_congr rfl fun i hi => by rw [hni i (Finset.ne_of_mem_erase hi)]
    rw [this]
    simp only [e0, zero_add, one_mul]
    omega
  · rw [hni i ((hi1 i).mpr hi)]
    exact hm_le i
  · have hp2 : (1 : ℝ) ≤ roundingRadius p := one_le_roundingRadius hp
    by_cases hie : i = e0
    · subst hie
      rw [hn0, Nat.cast_sub hSN]
      -- `n_0/N - η_0 = ∑_{i ≠ 0} (i+1)(η_i - m_i/N) ∈ [0, p²/N]`
      have hdiff : ((N : ℝ) - S) / N - η e0 =
          ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * (η i - m i / N) := by
        have : (S : ℝ) = ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * m i := by
          simp only [S]; push_cast; rfl
        rw [this]
        have hη0 : η e0 = 1 - ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * η i := by
          linarith
        have hR : ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * (η i - m i / N) =
            ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * η i -
              (∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * m i) / N := by
          rw [Finset.sum_div, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [hR, hη0]
        field_simp
        ring
      rw [hdiff]
      have hterm : ∀ i ∈ Finset.univ.erase e0, 0 ≤ ((i : ℕ) + 1 : ℝ) * (η i - m i / N) ∧
          ((i : ℕ) + 1 : ℝ) * (η i - m i / N) ≤ ((i : ℕ) + 1 : ℝ) / N := by
        intro i _
        have h1 : (m i : ℝ) / N ≤ η i := by rw [div_le_iff₀ hN0]; linarith [hm_le i]
        have h2 : η i - m i / N < 1 / N := by
          have e : (η i - m i / N) * N = N * η i - m i := by field_simp
          rw [lt_div_iff₀ hN0, e]
          linarith [hm_gt i]
        constructor
        · exact mul_nonneg (by positivity) (by linarith)
        · calc ((i : ℕ) + 1 : ℝ) * (η i - m i / N) ≤ ((i : ℕ) + 1 : ℝ) * (1 / N) :=
                mul_le_mul_of_nonneg_left h2.le (by positivity)
            _ = ((i : ℕ) + 1 : ℝ) / N := by ring
      have hlo : 0 ≤ ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * (η i - m i / N) :=
        Finset.sum_nonneg fun i hi => (hterm i hi).1
      have hhi : ∑ i ∈ Finset.univ.erase e0, ((i : ℕ) + 1 : ℝ) * (η i - m i / N) ≤
          roundingRadius p / N := by
        refine (Finset.sum_le_sum fun i hi => (hterm i hi).2).trans ?_
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by
            intro i _ _; positivity)) hN0.le
      rw [abs_of_nonneg hlo]
      exact hhi
    · rw [hni i hie]
      have h1 : (m i : ℝ) / N ≤ η i := by rw [div_le_iff₀ hN0]; linarith [hm_le i]
      have h2 : η i - m i / N < 1 / N := by
        have e : (η i - m i / N) * N = N * η i - m i := by field_simp
        rw [lt_div_iff₀ hN0, e]
        linarith [hm_gt i]
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      calc η i - m i / N ≤ 1 / N := h2.le
        _ ≤ roundingRadius p / N := div_le_div_of_nonneg_right hp2 hN0.le

/-- The retained profile interface with the coarser `p²/N` bound. -/
theorem exists_profile {p : ℕ} (hp : 1 ≤ p) {η : Fin p → ℝ} (hη : η ∈ simplex p 0) {N : ℕ}
    (hN : 1 ≤ N) :
    ∃ n : Fin p → ℕ, ∑ i : Fin p, ((i : ℕ) + 1) * n i = N ∧
      (∀ i : Fin p, 1 ≤ (i : ℕ) → (n i : ℝ) ≤ N * η i) ∧
      ∀ i : Fin p, |(n i : ℝ) / N - η i| ≤ (p : ℝ) ^ 2 / N := by
  obtain ⟨n, hn, hle, hclose⟩ := exists_profile_sharp hp hη hN
  exact ⟨n, hn, hle, fun i => (hclose i).trans
    (div_le_div_of_nonneg_right (roundingRadius_le_sq p) (Nat.cast_nonneg N))⟩

/-! ### The segment construction of Step 3 -/

/-- **Step 3 of the proof of Theorem 2**: if `z ≥ 0`, `∑ i z_i ≤ 1` and `|z_i - γ_i| ≤ ρ` for
`γ ∈ Δ_{p,0}`, then the segment from `z` to `max(z, γ)` meets `Δ_{p,0}` at a point `η ≥ z` with
`‖η - γ‖ ≤ ρ`. -/
theorem exists_mem_simplex_ge {p : ℕ} {γ z : Fin p → ℝ} (hγ : γ ∈ simplex p 0) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hz0 : ∀ i, 0 ≤ z i) (hzsum : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * z i ≤ 1)
    (hzγ : ∀ i, |z i - γ i| ≤ ρ) :
    ∃ η ∈ simplex p 0, ‖η - γ‖ ≤ ρ ∧ ∀ i, z i ≤ η i := by
  set w : Fin p → ℝ := fun i => max (z i) (γ i)
  set Sz := ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * z i
  set Sw := ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * w i
  have hSγ : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * γ i = 1 := by
    have := hγ.2; rw [sub_zero] at this; exact this
  have hSw : 1 ≤ Sw := by
    rw [← hSγ]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hSzw : Sz ≤ Sw := Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  -- the parameter `θ ∈ [0,1]` with `Sz + θ (Sw - Sz) = 1`
  obtain ⟨θ, hθ0, hθ1, hθ⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ Sz + θ * (Sw - Sz) = 1 := by
    rcases hSzw.eq_or_lt with heq | hlt
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      rw [zero_mul, add_zero]
      linarith
    · refine ⟨(1 - Sz) / (Sw - Sz), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
      · rw [div_le_one (by linarith)]; linarith
      · field_simp; ring
  set η : Fin p → ℝ := fun i => z i + θ * (w i - z i)
  have hzw : ∀ i, z i ≤ w i := fun i => le_max_left _ _
  have hηz : ∀ i, z i ≤ η i := fun i => by
    have := mul_nonneg hθ0 (sub_nonneg.mpr (hzw i)); simp only [η]; linarith
  have hηsum : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * η i = 1 := by
    have : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * η i = Sz + θ * (Sw - Sz) := by
      simp only [η, Sz, Sw, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, hθ]
  have hηnn : ∀ i, 0 ≤ η i := fun i => (hz0 i).trans (hηz i)
  refine ⟨η, ⟨fun i => ⟨hηnn i, ?_⟩, by rw [sub_zero]; exact hηsum⟩, ?_, hηz⟩
  · have h1 : ((i : ℕ) + 1 : ℝ) * η i ≤ ∑ j : Fin p, ((j : ℕ) + 1 : ℝ) * η j :=
      Finset.single_le_sum (f := fun j : Fin p => ((j : ℕ) + 1 : ℝ) * η j)
        (fun j _ => mul_nonneg (by positivity) (hηnn j)) (Finset.mem_univ i)
    rw [hηsum] at h1
    have h2 : η i ≤ ((i : ℕ) + 1 : ℝ) * η i := by
      have : (1 : ℝ) ≤ (i : ℕ) + 1 := by linarith [(Nat.cast_nonneg (i : ℕ) : (0 : ℝ) ≤ (i : ℕ))]
      nlinarith [hηnn i]
    linarith
  · refine (pi_norm_le_iff_of_nonneg hρ).mpr fun i => ?_
    rw [Real.norm_eq_abs, Pi.sub_apply]
    have hwγ : |w i - γ i| ≤ ρ := by
      simp only [w]
      rcases le_total (z i) (γ i) with h | h
      · rw [max_eq_right h, sub_self, abs_zero]; exact hρ
      · rw [max_eq_left h]; exact hzγ i
    have heq : η i - γ i = (1 - θ) * (z i - γ i) + θ * (w i - γ i) := by simp only [η]; ring
    rw [heq]
    calc |(1 - θ) * (z i - γ i) + θ * (w i - γ i)|
        ≤ |(1 - θ) * (z i - γ i)| + |θ * (w i - γ i)| := abs_add_le _ _
      _ = (1 - θ) * |z i - γ i| + θ * |w i - γ i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ), abs_of_nonneg hθ0]
      _ ≤ (1 - θ) * ρ + θ * ρ :=
          add_le_add (mul_le_mul_of_nonneg_left (hzγ i) (by linarith))
            (mul_le_mul_of_nonneg_left hwγ hθ0)
      _ = ρ := by ring

end TheoremTwo

end MultipoleBKT

end
