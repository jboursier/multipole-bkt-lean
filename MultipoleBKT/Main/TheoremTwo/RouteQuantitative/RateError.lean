/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.RouteQuantitative.Entropy
public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# The two quantitative rate errors of Theorem 2

The entropy terms are compared directly and the cluster term uses its gradient bound,
as in Steps 1 and 3 of the proof of Theorem 2.
All constants are independent of both points, including the center of the LDP ball.
-/

@[expose] public section

open Finset Set Filter Topology

namespace MultipoleBKT.TheoremTwo

/-- An explicit coefficient for the mesh error of the rate function. -/
noncomputable def roundingConst (p : ℕ) (C D : ℝ) : ℝ :=
  3 * D * ((p : ℝ) * (|Real.log (p.factorial : ℝ)| + |Real.log C| + 2 * p + 3) + 1)

theorem roundingConst_pos (p : ℕ) (C : ℝ) {D : ℝ} (hD : 1 ≤ D) :
    0 < roundingConst p C D := by
  unfold roundingConst
  have : 0 < D := by linarith
  positivity

/-- The coefficient bounds give the logarithmic dependence on `λ` in the entropy error. -/
theorem RateSetup.abs_log_msf_le {p : ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ}
    {C lam : ℝ} (hs : RateSetup p msf kmult C lam) (i : Fin p) :
    |Real.log (msf ((i : ℕ) + 1))| ≤ |Real.log C| + 2 * p * |Real.log lam| := by
  rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
  · rw [hi, zero_add, hs.msf_one, Real.log_one, abs_zero]
    positivity
  · obtain ⟨hlo, hhi⟩ := hs.hmsf.2 ((i : ℕ) + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hlo hhi
    have hp : 0 < lam ^ (2 * (i : ℕ)) := pow_pos hs.hlam _
    have hl : Real.log (C⁻¹ * lam ^ (2 * (i : ℕ))) ≤ Real.log (msf ((i : ℕ) + 1)) :=
      Real.log_le_log (by have := hs.hC; positivity) hlo
    have hu : Real.log (msf ((i : ℕ) + 1)) ≤ Real.log (C * lam ^ (2 * (i : ℕ))) :=
      Real.log_le_log (lt_of_lt_of_le (by have := hs.hC; positivity) hlo) hhi
    rw [Real.log_mul (inv_ne_zero hs.hC.ne') hp.ne', Real.log_inv, Real.log_pow] at hl
    rw [Real.log_mul hs.hC.ne' hp.ne', Real.log_pow] at hu
    have hip : (i : ℝ) ≤ p := by exact_mod_cast i.2.le
    have h1 := neg_abs_le (Real.log C)
    have h2 := le_abs_self (Real.log C)
    have h3 := neg_abs_le (Real.log lam)
    have h4 := le_abs_self (Real.log lam)
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    push_cast at hl hu
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 2 * (i : ℝ)),
      mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 2 * (i : ℝ)),
      mul_le_mul_of_nonneg_right hip (abs_nonneg (Real.log lam))]

/-- Direct comparison of entropy terms plus the gradient estimate for `h`.
This single uniform estimate supplies both displayed `C(log N + |log λ|)` errors. -/
theorem rate_rounding_error {p N : ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ}
    {C lam D : ℝ} (hs : RateSetup p msf kmult C lam) (hD : 1 ≤ D) (hN : 2 ≤ N)
    {a b : Fin p → ℝ} (ha : a ∈ simplex p 0) (hb : b ∈ simplex p 0)
    (hab : ‖a - b‖ ≤ D / N) :
    (N : ℝ) * |rateFunction p msf kmult a - rateFunction p msf kmult b| ≤
      roundingConst p C D * (Real.log N + |Real.log lam|) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hloghalf : 1 / 2 ≤ Real.log N := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have hm : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    norm_num at h
    linarith
  set A := |Real.log (p.factorial : ℝ)| + |Real.log C| + 2 * p + 3
  set L := Real.log N + 1 + |Real.log lam|
  have hA : 0 ≤ A := by positivity
  have hL : 1 ≤ L := by have := abs_nonneg (Real.log lam); dsimp [L]; linarith
  have hcoord : ∀ i, |a i - b i| ≤ D / N := fun i => by
    have h := norm_le_pi_norm (a - b) i
    rw [Real.norm_eq_abs, Pi.sub_apply] at h
    exact h.trans hab
  have hcoef : ∀ i : Fin p,
      |Real.log ((i : ℕ) + 1).factorial - 1 - Real.log (msf ((i : ℕ) + 1))| ≤
        |Real.log (p.factorial : ℝ)| + 1 + |Real.log C| + 2 * p * |Real.log lam| := by
    intro i
    have hfact0 : 0 ≤ Real.log (((i : ℕ) + 1).factorial : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _))
    have hfact : |Real.log (((i : ℕ) + 1).factorial : ℝ)| ≤ |Real.log (p.factorial : ℝ)| := by
      rw [abs_of_nonneg hfact0]
      exact (Real.log_le_log (by exact_mod_cast Nat.factorial_pos _)
        (by exact_mod_cast Nat.factorial_le (by omega : (i : ℕ) + 1 ≤ p))).trans (le_abs_self _)
    calc |Real.log ((i : ℕ) + 1).factorial - 1 - Real.log (msf ((i : ℕ) + 1))| ≤
          |Real.log ((i : ℕ) + 1).factorial - 1| + |Real.log (msf ((i : ℕ) + 1))| := abs_sub _ _
      _ ≤ (|Real.log ((i : ℕ) + 1).factorial| + |(1 : ℝ)|) +
          (|Real.log C| + 2 * p * |Real.log lam|) := add_le_add (abs_sub _ _) (hs.abs_log_msf_le i)
      _ ≤ _ := by rw [abs_one]; linarith
  have hent : ∀ i, |rateEntTerm msf i (a i) - rateEntTerm msf i (b i)| ≤ D / N * (A * L) := by
    intro i
    have he := abs_mul_log_sub_le_mesh hN1 hD (ha.1 i) (hb.1 i) (hcoord i)
    have hid : rateEntTerm msf i (a i) - rateEntTerm msf i (b i) =
        (a i - b i) * (Real.log ((i : ℕ) + 1).factorial - 1 - Real.log (msf ((i : ℕ) + 1))) +
        (a i * Real.log (a i) - b i * Real.log (b i)) := by unfold rateEntTerm; ring
    rw [hid]
    calc |(a i - b i) * (Real.log ((i : ℕ) + 1).factorial - 1 - Real.log (msf ((i : ℕ) + 1))) +
          (a i * Real.log (a i) - b i * Real.log (b i))| ≤
          |a i - b i| * |Real.log ((i : ℕ) + 1).factorial - 1 - Real.log (msf ((i : ℕ) + 1))| +
          |a i * Real.log (a i) - b i * Real.log (b i)| := by
            simpa only [abs_mul] using abs_add_le
              ((a i - b i) * (Real.log ((i : ℕ) + 1).factorial - 1 - Real.log (msf ((i : ℕ) + 1))))
              (a i * Real.log (a i) - b i * Real.log (b i))
      _ ≤ D / N * (|Real.log (p.factorial : ℝ)| + 1 + |Real.log C| + 2 * p * |Real.log lam|) +
          2 * D * (Real.log N + 1) / N :=
            add_le_add (mul_le_mul (hcoord i) (hcoef i) (abs_nonneg _) (by positivity)) he
      _ ≤ D / N * (A * L) := by
        have hscale : |Real.log (p.factorial : ℝ)| + 1 + |Real.log C| +
            2 * p * |Real.log lam| + 2 * (Real.log N + 1) ≤ A * L := by
          have ht : |Real.log lam| ≤ L := by dsimp [L]; linarith
          have hn : Real.log N + 1 ≤ L := by dsimp [L]; have := abs_nonneg (Real.log lam); linarith
          have hbase : |Real.log (p.factorial : ℝ)| + 1 + |Real.log C| ≤
              (|Real.log (p.factorial : ℝ)| + 1 + |Real.log C|) * L :=
            le_mul_of_one_le_right (by positivity) hL
          have hpL := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ 2 * p)
          dsimp [A]
          nlinarith
        have := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ D / (N : ℝ))
        convert this using 1; ring
  have hcluster := abs_rateCluster_sub_le hs.hk hs.hlam.le hs.hsmall
    (RateSetup.mem_rateDomain hb) (RateSetup.mem_rateDomain ha)
  change |rateCluster p kmult a - rateCluster p kmult b| ≤ rateB p C lam * ‖a - b‖ at hcluster
  have hc : |rateCluster p kmult a - rateCluster p kmult b| ≤ D / N * L := by
    have hB1 : rateB p C lam ≤ 1 := hs.hB.trans (by norm_num)
    exact hcluster.trans ((mul_le_mul hB1 hab (norm_nonneg _) zero_le_one).trans
      (by simpa using (le_mul_of_one_le_right (by positivity : 0 ≤ D / (N : ℝ)) hL)))
  have htot : |rateFunction p msf kmult a - rateFunction p msf kmult b| ≤
      D / N * (((p : ℝ) * A + 1) * L) := by
    rw [rateFunction_sub_eq]
    refine (abs_add_le _ _).trans (le_trans (add_le_add (abs_sum_le_sum_abs _ _) le_rfl) ?_)
    have hsum := (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hent i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith
  have hNtot := mul_le_mul_of_nonneg_left htot hN0.le
  have heq : (N : ℝ) * (D / N * (((p : ℝ) * A + 1) * L)) = D * ((p : ℝ) * A + 1) * L := by
    field_simp
  rw [heq] at hNtot
  have hL3 : L ≤ 3 * (Real.log N + |Real.log lam|) := by
    dsimp [L]; have := abs_nonneg (Real.log lam); linarith
  have hlast := mul_le_mul_of_nonneg_left hL3 (by positivity : 0 ≤ D * ((p : ℝ) * A + 1))
  unfold roundingConst
  dsimp [A] at hNtot hlast
  nlinarith

/-- At fixed `λ`, the quantitative logarithmic error is absorbed in `Nδ`.
The threshold has no dependence on a profile or ball center. -/
theorem eventually_rounding_absorb {p : ℕ} {C lam D δ : ℝ} (hD : 1 ≤ D) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧
      roundingConst p C D * (Real.log N + |Real.log lam|) ≤ (N : ℝ) * δ := by
  set K := roundingConst p C D
  have hK : 0 < K := roundingConst_pos p C hD
  filter_upwards [eventually_ge_atTop 2,
    eventually_log_le δ hδ (K * (1 + |Real.log lam|))] with N hN hlog
  refine ⟨hN, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hmono : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hN0 (by linarith)
  have hdom : Real.log N + |Real.log lam| ≤
      (1 + |Real.log lam|) * (Real.log ((N : ℝ) + 1) + 1) := by
    nlinarith [mul_nonneg (abs_nonneg (Real.log lam)) hlog0]
  have h := mul_le_mul_of_nonneg_left hdom hK.le
  dsimp [K] at *
  nlinarith

end MultipoleBKT.TheoremTwo

end
