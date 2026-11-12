/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.API

/-!
# Fixed positive cutoffs for the frozen statements of Lemma A.7

See (A.42)
and (A.63). The frozen statements also
allow epsilon above one. The same three moment bounds apply, with the
fixed factor `1 + |log epsilon|` retained in their coefficient.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset Limits SmallIntegral SmallIntegral.RouteJext GeneralExpansion RouteSpatial
open scoped Classical ENNReal

/-- The written logarithmic moment product for any fixed positive cutoff. -/
theorem fixed_moment_product {β : ℝ} (hβ : 2 < β) (p₀ : ℕ)
    {k : ℕ} (hk : 1 ≤ k) (q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      RouteLog.radialLogMoment (4-β) lam (eps*truncationScale p₀ β lam) q *
        RouteLog.radialLogMoment (4-β) lam (eps*truncationScale p₀ β lam) 0 ^ (k-1) ≤
      C * lam ^ ((2-β)*k) := by
  by_cases hlt : β < 4
  · obtain ⟨A,hA,hb⟩ := moment_product_lt_four hβ hlt hk q
    refine ⟨A*eps^((4-β)*k),mul_pos hA (Real.rpow_pos_of_pos heps _),?_⟩
    intro lam hlam hle hl1
    have hlh := hle.trans (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hl1))
    refine (hb lam _ hlam hlh).trans_eq ?_
    rw [Real.mul_rpow heps.le (Appendix.truncationScale_pos hlam).le,
      Appendix.rpow_truncationScale_mul_of_lt hlam hlt]
    ring
  have hge : 4 ≤ β := le_of_not_gt hlt
  have hreg : ∃ A : ℝ, 0 < A ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      RouteLog.radialLogMoment (4-β) lam h q * RouteLog.radialLogMoment (4-β) lam h 0^(k-1) ≤
        A*lam^((4-β)*k)*(1+Real.log (h/lam))^(k+q) := by
    by_cases heq : β = 4
    · subst β
      obtain ⟨A,hA,hb⟩ := moment_product_four hk q
      refine ⟨A,hA,?_⟩
      intro lam h hlam hlh
      simpa only [sub_self,zero_mul,Real.rpow_zero,mul_one] using hb lam h hlam hlh
    · obtain ⟨A,hA,hb⟩ := moment_product_gt_four (lt_of_le_of_ne hge (Ne.symm heq)) hk q
      refine ⟨A,hA,?_⟩
      intro lam h hlam hlh
      refine (hb lam h hlam hlh).trans ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith [Real.log_nonneg ((one_le_div hlam).2 hlh)] :
          1 ≤ 1+Real.log (h/lam)) (Nat.le_add_left q k)) (by positivity)
  obtain ⟨A,hA,hb⟩ := hreg
  obtain ⟨B,hB,hlog⟩ := power_log_uniform (show (0 : ℝ) < k by exact_mod_cast hk)
    (show (0 : ℝ) ≤ 2*p₀+1 by positivity) (k+q)
  let D := 1+|Real.log eps|
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A*D^(k+q)*B,by positivity,?_⟩
  intro lam hlam hle hl1
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hlh := hle.trans (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hl1))
  have hL : 0 ≤ 1+Real.log (eps*truncationScale p₀ β lam/lam) := by
    linarith [Real.log_nonneg ((one_le_div hlam).2 hlh)]
  have hbase : 0 ≤ (2*(p₀ : ℝ)+1)*(-Real.log lam) := by
    exact mul_nonneg (by positivity) (neg_nonneg.2 (Real.log_nonpos hlam.le hl1))
  have hlogR := RouteLog.log_cutoff_le (p₀ := p₀) hge hlam hl1 (by norm_num : (0 : ℝ) < 1) le_rfl
  simp only [one_mul,abs_of_nonpos (Real.log_nonpos hlam.le hl1)] at hlogR
  have hlogs : Real.log (eps*truncationScale p₀ β lam/lam) =
      Real.log eps + Real.log (truncationScale p₀ β lam/lam) := by
    rw [mul_div_assoc,Real.log_mul heps.ne' (div_pos hR hlam).ne']
  have hp : (1+Real.log (eps*truncationScale p₀ β lam/lam))^(k+q) ≤
      D^(k+q)*(1+(2*(p₀ : ℝ)+1)*(-Real.log lam))^(k+q) := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ hL
    rw [hlogs]
    dsimp [D]
    nlinarith [le_abs_self (Real.log eps),mul_nonneg (abs_nonneg (Real.log eps)) hbase]
  have hpoly : lam^(k : ℝ)*(1+Real.log (eps*truncationScale p₀ β lam/lam))^(k+q) ≤ D^(k+q)*B := by
    calc
      _ ≤ lam^(k : ℝ)*(D^(k+q)*(1+(2*(p₀ : ℝ)+1)*(-Real.log lam))^(k+q)) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hlam.le _)
      _ = D^(k+q)*(lam^(k : ℝ)*(1+(2*(p₀ : ℝ)+1)*(-Real.log lam))^(k+q)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [abs_of_nonpos (Real.log_nonpos hlam.le hl1)] using hlog lam hlam hl1) (pow_nonneg hD.le _)
  have he : lam^((4-β)*k) = lam^((3-β)*k)*lam^(k : ℝ) := by
    rw [← Real.rpow_add hlam]; congr 1; ring
  have hpower : lam^((3-β)*k) ≤ lam^((2-β)*k) :=
    Real.rpow_le_rpow_of_exponent_ge hlam hl1 (by have hh : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith)
  refine (hb lam _ hlam hlh).trans ?_
  rw [he]
  calc
    _ = A*lam^((3-β)*k)*(lam^(k : ℝ)*(1+Real.log (eps*truncationScale p₀ β lam/lam))^(k+q)) := by ring
    _ ≤ A*lam^((2-β)*k)*(D^(k+q)*B) := mul_le_mul
      (mul_le_mul_of_nonneg_left hpower hA.le) hpoly (by positivity) (by positivity)
    _ = _ := by ring

/-- The actual vector integral for any fixed positive epsilon. -/
theorem fixed_vectorWeight_gain {χ : ℂ → ℝ} {β : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) (q : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I], Fintype.card I = k →
      ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      (∫⁻ u : I → ℂ, vectorWeight χ β lam (eps*truncationScale p₀ β lam) q u) ≤
        ENNReal.ofReal (C*lam^((2-β)*k)) := by
  obtain ⟨C,hC,hb⟩ := fixed_moment_product hβ p₀ hk q eps heps
  let D := (k : ℝ)*(1+Real.log 17)^q*(2*Real.pi*Real.exp (β*MultipoleIntegral.kernelConst χ))^k
  have hD : 0 < D := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 17)
    dsimp [D]; positivity
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro I _ _ _ hI lam hlam hle hl1
  have hlh := hle.trans (le_mul_of_one_le_right heps.le (Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hl1))
  have hv := lintegral_vectorWeight_le (I := I) (β := β) hχ (by linarith) hlam hlh q
  rw [hI] at hv
  exact hv.trans (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (hb lam hlam hle hl1) hD.le).trans_eq (by ring)))

/-- The screened-model counterpart of (A.63) for each normalized original tree. The fixed inverse screening radius supplies the area term. -/
theorem screened_fixed_activityTree_bound {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ (N : ℕ) (T : SimpleGraph W) [DecidableRel T.Adj], T.IsTree →
      ∀ (A E : Finset (Sym2 W)) (mark : Option (Sym2 W)) (root : W),
      (∫⁻ c : W → ℂ × ℂ, ((TwoComponentCoulomb.box N).indicator 1 (c root).2 *
          ENNReal.ofReal (((eps * truncationScale p₀ β lam) ^ 2)⁻¹)) *
        activityTree M lam (eps * truncationScale p₀ β lam) T A E mark c *
          activityDensity χ β lam (eps * truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (C * eps ^ (-2 : ℝ) * N *
          lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨Ca,hCa,hbound⟩ := fixed_vectorWeight_gain hχ hβ p₀ hk (k - 1) eps heps
  let K := (4 * Real.pi * (M ^ 2 + 5)) ^ (k - 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K * Ca, mul_pos hK hCa, fun lam hlam hle hl1 W _ _ _ hW N T _ hT A E mark root => ?_⟩
  have heps0 := heps
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hlh : lam ≤ eps * truncationScale p₀ β lam := hle.trans
    (le_mul_of_one_le_right heps0.le (Appendix.one_le_truncationScale (p₀ := p₀) hβ hlam hl1))
  have hm' := hbound W hW lam hlam hle hl1
  have hs := lintegral_screened_activityTree_le_vectors (β := β) hχ hlam hM hlh N T hT A E mark root
  rw [hW] at hs
  refine hs.trans ((mul_le_mul' le_rfl hm').trans_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.rpow_neg heps0.le, Real.rpow_two, Real.rpow_neg hscale.le, Real.rpow_two, mul_pow]
  dsimp only [K]
  simp only [mul_pow]
  ring

/-- The screened-root envelope gives the area part of (A.63) with no bad data. -/
theorem screened_fixed_spatialEnvelope_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k →
      ∀ N : ℕ, (∫⁻ c : W → ℂ × ℂ,
        spatialEnvelope χ β M lam (eps * truncationScale p₀ β lam)
          (fun c i => (TwoComponentCoulomb.box N).indicator 1 (c i).2 *
            ENNReal.ofReal (((eps * truncationScale p₀ β lam) ^ 2)⁻¹)) c) ≤
          ENNReal.ofReal (C * eps ^ (-2 : ℝ) * N *
            lam ^ ((2-β)*k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨A,hA,hb⟩ := screened_fixed_activityTree_bound hχ hβ hM p₀ hk eps heps
  let D : ℝ := spatialMultiplicity k + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro lam hlam hle hl1 W _ _ _ hW N
  have heps0 : 0 < eps := hlam.trans_le hle
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  let F (c : W → ℂ × ℂ) (i : W) := (TwoComponentCoulomb.box N).indicator (1 : ℂ → ℝ≥0∞) (c i).2 *
    ENNReal.ofReal (((eps * truncationScale p₀ β lam) ^ 2)⁻¹)
  have hF (i : W) : Measurable (fun c => F c i) :=
    ((measurable_const.indicator (TwoComponentCoulomb.measurableSet_box N)).comp
      (measurable_snd.comp (measurable_pi_apply i))).mul measurable_const
  change (∫⁻ c : W → ℂ × ℂ, spatialEnvelope χ β M lam _ F c) ≤ _
  rw [lintegral_spatialEnvelope hχ β M _ hlam F hF]
  let B := A * eps ^ (-2 : ℝ) * N * lam ^ ((2-β)*k) * truncationScale p₀ β lam ^ (-2 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    _ ≤ ∑ _s : SpatialChoice W, ENNReal.ofReal B := sum_le_sum fun s _ =>
      hb lam hlam hle hl1 W hW N s.1.val s.1.property s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2
    _ = ENNReal.ofReal ((Fintype.card (SpatialChoice W) : ℝ) * B) := by
      rw [sum_const,card_univ,nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (D*B) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
      have hc := card_spatialChoice_le (W := W)
      rw [hW] at hc
      dsimp [D]
      exact (Nat.cast_le.2 hc).trans (le_add_of_nonneg_right (by norm_num))) hB)
    _ = _ := by congr 1; dsimp [B]; ring

end MultipoleBKT.ExpansionK.RouteAssembly

end
