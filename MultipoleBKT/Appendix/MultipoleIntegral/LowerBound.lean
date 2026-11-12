/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.LowerGeometry
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Support

/-!
# Lemma A.3: the written lower bound on the multipole integral

See Lemma A.3. First bound the interaction on the full event `𝒞` through
the continuous Hessian estimate. Restrict to the specified endpoint-ball chain,
whose weighted volume gives (A.15).

The true, finite-cutoff and screened lower providers use the same chain integration
interface. The smaller `IsGood` geometry is retained separately for the frozen
compatibility interval beyond the written absorption threshold.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {lam β M : ℝ}

namespace MultipoleIntegral

/-- The integrand bound on the paper chain, through the Hessian estimate on `𝒞`.
See Lemma A.3. -/
theorem le_multipoleIntegrand_of_chain (hχ : IsMollifier χ) {B : ℝ} (hB : ∀ x, χ x ≤ B) (hβ : 0 ≤ β) (hlam : 0 < lam)
    (hM : 9 ≤ M) {S : Finset ℕ} {N k : ℕ} (σ : S ≃ Fin k) {r₀ : S}
    (hr₀ : (σ r₀ : ℕ) = 0) {c : S → ℂ × ℂ} (hc : RouteChain.Chain N lam σ r₀ c) :
    Real.exp (-β * (12 * Real.pi * B)) ^ (k * k) *
        ((4 * lam) ^ (-β)) ^ k ≤
      multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
  classical
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  set V₀ : ℝ := 12 * Real.pi * B
  have hB0 := hχ.nonneg_of_le hB
  have hV₀ : 0 ≤ V₀ := by positivity
  set E : ℝ := Real.exp (-β * V₀)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  -- connectedness
  have hconn : (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected :=
    (hc.event hlam hr₀).connected hlam (by linarith) r₀
  -- the pair factors
  have hpair : ∀ i j : S, E ≤ (if i < j then stablePairWeight χ β lam (c i) (c j) else 1) := by
    intro i j
    split_ifs with hij
    · have hst := hc.stable hlam hr₀ hij.ne
      unfold stablePairWeight
      simp only [hst, ↓reduceIte]
      refine Real.exp_le_exp.2 ?_
      have := le_abs_self (dipoleInteraction χ lam (c i) (c j))
      have := (hc.event hlam hr₀).abs_interaction_le hχ hB hlam i j
      nlinarith
    · exact hE1
  have hpairs : E ^ (k * k) ≤
      ∏ i : S, ∏ j : S, (if i < j then stablePairWeight χ β lam (c i) (c j) else 1) := by
    calc E ^ (k * k) = ∏ _i : S, ∏ _j : S, E := by
          rw [prod_const, prod_const, card_univ, hcard, ← pow_mul]
      _ ≤ _ := prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => hE0) fun i _ =>
          prod_le_prod₀ (fun j _ => hE0) fun j _ => hpair i j
  -- the dipole factors
  have h4 : 0 < 4 * lam := by positivity
  have hdip : ∀ i : S, (4 * lam) ^ (-β) ≤
      Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) :=
    (hc.event hlam hr₀).density_lower hχ hβ hlam
  have hdips : ((4 * lam) ^ (-β)) ^ k ≤
      ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
    calc ((4 * lam) ^ (-β)) ^ k = ∏ _i : S, (4 * lam) ^ (-β) := by
          rw [prod_const, card_univ, hcard]
      _ ≤ _ := prod_le_prod₀ (fun i _ => (Real.rpow_pos_of_pos h4 _).le) fun i _ => hdip i
  unfold multipolePartitionFunctionIntegrand
  simp only [hconn, ↓reduceIte, one_mul]
  exact mul_le_mul hpairs hdips (pow_nonneg (Real.rpow_pos_of_pos h4 _).le _)
    (prod_nonneg fun i _ => prod_nonneg fun j _ => le_trans hE0 (hpair i j))

/-- The exponents: `(λ^{-β})^k (λ²)^{2k-1} = λ^{(2-β)k} λ^{2(k-1)}` for `λ > 0`, `k ≥ 1`. -/
theorem rpow_neg_pow_mul_sq_pow (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) :
    (lam ^ (-β)) ^ k * (lam ^ 2) ^ (2 * k - 1) = lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  rw [← Real.rpow_natCast (lam ^ (-β)), ← Real.rpow_mul hlam.le, ← pow_mul,
    ← Real.rpow_natCast lam (2 * (2 * k - 1)), ← Real.rpow_natCast lam (2 * (k - 1)),
    ← Real.rpow_add hlam, ← Real.rpow_add hlam]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The threshold `N₀(λ) = ⌈(24 k λ)²⌉` of the lower bound. -/
noncomputable def lowerN₀ (lam : ℝ) (k : ℕ) : ℕ := ⌈(24 * lam * k) ^ 2⌉₊

theorem sqrt_ge_of_lowerN₀_le (hlam : 0 < lam) {k N : ℕ} (hN : lowerN₀ lam k ≤ N) :
    4 * (6 * lam * k) ≤ Real.sqrt N := by
  have h1 : (24 * lam * k) ^ 2 ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq (by positivity)] at h2
  linarith

/-- The weighted lower comparison on the exact chain of (A.15). The pointwise hypothesis is an internal integration interface. -/
theorem le_setIntegral_of_chain (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) {N : ℕ}
    (hN : 4 * (5 * k * lam) ≤ Real.sqrt N) {S : Finset ℕ} (σ : S ≃ Fin k)
    {F : (S → ℂ × ℂ) → ℝ} (hFm : Measurable F) (hF0 : ∀ c, 0 ≤ F c)
    (hfin : ∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (F c) ≠ ⊤)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ c, RouteChain.Chain N lam σ (σ.symm ⟨0, hk⟩) c → A * ((4 * lam) ^ (-β)) ^ k ≤ F c) :
    A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4 * N * lam ^ ((2 - β) * k) *
        lam ^ (2 * (k - 1)) ≤
      ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), F c := by
  classical
  set r₀ : S := σ.symm ⟨0, hk⟩
  have hr₀ : (σ r₀ : ℕ) = 0 := by simp [r₀]
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  set L : ℝ := A * ((4 * lam) ^ (-β)) ^ k
  have hL : 0 ≤ L := by positivity
  set V : ℝ := Real.pi * (lam / 16) ^ 2
  have hV : 0 ≤ V := by positivity
  -- pointwise comparison with the good clusters
  have hpt : ∀ c, ENNReal.ofReal L * RouteChain.chainWeight lam σ r₀ (innerBox N (5 * k * lam)) c ≤
      P.indicator (fun c => ENNReal.ofReal (F c)) c := by
    intro c
    by_cases h0 : RouteChain.chainWeight lam σ r₀ (innerBox N (5 * k * lam)) c = 0
    · rw [h0, mul_zero]
      exact zero_le
    have hgood := RouteChain.chain_of_weight_ne_zero h0
    have hcP : c ∈ P := Set.mem_univ_pi.2 fun i => hgood.mem_box hlam hr₀ i
    rw [Set.indicator_of_mem hcP]
    calc ENNReal.ofReal L * RouteChain.chainWeight lam σ r₀ (innerBox N (5 * k * lam)) c ≤ ENNReal.ofReal L * 1 := by
          gcongr
          exact RouteChain.chainWeight_le_one lam σ r₀ _ c
      _ = ENNReal.ofReal L := mul_one _
      _ ≤ ENNReal.ofReal (F c) := ENNReal.ofReal_le_ofReal (hF c hgood)
  have hlint : ENNReal.ofReal (L * V ^ k * (N / 4) * V ^ (k - 1)) ≤
      ∫⁻ c in P, ENNReal.ofReal (F c) := by
    rw [← lintegral_indicator (measurableSet_pi_box_prod N)]
    calc ENNReal.ofReal (L * V ^ k * (N / 4) * V ^ (k - 1))
        = ENNReal.ofReal L * (ENNReal.ofReal V ^ k *
            (ENNReal.ofReal (N / 4) * ENNReal.ofReal V ^ (k - 1))) := by
          rw [← ENNReal.ofReal_pow hV, ← ENNReal.ofReal_pow hV, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hL]
          ring_nf
      _ ≤ ENNReal.ofReal L * (ENNReal.ofReal V ^ k *
            (volume (innerBox N (5 * k * lam)) * ENNReal.ofReal V ^ (k - 1))) := by
          gcongr
          exact ofReal_quarter_le_volume_innerBox (by positivity) hN
      _ = ENNReal.ofReal L * ∫⁻ c, RouteChain.chainWeight lam σ r₀ (innerBox N (5 * k * lam)) c := by
          rw [RouteChain.lintegral_chainWeight hlam.le σ r₀ (measurableSet_innerBox N _), hcard]
          have hp : ENNReal.ofReal V ^ (2 * k - 1) =
              ENNReal.ofReal V ^ k * ENNReal.ofReal V ^ (k - 1) := by
            rw [← pow_add, show k + (k - 1) = 2 * k - 1 by omega]
          change ENNReal.ofReal L * (ENNReal.ofReal V ^ k *
              (volume (innerBox N (5 * k * lam)) * ENNReal.ofReal V ^ (k - 1))) =
            ENNReal.ofReal L * (volume (innerBox N (5 * k * lam)) * ENNReal.ofReal V ^ (2 * k - 1))
          rw [hp]
          ring
      _ = ∫⁻ c, ENNReal.ofReal L * RouteChain.chainWeight lam σ r₀ (innerBox N (5 * k * lam)) c :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ c, P.indicator (fun c => ENNReal.ofReal (F c)) c := lintegral_mono hpt
  have hI : ∫ c in P, F c = (∫⁻ c in P, ENNReal.ofReal (F c)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0)
      hFm.aestronglyMeasurable
  rw [hI]
  refine le_trans (le_of_eq ?_) ((ENNReal.ofReal_le_iff_le_toReal hfin).1 hlint)
  -- the algebra of the constants
  have h4 : (4 * lam) ^ (-β) = (4 : ℝ) ^ (-β) * lam ^ (-β) :=
    Real.mul_rpow (by norm_num) hlam.le
  have hVk : V ^ k * V ^ (k - 1) = (Real.pi / 256) ^ (2 * k - 1) * (lam ^ 2) ^ (2 * k - 1) := by
    rw [← pow_add, show k + (k - 1) = 2 * k - 1 by omega, ← mul_pow]
    congr 1
    simp only [V]
    ring
  have hexp := rpow_neg_pow_mul_sq_pow (β := β) hlam hk
  calc A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4 * N *
        lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
      = A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4 * N *
          ((lam ^ (-β)) ^ k * (lam ^ 2) ^ (2 * k - 1)) := by rw [hexp]; ring
    _ = L * V ^ k * (N / 4) * V ^ (k - 1) := by
        simp only [L]
        rw [h4, mul_pow]
        linear_combination (A * ((4 : ℝ) ^ (-β)) ^ k * (lam ^ (-β)) ^ k * (N / 4)) * hVk.symm

end MultipoleIntegral

open MultipoleIntegral

/-- **Lemma A.3, lower bound** (equation (A.15)), for
the model `(v, ∞, 0, ∅)` with cutoff `ε₀ = ∞`: for `k ≥ 1` and `M ≥ 9` there is `C > 0`
depending on `χ, β, k` such that, for every `λ > 0`, there is `N₀` with
`C⁻¹ N λ^{(2-β)k} λ^{2(k-1)} ≤ I^0_{mult,∞}(S)` for all `N ≥ N₀` and `|S| = k`. -/
theorem le_multipoleIntegral (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hM : 9 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S.card = k →
        C⁻¹ * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) ≤ multipoleIntegral χ N β lam M S := by
  obtain ⟨B, hB⟩ := hχ.exists_bound
  set E : ℝ := Real.exp (-β * (12 * Real.pi * B))
  set c₀ : ℝ := E ^ (k * k) * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 256) ^ (2 * k - 1) / 4
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨c₀⁻¹, inv_pos.2 hc₀, fun lam hlam => ⟨lowerN₀ lam k, fun N hN S hS => ?_⟩⟩
  rw [inv_inv]
  set σ : S ≃ Fin k := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hS])
  have hr₀ : (σ (σ.symm ⟨0, hk⟩) : ℕ) = 0 := by simp
  exact le_setIntegral_of_chain hlam hk (by
      have := sqrt_ge_of_lowerN₀_le hlam hN
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith) σ
    (measurable_multipoleIntegrand hχ hlam β M) multipoleIntegrand_nonneg
    (lintegral_multipoleIntegrand_ne_top hχ hlam N β M S) (by positivity)
    fun c hc => le_multipoleIntegrand_of_chain hχ hB (by linarith) hlam hM σ hr₀ hc

end MultipoleBKT

end
