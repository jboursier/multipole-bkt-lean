/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.FrozenRoot
import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.PlusRoot
public import MultipoleBKT.Appendix.GeneralExpansion.MinusModel
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Bounds

/-!
# The multipole error with frozen bad points

See Lemma A.6. The pointwise expansion is (A.36). The root estimate
uses the actual translated endpoints and truncated inverse-square integral,
then the zeroth and first logarithmic radial moments. Their three temperature
regimes give (A.43) and (A.44), with a bad-point coefficient independent
of `ε₀`. Step 3 uses the three evaluated cutoff tails before normalization.
The final triangle inequality gives the consumed minus and plus interfaces.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound MultipoleIntegralZ

variable {χ : ℂ → ℝ} {β M lam : ℝ}

/-- Powers of `u = λ^a h^b`: `u^{k-1} λ^c h^d = λ^{a(k-1)+c} h^{b(k-1)+d}` for `λ, h > 0`, `k ≥ 1`. -/
theorem pow_mul_rpow_eq {lam h a b c d : ℝ} (hlam : 0 < lam) (hh : 0 < h) {k : ℕ} (hk : 1 ≤ k) :
    (lam ^ a * h ^ b) ^ (k - 1) * (lam ^ c * h ^ d) =
      lam ^ (a * ((k : ℝ) - 1) + c) * h ^ (b * ((k : ℝ) - 1) + d) := by
  rw [mul_pow, ← Real.rpow_natCast (lam ^ a), ← Real.rpow_natCast (h ^ b),
    ← Real.rpow_mul hlam.le, ← Real.rpow_mul hh.le, Nat.cast_sub hk, Nat.cast_one,
    Real.rpow_add hlam, Real.rpow_add hh]
  ring

/-- **Step 2 for the model `(v^Z, τ^Z)`** (eqs. (A.43), (A.44), (A.41), (A.42)): for `1 ≤ k`, `M ≥ 0`, `p₀`, there are `C₁, C₂ ≥ 0` (depending on `χ, β, M, k, p₀`) such
that for `0 < λ ≤ ε₀ ≤ 1`, `3^{p(β)} ≤ M`, every frozen configuration `(V, Z)` with
`I_bad^V(Z) = V`, every `S` with `|S| = k` and `i₀ ∈ S`,
`∫ 𝟙_{𝓑_S} ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} rootZ(r_{i₀}, y_{i₀}) ≤
C₁ ε₀^{σk-2} N λ^{(2-β)k} R̄^{-2} + C₂ ε₀^{α(β)k} |V| λ^{(2-β)k}`. -/
theorem lintegral_plus_root_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hM : 0 ≤ M) (p₀ : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (ε₀ lam : ℝ), 0 < lam → lam ≤ ε₀ → ε₀ ≤ 1 →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ (N : ℕ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      badPointsOn p₀ β lam M ε₀ V Z = V → ∀ (S : Finset ℕ), S.card = k → ∀ i₀ : S,
        ∫⁻ c : S → ℂ × ℂ, connInd M lam c *
            ((∏ i, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam) ((c i).1 - (c i).2)) *
              rootZ p₀ β lam M ε₀ V Z ((c i₀).1 - (c i₀).2) (c i₀).2) ≤
          ENNReal.ofReal (C₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) * N *
              (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) +
            C₂ * ε₀ ^ (alphaExponent β * k) * V.card * lam ^ ((2 - β) * k)) := by
  exact lintegral_plus_root_log_le hχ hβ hk hM p₀

/-! ### Step 1 for the frozen model: the pointwise expansion -/

/-- The constant of Step 1 for the model `(v^Z, τ^Z)`: with `W = e^{β(C_b + 16 C₃)}`,
`W^{k²} (e^{16k|L|} (2k K₁ + K₂) + 1)`, `K₁ = W β C₃/2`, `K₂ = e^{16|L|} |L|`. -/
noncomputable def plusK (β L Cb C₃ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (β * (Cb + 16 * C₃)) ^ (k * k) *
    (Real.exp (16 * |L|) ^ k * (2 * k * (Real.exp (β * (Cb + 16 * C₃)) * β * C₃ / 2) +
      Real.exp (16 * |L|) * |L|) + 1)

theorem plusK_nonneg {β L Cb C₃ : ℝ} (hβ : 0 ≤ β) (hC₃ : 0 ≤ C₃) (k : ℕ) :
    0 ≤ plusK β L Cb C₃ k := by
  unfold plusK
  positivity

open scoped Classical in
/-- **Step 1 for the model `(v^Z, τ^Z)`** (eqs. (A.31)–(A.36)): for a
configuration `c ∈ (Λ²)^S`, with `h = ε₀ R̄ ≥ λ`, `I_bad^V(Z) = V`, `3^{p(β)} ≤ M`, `C_b` the bond
bound and `C₃` the constant of eq. (A.35),
`|v^Z-integrand - v-integrand| ≤ K (∑_{i₀} 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_i ≤ h} rootZ(r_{i₀}, y_{i₀})
+ ∑_{i₀} 𝟙_{𝓑} ∏_i e^{β g_λ(r_i)} 𝟙_{r_{i₀} > h})`, `K = plusK`. -/
theorem plus_pointwise_le (hβ : 0 ≤ β) (hlam : 0 < lam) {N p₀ : ℕ} {ε₀ L : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM3 : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hV : badPointsOn p₀ β lam M ε₀ V Z = V) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ d e : ℂ × ℂ, IsStableDipolePair d e → -Cb ≤ dipoleInteraction χ lam d e)
    {C₃ : ℝ} (hC₃0 : 0 < C₃)
    (hC₃ : ∀ d e : ℂ × ℂ,
      |interactionGoodZ χ p₀ β lam ε₀ V Z d e - dipoleInteraction χ lam d e| ≤
        C₃ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
          max (goodRadiusZ p₀ β lam ε₀ V Z d) (goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2)
    {S : Finset ℕ} {c : S → ℂ × ℂ} (hc : c ∈ Set.univ.pi fun _ : S => box N ×ˢ box N) :
    ENNReal.ofReal |plusIntegrand χ p₀ β lam M ε₀ L V Z c -
        multipolePartitionFunctionIntegrand χ β lam M c *
          ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))| ≤
      ENNReal.ofReal (plusK β L Cb C₃ S.card) *
        ((∑ i₀ : S, connInd M lam c *
            ((∏ i, cutWeight χ β lam (ε₀ * truncationScale p₀ β lam) ((c i).1 - (c i).2)) *
              rootZ p₀ β lam M ε₀ V Z ((c i₀).1 - (c i₀).2) (c i₀).2)) +
          ∑ i₀ : S, (Set.univ.pi fun _ : S => box N ×ˢ box N).indicator
              (fun c => connInd M lam c *
                ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
            {u : ℂ | ε₀ * truncationScale p₀ β lam < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)) := by
  set h := ε₀ * truncationScale p₀ β lam with hh_def
  have hh0 : 0 < h := hlam.trans_le hlh
  set k := S.card
  have hcard : Fintype.card S = k := Fintype.card_coe S
  set W := Real.exp (β * (Cb + 16 * C₃))
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ (by positivity))
  set Ψ := Real.exp (16 * |L|)
  have hΨ : 1 ≤ Ψ := Real.one_le_exp (by positivity)
  set K₁ := W * β * C₃ / 2
  have hK₁ : 0 ≤ K₁ := by positivity
  set K₂ := Ψ * |L|
  have hK₂ : 0 ≤ K₂ := by positivity
  set E : ℝ := ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2))
  have hE0 : 0 ≤ E := prod_nonneg fun i _ => (Real.exp_pos _).le
  have hmK : plusK β L Cb C₃ k = W ^ (k * k) * (Ψ ^ k * (2 * k * K₁ + K₂) + 1) := rfl
  have hWk : 0 ≤ W ^ (k * k) := by positivity
  have hX : 0 ≤ Ψ ^ k * (2 * k * K₁ + K₂) := by positivity
  have hK : W ^ (k * k) * Ψ ^ k * (2 * k * K₁ + K₂) ≤ plusK β L Cb C₃ k := by
    rw [hmK]; nlinarith
  have hKW : W ^ (k * k) ≤ plusK β L Cb C₃ k := by rw [hmK]; nlinarith
  have hKn : 0 ≤ plusK β L Cb C₃ k := plusK_nonneg hβ hC₃0.le k
  -- the `v`-integrand is bounded by `W^{k²} E`
  have hstab : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W := by
    intro d e
    unfold stablePairWeight
    split_ifs with hst
    · exact Real.exp_le_exp.2 (by nlinarith [hCb d e hst])
    · linarith
  have hstab0 : ∀ d e : ℂ × ℂ, 0 ≤ stablePairWeight χ β lam d e := fun d e => by
    unfold stablePairWeight; split_ifs <;> positivity
  have hPb : multipolePartitionFunctionIntegrand χ β lam M c ≤ W ^ (k * k) := by
    refine (multipolePartitionFunctionIntegrand_le (M := M) hW hstab c).trans ?_
    refine (mul_le_mul_of_nonneg_left ?_ (by positivity)).trans (le_of_eq (mul_one _))
    split_ifs <;> norm_num
  have hFinf : ENNReal.ofReal (multipolePartitionFunctionIntegrand χ β lam M c * E) ≤
      ENNReal.ofReal (plusK β L Cb C₃ k) * ENNReal.ofReal E := by
    rw [← ENNReal.ofReal_mul hKn]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hPb.trans hKW) hE0)
  have hroot_eq : ∀ i₀ : S,
      ((c i₀).2 + ((c i₀).1 - (c i₀).2), (c i₀).2) = c i₀ := fun i₀ => by
    ext <;> simp
  by_cases hconn : (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
  · have hci : connInd M lam c = 1 := by unfold connInd; simp only [hconn, ↓reduceIte]
    by_cases hall : ∀ i : S, ‖(c i).1 - (c i).2‖ ≤ h
    · have hmem : ∀ i : S, (c i).1 - (c i).2 ∈ closedBall (0 : ℂ) h := fun i => by
        rw [mem_closedBall_zero_iff]; exact hall i
      have hEcut : ENNReal.ofReal E = ∏ i, cutWeight χ β lam h ((c i).1 - (c i).2) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
        refine prod_congr rfl fun i _ => ?_
        unfold cutWeight
        rw [indicator_of_mem (hmem i)]
      by_cases hgood : ∀ i : S, IsGoodZ p₀ β lam M ε₀ V Z (c i)
      · -- all dipoles good and short: the expansion
        set τ : S → ℝ := fun i => goodRadiusZ p₀ β lam ε₀ V Z (c i) with hτ_def
        have hτ0 : ∀ i, 0 < τ i := fun i => goodRadiusZ_pos hlam _
        have hτr : ∀ i, ‖(c i).1 - (c i).2‖ ≤ 4 * τ i := fun i => by
          have := goodRadiusZ_ge hlam (by linarith) hM3 hV (hgood i) (by linarith [hall i])
          have := le_max_left ‖(c i).1 - (c i).2‖ lam
          simp only [hτ_def]
          linarith
        set a : S → S → ℝ := fun i j => if i < j then
          (if IsStableDipolePair (c i) (c j) then
            Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1
          with ha_def
        set b : S → S → ℝ := fun i j => if i < j then stablePairWeight χ β lam (c i) (c j) else 1
          with hb_def
        set ρ : S → ℝ := fun i => (‖(c i).1 - (c i).2‖ / τ i) ^ 2 with hρ_def
        set ψ : S → ℝ := fun i => Real.exp (L * ρ i) with hψ_def
        have hq : ∀ i, 0 ≤ ‖(c i).1 - (c i).2‖ / τ i := fun i => div_nonneg (norm_nonneg _)
          (hτ0 i).le
        have hq4 : ∀ i, ‖(c i).1 - (c i).2‖ / τ i ≤ 4 := fun i => by
          rw [div_le_iff₀ (hτ0 i)]; exact hτr i
        have hρ0 : ∀ i, 0 ≤ ρ i := fun i => by rw [hρ_def]; positivity
        have hρ16 : ∀ i, ρ i ≤ 16 := fun i => by
          rw [hρ_def]; nlinarith [hq i, hq4 i]
        have hdip : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
            (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
              (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) =
            (∏ i, ψ i) * E := by
          rw [← prod_mul_distrib]
          refine prod_congr rfl fun i _ => ?_
          unfold dipoleWeightZ
          rw [indicator_of_mem (hmem i)]
          simp only [hgood i, ↓reduceIte, mul_one, hψ_def, hρ_def, hτ_def]
        have hrwp : plusIntegrand χ p₀ β lam M ε₀ L V Z c = (∏ i, ∏ j, a i j) * (∏ i, ψ i) * E := by
          unfold plusIntegrand
          simp only [hconn, ↓reduceIte, one_mul]
          rw [hdip, ha_def]
          ring
        have hrwi : multipolePartitionFunctionIntegrand χ β lam M c = ∏ i, ∏ j, b i j := by
          unfold multipolePartitionFunctionIntegrand
          simp only [hconn, ↓reduceIte, one_mul, hb_def]
        -- eq. (A.35) in terms of `ρ`
        have hvZ : ∀ i j : S, |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
            dipoleInteraction χ lam (c i) (c j)| ≤ C₃ * ((ρ i + ρ j) / 2) := by
          intro i j
          refine (hC₃ (c i) (c j)).trans ?_
          have hmax : τ i * τ j ≤ max (τ i) (τ j) ^ 2 := by
            rw [sq]
            exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (hτ0 j).le
              ((hτ0 i).le.trans (le_max_left _ _))
          have h1 : C₃ * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τ i) (τ j) ^ 2 ≤
              C₃ * ((‖(c i).1 - (c i).2‖ / τ i) * (‖(c j).1 - (c j).2‖ / τ j)) := by
            rw [div_mul_div_comm, mul_div_assoc]
            refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity)
              (mul_pos (hτ0 i) (hτ0 j)) hmax) hC₃0.le
          refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC₃0.le)
          have := two_mul_le_add_sq (‖(c i).1 - (c i).2‖ / τ i) (‖(c j).1 - (c j).2‖ / τ j)
          simp only [hρ_def]
          linarith
        have hvZ16 : ∀ i j : S, |interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
            dipoleInteraction χ lam (c i) (c j)| ≤ 16 * C₃ := fun i j => by
          refine (hvZ i j).trans ?_
          nlinarith [hρ16 i, hρ16 j]
        have hab : ∀ i j, |a i j - b i j| ≤ K₁ * (ρ i + ρ j) := by
          intro i j
          simp only [ha_def, hb_def]
          by_cases hij : i < j
          · simp only [hij, ↓reduceIte]
            unfold stablePairWeight
            by_cases hst : IsStableDipolePair (c i) (c j)
            · simp only [hst, ↓reduceIte]
              refine (abs_exp_sub_exp_le _ _).trans ?_
              have h2 := hvZ16 i j
              have h3 := hCb (c i) (c j) hst
              rw [abs_le] at h2
              have hmax : max (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j))
                  (-β * dipoleInteraction χ lam (c i) (c j)) ≤ β * (Cb + 16 * C₃) :=
                max_le (by nlinarith) (by nlinarith)
              have hdiff : |-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
                  -β * dipoleInteraction χ lam (c i) (c j)| ≤ β * (C₃ * ((ρ i + ρ j) / 2)) := by
                rw [show -β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
                  -β * dipoleInteraction χ lam (c i) (c j) =
                  -(β * (interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
                    dipoleInteraction χ lam (c i) (c j))) by ring, abs_neg, abs_mul,
                  abs_of_nonneg hβ]
                exact mul_le_mul_of_nonneg_left (hvZ i j) hβ
              calc Real.exp (max (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j))
                    (-β * dipoleInteraction χ lam (c i) (c j))) *
                    |-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) -
                      -β * dipoleInteraction χ lam (c i) (c j)|
                  ≤ W * (β * (C₃ * ((ρ i + ρ j) / 2))) :=
                    mul_le_mul (Real.exp_le_exp.2 hmax) hdiff (abs_nonneg _) (by positivity)
                _ = K₁ * (ρ i + ρ j) := by simp only [K₁]; ring
            · simp only [hst, ↓reduceIte, sub_zero, abs_zero]
              exact mul_nonneg hK₁ (add_nonneg (hρ0 i) (hρ0 j))
          · simp only [hij, ↓reduceIte, sub_self, abs_zero]
            exact mul_nonneg hK₁ (add_nonneg (hρ0 i) (hρ0 j))
        have ha0 : ∀ i j, 0 ≤ a i j := fun i j => by
          simp only [ha_def]
          split_ifs <;> positivity
        have haW : ∀ i j, a i j ≤ W := fun i j => by
          simp only [ha_def]
          split_ifs with hij hst
          · refine Real.exp_le_exp.2 ?_
            have h2 := hvZ16 i j
            have h3 := hCb (c i) (c j) hst
            rw [abs_le] at h2
            nlinarith
          · linarith
          · exact hW
        have hb0 : ∀ i j, 0 ≤ b i j := fun i j => by
          simp only [hb_def]
          split_ifs
          · exact hstab0 _ _
          · exact zero_le_one
        have hbW : ∀ i j, b i j ≤ W := fun i j => by
          simp only [hb_def]
          split_ifs
          · exact hstab _ _
          · exact hW
        have hψ0 : ∀ i, 0 ≤ ψ i := fun i => by rw [hψ_def]; exact (Real.exp_pos _).le
        have hLρ : ∀ i, |L * ρ i| ≤ 16 * |L| := fun i => by
          rw [abs_mul, abs_of_nonneg (hρ0 i)]
          nlinarith [abs_nonneg L, hρ16 i]
        have hψΨ : ∀ i, ψ i ≤ Ψ := fun i => by
          rw [hψ_def]
          exact Real.exp_le_exp.2 ((le_abs_self _).trans (hLρ i))
        have hψ1 : ∀ i, |ψ i - 1| ≤ K₂ * ρ i := fun i => by
          rw [hψ_def]
          have := abs_exp_sub_exp_le (L * ρ i) 0
          rw [Real.exp_zero, sub_zero] at this
          refine this.trans ?_
          have hmax : max (L * ρ i) 0 ≤ 16 * |L| :=
            max_le ((le_abs_self _).trans (hLρ i)) (by positivity)
          calc Real.exp (max (L * ρ i) 0) * |L * ρ i|
              ≤ Ψ * (|L| * ρ i) := by
                rw [abs_mul, abs_of_nonneg (hρ0 i)]
                exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hmax)
                  (mul_nonneg (abs_nonneg L) (hρ0 i))
            _ = K₂ * ρ i := by simp only [K₂]; ring
        have hexp := abs_pairs_mul_sub_le hW hΨ hK₁ ha0 haW hb0 hbW hψ0 hψΨ hρ0 hab hψ1
        rw [hcard] at hexp
        have hreal : |plusIntegrand χ p₀ β lam M ε₀ L V Z c -
            multipolePartitionFunctionIntegrand χ β lam M c * E| ≤
            plusK β L Cb C₃ k * ∑ i₀, E * ρ i₀ := by
          rw [hrwp, hrwi, show (∏ i, ∏ j, a i j) * (∏ i, ψ i) * E - (∏ i, ∏ j, b i j) * E =
            ((∏ i, ∏ j, a i j) * (∏ i, ψ i) - ∏ i, ∏ j, b i j) * E by ring, abs_mul,
            abs_of_nonneg hE0, ← mul_sum]
          calc |(∏ i, ∏ j, a i j) * (∏ i, ψ i) - ∏ i, ∏ j, b i j| * E
              ≤ W ^ (k * k) * Ψ ^ k * (2 * k * K₁ + K₂) * (∑ i, ρ i) * E :=
                mul_le_mul_of_nonneg_right hexp hE0
            _ ≤ plusK β L Cb C₃ k * (∑ i, ρ i) * E := by gcongr
            _ = plusK β L Cb C₃ k * (E * ∑ i, ρ i) := by ring
        refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
        rw [ENNReal.ofReal_mul hKn]
        gcongr
        refine le_trans ?_ (le_add_of_nonneg_right zero_le)
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg hE0 (hρ0 i)]
        refine sum_le_sum fun i₀ _ => le_of_eq ?_
        have hrootρ : rootZ p₀ β lam M ε₀ V Z ((c i₀).1 - (c i₀).2) (c i₀).2 =
            ENNReal.ofReal (ρ i₀) := by
          unfold rootZ
          rw [hroot_eq i₀, indicator_of_mem (Set.mem_univ_pi.1 hc i₀).2]
          simp only [hgood i₀, ↓reduceIte, Pi.one_apply, one_mul, add_zero, hρ_def, hτ_def]
        rw [hci, one_mul, hrootρ, ENNReal.ofReal_mul hE0, hEcut]
      · -- some dipole outside `I_good^Z`
        push Not at hgood
        obtain ⟨i₀, hi₀⟩ := hgood
        have h1 : plusIntegrand χ p₀ β lam M ε₀ L V Z c = 0 := by
          unfold plusIntegrand
          have hz : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
              (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
                (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) = 0 :=
            prod_eq_zero (mem_univ i₀) (plusDipole_eq_zero (fun h' => hi₀ h'.2))
          rw [hz, mul_zero]
        rw [h1, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg
          (multipolePartitionFunctionIntegrand_nonneg χ β lam M c) hE0)]
        refine hFinf.trans ?_
        gcongr
        refine le_trans ?_ (le_add_of_nonneg_right zero_le)
        refine le_trans (le_of_eq ?_) (single_le_sum (fun j _ => zero_le) (mem_univ i₀))
        have hroot1 : rootZ p₀ β lam M ε₀ V Z ((c i₀).1 - (c i₀).2) (c i₀).2 = 1 := by
          unfold rootZ
          rw [hroot_eq i₀, indicator_of_mem (Set.mem_univ_pi.1 hc i₀).2]
          simp [hi₀]
        rw [hci, one_mul, hroot1, mul_one, hEcut]
    · -- some dipole longer than the cutoff
      push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have h1 : plusIntegrand χ p₀ β lam M ε₀ L V Z c = 0 := by
        unfold plusIntegrand
        have hz : ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
            (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
              (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) = 0 :=
          prod_eq_zero (mem_univ i₀) (plusDipole_eq_zero (fun h' => absurd h'.1 (not_le.2 hi₀)))
        rw [hz, mul_zero]
      rw [h1, zero_sub, abs_neg, abs_of_nonneg (mul_nonneg
        (multipolePartitionFunctionIntegrand_nonneg χ β lam M c) hE0)]
      refine hFinf.trans ?_
      gcongr
      refine le_trans ?_ (le_add_of_nonneg_left zero_le)
      refine le_trans (le_of_eq ?_) (single_le_sum (fun j _ => zero_le) (mem_univ i₀))
      rw [indicator_of_mem hc, hci, one_mul,
        indicator_of_mem (show (c i₀).1 - (c i₀).2 ∈ {u : ℂ | h < ‖u‖} from hi₀),
        Pi.one_apply, mul_one, ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
  · have h1 : plusIntegrand χ p₀ β lam M ε₀ L V Z c = 0 := by
      unfold plusIntegrand
      simp only [hconn, ↓reduceIte, zero_mul]
    have h2 : multipolePartitionFunctionIntegrand χ β lam M c = 0 := by
      unfold multipolePartitionFunctionIntegrand
      simp only [hconn, ↓reduceIte, zero_mul]
    rw [h1, h2, zero_mul, sub_zero, abs_zero, ENNReal.ofReal_zero]
    exact zero_le

/-! ### Lemma A.6 for the model `(v^Z, τ^Z)` -/

/-- **Lemma A.6 for the model with frozen bad points** (for `(w, τ) = (v^Z, τ^Z)`, used for equation (5.68)): for
`1 ≤ k ≤ p*(β)`, `M ≥ 0`, `L ∈ ℝ` and `p₀`, there is `C > 0` (depending on `χ, β, M, L, k, p₀`, not
on `ε₀`) such that for every `ε₀ ∈ (0, 1]` there is `C_{ε₀} > 0` with
`|I^{+,Z}_{mult,ε₀}(S) - I^0_{mult,∞}(S)| ≤ λ^{(2-β)k} (C_{ε₀} N R̄^{-2} + C ε₀^{α(β)k} |V_bad|)`
for all `λ ∈ (0, ε₀]`, `N`, frozen configurations `(V, Z)` with `I_bad^V(Z) = V` (when
`3^{p(β)} ≤ M`) and `S` with `|S| = k`. -/
theorem multipoleIntegralPlus_sub_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (L : ℝ) (p₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ ε₀ → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ (N : ℕ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S.card = k →
        |multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S - multipoleIntegral χ N β lam M S| ≤
          lam ^ ((2 - β) * k) * (Cε * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * k) * V.card) := by
  classical
  have hβ0 : 0 ≤ β := by linarith
  have hkp' : (4 - β) * k - 2 < 0 :=
    (Appendix.transitionBeta_lt_iff hk β).1 ((Appendix.le_pStar_iff hk).1 hkp)
  obtain ⟨Cb, hCb0, hCb⟩ := neg_le_dipoleInteraction hχ
  obtain ⟨C₃, hC₃0, hC₃⟩ := abs_interactionGoodZ_sub_le hχ
  obtain ⟨C₁, C₂, hC₁, hC₂, hroot⟩ := lintegral_plus_root_le (χ := χ) hχ hβ hk hM p₀
  obtain ⟨CT, hCT0, htail⟩ := lintegral_cutoff_tail_le (M := M) hχ hβ hk hkp' hM p₀
  set K := plusK β L Cb C₃ k
  have hK : 0 ≤ K := plusK_nonneg hβ0 hC₃0.le k
  refine ⟨K * k * C₂ + 1, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  set D := C₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) + CT * ε₀ ^ tailExp p₀ β k
  have hD : 0 ≤ D := by positivity
  refine ⟨K * k * D + 1, by positivity, fun lam hlam hlε hM3 N V Z hV S hS => ?_⟩
  have hlam1 : lam ≤ 1 := hlε.trans hε₁
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  set R := truncationScale p₀ β lam
  set h := ε₀ * R
  have hlh : lam ≤ h := hlε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set T : ℝ := lam ^ ((2 - β) * k) * R ^ (-2 : ℝ)
  set U : ℝ := ε₀ ^ (alphaExponent β * k) * V.card * lam ^ ((2 - β) * k)
  have hT : 0 ≤ T := by positivity
  have hU : 0 ≤ U := by positivity
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  set F₁ : S → (S → ℂ × ℂ) → ℝ≥0∞ := fun i₀ c => connInd M lam c *
    ((∏ i, cutWeight χ β lam h ((c i).1 - (c i).2)) *
      rootZ p₀ β lam M ε₀ V Z ((c i₀).1 - (c i₀).2) (c i₀).2)
  set F₂ : S → (S → ℂ × ℂ) → ℝ≥0∞ := fun i₀ c => P.indicator (fun c => connInd M lam c *
      ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) c *
    {u : ℂ | h < ‖u‖}.indicator 1 ((c i₀).1 - (c i₀).2)
  have hF₁m : ∀ i₀, Measurable (F₁ i₀) := by
    intro i₀
    refine (measurable_connInd M lam).mul ((Finset.measurable_prod _ fun i _ =>
      (measurable_cutWeight hχ hlam β h).comp
        ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd)).mul ?_)
    exact (measurable_rootZ p₀ β lam M ε₀ V Z).comp
      (((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd).prodMk
        (measurable_pi_apply i₀).snd)
  have hF₂m : ∀ i₀, Measurable (F₂ i₀) := by
    intro i₀
    refine (Measurable.indicator ((measurable_connInd M lam).mul (Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp ((measurable_exp_smearedKernel hχ hlam β).comp
        ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd))))
      (measurableSet_pi_box_prod N)).mul ?_
    exact (measurable_one.indicator (measurableSet_lt measurable_const measurable_norm)).comp
      ((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd)
  have hlint : ∫⁻ c in P, ENNReal.ofReal |plusIntegrand χ p₀ β lam M ε₀ L V Z c -
      (multipolePartitionFunctionIntegrand χ β lam M c *
        ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))| ≤
      ENNReal.ofReal (K * k * (D * N * T + C₂ * U)) := by
    calc _ ≤ ∫⁻ c in P, ENNReal.ofReal K * ((∑ i₀, F₁ i₀ c) + ∑ i₀, F₂ i₀ c) :=
          setLIntegral_mono' (measurableSet_pi_box_prod N) fun c hc => by
            have := plus_pointwise_le (L := L) hβ0 hlam hlh hM3 hV hCb0 (hCb lam hlam) hC₃0
              (hC₃ p₀ β lam ε₀ V Z hlam) hc
            rw [hS] at this
            exact this
      _ ≤ ∫⁻ c, ENNReal.ofReal K * ((∑ i₀, F₁ i₀ c) + ∑ i₀, F₂ i₀ c) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K * ((∑ i₀, ∫⁻ c, F₁ i₀ c) + ∑ i₀, ∫⁻ c, F₂ i₀ c) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_add_left (f := fun c => ∑ i₀, F₁ i₀ c)
              (Finset.measurable_sum _ fun i₀ _ => hF₁m i₀),
            lintegral_finsetSum _ fun i₀ _ => hF₁m i₀, lintegral_finsetSum _ fun i₀ _ => hF₂m i₀]
      _ ≤ ENNReal.ofReal K *
            ((∑ _i₀ : S, ENNReal.ofReal (C₁ * ε₀ ^ (tailSigma p₀ β k * k - 2) * N * T +
              C₂ * U)) + ∑ _i₀ : S, ENNReal.ofReal (CT * ε₀ ^ tailExp p₀ β k * N * T)) := by
          refine mul_le_mul' le_rfl (add_le_add (sum_le_sum fun i₀ _ => ?_)
            (sum_le_sum fun i₀ _ => ?_))
          · refine (hroot ε₀ lam hlam hlε hε₁ hM3 N V Z hV S hS i₀).trans (le_of_eq ?_)
            congr 1
            simp only [U, T]
            ring
          · exact htail ε₀ lam hε₀ hlam hlam1 hlh N S hS i₀
      _ = ENNReal.ofReal (K * k * (D * N * T + C₂ * U)) := by
          rw [sum_const, sum_const, card_univ, hcard, nsmul_eq_mul, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_add (by positivity)
              (by positivity), ← ENNReal.ofReal_mul hK]
          congr 1
          simp only [D]
          ring
  have hmain := abs_setIntegral_sub_le (μ := volume) (P := P)
    (measurable_plusIntegrand hχ hlam) (integrableOn_multipoleIntegrand hχ hlam N S)
    (by positivity) hlint
  refine hmain.2.trans ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNT : 0 ≤ N * T := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc K * k * (D * N * T + C₂ * U)
      = (K * k * D) * (N * T) + (K * k * C₂) * U := by ring
    _ ≤ (K * k * D + 1) * (N * T) + (K * k * C₂ + 1) * U := by nlinarith
    _ = lam ^ ((2 - β) * k) * ((K * k * D + 1) * N * R ^ (-2 : ℝ) +
          (K * k * C₂ + 1) * ε₀ ^ (alphaExponent β * k) * V.card) := by
        simp only [T, U]
        ring

end GeneralExpansion

end MultipoleBKT

end
