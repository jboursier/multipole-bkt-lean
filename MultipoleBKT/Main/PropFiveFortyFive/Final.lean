/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Goal
public import MultipoleBKT.Main.TheoremOne.Inputs
public import MultipoleBKT.Main.TheoremOne.ItemOne
public import MultipoleBKT.Main.TheoremTwo.Coefficients
public import MultipoleBKT.Main.TheoremTwo.RateAnalysis

/-!
# Proposition 5.45 from the statement of Theorem 2

**Proposition 5.45**, as the internal conditional theorem
`MultipoleBKT.PropFiveFortyFive.proposition_5_45_of_theorem_2`, whose only hypothesis is the
statement of Theorem 2 (`MultipoleBKT.TheoremTwo.Theorem2Statement`, the type of the frozen statement
`MultipoleBKT.theorem_2`) and whose conclusion is `MultipoleBKT.TheoremOne.Prop545Statement`, the type of the frozen
statement `MultipoleBKT.proposition_5_45`. Theorem 2 is proved, and the provider of
Proposition 5.45 (`MultipoleBKT.Main.proposition_5_45`) is
`proposition_5_45_of_theorem_2 MultipoleBKT.theorem_2`.

The proof follows the paper:

* (5.162): Theorem 2 item (2), the relabeling identity
  `Z_{N,β}^λ = N! ∫_{σ_N = Id} e^{-βF_λ}`
  (`MultipoleBKT.TheoremOne.partitionFunction_eq_factorial_mul`),
 Stirling's formula and the limit (2.32) of `C_{β,λ}` give
  `log ∫_{σ_N = Id} e^{-βF_λ} = N log(N C_{β,λ}) - N inf_{Δ_{p,0}} ℐ + O(N δ_{β,λ})`;
* (5.163): `log ∑_{π ∈ 𝚷_p([N])} Ẑ(π) = N log(N C_{β,λ}) - N inf_{Δ_{p,0}} ℐ + o_λ(N)`
  (`MultipoleBKT.PropFiveFortyFive.eventually_abs_log_sum_le` with the profile asymptotics). The
  coefficients `𝗆`, `𝗄^mult` of `ℐ` are those of Theorem 2, pinned by the limits (2.45), (2.46); the
 activity bound `|𝖪^mult(X)| ≤ 2C (λ²/N)^{|X|-1}` follows from (2.46) and (2.48)
  since there are finitely many block profiles (`eventually_abs_multipoleActivity_le`);
* the comparison: for fixed `λ`, `o_λ(N) ≤ N δ_{β,λ}` for `N` large since `δ_{β,λ} > 0`.
-/

@[expose] public section

open Finset Filter Topology
open scoped ENNReal

namespace MultipoleBKT

namespace PropFiveFortyFive

/-! ### The activity bound -/

/-- **The activity bound**: from the limits (2.46) and the bound (2.48) with
constant `C`, for `N` large, `|𝖪^mult(X)| ≤ 2C (λ²/N)^{|X|-1}` for every subpartition `X` with
`2 ≤ |X|` and `|V_X| ≤ p`. There are finitely many block profiles, and `𝖪^mult(X)` depends only
on the profile of `X`. -/
theorem eventually_abs_multipoleActivity_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β M lam C : ℝ}
    {p : ℕ} (hpS : (p : ℕ∞) ≤ pStar β) (hlam : 0 < lam) (hC : 0 < C)
    {kmult : (ℕ →₀ ℕ) → ℝ} (hk : KmultBound p kmult C lam)
    (hlim : ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X)
        atTop (𝓝 (kmult (blockProfile X)))) :
    ∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card ≤ p →
        |multipoleActivity χ N β lam M X| ≤ (2 * C) * (lam ^ 2 / N) ^ (X.card - 1) := by
  have hP : ∀ P ∈ profileBound p, ∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ),
      IsSubpartition X → 2 ≤ X.card → (X.biUnion id).card ≤ p → blockProfile X = P →
        |multipoleActivity χ N β lam M X| ≤ (2 * C) * (lam ^ 2 / N) ^ (X.card - 1) := by
    intro P _
    by_cases h : ∃ X₀ : Finset (Finset ℕ), IsSubpartition X₀ ∧ 2 ≤ X₀.card ∧
        (X₀.biUnion id).card ≤ p ∧ blockProfile X₀ = P
    · obtain ⟨X₀, hX₀, h2, hV, rfl⟩ := h
      have hS : ((∑ S ∈ X₀, S.card : ℕ) : ℕ∞) ≤ pStar β := by
        rw [TheoremTwo.sum_card_eq_card_biUnion hX₀]
        exact (Nat.cast_le.2 hV).trans hpS
      have hT := (hlim X₀ hX₀ hS).abs
      have hkb := hk X₀ hX₀ hV
      rw [TheoremTwo.zpow_two_mul_card_sub_one (by omega)] at hkb
      have hlt : |kmult (blockProfile X₀)| < 2 * C * lam ^ (2 * (X₀.card - 1)) := by
        have : 0 < C * lam ^ (2 * (X₀.card - 1)) := by positivity
        linarith
      filter_upwards [hT.eventually (gt_mem_nhds hlt), eventually_ge_atTop 1]
        with N hN hN1 X hX _ _ hprof
      have hKeq := Limits.multipoleActivity_eq_of_blockProfile_eq (M := M) (β := β) hχ hlam hN1
        hX hX₀ hprof
      have hcard := Limits.card_eq_of_blockProfile_eq hprof
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      rw [TheoremTwo.zpow_card_sub_one (by omega), abs_mul, abs_of_pos (by positivity)] at hN
      rw [hKeq, hcard, div_pow, ← pow_mul, mul_div_assoc', le_div_iff₀ (by positivity), mul_comm]
      exact hN.le
    · exact Eventually.of_forall fun N X hX h2 hV hprof => absurd ⟨X, hX, h2, hV, hprof⟩ h
  filter_upwards [(eventually_all_finset (profileBound p)).2 hP] with N hN X hX h2 hV
  exact hN (blockProfile X) (blockProfile_mem_profileBound hX hV) X hX h2 hV rfl

/-! ### The right-hand side (5.163) -/

/-- `Ẑ(π) = (N C_{β,λ})^N ∏_{S ∈ π} 𝖬([|S|]) polymerSum(π)` for `N ≥ 1`. -/
theorem truncatedPartitionWeight_eq' {χ : ℂ → ℝ} (hχ : IsMollifier χ) {N : ℕ} (hN : 1 ≤ N)
    {β lam M : ℝ} (hlam : 0 < lam) (p : ℕ) (π : Finset (Finset ℕ)) :
    truncatedPartitionWeight χ N β lam M p π =
      ((N : ℝ) * dipoleNormalization χ N β lam) ^ N *
        ((∏ S ∈ π, multipolePartitionFunction χ N β lam M (Finset.range S.card)) *
          polymerSum p (multipoleActivity χ N β lam M) π) := by
  rw [truncatedPartitionWeight_eq, mul_assoc]
  congr 2
  exact prod_congr rfl fun S _ =>
    Limits.multipolePartitionFunction_congr_card hχ hlam hN (card_range _).symm

/-- **(5.163)** at a fixed small `λ`: `log ∑_{π ∈ 𝚷_p([N])} Ẑ(π) =
N log(N C_{β,λ}) - N inf_{Δ_{p,0}} ℐ + o(N)`. -/
theorem eventually_abs_log_zHat_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β M lam C : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hpS : (p : ℕ∞) ≤ pStar β) (hlam : 0 < lam)
    {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} (hs : TheoremTwo.RateSetup p msf kmult C lam)
    {γs : Fin p → ℝ} (hγs : γs ∈ simplex p 0)
    (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γs)
    (hmlim : ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S)
        atTop (𝓝 (msf S.card)))
    (hklim : ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X)
        atTop (𝓝 (kmult (blockProfile X))))
    {Ct : ℝ} (hCt : Ct * lam ^ 2 ≤ 1 / 2)
    (hlogpoly : ∀ (K : ℕ → Finset (Finset ℕ) → ℝ),
      Ct * lam ^ 2 ≤ 1 / 2 → KmultBound p kmult C lam → rateSeriesConst p C * lam ^ 2 ≤ 1 / 4 →
      (∀ N, 1 ≤ N → IsProfileInvariant (K N)) →
      (∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card → (X.biUnion id).card ≤ p →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop
          (𝓝 (kmult (blockProfile X)))) →
      (∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
        (X.biUnion id).card ≤ p → |K N X| ≤ (2 * C) * (lam ^ 2 / N) ^ (X.card - 1)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π ∈ boundedBlockPartitions N p,
        0 < polymerSum p (K N) π ∧
          |Real.log (polymerSum p (K N) π) + N * rateCluster p kmult (profileVec p N π)| ≤
            ε * N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      0 < ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π ∧
        |Real.log (∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π) -
          (N * Real.log ((N : ℝ) * dipoleNormalization χ N β lam) -
            N * rateFunction p msf kmult γs)| ≤ ε * N := by
  set K : ℕ → Finset (Finset ℕ) → ℝ := fun N => multipoleActivity χ N β lam M
  -- the inputs on the activities
  have hKinv : ∀ N, 1 ≤ N → IsProfileInvariant (K N) := fun N hN X X' hX hX' hprof =>
    Limits.multipoleActivity_eq_of_blockProfile_eq hχ hlam hN hX hX' hprof
  have hKlim : ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop
        (𝓝 (kmult (blockProfile X))) := by
    intro X hX h2 hV
    have hS : ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β := by
      rw [TheoremTwo.sum_card_eq_card_biUnion hX]
      exact (Nat.cast_le.2 hV).trans hpS
    refine (hklim X hX hS).congr fun N => ?_
    rw [TheoremTwo.zpow_card_sub_one (by omega)]
  have hact := eventually_abs_multipoleActivity_le hχ hpS hlam hs.hC hs.hk hklim
  have hΞ := hlogpoly K hCt hs.hk hs.hsmall hKinv hKlim hact
  -- the multipole partition functions
  set Mf : ℕ → ℕ → ℝ := fun N k => multipolePartitionFunction χ N β lam M (Finset.range k)
  have hmsf : ∀ k ∈ Icc 1 p, 0 < msf k := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := mem_Icc.1 hk
    rcases Nat.lt_or_ge k 2 with h | h
    · rw [show k = 1 by omega, hs.msf_one]
      exact one_pos
    · have h1 := (hs.hmsf.2 k h hkp).1
      have hC := hs.hC
      have hpos : 0 < C⁻¹ * lam ^ (2 * (k - 1)) := by positivity
      linarith
  have hMf : ∀ k ∈ Icc 1 p, Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * Mf N k) atTop
      (𝓝 (msf k)) := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := mem_Icc.1 hk
    have h := hmlim (Finset.range k) (by rw [card_range]; exact hk1)
      (by rw [card_range]; exact (Nat.cast_le.2 hkp).trans hpS)
    rw [card_range] at h
    exact h
  have hW := eventually_abs_log_count_mul_le (p := p) (kmult := kmult) hmsf hMf
    (Ξ := fun N π => polymerSum p (K N) π) hΞ
  have hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ simplex p 0, ‖γ - γs‖ < δ →
      rateFunction p msf kmult γ ≤ rateFunction p msf kmult γs + ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hs.uniformContinuous hε
    exact ⟨δ, hδ, fun γ hγ hd => by linarith [(abs_lt.1 (h γ hγ γs hγs hd)).2]⟩
  have hsum := eventually_abs_log_sum_le hp hγs hmin hcont hW ε hε
  filter_upwards [hsum, eventually_ge_atTop 1] with N hN hN1
  obtain ⟨hpos, hb⟩ := hN
  have hNC : 0 < (N : ℝ) * dipoleNormalization χ N β lam :=
    natCast_mul_dipoleNormalization_pos hχ hlam β hN1
  have heq : ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π =
      ((N : ℝ) * dipoleNormalization χ N β lam) ^ N *
        ∑ π ∈ boundedBlockPartitions N p, (∏ S ∈ π, Mf N S.card) * polymerSum p (K N) π := by
    rw [mul_sum]
    exact sum_congr rfl fun π _ => truncatedPartitionWeight_eq' hχ hN1 hlam p π
  rw [heq]
  refine ⟨mul_pos (pow_pos hNC N) hpos, ?_⟩
  rw [Real.log_mul (pow_pos hNC N).ne' hpos.ne', Real.log_pow]
  have e : (N : ℝ) * Real.log ((N : ℝ) * dipoleNormalization χ N β lam) +
      Real.log (∑ π ∈ boundedBlockPartitions N p, (∏ S ∈ π, Mf N S.card) *
        polymerSum p (K N) π) -
      (N * Real.log ((N : ℝ) * dipoleNormalization χ N β lam) -
        N * rateFunction p msf kmult γs) =
      Real.log (∑ π ∈ boundedBlockPartitions N p, (∏ S ∈ π, Mf N S.card) *
        polymerSum p (K N) π) + N * rateFunction p msf kmult γs := by ring
  rw [e]
  exact hb

/-! ### Proposition 5.45 -/

/-- The bookkeeping of the comparison: with `log Z = log N! + log z_{Id}`,
(5.162) and (5.163) give `|log z_{Id} - log ẑ| ≤ (C + 1) N δ`. -/
theorem abs_sub_le_of_estimates {A B D E c ℓ I N δ C : ℝ}
    (hA : |A - (2 * N * Real.log N + N * (ℓ - 1) - N * I)| ≤ C * N * δ)
    (hABD : A = B + D) (hB : |B - (N * Real.log N - N)| ≤ N * (δ / 3))
    (hE : |E - (N * (Real.log N + c) - N * I)| ≤ δ / 3 * N) (hc : |c - ℓ| ≤ δ / 3)
    (hN : 0 ≤ N) : |D - E| ≤ (C + 1) * N * δ := by
  have hNc : |N * c - N * ℓ| ≤ N * (δ / 3) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hN]
    exact mul_le_mul_of_nonneg_left hc hN
  have e : D - E = (A - (2 * N * Real.log N + N * (ℓ - 1) - N * I)) -
      (B - (N * Real.log N - N)) - (E - (N * (Real.log N + c) - N * I)) - (N * c - N * ℓ) := by
    rw [hABD]
    ring
  rw [e]
  rw [abs_le] at hA hB hE hNc ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hE.1, hE.2, hNc.1, hNc.2]

/-- **Proposition 5.45**, from the
statement of Theorem 2: the conclusion is the type of the frozen statement
`MultipoleBKT.proposition_5_45`. -/
theorem proposition_5_45_of_theorem_2 (h2 : TheoremTwo.Theorem2Statement) :
    TheoremOne.Prop545Statement := by
  intro χ hχ p₀ hp₀ β hβ
  have hp : 1 ≤ pBeta p₀ β := TheoremTwo.one_le_pBeta' hp₀ hβ
  have hpS : (pBeta p₀ β : ℕ∞) ≤ pStar β := TheoremTwo.pBeta_le_pStar hp₀ hβ
  obtain ⟨M₀, hM₀, hT⟩ := h2 χ hχ p₀ hp₀ β hβ
  refine ⟨M₀, hM₀, fun M hM => ?_⟩
  obtain ⟨msf, kmult, h1, h247, h248, h2item, -⟩ := hT M hM
  have hMsfL : TheoremTwo.MsfLimits χ β M msf := fun lam hlam hlam1 => (h1 lam hlam hlam1).1
  -- uniform constants in (2.47), (2.48)
  obtain ⟨Cm, hCm, lm, hlm, -, hmb⟩ := msfBound_uniform (p := pBeta p₀ β) (msf := msf)
    (fun lam hlam hlam1 => TheoremTwo.msf_one hχ hβ hMsfL hlam hlam1) h247
  obtain ⟨Ck, hCk, lk, hlk, -, hkb⟩ := kmultBound_uniform (p := pBeta p₀ β) (kmult := kmult) h248
  set C₁ := max Cm Ck with hC₁_def
  have hC₁ : 0 < C₁ := lt_max_of_lt_left hCm
  -- the rate function, the polymer gas and Theorem 2 item (2)
  obtain ⟨lr, hlr, -, C'', -, hrate⟩ := TheoremTwo.exists_rateSetup hp hC₁
  obtain ⟨Ct, hCt, hlogpoly⟩ := exists_log_polymerSum (2 * C₁) (by positivity) (pBeta p₀ β)
  obtain ⟨C₂, hC₂, l₂, hl₂, hl₂1, hZ⟩ := h2item
  set lt : ℝ := min 1 (1 / (2 * Ct)) with hlt_def
  have hlt : 0 < lt := lt_min one_pos (by positivity)
  refine ⟨C₂ + 1, by positivity, min (min l₂ lm) (min lk (min lr lt)),
    lt_min (lt_min hl₂ hlm) (lt_min hlk (lt_min hlr hlt)),
    (min_le_left _ _).trans ((min_le_left _ _).trans hl₂1), fun lam hlam hlaml => ?_⟩
  have hlam₂ : lam < l₂ := hlaml.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hlamm : lam < lm := hlaml.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlamk : lam < lk := hlaml.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlamr : lam < lr :=
    hlaml.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlamt : lam < lt :=
    hlaml.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlam1 : lam < 1 := hlamt.trans_le (min_le_left _ _)
  have hms : MsfBound (pBeta p₀ β) (msf lam) C₁ lam :=
    TheoremTwo.MsfBound.mono (hmb lam hlam hlamm) hCm (le_max_left _ _) hlam.le
  have hks : KmultBound (pBeta p₀ β) (kmult lam) C₁ lam :=
    TheoremTwo.KmultBound.mono (hkb lam hlam hlamk) (le_max_right _ _) hlam
  obtain ⟨hs, ⟨γs, ⟨hγs, hmin⟩, -⟩, -⟩ := hrate lam hlam hlamr (msf lam) (kmult lam) hms hks
  have hCtl : Ct * lam ^ 2 ≤ 1 / 2 := by
    have h1' : lam < 1 / (2 * Ct) := hlamt.trans_le (min_le_right _ _)
    have h2' : lam ^ 2 ≤ lam := by nlinarith
    have h3' : Ct * lam < 1 / 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Ct)] at h1'
      linarith
    nlinarith
  -- the error rate
  set δ := errorRate p₀ β lam with hδ_def
  have hδ : 0 < δ := TheoremTwo.errorRate_pos hβ hlam
  have hδ3 : 0 < δ / 3 := by positivity
  -- the right-hand side (5.163)
  have hR := eventually_abs_log_zHat_le hχ hp hpS hlam hs hγs hmin (h1 lam hlam hlam1).1
    (h1 lam hlam hlam1).2 hCtl (fun K => hlogpoly (kmult lam) C₁ lam K hlam hlam1.le) hδ3
  -- the left-hand side (5.162)
  obtain ⟨-, N₀, hN₀⟩ := hZ lam hlam hlam₂
  have hS := TheoremOne.eventually_abs_log_factorial_sub_le hδ3
  have hCN := TheoremOne.eventually_abs_log_dipoleNormalization_sub_le hχ hβ hlam hδ3
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    (hR.and (hS.and (hCN.and ((eventually_ge_atTop N₀).and (eventually_ge_atTop 1)))))
  refine ⟨N₁, fun N hN => ?_⟩
  obtain ⟨⟨hzpos, hzb⟩, hSN, hCNN, hNN₀, hN1⟩ := hN₁ N hN
  obtain ⟨hZpos, hZtop, hZb⟩ := hN₀ N hNN₀
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  intro zId zHat
  -- `Z = N! z_{Id}`
  have hZeq : partitionFunction χ N β lam = (N.factorial : ℝ≥0∞) * zId :=
    TheoremOne.partitionFunction_eq_factorial_mul χ N β lam
  have hfac : (N.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hzId0 : 0 < zId := by
    rw [hZeq] at hZpos
    exact pos_iff_ne_zero.2 fun h => by rw [h, mul_zero] at hZpos; exact lt_irrefl 0 hZpos
  have hzIdtop : zId < ∞ := by
    rw [hZeq] at hZtop
    refine lt_of_le_of_lt (le_mul_of_one_le_left (by simp) ?_) hZtop
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero N)
  refine ⟨hzId0, hzIdtop, hzpos, ?_⟩
  have hzr : 0 < zId.toReal := ENNReal.toReal_pos hzId0.ne' hzIdtop.ne
  have hZr : (partitionFunction χ N β lam).toReal = (N.factorial : ℝ) * zId.toReal := by
    rw [hZeq, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hlogZ : Real.log (partitionFunction χ N β lam).toReal =
      Real.log (N.factorial : ℝ) + Real.log zId.toReal := by
    rw [hZr, Real.log_mul (by exact_mod_cast Nat.factorial_ne_zero N) hzr.ne']
  have hCpos : 0 < dipoleNormalization χ N β lam := dipoleNormalization_pos hχ hlam β hN1
  have hlogNC : Real.log ((N : ℝ) * dipoleNormalization χ N β lam) =
      Real.log N + Real.log (dipoleNormalization χ N β lam) :=
    Real.log_mul hN0.ne' hCpos.ne'
  rw [TheoremTwo.RateSetup.sInf_eq_of_isMinOn hγs hmin] at hZb
  rw [hlogNC] at hzb
  exact abs_sub_le_of_estimates hZb hlogZ hSN hzb hCNN hN0.le

end PropFiveFortyFive

end MultipoleBKT

end
