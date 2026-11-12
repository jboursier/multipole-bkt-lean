/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.GoodEstimates
public import MultipoleBKT.UpperBound.UpperBoundLDP.PolymerLog
public import MultipoleBKT.UpperBound.UpperBoundLDP.Core
public import MultipoleBKT.UpperBound.AbsoluteUpper.Majorant
public import MultipoleBKT.LowerBound.LowerBoundLDP.AtLambda
public import MultipoleBKT.UpperBound.Hierarchical.Expansion
public import MultipoleBKT.UpperBound.BoundedUpper.Inputs
public import MultipoleBKT.UpperBound.ExpansionPlus.ActivityDiff
public import MultipoleBKT.UpperBound.AbsoluteUpper.Bounded

/-!
# Proposition 5.43, Steps 1–2: the good dipoles of a frozen configuration

The paper: proof of Proposition 5.43.
At fixed `N` and `λ`, from the estimates of Propositions 5.18–5.20, 4.23–4.24 and the limits (2.45)
(all hypotheses here, with their constants), for every frozen configuration `(V_bad, Z)` and every
partition `π` of `V_good` with the profile `n` (satisfying (5.56)),

  `𝖬̂^{+,Z}(π) W(Z) ≤ exp(∑ₖ n_k log 𝗆(k) - (N' - m) log N - N h(n/N) + K_δ N δ + K_V |V_bad|)`

(`good_bound`), where `K_δ` may depend on `ε₀` but `K_V` does not:

* Step 1:
  `𝖬̂(S) ≤ (𝗆(|S|) + (C_{ε₀} + C₀ + 1) R̄^{-2} + C ε₀^{α|S|} |V_bad|/N) N^{1-|S|}`
  from (5.68) (Proposition 5.19, hatted), `|𝖬^0_{ε₀} - 𝖬^0_∞|` and the limit (2.45), then
  `MultipoleBKT.UpperBoundLDP.prod_le_of_bounds`;
* Step 2: `log W(Z) ≤ log polymerSum_p(𝖪^mult)(π) + 4 e² D + C N δ`
  (`MultipoleBKT.UpperBoundLDP.exists_log_disjointSum_le`, with Proposition 5.20 for the absolute
  convergence and (5.71)), `D ≤ C_{ε₀} N δ + C |V_bad|` from (5.69) (hatted), (4.45) and
  `𝖪^0_∞ = 𝖪^mult` (Corollary 4.61), and `log polymerSum = -N h(γ) + o(N)` (eq. (4.155),
  `MultipoleBKT.UpperBoundLDP.exists_log_polymerSum_subpartition`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical PropFiveFortyFive LowerBoundLDP UpperBound SetPartition

/-- `∏_{S ∈ π} 𝗆(|S|)/N^{|S|-1} = exp(∑ₖ n_k log 𝗆(k) - (N' - m) log N)`. -/
theorem prod_msf_div_eq {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) {n : Fin p → ℕ} (hbc : blockCount p π = n)
    {msf : ℕ → ℝ} (hmsf : ∀ k, 1 ≤ k → k ≤ p → 0 < msf k) :
    ∏ S ∈ π, msf S.card / (N : ℝ) ^ (S.card - 1) =
      Real.exp (∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
        ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) * Real.log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [prod_card_eq_prod_blockCount hπ1 (fun k => msf k / (N : ℝ) ^ (k - 1)), hbc]
  have hpos : ∀ i : Fin p, 0 < msf ((i : ℕ) + 1) / (N : ℝ) ^ ((i : ℕ) + 1 - 1) := fun i =>
    div_pos (hmsf _ (by omega) i.2) (by positivity)
  rw [← Real.exp_log (prod_pos fun i _ => pow_pos (hpos i) (n i)),
    Real.log_prod (fun i _ => (pow_pos (hpos i) (n i)).ne')]
  congr 1
  simp only [Real.log_pow, Nat.add_sub_cancel]
  rw [show ∑ i : Fin p, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1) / (N : ℝ) ^ (i : ℕ)) =
      ∑ i : Fin p, ((n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
        (n i : ℝ) * (i : ℕ) * Real.log N) from
    sum_congr rfl fun i _ => by
      rw [Real.log_div (hmsf _ (by omega) i.2).ne' (by positivity), Real.log_pow]
      ring]
  rw [sum_sub_distrib]
  congr 1
  push_cast
  rw [← sum_mul, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  ring

/-! ### Step 1: the hatted multipole partition functions -/

/-- **Step 1 at fixed `N`**: from (5.68), `|𝖬^0_{ε₀} - 𝖬^0_∞|`, the limit (2.45)
at `N` and the lower bound on `𝗆`, for a partition `π` with the profile `n` and (5.56),
`∏_{S ∈ π} 𝖬̂(S) ≤ exp(∑ₖ n_k log 𝗆(k) - (N' - m) log N + C_m (C_{ε₀} + C₀ + 1) p (1 + A) R N
+ C_m C p |V_bad|)`. -/
theorem hat_prod_le_exp {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) (hπN : π.card ≤ N) {n : Fin p → ℕ}
    (hbc : blockCount p π = n) {lam ε₀ α A R Cε CM C0 Cm Vc : ℝ} (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hα : 0 ≤ α) (hA : A = ε₀ ^ (-α)) (hR : 0 ≤ R)
    (hCε : 0 ≤ Cε) (hCM : 0 ≤ CM) (hC0 : 0 ≤ C0) (hCm : 1 ≤ Cm) (hVc : 0 ≤ Vc)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1)))
    {Mh M0 Mz : Finset ℕ → ℝ} {msf : ℕ → ℝ}
    (hmsf : ∀ k, 1 ≤ k → k ≤ p → lam ^ (2 * (k - 1)) / Cm ≤ msf k)
    (hMh0 : ∀ S ∈ π, 0 ≤ Mh S)
    (hMplus : ∀ S ∈ π, |Mh S - M0 S| ≤
      (Cε * R + CM * ε₀ ^ (α * S.card) * (Vc / N)) / (N : ℝ) ^ (S.card - 1))
    (hM0 : ∀ S ∈ π, |M0 S - Mz S| ≤ C0 / (N : ℝ) ^ (S.card - 1) * R)
    (hlim : ∀ S ∈ π, |(N : ℝ) ^ (S.card - 1) * Mz S - msf S.card| ≤ R) :
    ∏ S ∈ π, Mh S ≤ Real.exp (∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
        ((∑ i : Fin p, ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) * Real.log N +
      (Cm * (Cε + C0 + 1) * (p * (1 + A)) * R * N + Cm * CM * p * Vc)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.rpow_nonneg hε₀.le _
  have hCm0 : (0 : ℝ) < Cm := by linarith
  have hmpos : ∀ k, 1 ≤ k → k ≤ p → 0 < msf k := fun k hk1 hkp =>
    lt_of_lt_of_le (div_pos (pow_pos hlam _) hCm0) (hmsf k hk1 hkp)
  set a := (Cε + C0 + 1) * R with ha
  set b := CM * (Vc / N) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hMh : ∀ S ∈ π, Mh S ≤ (msf S.card + a + b * ε₀ ^ (α * S.card)) / (N : ℝ) ^ (S.card - 1) := by
    intro S hS
    have hNk : (0 : ℝ) < (N : ℝ) ^ (S.card - 1) := by positivity
    have e1 := (abs_le.1 (hMplus S hS)).2
    have e2 := (abs_le.1 (hM0 S hS)).2
    have e3 := (abs_le.1 (hlim S hS)).2
    have e3' : Mz S ≤ (msf S.card + R) / (N : ℝ) ^ (S.card - 1) := by
      rw [le_div_iff₀ hNk]; linarith
    have hsum : Mh S ≤
        (Cε * R + CM * ε₀ ^ (α * S.card) * (Vc / N)) / (N : ℝ) ^ (S.card - 1) +
          C0 / (N : ℝ) ^ (S.card - 1) * R + (msf S.card + R) / (N : ℝ) ^ (S.card - 1) := by
      linarith
    refine hsum.trans (le_of_eq ?_)
    rw [ha, hb]
    field_simp
    ring
  have hprod := prod_le_of_bounds hN hπ1 hπN hlam hε₀ hε₀1 hα hA0 hA hCm ha0 hb0 hn
    (fun k hk1 hkp => hmsf k hk1 hkp) hMh0 hMh
  rw [prod_msf_div_eq hN hπ1 hbc hmpos, ← Real.exp_add] at hprod
  refine hprod.trans (Real.exp_le_exp.2 (le_of_eq ?_))
  have hNV : (N : ℝ) * (Vc / N) = Vc := mul_div_cancel₀ _ hN0.ne'
  rw [ha, hb]
  have : Cm * N * ((Cε + C0 + 1) * R * (p * (1 + A)) + CM * (Vc / N) * p) =
      Cm * (Cε + C0 + 1) * (p * (1 + A)) * R * N + Cm * CM * p * (N * (Vc / N)) := by ring
  rw [this, hNV]

/-! ### Step 2: the cluster series -/

/-- **The activity difference on a retained cluster**: from (5.69) (hatted),
(4.45), `𝖪^0_∞ = 𝖪^mult` and the lower bounds on the blocks,
`|𝖪̂(X) - 𝖪^mult(X)| ≤ (C_{ε₀} C_z^p + C_K C_l^p) R N ∏ u(S) + C C_z^p |V_bad| ∏ ε₀^{α|S|} u(S)`. -/
theorem retained_diff_le {N p : ℕ} (hN : 1 ≤ N) {X : Finset (Finset ℕ)} (hXP : IsSubpartition X)
    (hX1 : 1 ≤ X.card) (hXp : X.card ≤ p) {lam ε₀ α R Cε CK1 CK0 Cz Clow Vc : ℝ}
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hR : 0 ≤ R) (hCε : 0 ≤ Cε) (hCK1 : 0 ≤ CK1)
    (hCK0 : 0 ≤ CK0) (hCz : 1 ≤ Cz) (hClow : 1 ≤ Clow) (hVc : 0 ≤ Vc)
    {K₁ K₀ K₂ : ℝ} {M0 Mz : Finset ℕ → ℝ}
    (hz : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (Cz * (N : ℝ) ^ (S.card - 1)) ≤ M0 S)
    (hm : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (Clow * (N : ℝ) ^ (S.card - 1)) ≤ Mz S)
    (e1 : |K₁ - K₀| ≤ (Cε * R + CK1 * ε₀ ^ (α * (X.biUnion id).card) * (Vc / N)) /
      ((N : ℝ) ^ ((X.biUnion id).card - 1) * ∏ S ∈ X, M0 S))
    (e2 : |K₀ - K₂| ≤ CK0 * R / ((∏ S ∈ X, Mz S) * (N : ℝ) ^ ((X.biUnion id).card - 1))) :
    |K₁ - K₂| ≤ ((Cε * Cz ^ p + CK0 * Clow ^ p) * R) * N * ∏ S ∈ X, blockWeight lam N S +
      (CK1 * Cz ^ p * Vc) * ∏ S ∈ X, (ε₀ ^ (α * S.card) * blockWeight lam N S) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hI1 := inv_prod_mul_pow_le hXP hX1 hXp hlam hCz hN hz
  have hI2 := inv_prod_mul_pow_le hXP hX1 hXp hlam hClow hN hm
  have hnum1 : 0 ≤ Cε * R + CK1 * ε₀ ^ (α * (X.biUnion id).card) * (Vc / N) := by positivity
  have e1' : |K₁ - K₀| ≤ (Cε * R + CK1 * ε₀ ^ (α * (X.biUnion id).card) * (Vc / N)) *
      (Cz ^ p * (N * ∏ S ∈ X, blockWeight lam N S)) := by
    refine e1.trans ?_
    rw [div_eq_mul_one_div, mul_comm ((N : ℝ) ^ _)]
    exact mul_le_mul_of_nonneg_left hI1 hnum1
  have e2' : |K₀ - K₂| ≤ CK0 * R * (Clow ^ p * (N * ∏ S ∈ X, blockWeight lam N S)) := by
    refine e2.trans ?_
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hI2 (by positivity)
  have hεprod : ε₀ ^ (α * (X.biUnion id).card) * ∏ S ∈ X, blockWeight lam N S =
      ∏ S ∈ X, (ε₀ ^ (α * S.card) * blockWeight lam N S) := by
    rw [rpow_card_biUnion hXP hε₀, prod_mul_distrib]
  have hNV : (Vc / N) * N = Vc := div_mul_cancel₀ _ hN0.ne'
  calc |K₁ - K₂| ≤ |K₁ - K₀| + |K₀ - K₂| := abs_sub_le _ _ _
    _ ≤ (Cε * R + CK1 * ε₀ ^ (α * (X.biUnion id).card) * (Vc / N)) *
          (Cz ^ p * (N * ∏ S ∈ X, blockWeight lam N S)) +
        CK0 * R * (Clow ^ p * (N * ∏ S ∈ X, blockWeight lam N S)) := add_le_add e1' e2'
    _ = ((Cε * Cz ^ p + CK0 * Clow ^ p) * R) * N * ∏ S ∈ X, blockWeight lam N S +
          (CK1 * Cz ^ p) * ((Vc / N) * N) *
            (ε₀ ^ (α * (X.biUnion id).card) * ∏ S ∈ X, blockWeight lam N S) := by ring
    _ = _ := by rw [hεprod, hNV]

/-- **Step 2 at fixed `N`** (5.144), as a real inequality: if
`log W ≤ log P + 4 e² D + B`, `D ≤ a' N e^{p(1+A)} + b' e^p`, `log P + N h ≤ δ N`,
then `log W ≤ -N h + δ N + 4 e² (a' N e^{p(1+A)} + b' e^p) + B`. -/
theorem log_W_arith {logW logP D B a' b' Nr h δ E1 E2 : ℝ}
    (hW : logW ≤ logP + 4 * Real.exp 2 * D + B)
    (hD : D ≤ a' * Nr * E1 + b' * E2) (hP : logP + Nr * h ≤ δ * Nr) :
    logW ≤ -(Nr * h) + δ * Nr + 4 * Real.exp 2 * (a' * Nr * E1 + b' * E2) + B := by
  have h4 : 0 ≤ 4 * Real.exp 2 := by positivity
  have := mul_le_mul_of_nonneg_left hD h4
  linarith

/-- **The final combination** (Steps 1–2): with `R ≤ δ`,
`P W ≤ exp(S + c₁ R N + c₂ V) exp(-N h + δ N + 4e² (c₃ R N E₁ + c₄ V E₂) + C N δ)`
is at most `exp(S - N h + (c₁ + 4e² c₃ E₁ + C + 1) N δ + (c₂ + 4e² c₄ E₂) V)`. -/
theorem good_arith {P W S h R δ Nr Vc c₁ c₂ c₃ c₄ E₁ E₂ C : ℝ} (_hP0 : 0 ≤ P) (hW : 0 < W)
    (hPle : P ≤ Real.exp (S + (c₁ * R * Nr + c₂ * Vc)))
    (hlogW : Real.log W ≤ -(Nr * h) + δ * Nr +
      4 * Real.exp 2 * ((c₃ * R) * Nr * E₁ + (c₄ * Vc) * E₂) + C * Nr * δ)
    (hRδ : R ≤ δ) (hNr : 0 ≤ Nr) (hc₁ : 0 ≤ c₁) (hc₃ : 0 ≤ c₃) (hE₁ : 0 ≤ E₁) :
    P * W ≤ Real.exp (S - Nr * h + (c₁ + 4 * Real.exp 2 * c₃ * E₁ + C + 1) * Nr * δ +
      (c₂ + 4 * Real.exp 2 * c₄ * E₂) * Vc) := by
  rw [← Real.exp_log hW]
  refine (mul_le_mul_of_nonneg_right hPle (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : c₁ * R * Nr ≤ c₁ * δ * Nr :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRδ hc₁) hNr
  have h2 : 4 * Real.exp 2 * (c₃ * R * Nr * E₁) ≤ 4 * Real.exp 2 * (c₃ * δ * Nr * E₁) := by
    have h4 : 0 ≤ 4 * Real.exp 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ h4
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRδ hc₃) hNr) hE₁
  nlinarith [h1, h2, hlogW]

open scoped Classical in
/-- **Steps 1–2 at fixed `N`** (see the module docstring). -/
theorem good_bound {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ N : ℕ} {β lam M ε₀ L : ℝ}
    (hN : 1 ≤ N) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hM : 1 ≤ M)
    {n : Fin (pBeta p₀ β) → ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ}
    {R δ Cε CM C0 Cm CK1 CK0 Cz Clow Cs Ccoef C20 : ℝ}
    (hR : 0 ≤ R) (hRδ : R ≤ δ) (hCε : 0 ≤ Cε) (hCM : 0 ≤ CM) (hC0 : 0 ≤ C0) (hCm : 1 ≤ Cm)
    (hCK1 : 0 ≤ CK1) (hCK0 : 0 ≤ CK0) (hCz : 1 ≤ Cz) (hClow : 1 ≤ Clow) (hCs : 0 ≤ Cs)
    (hCcoef : 0 ≤ Ccoef)
    (h556 : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
      (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N)
    (hMplus : ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ S : Finset ℕ, S ⊆ BoundedUpper.goodLabels V → 1 ≤ S.card → S.card ≤ pBeta p₀ β →
        |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
          (Cε * R + CM * ε₀ ^ (alphaExponent β * S.card) * (V.card / N)) /
            (N : ℝ) ^ (S.card - 1))
    (hM0 : ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ pBeta p₀ β →
      |zeroPartitionFunction χ N p₀ β lam M ε₀ {S} - multipolePartitionFunction χ N β lam M S| ≤
        C0 / (N : ℝ) ^ (S.card - 1) * R)
    (hlim : ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ pBeta p₀ β →
      |(N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S - msf S.card| ≤ R)
    (hmsf : ∀ k, 1 ≤ k → k ≤ pBeta p₀ β → lam ^ (2 * (k - 1)) / Cm ≤ msf k)
    (hKplus : ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ BoundedUpper.goodLabels V →
        2 ≤ X.card → (X.biUnion id).card ≤ pBeta p₀ β →
        |hatActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
          (Cε * R + CK1 * ε₀ ^ (alphaExponent β * (X.biUnion id).card) * (V.card / N)) /
            ((N : ℝ) ^ ((X.biUnion id).card - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X))
    (hK0 : ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
      2 ≤ X.card → (X.biUnion id).card ≤ pBeta p₀ β →
      |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
        CK0 * R / ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
          (N : ℝ) ^ ((X.biUnion id).card - 1)))
    (hlow0 : ∀ S : Finset ℕ, 2 ≤ S.card → S.card ≤ pBeta p₀ β →
      lam ^ (2 * (S.card - 1)) / (Cz * (N : ℝ) ^ (S.card - 1)) ≤
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S})
    (hlow : ∀ S : Finset ℕ, S ⊆ Finset.range N → 1 ≤ S.card → S.card ≤ pBeta p₀ β →
      lam ^ (2 * (S.card - 1)) / (Clow * (N : ℝ) ^ (S.card - 1)) ≤
        multipolePartitionFunction χ N β lam M S)
    (hret : ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ BoundedUpper.goodLabels V →
        2 ≤ X.card → (X.biUnion id).card ≤ pBeta p₀ β →
        |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1))
    (hretm : ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card ≤ pBeta p₀ β →
      |multipoleActivity χ N β lam M X| ≤ (2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1))
    (h20 : ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
      ∀ π : Finset (Finset ℕ), IsSubpartition π →
        (∀ S ∈ π, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
        (∀ S ∈ π, S.card ≤ pBeta p₀ β) → AbsoluteUpper.ProfileBound p₀ β lam ε₀ N π →
        AbsoluteUpper.AbsoluteUpperBounds (hatActivity χ N p₀ β lam M ε₀ L V Z) π (pBeta p₀ β)
          (C20 * N * δ))
    (hpoly : ∀ π : Finset (Finset ℕ), IsSubpartition π → (∀ S ∈ π, S.card ≤ pBeta p₀ β) →
      π.card ≤ N →
      0 < polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π ∧
        |Real.log (polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π) +
          N * rateCluster (pBeta p₀ β) kmult (profileVec (pBeta p₀ β) N π)| ≤ δ * N)
    (hlogD : ∀ (π : Finset (Finset ℕ)) (K₁ K₂ : Finset (Finset ℕ) → ℝ) (B : ℝ),
      IsSubpartition π → π.card ≤ N →
      (∀ X ⊆ π, X.card ≤ 1 → K₁ X = 0) →
      (∀ X ⊆ π, Retained (pBeta p₀ β) X →
        |K₁ X| ≤ (Cs + 2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1)) →
      (∀ X ⊆ π, Retained (pBeta p₀ β) X →
        |K₂ X| ≤ (Cs + 2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1)) →
      (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
          |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)|) →
      (∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected ∧
              ∃ i, pBeta p₀ β < ((X i).biUnion id).card),
          |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)| ≤ B) →
      0 < LowerBoundLDP.disjointSum K₁ π ∧ 0 < polymerSum (pBeta p₀ β) K₂ π ∧
        Real.log (LowerBoundLDP.disjointSum K₁ π) ≤ Real.log (polymerSum (pBeta p₀ β) K₂ π) +
          4 * Real.exp 2 *
            (∑ Y ∈ π.powerset, if Retained (pBeta p₀ β) Y then |K₁ Y - K₂ Y| else 0) + B) :
    ∀ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
        (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
      ∀ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
          (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
        ∀ Z : Fin N → ℂ × ℂ, AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
          hatPartitionFunctions χ N p₀ β lam M ε₀ L V Z π *
              clusterSeriesW χ N p₀ β lam M ε₀ L V Z π ≤
            Real.exp (∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
              ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) *
                Real.log N -
              N * rateCluster (pBeta p₀ β) kmult (fun i => (n i : ℝ) / N) +
              (Cm * (Cε + C0 + 1) * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) +
                4 * Real.exp 2 * (Cε * Cz ^ pBeta p₀ β + CK0 * Clow ^ pBeta p₀ β) *
                  Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) + C20 + 1) * N * δ +
              (Cm * CM * pBeta p₀ β + 4 * Real.exp 2 * (CK1 * Cz ^ pBeta p₀ β) *
                Real.exp (pBeta p₀ β)) *
                (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ)) := by
  intro V hV π hπ Z hZ
  have hα : 0 ≤ alphaExponent β := (TheoremTwo.alphaExponent_pos β).le
  have hA : 0 ≤ ε₀ ^ (-alphaExponent β) := Real.rpow_nonneg hε₀.le _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hVcard : V.card = N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i :=
    (mem_powersetCard.1 hV).2
  obtain ⟨hπpart, hπp, hbc⟩ := mem_filter.1 hπ
  obtain ⟨hπP, hπU⟩ := mem_partitions.1 hπpart
  have hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ pBeta p₀ β := fun S hS =>
    ⟨card_pos.2 (hπP.1 S hS), hπp S hS⟩
  have hgoodsub : ∀ S ∈ π, S ⊆ BoundedUpper.goodLabels V := fun S hS => by
    rw [BoundedUpper.goodLabels, ← hπU]
    exact subset_biUnion_of_mem id hS
  have hrange : ∀ S ∈ π, S ⊆ Finset.range N := fun S hS =>
    (hgoodsub S hS).trans (ExpansionPlus.goodLabels_subset_range V)
  have hπN : π.card ≤ N := by
    have h1 := PropFiveFortyFive.card_le_card_biUnion hπP
    have h2 : (π.biUnion id).card ≤ N := by
      calc (π.biUnion id).card ≤ (Finset.range N).card :=
            card_le_card (biUnion_subset.2 fun S hS => hrange S hS)
        _ = N := card_range N
    omega
  have hn' := blockCount_le_of_profile hbc h556
  have hprof : AbsoluteUpper.ProfileBound p₀ β lam ε₀ N π := fun k hk2 hkp => by
    have := hn' k hk2 hkp
    linarith [show ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) =
      ε₀ ^ (-alphaExponent β) * lam ^ (2 * (k - 1)) * N by ring]
  have hbad : badPointsOn p₀ β lam M ε₀ V Z = V := hZ.1
  -- Step 1
  have hstep1 := hat_prod_le_exp hN hπ1 hπN hbc hlam hε₀ hε₀1 hα rfl hR hCε hCM hC0 hCm
    (Nat.cast_nonneg V.card) hn' hmsf
    (fun S _ => hatPartitionFunction_nonneg (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN S)
    (fun S hS => hMplus V Z hbad S (hgoodsub S hS) (hπ1 S hS).1 (hπ1 S hS).2)
    (fun S hS => hM0 S (hπ1 S hS).1 (hπ1 S hS).2)
    (fun S hS => hlim S (hπ1 S hS).1 (hπ1 S hS).2)
  -- Step 2
  set K₁ := hatActivity χ N p₀ β lam M ε₀ L V Z
  set K₂ := multipoleActivity χ N β lam M
  have hXsub : ∀ X ⊆ π, IsSubpartition X := fun X hX => isSubpartition_mono hπP hX
  have hXgood : ∀ X ⊆ π, X.biUnion id ⊆ BoundedUpper.goodLabels V := fun X hX =>
    biUnion_subset.2 fun S hS => hgoodsub S (hX hS)
  have hXrange : ∀ X ⊆ π, X.biUnion id ⊆ Finset.range N := fun X hX =>
    biUnion_subset.2 fun S hS => hrange S (hX hS)
  have hb₁ : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |K₁ X| ≤ (Cs + 2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1) :=
    fun X hX hr => (hret V Z hZ X (hXsub X hX) (hXgood X hX) hr.1 hr.2).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hb₂ : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |K₂ X| ≤ (Cs + 2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1) :=
    fun X hX hr => (hretm X (hXsub X hX) hr.1 hr.2).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hK1 : ∀ X ⊆ π, X.card ≤ 1 → K₁ X = 0 := fun X _ h =>
    hatActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h
  obtain ⟨-, habs, -, hbadsum⟩ := h20 V Z hZ π hπP (fun S hS => hgoodsub S hS) hπp hprof
  obtain ⟨hW, -, hlogW⟩ := hlogD π K₁ K₂ (C20 * N * δ) hπP hπN hK1 hb₁ hb₂ habs hbadsum
  have hd : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |K₁ X - K₂ X| ≤ ((Cε * Cz ^ pBeta p₀ β + CK0 * Clow ^ pBeta p₀ β) * R) * N *
          ∏ S ∈ X, blockWeight lam N S +
        (CK1 * Cz ^ pBeta p₀ β * V.card) *
          ∏ S ∈ X, (ε₀ ^ (alphaExponent β * S.card) * blockWeight lam N S) := by
    intro X hX hr
    have hXP := hXsub X hX
    have hz : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (Cz * (N : ℝ) ^ (S.card - 1)) ≤
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
      intro S hS
      rw [← pow_mul]
      rcases Nat.lt_or_ge S.card 2 with h | h
      · have hc : S.card = 1 := by have := (hπ1 S (hX hS)).1; omega
        rw [AbsoluteUpper.zeroPartitionFunction_singleton hχ hlam hε₀ hN hc, hc]
        simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
        exact div_le_one_of_le₀ hCz (by linarith)
      · exact hlow0 S h (hπ1 S (hX hS)).2
    have hm : ∀ S ∈ X, (lam ^ 2) ^ (S.card - 1) / (Clow * (N : ℝ) ^ (S.card - 1)) ≤
        multipolePartitionFunction χ N β lam M S := by
      intro S hS
      rw [← pow_mul]
      exact hlow S (hrange S (hX hS)) (hπ1 S (hX hS)).1 (hπ1 S (hX hS)).2
    have hzX : zeroPartitionFunction χ N p₀ β lam M ε₀ X =
        ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
      rw [zeroPartitionFunction]
      exact prod_congr rfl fun S _ => (prod_singleton _ S).symm
    have e1 := hKplus V Z hbad X hXP (hXgood X hX) hr.1 hr.2
    rw [hzX] at e1
    have e2 := hK0 X hXP (hXrange X hX) hr.1 hr.2
    rw [zeroActivityInf_eq_multipoleActivity hχ hlam β hN hM hXP] at e2
    exact retained_diff_le hN hXP (by have := hr.1; omega) (card_le_of_retained hπP hX hr)
      hlam hε₀ hR hCε hCK1 hCK0 hCz hClow (Nat.cast_nonneg _) hz hm e1 e2
  have hD := sum_retained_diff_le' hN hπ1 hπN hlam hε₀ hε₀1 hα hA rfl (by positivity)
    (by positivity) hn' hd
  obtain ⟨-, hpolyb⟩ := hpoly π hπP hπp hπN
  have hγ : profileVec (pBeta p₀ β) N π = fun i => (n i : ℝ) / N := by
    funext i
    simp only [profileVec, hbc]
  rw [hγ] at hpolyb
  have hlogW' := log_W_arith hlogW hD (abs_le.1 hpolyb).2
  have hWeq : clusterSeriesW χ N p₀ β lam M ε₀ L V Z π = LowerBoundLDP.disjointSum K₁ π := rfl
  rw [hWeq, hatPartitionFunctions]
  have hPh0 : 0 ≤ ∏ S ∈ π, hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
    prod_nonneg fun S _ => hatPartitionFunction_nonneg hχ hlam hε₀ hN S
  have hfin := good_arith (c₁ := Cm * (Cε + C0 + 1) * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))))
    (c₂ := Cm * CM * pBeta p₀ β) (c₃ := Cε * Cz ^ pBeta p₀ β + CK0 * Clow ^ pBeta p₀ β)
    (c₄ := CK1 * Cz ^ pBeta p₀ β) (E₁ := Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))))
    (E₂ := Real.exp (pBeta p₀ β)) (C := C20) hPh0 hW hstep1 hlogW' hRδ hN0.le
    (by positivity) (by positivity) (Real.exp_pos _).le
  rw [← hVcard]
  refine hfin.trans (le_of_eq ?_)
  congr 1

end UpperBoundLDP

end MultipoleBKT

end
