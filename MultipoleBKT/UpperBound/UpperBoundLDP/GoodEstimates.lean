/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.Estimates
public import MultipoleBKT.LowerBound.ExpansionErrors.Blocks
public import MultipoleBKT.UpperBound.ExpansionPlus.MultipoleDiff
public import MultipoleBKT.Main.TheoremTwo.Coefficients

/-!
# Proposition 5.43, Steps 1–2: the estimates on the good dipoles at fixed `N`

The paper: proof of Proposition 5.43.

* `zero_M_diff`: the one-sentence statement
  `|𝖬^0_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C_{ε₀} N^{1-|S|} R̄^{-2}`
  used in Step 1: as equation (4.42) of
  Proposition 4.24 (`MultipoleBKT.ExpansionErrors.eq_M_diff`), with eq. (A.47) in place of Lemma A.6.
* The block weights `u(S) = λ^{-2(|S|-1)}/N` of a subpartition with the profile bound (5.56):
  `∑_{S ∈ π} u(S) ≤ p (1 + ε₀^{-α(β)})` (`sum_blockWeight_le'`) and
  `∑_{S ∈ π} ε₀^{α(β)|S|} u(S) ≤ p` (`sum_epsBlockWeight_le`, the paper's "a profile with `r`
  multipoles and `k` dipoles contributes at most `C |V_bad| ε₀^{α(β)(k-r)}`", whose
  constant does not depend on `ε₀`).
* `prod_le_of_bounds` (Step 1): from
  `0 ≤ 𝖬̂(S) ≤ (𝗆(|S|) + a + b ε₀^{α|S|}) N^{1-|S|}` and `𝗆(k) ≥ λ^{2(k-1)}/C`,
  `∏_{S ∈ π} 𝖬̂(S) ≤ ∏_{S ∈ π} 𝗆(|S|) N^{1-|S|} e^{C N (a p (1+A) + b p)}`.
* `sum_retained_diff_le'` (Step 2, `D ≤ C_{ε₀} N δ + C |V_bad|`).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset Hierarchical PropFiveFortyFive LowerBoundLDP
open TwoComponentCoulomb (box)

/-! ### `𝖬^0_{ε₀}` against `𝖬^0_∞` -/

section ZeroMDiff

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- **`|𝖬^0_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C N^{1-|S|} R̄^{-2}`** (Step 1 of the proof of Proposition 5.43), for
`1 ≤ |S| = k ≤ p*(β)`: as (4.42), with the cutoff estimate (A.47) in place of Lemma A.6. `C` may
depend on `ε₀`. -/
theorem zero_M_diff (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (p₀ : ℕ) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = k →
          |zeroPartitionFunction χ N p₀ β lam M ε₀ {S} -
              multipolePartitionFunction χ N β lam M S| ≤
            C / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  intro ε₀ hε₀ hε₁
  obtain ⟨CA, hCA, hCC2⟩ := ExpansionErrors.multipoleIntegralCut_sub_le hχ hβ hk hkp hM p₀
    ε₀ hε₀
  obtain ⟨Cu, hCu, hup⟩ := multipoleIntegral_le hχ hβ hk hkp hM
  obtain ⟨Cn, hCn, lam₀, hlam₀, hlam₀1, hnorm⟩ :=
    ExpansionErrors.normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨CA * (2 / Z) ^ k + k * 2 ^ (k - 1) * Cn * (Cu * (2 / Z) ^ k), by positivity, lam₀,
    hlam₀, hlam₀1, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hnorm lam hlam hlt
  refine ⟨N₀, fun N hN S hS => ?_⟩
  obtain ⟨hN1, h2, hCe, -, hC, hCZ, hδ⟩ := hN₀ N hN
  have hlam1 : lam ≤ 1 := (hlt.trans_le hlam₀1).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  set R := truncationScale p₀ β lam
  have hR : 0 < R := Appendix.truncationScale_pos hlam
  set Ce := cutoffDipoleNormalization χ N p₀ β lam ε₀
  set C := dipoleNormalization χ N β lam
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hCe0 : 0 < Ce := lt_of_lt_of_le (by positivity) hCe
  have hratio : C / Ce ≤ 2 := by
    rw [div_le_iff₀ hCe0]
    nlinarith
  have hCe' : Z / 2 * lam ^ (2 - β) ≤ Ce := by linarith
  rw [UpperBound.ExpansionPlus.zeroPartitionFunction_singleton_eq_cut hχ hlam hε₀ hN1 S,
    multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN1 S, hS]
  have hJ : |multipoleIntegralCut χ N β lam M (ε₀ * R) S -
      multipoleIntegral χ N β lam M S| ≤ CA * N * (lam ^ (2 - β)) ^ k * R ^ (-2 : ℝ) := by
    have := hCC2 lam hlam hlam1 (by linarith) N S hS
    rw [ExpansionErrors.rpow_mul_natCast_eq hlam k] at this
    linarith
  have hQ : |((N : ℝ) * C)⁻¹ ^ k * multipoleIntegral χ N β lam M S| ≤
      Cu * (2 / Z) ^ k / (N : ℝ) ^ (k - 1) := by
    have hI0 : 0 ≤ multipoleIntegral χ N β lam M S := by
      rw [multipoleIntegral_eq_toReal_lintegral hχ hlam N β M S]
      exact ENNReal.toReal_nonneg
    have hI := hup lam hlam N S hS
    rw [ExpansionErrors.rpow_mul_natCast_eq hlam k] at hI
    have hA : (N : ℝ) * (Z / 2) * lam ^ (2 - β) ≤ N * C := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      linarith
    have h := MultipoleIntegral.gate_upper_algebra hk hNpos hℓ hZ hA hI hI0
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 (by positivity)) _) hI0)]
    refine h.trans ?_
    have hΛ : lam ^ (2 * (k - 1)) ≤ 1 := pow_le_one₀ hlam.le hlam1
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    rw [div_le_div_iff_of_pos_right hNk]
    calc Cu * (2 / Z) ^ k * lam ^ (2 * (k - 1)) ≤ Cu * (2 / Z) ^ k * 1 := by gcongr
      _ = Cu * (2 / Z) ^ k := mul_one _
  have h := ExpansionErrors.abs_normalized_sub_le hk hNpos hZ hℓ hCe' hC0 hratio hδ hJ hQ
  refine h.trans (le_of_eq ?_)
  ring

end ZeroMDiff

/-! ### Block weights of a subpartition -/

section BlockWeights

/-- For a subpartition `π` with blocks of sizes in `[1, p]`, at most `N` blocks and for `2 ≤ k ≤ p`: `∑_{S ∈ π} u(S) ≤ p (1 + A)`. -/
theorem sum_blockWeight_le' {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) (hπN : π.card ≤ N) {lam A : ℝ} (hlam : 0 < lam)
    (hA : 0 ≤ A)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1))) :
    ∑ S ∈ π, blockWeight lam N S ≤ p * (1 + A) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := sum_card_eq_sum_blockCount hπ1 (fun k => ((lam ^ 2) ^ (k - 1))⁻¹ / (N : ℝ))
  have hπN' : (π.card : ℝ) ≤ N := by exact_mod_cast hπN
  unfold blockWeight
  rw [hsum]
  calc ∑ i : Fin p, blockCount p π i • (((lam ^ 2) ^ ((i : ℕ) + 1 - 1))⁻¹ / (N : ℝ))
      ≤ ∑ _i : Fin p, (1 + A) := by
        refine sum_le_sum fun i _ => ?_
        rw [nsmul_eq_mul, Nat.add_sub_cancel]
        rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
        · rw [h0, pow_zero, inv_one]
          have hb : (blockCount p π i : ℝ) ≤ N :=
            (by exact_mod_cast blockCount_le_card p π i : (blockCount p π i : ℝ) ≤ π.card).trans
              hπN'
          calc (blockCount p π i : ℝ) * (1 / N) ≤ N * (1 / N) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = 1 := by field_simp
            _ ≤ 1 + A := by linarith
        · have hk := hn ((i : ℕ) + 1) (by omega) (by omega)
          rw [Nat.add_sub_cancel, pow_mul] at hk
          have hb : (blockCount p π i : ℝ) ≤ A * N * (lam ^ 2) ^ (i : ℕ) := hk
          have hl : (0 : ℝ) < (lam ^ 2) ^ (i : ℕ) := by positivity
          calc (blockCount p π i : ℝ) * (((lam ^ 2) ^ (i : ℕ))⁻¹ / N)
              ≤ A * N * (lam ^ 2) ^ (i : ℕ) * (((lam ^ 2) ^ (i : ℕ))⁻¹ / N) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = A := by field_simp
            _ ≤ 1 + A := by linarith
    _ = p * (1 + A) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The `ε₀`-weighted block weights**: for `2 ≤ k ≤ p`,
`ε₀ ∈ (0, 1]` and `α ≥ 0`, `∑_{S ∈ π} ε₀^{α|S|} u(S) ≤ p`. -/
theorem sum_epsBlockWeight_le {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) (hπN : π.card ≤ N) {lam ε₀ α : ℝ} (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hα : 0 ≤ α)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ ε₀ ^ (-α) * N * lam ^ (2 * (k - 1))) :
    ∑ S ∈ π, ε₀ ^ (α * S.card) * blockWeight lam N S ≤ p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := sum_card_eq_sum_blockCount hπ1
    (fun k => ε₀ ^ (α * k) * (((lam ^ 2) ^ (k - 1))⁻¹ / (N : ℝ)))
  have hπN' : (π.card : ℝ) ≤ N := by exact_mod_cast hπN
  unfold blockWeight
  rw [hsum]
  calc ∑ i : Fin p, blockCount p π i • (ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) *
        (((lam ^ 2) ^ ((i : ℕ) + 1 - 1))⁻¹ / (N : ℝ)))
      ≤ ∑ _i : Fin p, (1 : ℝ) := by
        refine sum_le_sum fun i _ => ?_
        rw [nsmul_eq_mul, Nat.add_sub_cancel]
        have he1 : ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) ≤ 1 :=
          Real.rpow_le_one hε₀.le hε₀1 (by positivity)
        rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
        · have hpow : (lam ^ 2) ^ (i : ℕ) = 1 := by rw [h0, pow_zero]
          rw [hpow, inv_one]
          have hb : (blockCount p π i : ℝ) ≤ N :=
            (by exact_mod_cast blockCount_le_card p π i : (blockCount p π i : ℝ) ≤ π.card).trans
              hπN'
          have he : 0 ≤ ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hε₀.le _
          calc (blockCount p π i : ℝ) * (ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) * (1 / N))
              ≤ N * (1 * (1 / N)) := by gcongr
            _ = 1 := by field_simp
        · have hk := hn ((i : ℕ) + 1) (by omega) (by omega)
          rw [Nat.add_sub_cancel, pow_mul] at hk
          have hb : (blockCount p π i : ℝ) ≤ ε₀ ^ (-α) * N * (lam ^ 2) ^ (i : ℕ) := hk
          have hl : (0 : ℝ) < (lam ^ 2) ^ (i : ℕ) := by positivity
          have hexp : ε₀ ^ (-α) * ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) ≤ 1 := by
            rw [← Real.rpow_add hε₀]
            refine Real.rpow_le_one hε₀.le hε₀1 ?_
            push_cast
            nlinarith
          have he : 0 ≤ ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hε₀.le _
          calc (blockCount p π i : ℝ) * (ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) *
                (((lam ^ 2) ^ (i : ℕ))⁻¹ / N))
              ≤ ε₀ ^ (-α) * N * (lam ^ 2) ^ (i : ℕ) * (ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) *
                (((lam ^ 2) ^ (i : ℕ))⁻¹ / N)) :=
                mul_le_mul_of_nonneg_right hb (by positivity)
            _ = ε₀ ^ (-α) * ε₀ ^ (α * (((i : ℕ) + 1 : ℕ) : ℝ)) := by field_simp
            _ ≤ 1 := hexp
    _ = p := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- `ε₀^{α |V_X|} = ∏_{S ∈ X} ε₀^{α |S|}` for a subpartition `X`. -/
theorem rpow_card_biUnion {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {ε₀ α : ℝ}
    (hε₀ : 0 < ε₀) :
    ε₀ ^ (α * (X.biUnion id).card) = ∏ S ∈ X, ε₀ ^ (α * S.card) := by
  rw [← TheoremTwo.sum_card_eq_card_biUnion hX]
  push_cast
  rw [mul_sum, Real.rpow_sum_of_pos hε₀]

end BlockWeights

/-! ### Step 1: the product of the hatted multipole partition functions -/

section Product

/-- **The product of the block factors** (Step 1): if for every block
`0 ≤ Mh(S) ≤ (𝗆(|S|) + a + b ε₀^{α|S|}) / N^{|S|-1}` with `𝗆(k) ≥ λ^{2(k-1)}/C_m` (`C_m ≥ 1`) and
the profile bound (5.56), then
`∏_{S ∈ π} Mh(S) ≤ ∏_{S ∈ π} 𝗆(|S|)/N^{|S|-1} · e^{C_m N (a p (1+A) + b p)}`. -/
theorem prod_le_of_bounds {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) (hπN : π.card ≤ N) {lam ε₀ α A Cm a b : ℝ}
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hα : 0 ≤ α) (hA : 0 ≤ A) (hAα : A = ε₀ ^ (-α))
    (hCm : 1 ≤ Cm) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1)))
    {Mh : Finset ℕ → ℝ} {msf : ℕ → ℝ} (hmsf : ∀ k, 1 ≤ k → k ≤ p →
      lam ^ (2 * (k - 1)) / Cm ≤ msf k)
    (hMh0 : ∀ S ∈ π, 0 ≤ Mh S)
    (hMh : ∀ S ∈ π, Mh S ≤ (msf S.card + a + b * ε₀ ^ (α * S.card)) / (N : ℝ) ^ (S.card - 1)) :
    ∏ S ∈ π, Mh S ≤ (∏ S ∈ π, msf S.card / (N : ℝ) ^ (S.card - 1)) *
      Real.exp (Cm * N * (a * (p * (1 + A)) + b * p)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hmpos : ∀ S ∈ π, 0 < msf S.card := fun S hS =>
    lt_of_lt_of_le (by have := (hπ1 S hS).1; positivity) (hmsf _ (hπ1 S hS).1 (hπ1 S hS).2)
  -- each factor
  have hfac : ∀ S ∈ π, Mh S ≤ msf S.card / (N : ℝ) ^ (S.card - 1) *
      Real.exp (Cm * N * (a * blockWeight lam N S +
        b * (ε₀ ^ (α * S.card) * blockWeight lam N S))) := by
    intro S hS
    have hm := hmpos S hS
    have hm' := hmsf _ (hπ1 S hS).1 (hπ1 S hS).2
    have hNk : (0 : ℝ) < (N : ℝ) ^ (S.card - 1) := by positivity
    have hl : (0 : ℝ) < lam ^ (2 * (S.card - 1)) := by positivity
    have he : 0 ≤ ε₀ ^ (α * S.card) := Real.rpow_nonneg hε₀.le _
    -- `(a + b e)/𝗆 ≤ C_m N (a + b e) u(S)`
    have hCm0 : 0 < Cm := by linarith
    have hinv : 1 / msf S.card ≤ Cm / lam ^ (2 * (S.card - 1)) := by
      rw [div_le_div_iff₀ hm hl, one_mul]
      have := (div_le_iff₀ hCm0).1 hm'
      linarith
    have hab0 : 0 ≤ a + b * ε₀ ^ (α * S.card) := by positivity
    have hu : (a + b * ε₀ ^ (α * S.card)) / msf S.card ≤
        Cm * N * (a * blockWeight lam N S + b * (ε₀ ^ (α * S.card) * blockWeight lam N S)) := by
      unfold blockWeight
      have h1 : (lam ^ 2) ^ (S.card - 1) = lam ^ (2 * (S.card - 1)) := by rw [pow_mul]
      rw [h1]
      calc (a + b * ε₀ ^ (α * S.card)) / msf S.card
          = (a + b * ε₀ ^ (α * S.card)) * (1 / msf S.card) := by ring
        _ ≤ (a + b * ε₀ ^ (α * S.card)) * (Cm / lam ^ (2 * (S.card - 1))) :=
          mul_le_mul_of_nonneg_left hinv hab0
        _ = Cm * N * (a * ((lam ^ (2 * (S.card - 1)))⁻¹ / N) +
              b * (ε₀ ^ (α * S.card) * ((lam ^ (2 * (S.card - 1)))⁻¹ / N))) := by
          field_simp
    calc Mh S ≤ (msf S.card + a + b * ε₀ ^ (α * S.card)) / (N : ℝ) ^ (S.card - 1) := hMh S hS
      _ = msf S.card / (N : ℝ) ^ (S.card - 1) *
            (1 + (a + b * ε₀ ^ (α * S.card)) / msf S.card) := by
          field_simp
          ring
      _ ≤ msf S.card / (N : ℝ) ^ (S.card - 1) *
            Real.exp ((a + b * ε₀ ^ (α * S.card)) / msf S.card) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [Real.add_one_le_exp ((a + b * ε₀ ^ (α * S.card)) / msf S.card)]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hu) (by positivity)
  calc ∏ S ∈ π, Mh S
      ≤ ∏ S ∈ π, (msf S.card / (N : ℝ) ^ (S.card - 1) *
          Real.exp (Cm * N * (a * blockWeight lam N S +
            b * (ε₀ ^ (α * S.card) * blockWeight lam N S)))) :=
        Finset.prod_le_prod₀ hMh0 hfac
    _ = (∏ S ∈ π, msf S.card / (N : ℝ) ^ (S.card - 1)) *
          Real.exp (Cm * N * (a * ∑ S ∈ π, blockWeight lam N S +
            b * ∑ S ∈ π, ε₀ ^ (α * S.card) * blockWeight lam N S)) := by
        rw [prod_mul_distrib, ← Real.exp_sum, mul_sum, mul_sum, ← sum_add_distrib, mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
          (prod_nonneg fun S hS => div_nonneg (hmpos S hS).le (by positivity))
        have h1 := sum_blockWeight_le' hN hπ1 hπN hlam hA hn
        have h2 := sum_epsBlockWeight_le hN hπ1 hπN hlam hε₀ hε₀1 hα (by rw [← hAα]; exact hn)
        have hCN : 0 ≤ Cm * N := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hCN
        have := mul_le_mul_of_nonneg_left h1 ha
        have := mul_le_mul_of_nonneg_left h2 hb
        linarith

end Product

/-! ### Step 2: the sum of the activity differences -/

section Retained

/-- **`D ≤ a N e^{p(1+A)} + b e^p`**: if on the retained subfamilies `X ⊂ π`,
`|K₁(X) - K₂(X)| ≤ a N ∏_{S ∈ X} u(S) + b ∏_{S ∈ X} ε₀^{α|S|} u(S)`, with the profile bound
(5.56). -/
theorem sum_retained_diff_le' {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ1 : ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p) (hπN : π.card ≤ N) {lam ε₀ α A a b : ℝ}
    (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hα : 0 ≤ α) (hA : 0 ≤ A)
    (hAα : A = ε₀ ^ (-α)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hn : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1)))
    {K₁ K₂ : Finset (Finset ℕ) → ℝ}
    (hd : ∀ X ⊆ π, Retained p X →
      |K₁ X - K₂ X| ≤ a * N * ∏ S ∈ X, blockWeight lam N S +
        b * ∏ S ∈ X, (ε₀ ^ (α * S.card) * blockWeight lam N S)) :
    (∑ Y ∈ π.powerset, if Retained p Y then |K₁ Y - K₂ Y| else 0) ≤
      a * N * Real.exp (p * (1 + A)) + b * Real.exp p := by
  have hu : ∀ S, 0 ≤ blockWeight lam N S := blockWeight_nonneg hlam N
  have hv : ∀ S, 0 ≤ ε₀ ^ (α * S.card) * blockWeight lam N S := fun S =>
    mul_nonneg (Real.rpow_nonneg hε₀.le _) (hu S)
  calc (∑ Y ∈ π.powerset, if Retained p Y then |K₁ Y - K₂ Y| else 0)
      ≤ ∑ Y ∈ π.powerset, (a * N * ∏ S ∈ Y, blockWeight lam N S +
          b * ∏ S ∈ Y, (ε₀ ^ (α * S.card) * blockWeight lam N S)) := by
        refine sum_le_sum fun Y hY => ?_
        split_ifs with hr
        · exact hd Y (mem_powerset.mp hY) hr
        · exact add_nonneg (mul_nonneg (by positivity) (prod_nonneg fun S _ => hu S))
            (mul_nonneg hb (prod_nonneg fun S _ => hv S))
    _ = a * N * ∑ Y ∈ π.powerset, ∏ S ∈ Y, blockWeight lam N S +
          b * ∑ Y ∈ π.powerset, ∏ S ∈ Y, (ε₀ ^ (α * S.card) * blockWeight lam N S) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ a * N * Real.exp (∑ S ∈ π, blockWeight lam N S) +
          b * Real.exp (∑ S ∈ π, ε₀ ^ (α * S.card) * blockWeight lam N S) := by
        gcongr
        · exact sum_powerset_prod_le_exp π hu
        · exact sum_powerset_prod_le_exp π hv
    _ ≤ a * N * Real.exp (p * (1 + A)) + b * Real.exp p := by
        gcongr
        · exact sum_blockWeight_le' hN hπ1 hπN hlam hA hn
        · exact sum_epsBlockWeight_le hN hπ1 hπN hlam hε₀ hε₀1 hα (by rw [← hAα]; exact hn)

end Retained

end UpperBoundLDP

end MultipoleBKT

end
