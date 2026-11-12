/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.ActivityFromTrees
public import MultipoleBKT.LowerBound.BoundedLowerEps.Activity

/-!
# The infinite-cutoff bounded activity through hatted J infinity

The proof of Proposition 4.23. Apply the grouped reduction with the true interaction,
then use infinite radial integral under `k ≤ p*(β)`.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits SmallIntegral
open UpperBound.BoundedUpper BoundedLowerEps
open scoped Classical

/-- Uniform bound before choosing a small-λ threshold. The infinite-cutoff
hatted integral gives the stronger range of every positive λ. -/
theorem exists_abs_activity_infinity_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {β M : ℝ} (hβ : 2 < β) (hM : 1 ≤ M) (k : ℕ) (hk : 1 ≤ k)
    (hsize : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, 1 ≤ N →
      1 / 2 * dipoleConstant χ β * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → 1 < X.card → (X.biUnion id).card = k →
        |multipoleActivity χ N β lam M X| ≤ C * lam ^ (2 * (k - 1)) /
          ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨CT, hCT, ht⟩ := exists_hatTreeIntegral_infinity_le hχ hβ hM k hsize
  obtain ⟨Cd, hCd0, hCd⟩ := dipoleBond_le hχ
  obtain ⟨Cw, hCw0, hCw⟩ := abs_dipoleInteraction_le_ahat hχ
  let Wb := Real.exp (β * Cd)
  let Cab := bondConst β Cw
  have hWb : 1 ≤ Wb := Real.one_le_exp (mul_nonneg hβ0 hCd0)
  have hCab : 1 ≤ Cab := one_le_bondConst hβ0 hCw0
  let A : ℝ := parityCount k * (Wb ^ (k * k) * 1 ^ k * Cab ^ (k * k)) * (2 ^ (k * k * k) * CT)
  have hA : 0 < A := by dsimp [A, parityCount]; positivity
  have hZ : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  refine ⟨A * (2 / dipoleConstant χ β) ^ k, by positivity, ?_⟩
  intro lam hlam N hN hCn X hX h2 hXk
  have h := modelHyp_infinity hχ hlam β hN
  have hg0 := gammaBeta_nonneg hlam 0 β k
  have hmain := prod_mul_abs_activity_le hχ h (measurePreserving_swap_dipoleMeasure hχ N β lam)
    (fun d e => Parity.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Parity.dipoleInteraction_swap_right d e hχ lam) (fun _ => rfl)
    (exists_abs_dipoleInteraction_le hχ hlam N) hlam hM hX h2 hXk
    (pairDensity χ β lam) (measurable_pairDensity hχ hlam β) (fun d => (pairDensity_pos _ _ _ _).le)
    (fun y hy _ i => hy i (Set.mem_univ i)) (natCast_mul_dipoleNormalization_pos hχ hlam β hN)
    (fun f => by simpa only [Fintype.card_coe, hXk] using integral_pi_dipoleMeasure hχ hlam β hN f)
    hWb le_rfl hCab (fun d _ e _ => by unfold stableWeight; exact hCd β hβ0 lam hlam d e)
    (fun _ _ => le_rfl)
    (fun d _ e _ => abs_bonds_le hβ0 hM hCw0 (fun hnl => hCw lam hlam M hM d e hnl)
      (fun hnl => ahat_le_one_of_not_linked hχ hlam hM hnl))
    (show 0 ≤ CT * N * (lam ^ ((2 - β) * k) * Appendix.gammaBeta 0 β lam k) by positivity)
    (fun Ys hYs hdisj Ta hTa Tb hTb => ht X hX h2 hXk Ys hYs hdisj Ta hTa Tb hTb 0 lam hlam N)
  have hgamma : Appendix.gammaBeta 0 β lam k = lam ^ (2 * (k - 1)) := by
    unfold Appendix.gammaBeta
    have he : 2 * ((k : ℤ) - 1) = ((2 * (k - 1) : ℕ) : ℤ) := by omega
    rw [ite_eq_left hsize, he, zpow_natCast]
  rw [hgamma] at hmain
  simp only [modelPartitionFunction_dipoleMeasure] at hmain
  change (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * |zeroActivityInf χ N β lam M X| ≤ _ at hmain
  rw [zeroActivityInf_eq_multipoleActivity hχ hlam β hN hM hX] at hmain
  have hscale := scaling_le (β := β) hN hlam hZ hCn hk hA.le (show (0 : ℝ) ≤ 1 by norm_num)
    (show 0 ≤ lam ^ (2 * (k - 1)) by positivity)
  have hbound : (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
      |multipoleActivity χ N β lam M X| ≤ A * (2 / dipoleConstant χ β) ^ k *
        lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
    apply hmain.trans
    convert hscale using 1 <;> (dsimp [A]; ring)
  have hP : 0 < ∏ S ∈ X, multipolePartitionFunction χ N β lam M S :=
    prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β (by linarith) hN (hX.1 S hS)
  rw [le_div_iff₀ (mul_pos hP (by positivity))]
  have hb := mul_le_mul_of_nonneg_right hbound (show 0 ≤ (N : ℝ) ^ (k - 1) by positivity)
  have hNpow : (N : ℝ) ^ (k - 1) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : N ≠ 0))
  rw [div_mul_cancel₀ _ hNpow] at hb
  convert hb using 1
  ring

end MultipoleBKT.LowerBound.RouteBounded

end
