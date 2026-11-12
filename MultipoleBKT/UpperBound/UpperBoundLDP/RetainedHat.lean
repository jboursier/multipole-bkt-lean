/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.Discharge

/-!
# The retained hatted activities

The paper: proof of Proposition 5.43 ("By Proposition 5.18, the retained activities satisfy `q ≤ C_{ε₀} λ²`"): for the clusters with at
least two blocks and at most `p(β)` points, eq. (5.67) of Proposition 5.18
(`MultipoleBKT.UpperBound.AbsoluteUpper.uniform_bounded_estimates`), the lower bound (4.38) on
the blocks and `g^Z_{ε₀} ≥ 1` (eq. (5.101)) give
`|𝖪̂^{+,Z}_{ε₀}(X)| ≤ |𝖪^{+,Z}_{ε₀}(X)| ≤ C_s (λ²/N)^{|X|-1}` (`hat_retained_bound`). This is the
small-cluster majorant of the proof of Proposition 5.20
(`MultipoleBKT.UpperBound.AbsoluteUpper.prop_5_20_of_inputs`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical UpperBound AbsoluteUpper

/-- **The retained hatted activities** (see the module docstring). -/
theorem hat_retained_bound {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ}
    (hβ : 2 < β) (L : ℝ) {M : ℝ} (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        IsFrozenConfig p₀ β lam M ε₀ V Z →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ BoundedUpper.goodLabels V →
          2 ≤ X.card → (X.biUnion id).card ≤ pBeta p₀ β →
          |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1) := by
  set p := pBeta p₀ β with hp
  obtain ⟨CK, hCK, Cm, hCm, lamU, hlamU, hU⟩ :=
    uniform_bounded_estimates hχ hp₀ hβ L (kPlusBoundInput_holds hχ hp₀ hβ L) hM hMp hε₀ hε₁ p
  set Cb : ℝ := ∑ k ∈ range (p + 1), CK k with hCb
  have hCb0 : 0 ≤ Cb := sum_nonneg fun k _ => hCK k
  have hCKb : ∀ k, k ≤ p → CK k ≤ Cb := fun k hk =>
    single_le_sum (f := CK) (fun k _ => hCK k) (mem_range.2 (Nat.lt_succ_of_le hk))
  refine ⟨Cb * Cm ^ p, by positivity, min lamU (min (ε₀ / 2) 1),
    lt_min hlamU (lt_min (by linarith) one_pos), fun lam hlam hlt => ?_⟩
  have hltU : lam < lamU := hlt.trans_le (min_le_left _ _)
  have hltε : lam < ε₀ / 2 := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hlamR : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
    nlinarith
  obtain ⟨NU, hNU⟩ := hU lam hlam hltU
  refine ⟨max NU 1, fun N hN V Z hVZ X hXs hXg hX2 hkp => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hKb, hM0b, hMpos⟩ := hNU N ((le_max_left _ _).trans hN)
  have hk1 : 1 ≤ (X.biUnion id).card :=
    (by omega : 1 ≤ X.card).trans (card_le_card_biUnion_of_isSubpartition hXs)
  have hXg' : ∀ S ∈ X, S ⊆ (Finset.univ \ V).map Fin.valEmbedding := fun S hS =>
    (subset_biUnion_of_mem id hS).trans hXg
  have hXp : ∀ S ∈ X, S.card ≤ p := fun S hS =>
    (card_le_card (subset_biUnion_of_mem id hS)).trans hkp
  have hb := hKb _ hk1 hkp V Z hVZ X hXs (card_pos.1 (by omega)) hXg' hXp rfl
  rw [gammaBeta_of_le_pStar hk1 (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)] at hb
  have hm : ∀ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤
      zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
    intro S hS
    have hS1 := (hXs.1 S hS).card_pos
    by_cases hS2 : 2 ≤ S.card
    · exact hM0b S hS2 (hXp S hS)
    · have hc : S.card = 1 := by omega
      rw [zeroPartitionFunction_singleton hχ hlam hε₀ hN1 hc, hc]
      simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
      exact div_le_one_of_le₀ hCm (by linarith)
  have hprod : zeroPartitionFunction χ N p₀ β lam M ε₀ X =
      ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
    rw [zeroPartitionFunction]
    exact prod_congr rfl fun S _ => (prod_singleton _ S).symm
  rw [hprod] at hb
  have hplus := (abs_le_of_gamma_bound hXs (by omega) hNpos hlam (by linarith) (hCK _) hm hb)
  -- `g ≥ 1`
  have hg : ∀ S ∈ X, 1 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S := by
    intro S hS
    have hSne := hXs.1 S hS
    exact externalPositivityInput_holds hχ p₀ β L lam M ε₀ V Z hlam hε₀ hN1 hlamR hMp
      (by linarith) hVZ.1.symm.subset S hSne
      (hMpos V Z hVZ.1 S hSne.card_pos (hXp S hS))
  have hXc : X.card ≤ p := (card_le_card_biUnion_of_isSubpartition hXs).trans hkp
  have hpow : Cm ^ X.card ≤ Cm ^ p := pow_le_pow_right₀ hCm hXc
  have hb0 : 0 ≤ (lam ^ 2 / N) ^ (X.card - 1) := by positivity
  calc |hatActivity χ N p₀ β lam M ε₀ L V Z X|
      ≤ |plusActivity χ N p₀ β lam M ε₀ L V Z X| := abs_hatActivity_le hg
    _ ≤ CK (X.biUnion id).card * Cm ^ X.card * (lam ^ 2 / N) ^ (X.card - 1) := hplus
    _ ≤ Cb * Cm ^ p * (lam ^ 2 / N) ^ (X.card - 1) := by
        gcongr
        · exact hCKb _ hkp

end UpperBoundLDP

end MultipoleBKT

end
