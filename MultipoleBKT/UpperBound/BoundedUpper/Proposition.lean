/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Integration
public import MultipoleBKT.UpperBound.BoundedUpper.MultipoleBounds
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.JBridge
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Activity
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole

/-!
# Proposition 5.18

The paper: Proposition 5.18 and its proof.

* `plusActivity_bound`: **eq. (5.67)** for `𝖪^{+,Z}_{ε₀}` and `𝖪̂^{+,Z}_{ε₀}`
  : the raw grouped
  expansion (`RouteRaw.plusActivity_eq_raw`), parity cancellation, the bound of each term by `J`
  (`integral_abs_separatedReducedTerm_le`), (A.19) (`LemmaA6J`), the counting of the terms,
  `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2` (Lemma 4.12) and the block comparison
  `𝖬^0_{ε₀}(X) ≤ C 𝖬^{+,Z}_{ε₀}(X)` (`block_comparison`, from (5.65) and (4.39) for
  `𝖬^0_{ε₀}`). `|𝖪̂| ≤ |𝖪|` by eq. (5.101).
* `mxZeroBounds_holds`: (4.38)/(4.39) for `𝖬^0_{ε₀}` from
  (`MultipoleBKT.BoundedLowerEps.zeroPartitionFunction_two_sided`).
* `prop_5_18_of_inputs` (internal): Proposition 5.18 from the hypotheses `MXZeroBounds` and
  `LemmaA6J`.
* `prop_5_18`: **Proposition 5.18**, eqs. (5.65)–(5.67) for `𝖬^{+,Z}`, `𝖪^{+,Z}` and their hatted
  versions, for fixed `p₀ ≥ 1`, `β > 2`, `ε₀ ∈ (0, 1)`, `L`, and `M > 20` with `3^{p(β)} ≤ M`,
  unconditionally. The paper's quantifier "for `λ` small and `N` large" is explicit.
  The bad points are frozen (`I_bad^V(Z) = V`, Section 5.3).

The paper's constant in (5.67) depends on `β`, `M`, `ε₀` and `|V_X|`. Here it also depends on `χ`,
`p₀`, `L` (fixed throughout the paper). The hypotheses `S ⊂ V_good`, `V_X ⊂ V_good` of the paper
are kept although the bounds do not use them.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Multipole Parity

variable {χ : ℂ → ℝ} {β M ε₀ : ℝ}

theorem gammaBeta_nonneg' {lam : ℝ} (hlam : 0 < lam) (p₀ : ℕ) (β : ℝ) (k : ℕ) :
    0 ≤ Appendix.gammaBeta p₀ β lam k := by
  unfold Appendix.gammaBeta
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  split_ifs
  · exact (zpow_pos hlam _).le
  · exact mul_nonneg (zpow_pos hR _).le (abs_nonneg _)
  · exact (zpow_pos hR _).le

/-- The number of simple graphs on a finite type with `n` elements is at most `2^{n²}`. -/
theorem card_simpleGraph_le (W : Type*) [Fintype W] [DecidableEq W]
    [Fintype (SimpleGraph W)] :
    Fintype.card (SimpleGraph W) ≤ 2 ^ (Fintype.card W * Fintype.card W) := by
  classical
  have h := Fintype.card_le_of_injective (fun G : SimpleGraph W => fun i j => decide (G.Adj i j))
    (fun G H hGH => by
      ext i j
      have := congrFun (congrFun hGH i) j
      simpa using this)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ← pow_mul] at h
  exact h

theorem zeroPartitionFunction_eq_prod {N p₀ : ℕ} {lam : ℝ} (X : Finset (Finset ℕ)) :
    zeroPartitionFunction χ N p₀ β lam M ε₀ X =
      ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
  unfold zeroPartitionFunction
  exact Finset.prod_congr rfl fun S _ => (Finset.prod_singleton _ S).symm

open scoped Classical in
/-- **Eq. (5.67)** for `𝖪^{+,Z}_{ε₀}` and `𝖪̂^{+,Z}_{ε₀}` (proof of Proposition 5.18),
from the inputs `MXZeroBounds` and `LemmaA6J`. Also `𝖬^0_{ε₀}(X) > 0`. -/
theorem plusActivity_bound (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) (hM9 : 9 ≤ M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hMX : MXZeroBounds χ p₀ β M ε₀) (hA6 : LemmaA6J χ p₀ β M ε₀) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty →
        (∀ S ∈ X, S.card ≤ pBeta p₀ β) → (X.biUnion id).card = k →
          0 < zeroPartitionFunction χ N p₀ β lam M ε₀ X ∧
          |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
            C * Appendix.gammaBeta p₀ β lam k /
              (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) ∧
          |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤
            C * Appendix.gammaBeta p₀ β lam k /
              (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hM3 : 3 ≤ M := by linarith
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨Cb, hCb1, lamb, hlamb, hlamb1, hblock⟩ :=
    block_comparison hχ hβ p₀ L hε₀ hε₁ hM9 hMp hMX k
  obtain ⟨K₀, hK₀, hint⟩ := integral_abs_separatedReducedTerm_le hχ hβ0 p₀ M L hM3 k
  obtain ⟨CJ, hCJ, lamJ, hlamJ, hJ⟩ := hA6 k hk
  obtain ⟨laml, hlaml, hlow⟩ := lem411_lower hχ hβ hε₀
  set Zc := dipoleConstant χ β with hZc
  have hZ : 0 < Zc := dipoleConstant_pos hχ hβ
  set G : ℝ := 2 ^ (k * k * k) with hG
  set T : ℝ := RouteRaw.rawCount k with hT
  have hTpos : 0 < T := by unfold T RouteRaw.rawCount; positivity
  set Cf : ℝ := T * K₀ * G * CJ * (2 / Zc) ^ k * Cb ^ k with hCf
  have hCfpos : 0 < Cf := by positivity
  refine ⟨Cf, hCfpos, min lamb (min lamJ laml), lt_min hlamb (lt_min hlamJ hlaml),
    fun lam hlam hlt => ?_⟩
  have hltb : lam < lamb := hlt.trans_le (min_le_left _ _)
  have hltJ : lam < lamJ := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hltl : lam < laml := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Nb, hNb1, hNb⟩ := hblock lam hlam hltb
  obtain ⟨NJ, hNJ⟩ := hJ lam hlam hltJ
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hltl)
  refine ⟨max Nb (max NJ Nl), fun N hN V Z hVZ X hX hXne hXp hXk => ?_⟩
  have hN1 : 1 ≤ N := le_trans hNb1 (le_trans (le_max_left _ _) hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlam1 : lam ≤ 1 := (hltb.trans_le (hlamb1.trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ := (hltb.trans_le (hlamb1.trans (min_le_right _ _))).le
  have hlamh := lam_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
  have hVZ' : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hVZ.symm.subset
  have hγ0 := gammaBeta_nonneg' hlam p₀ β k
  -- the blocks
  have hXcard : X.card ≤ k := hXk ▸ Finset.card_le_card_biUnion hX.2 hX.1
  have hblocks : ∀ S ∈ X, 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
      0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
      zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
        Cb * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
    intro S hS
    refine hNb N (le_trans (le_max_left _ _) hN) V Z hVZ S (Finset.card_pos.2 (hX.1 S hS))
      (hXk ▸ Finset.card_le_card (subset_biUnion_of_mem id hS)) ?_
    exact TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ (hXp S hS)
  have hP0 : 0 < zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
    rw [zeroPartitionFunction_eq_prod]
    exact Finset.prod_pos fun S hS => (hblocks S hS).2.1
  have hPplus : 0 < ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
    Finset.prod_pos fun S hS => (hblocks S hS).1
  have hcmp : zeroPartitionFunction χ N p₀ β lam M ε₀ X ≤
      Cb ^ k * ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
    rw [zeroPartitionFunction_eq_prod]
    calc ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S}
        ≤ ∏ S ∈ X, (Cb * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) :=
          Finset.prod_le_prod₀ (fun S hS => (hblocks S hS).2.1.le) fun S hS => (hblocks S hS).2.2
      _ = Cb ^ X.card * ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ Cb ^ k * ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCb1 hXcard) hPplus.le
  have hNk : 0 < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  have hRHS0 : 0 ≤ Cf * Appendix.gammaBeta p₀ β lam k /
      (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) :=
    div_nonneg (mul_nonneg hCfpos.le hγ0) (mul_nonneg hP0.le hNk.le)
  -- eq. (5.67) for `𝖪^{+,Z}`
  have hK : |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
      Cf * Appendix.gammaBeta p₀ β lam k /
        (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) := by
    by_cases h2 : 2 ≤ X.card
    swap
    · unfold plusActivity
      rw [ite_eq_left (by omega : X.card ≤ 1), abs_zero]
      exact hRHS0
    have hM0 : ∀ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≠ 0 :=
      fun S hS => (hblocks S hS).1.ne'
    set A : ℝ := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ with hA
    have hA0 : 0 ≤ A := inv_nonneg.2 (natCast_mul_cutoffDipoleNormalization_pos
      (p₀ := p₀) hχ hlam β hε₀ hN1).le
    set B : ℝ := CJ * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k) with hB
    have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hCJ.le hNpos.le)
      (mul_nonneg (Real.rpow_pos_of_pos hlam _).le hγ0)
    set P := ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S with hPdef
    set Q : ℝ := K₀ * A ^ k * G * B / P with hQ
    have hQ0 : 0 ≤ Q := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK₀.le
      (pow_nonneg hA0 _)) (by positivity)) hB0) hPplus.le
    -- each term
    have hterm : ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset,
        ∀ V₁ ∈ (X.biUnion id).powerset.filter (fun V₁ => IsParityPair X E₁ V₁),
        ∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ (extendConfig (X.biUnion id) y)| *
            RouteRaw.oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
          ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ Q := by
      intro E hE E₁ hE₁ V₁ hV₁
      obtain ⟨hV₁p, hpar⟩ := Finset.mem_filter.1 hV₁
      obtain ⟨n, Xs, hnk, hXs, hdisj, Tb, hTb, hle⟩ := hint lam ε₀ V Z hlam hε₀ hN1 hlamh hMp hVZ'
        X hX hXk.le E hE E₁ hE₁ V₁ hV₁p hpar
      rw [hXk] at hle
      set 𝒯 := (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
        (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l)) with h𝒯
      have hJle : ∀ Ta ∈ 𝒯, jIntegral M lam ε₀ (truncationScale p₀ β lam) χ N β X Xs Ta Tb ≤
          ENNReal.ofReal B := fun Ta hTa =>
        hNJ N (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hN) X hX h2 hXk n Xs hXs
          hdisj Ta (Finset.mem_filter.1 hTa).2 Tb hTb
      have hcard : (𝒯.card : ℝ) ≤ G := by
        have h1 : 𝒯.card ≤ ∏ l, Fintype.card (SimpleGraph ((Xs l).biUnion id)) := by
          refine (Finset.card_filter_le _ _).trans ?_
          rw [Finset.card_univ, Fintype.card_pi]
        have h2' : ∏ l, Fintype.card (SimpleGraph ((Xs l).biUnion id)) ≤ 2 ^ (k * k * k) := by
          calc ∏ l, Fintype.card (SimpleGraph ((Xs l).biUnion id))
              ≤ ∏ _l : Fin n, 2 ^ (k * k) := by
                refine Finset.prod_le_prod fun l _ => (card_simpleGraph_le _).trans ?_
                have hl : Fintype.card ((Xs l).biUnion id) ≤ k := by
                  rw [Fintype.card_coe, ← hXk]
                  exact Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left _ (hXs l))
                exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hl hl)
            _ = 2 ^ (k * k * n) := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
            _ ≤ 2 ^ (k * k * k) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul le_rfl hnk)
        have := h1.trans h2'
        rw [hG]
        exact_mod_cast this
      have hsum : ∑ Ta ∈ 𝒯, jIntegral M lam ε₀ (truncationScale p₀ β lam) χ N β X Xs Ta Tb ≤
          ENNReal.ofReal (G * B) := by
        refine (Finset.sum_le_card_nsmul _ _ _ hJle).trans ?_
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hB0)
      have h1 : ENNReal.ofReal (P * ∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁
          (extendConfig (X.biUnion id) y)| *
          RouteRaw.oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y)) ∂plusModel χ N p₀ β lam M ε₀ L V Z X) ≤
          ENNReal.ofReal (K₀ * A ^ k) * ENNReal.ofReal (G * B) :=
        hle.trans (by gcongr)
      rw [← ENNReal.ofReal_mul (mul_nonneg hK₀.le (pow_nonneg hA0 _)),
        ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hK₀.le (pow_nonneg hA0 _))
          (mul_nonneg (by positivity) hB0))] at h1
      rw [hQ, le_div_iff₀ hPplus]
      calc (∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ (extendConfig (X.biUnion id) y)| *
            RouteRaw.oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X) * P
          = P * ∫ y, (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ (extendConfig (X.biUnion id) y)| *
            RouteRaw.oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X := mul_comm _ _
        _ ≤ K₀ * A ^ k * (G * B) := h1
        _ = K₀ * A ^ k * G * B := by ring
    -- Start with the nested marked groups, then cancel by reversal.
    have hsum : |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤ T * Q :=
      RouteRaw.activity_le_of_reduced hχ hlam hε₀ hN1 hM1 hX h2 hM0 hXk.le hQ0 hterm
    -- the algebra: `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2` and the block comparison
    have hCN := hNl N (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hN)
    set ℓ : ℝ := lam ^ (2 - β) with hℓ
    have hℓ0 : 0 < ℓ := Real.rpow_pos_of_pos hlam _
    set D : ℝ := N * (1 / 2 * Zc * ℓ) with hD
    have hD0 : 0 < D := by positivity
    have hAD : A ≤ D⁻¹ := by
      rw [hA]
      exact inv_anti₀ hD0 (mul_le_mul_of_nonneg_left hCN hNpos.le)
    have hΛ : lam ^ ((2 - β) * (k : ℝ)) = ℓ ^ k := by
      rw [hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    have hkey : D⁻¹ ^ k * N * ℓ ^ k = (2 / Zc) ^ k / (N : ℝ) ^ (k - 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, hD, inv_pow, mul_pow, mul_pow, mul_pow, pow_succ (N : ℝ) j]
      field_simp
      rw [← mul_pow, ← mul_pow]
      have : 1 / 2 * Zc * (2 / Zc) = 1 := by field_simp
      rw [this, one_pow]
    have hA' : A ^ k * N * lam ^ ((2 - β) * (k : ℝ)) ≤ (2 / Zc) ^ k / (N : ℝ) ^ (k - 1) := by
      rw [hΛ, ← hkey]
      gcongr
    have hP' : P⁻¹ ≤ Cb ^ k / zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
      rw [div_eq_mul_inv]
      have h1 : (Cb ^ k * P)⁻¹ ≤ (zeroPartitionFunction χ N p₀ β lam M ε₀ X)⁻¹ :=
        inv_anti₀ hP0 hcmp
      have hCbk : 0 < Cb ^ k := by positivity
      calc P⁻¹ = Cb ^ k * (Cb ^ k * P)⁻¹ := by field_simp
        _ ≤ Cb ^ k * (zeroPartitionFunction χ N p₀ β lam M ε₀ X)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 hCbk.le
    have hX0 : 0 ≤ T * K₀ * G * CJ * Appendix.gammaBeta p₀ β lam k := by positivity
    calc |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤ T * Q := hsum
      _ = T * K₀ * G * CJ * Appendix.gammaBeta p₀ β lam k *
          ((A ^ k * N * lam ^ ((2 - β) * (k : ℝ))) * P⁻¹) := by
        rw [hQ, hB]
        ring
      _ ≤ T * K₀ * G * CJ * Appendix.gammaBeta p₀ β lam k *
          (((2 / Zc) ^ k / (N : ℝ) ^ (k - 1)) *
            (Cb ^ k / zeroPartitionFunction χ N p₀ β lam M ε₀ X)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hA' hP' (inv_nonneg.2 hPplus.le)
          (by positivity)) hX0
      _ = Cf * Appendix.gammaBeta p₀ β lam k /
          (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) := by
        rw [hCf]
        field_simp
  -- the hatted activity: `|𝖪̂| ≤ |𝖪|`
  have hg1 : 1 ≤ ∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S := by
    have := Finset.prod_le_prod₀ (s := X) (f := fun _ => (1 : ℝ))
      (g := fun S => externalNormalization χ N p₀ β lam M ε₀ L V Z S)
      (fun _ _ => zero_le_one) fun S hS =>
        one_le_externalNormalization hχ hlam hε₀ hN1 hlamh hMp hM3 hVZ' (hX.1 S hS)
          (hblocks S hS).1
    simpa using this
  refine ⟨hP0, hK, ?_⟩
  unfold hatActivity
  rw [abs_div, abs_of_pos (zero_lt_one.trans_le hg1)]
  exact (div_le_self (abs_nonneg _) hg1).trans hK

/-- **The input (4.38)/(4.39) for `𝖬^0_{ε₀}` holds** (Proposition 4.23 for `𝖬^0_{ε₀}`,
`MultipoleBKT.BoundedLowerEps.zeroPartitionFunction_two_sided`), for `M > 20`. -/
theorem mxZeroBounds_holds (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) (hM : 20 < M)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) : MXZeroBounds χ p₀ β M ε₀ := by
  intro k hk hkp
  obtain ⟨C, hC, h⟩ := BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ hk hkp hM
  obtain ⟨lam₀, hlam₀, -, h'⟩ := h ε₀ hε₀ hε₁
  exact ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => h' p₀ lam hlam hlt⟩

/-- **Proposition 5.18 from the inputs `MXZeroBounds` and `LemmaA6J`** (internal form, see
`prop_5_18` for the unconditional statement). -/
theorem prop_5_18_of_inputs (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hMX : MXZeroBounds χ p₀ β M ε₀) (hA6 : LemmaA6J χ p₀ β M ε₀) :
    (∀ k : ℕ, 1 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ S : Finset ℕ, S ⊆ goodLabels V → S.card = k →
          (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) ∧
          (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1))) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty → X.biUnion id ⊆ goodLabels V →
        (∀ S ∈ X, S.card ≤ pBeta p₀ β) → (X.biUnion id).card = k →
          |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
              C * Appendix.gammaBeta p₀ β lam k /
                (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) ∧
            |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤
              C * Appendix.gammaBeta p₀ β lam k /
                (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1))) := by
  have hM9 : 9 ≤ M := by linarith
  refine ⟨fun k hk hkp => ?_, fun k hk => ?_⟩
  · obtain ⟨C, hC, lam₀, hlam₀, -, h⟩ :=
      plusPartitionFunction_bounds (χ := χ) hχ hβ p₀ L hε₀ hε₁ hM9 hMp hk hkp
    refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
    obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
    exact ⟨N₀, fun N hN V Z hVZ S _ hS => hN₀ N hN V Z hVZ S hS⟩
  · obtain ⟨C, hC, lam₀, hlam₀, h⟩ := plusActivity_bound hχ hβ hp₀ L hε₀ hε₁ hM9 hMp hMX hA6 hk
    refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
    obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
    exact ⟨N₀, fun N hN V Z hVZ X hX hXne _ hXp hXk =>
      (hN₀ N hN V Z hVZ X hX hXne hXp hXk).2⟩

/-- **Proposition 5.18**: for
`χ` a mollifier, `β > 2`, `p₀ ≥ 1`, `L ∈ ℝ`, `ε₀ ∈ (0, 1)` and `M > 20` with `3^{p(β)} ≤ M`,
for frozen bad points (`I_bad^V(Z) = V`, Section 5.3):

* eqs. (5.65)–(5.66): for `1 ≤ k ≤ p*(β)` there is `C > 0` such that,
  for `λ` small and `N` large, `λ^{2(k-1)} / (C N^{k-1}) ≤ 𝖬^{+,Z}_{ε₀}(S) ≤ C λ^{2(k-1)} / N^{k-1}`
  for every `S ⊂ [N] ∖ V` with `|S| = k`, and the same for `𝖬̂^{+,Z}_{ε₀}`.
* eq. (5.67): for `k ≥ 1` there is `C > 0` such that, for `λ` small and `N` large,
  `|𝖪^{+,Z}_{ε₀}(X)| ≤ C γ_{β,λ,k} / (𝖬^0_{ε₀}(X) N^{k-1})` for every nonempty subpartition `X` of
  `[N] ∖ V` with blocks of size at most `p(β)` and `|V_X| = k`, and the same for `𝖪̂^{+,Z}_{ε₀}`. -/
theorem prop_5_18 (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) :
    (∀ k : ℕ, 1 ≤ k → (k : ℕ∞) ≤ pStar β → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ S : Finset ℕ, S ⊆ goodLabels V → S.card = k →
          (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) ∧
          (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1))) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty → X.biUnion id ⊆ goodLabels V →
        (∀ S ∈ X, S.card ≤ pBeta p₀ β) → (X.biUnion id).card = k →
          |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
              C * Appendix.gammaBeta p₀ β lam k /
                (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) ∧
            |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤
              C * Appendix.gammaBeta p₀ β lam k /
                (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1))) :=
  prop_5_18_of_inputs hχ hβ hp₀ L hε₀ hε₁ hM hMp (mxZeroBounds_holds hχ hβ p₀ hM hε₀ hε₁)
    (RouteRaw.lemmaA6J_source_holds hχ hβ p₀ (by linarith) hε₀ hε₁)

end BoundedUpper

end UpperBound

end MultipoleBKT

end
