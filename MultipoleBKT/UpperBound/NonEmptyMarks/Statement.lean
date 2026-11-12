/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.Integration
public import MultipoleBKT.UpperBound.ExpansionPlus.Inputs

/-!
# The nonempty-mark claim in Proposition 5.19

The paper: Proposition 5.19,
(5.106).

The raw Mayer expansion is reduced by block parity. Each surviving
marked term follows the three cases in `pointwise_marked` and is
integrated by `integral_abs_markedTerm_le`. `lemma_A6_J2` bounds
its `J_ext` integral through common translation, retained tree logarithms,
radius cancellation and the radial cutoff gain.

The normalization lower bound turns `λ^((2-β)k) N` into a multiple
of `N^(1-k)`. Counts of marked terms and tree families depend only on
`k`. A vanishing block partition function gives the zero measure.
`nonEmptyMarks_holds` discharges the `NonEmptyMarksStatement`.
Its bad-point coefficient is chosen before `ε₀`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Hierarchical Multipole Parity SetPartition BoundedUpper

variable {χ : ℂ → ℝ}

/-- If some `𝖬^{+,Z}_{ε₀}(S)`, `S ∈ X`, vanishes, `𝖯^{+,ε₀,Z}_X` is the zero measure. -/
theorem plusModel_eq_zero {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} {X : Finset (Finset ℕ)} {S : Finset ℕ} (hS : S ∈ X)
    (h0 : plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S = 0) :
    plusModel χ N p₀ β lam M ε₀ L V Z X = 0 := by
  classical
  unfold plusModel modelHierarchical
  unfold plusPartitionFunction at h0
  convert withDensity_zero (μ := Measure.pi fun _ : X.biUnion id =>
    cutoffDipoleMeasure χ N p₀ β lam ε₀) using 2
  funext c
  simp only [Pi.zero_apply]
  refine Finset.prod_eq_zero hS ?_
  rw [h0, inv_zero, zero_mul, ENNReal.ofReal_zero]

/-- The number of simple graphs on a finite type with `n` elements is at most `2^{n²}`. -/
theorem card_simpleGraph_le' (W : Type*) [Fintype W] [DecidableEq W]
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

/-- The number of families of graphs on the groups `Y_l` (`|V_X| = k`, `m ≤ k` groups). -/
theorem card_trees_family_le {X : Finset (Finset ℕ)} {k m : ℕ} (hXk : (X.biUnion id).card = k)
    (Ys : Fin m → Finset (Finset ℕ)) (hYs : ∀ l, Ys l ⊆ X) (hm : m ≤ k)
    (P : (∀ l, SimpleGraph ((Ys l).biUnion id)) → Prop) [DecidablePred P] :
    (((univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter P).card : ℝ) ≤
      2 ^ (k * k * k) := by
  classical
  have h1 : ((univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter P).card ≤
      ∏ l, Fintype.card (SimpleGraph ((Ys l).biUnion id)) := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_pi]
  have h2 : ∏ l, Fintype.card (SimpleGraph ((Ys l).biUnion id)) ≤ 2 ^ (k * k * k) := by
    calc ∏ l, Fintype.card (SimpleGraph ((Ys l).biUnion id))
        ≤ ∏ _l : Fin m, 2 ^ (k * k) := by
          refine Finset.prod_le_prod fun l _ => (card_simpleGraph_le' _).trans ?_
          have hl : Fintype.card ((Ys l).biUnion id) ≤ k := by
            rw [Fintype.card_coe, ← hXk]
            exact Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left _ (hYs l))
          exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hl hl)
      _ = 2 ^ (k * k * m) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      _ ≤ 2 ^ (k * k * k) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul le_rfl hm)
  exact_mod_cast h1.trans h2

open scoped Classical in
/-- **The claim (5.106)** of the proof of Proposition 5.19 (paper), in the form
`ExpansionPlus.NonEmptyMarksStatement` used by `ExpansionPlus.prop_5_19_of_inputs`: for every
mollifier `χ`, `β > 2`, `p₀`, `L`, `M ≥ 3` and `k`. -/
theorem nonEmptyMarks_holds (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β) (p₀ : ℕ) (L : ℝ) {M : ℝ}
    (hM3 : 3 ≤ M) (k : ℕ) : ExpansionPlus.NonEmptyMarksStatement χ β M L p₀ k := by
  have hβ0 : 0 ≤ β := by linarith
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨K₀, hK₀, hint⟩ := integral_abs_markedTerm_le hχ hβ0 p₀ M L hM3 k
  obtain ⟨CJ, hCJ, hJ2⟩ := SmallIntegral.lemma_A6_J2 hχ hβ k hM1 p₀
  set Zc := dipoleConstant χ β with hZc
  have hZ : 0 < Zc := dipoleConstant_pos hχ hβ
  set G : ℝ := 2 ^ (k * k * k) with hG
  set T : ℝ := 2 ^ (k * k) * 2 ^ k with hT
  set D : ℝ := T * K₀ * G * (2 / Zc) ^ k with hD
  have hD0 : 0 < D := by positivity
  refine ⟨D * CJ, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨CεJ, hCεJ, hJ⟩ := hJ2 ε₀ hε₀ hε₁
  obtain ⟨laml, hlaml, hlow⟩ := lem411_lower hχ hβ hε₀
  refine ⟨D * CεJ, by positivity, min laml ε₀, lt_min hlaml hε₀, fun lam hlam hlt => ?_⟩
  have hltl : lam < laml := hlt.trans_le (min_le_left _ _)
  have hlε : lam < ε₀ := hlt.trans_le (min_le_right _ _)
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hltl)
  refine ⟨max Nl 1, fun N hN hMp V Z hVZ X hX hXV h2 hXk U hU hUne n Xs hXs hdisj Es hEs F hF =>
    ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlam1 : lam ≤ 1 := (hlε.trans hε₁).le
  have hlamh : lam ≤ ε₀ * truncationScale p₀ β lam := lam_le_cutoff hβ hlam hlam1 hε₀ hlε.le p₀
  have hVZ' : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hVZ.symm.subset
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hXcard : X.card ≤ k := hXk ▸ Finset.card_le_card_biUnion hX.2 hX.1
  have hk1 : 1 ≤ k := by omega
  set P := ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S with hPdef
  have hP0 : 0 ≤ P := prod_nonneg fun S _ => plusPartitionFunction_nonneg hχ hlam hε₀ hN1 S
  set R2 := truncationScale p₀ β lam ^ (-2 : ℝ) with hR2
  have hR20 : 0 ≤ R2 := Real.rpow_nonneg hR.le _
  set e := ε₀ ^ (alphaExponent β * k) with he
  have he0 : 0 ≤ e := Real.rpow_nonneg hε₀.le _
  rcases hP0.eq_or_lt with hPz | hPpos
  · -- some `𝖬^{+,Z}_{ε₀}(S)` vanishes
    obtain ⟨S, hS, hS0⟩ := Finset.prod_eq_zero_iff.1 hPz.symm
    rw [plusModel_eq_zero hS hS0, integral_zero_measure, abs_zero, ← hPz, zero_mul, div_zero]
  -- the main case
  have hEs' : ∀ l, Es l ∈ relEdgeSets (Xs l) := Fintype.mem_piFinset.1 hEs
  have hEsi : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs' l)).1
  have hFV : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := by
    intro p hp
    have hpE := (mem_relEdgeSets₀.1 (union_mem_relEdgeSets₀ hX hXs hEs' hF)).1
      (Finset.mem_union_right _ hp)
    exact ⟨(mem_pairsOn.1 (interPairs_subset_pairsOn hpE)).1,
      (mem_pairsOn.1 (interPairs_subset_pairsOn hpE)).2.1⟩
  set A : ℝ := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ with hA
  have hA0 : 0 ≤ A := inv_nonneg.2 (natCast_mul_cutoffDipoleNormalization_pos
    (p₀ := p₀) hχ hlam β hε₀ hN1).le
  set B : ℝ := lam ^ ((2 - β) * (k : ℝ)) * (CεJ * N * R2 + CJ * e * V.card) with hB
  have hB0 : 0 ≤ B := by
    have := Real.rpow_nonneg hlam.le ((2 - β) * (k : ℝ))
    positivity
  set Q : ℝ := K₀ * A ^ k * G * B / P with hQ
  have hQ0 : 0 ≤ Q := by positivity
  -- each marked term with parity
  have hterm : ∀ E₁ ∈ (univ.biUnion Es).powerset,
      ∀ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
      ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)|
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ Q := by
    intro E₁ hE₁ U₁ hU₁
    obtain ⟨hU₁p, hpar⟩ := Finset.mem_filter.1 hU₁
    obtain ⟨m, Ys, hm, hYs, hYd, Tb, hTb, hle⟩ := hint lam ε₀ V Z hlam hε₀ hN1 hlamh hMp hVZ' X
      hX hXk.le Xs hXs hdisj Es hEs F hF U hU hUne E₁ hE₁ U₁ hU₁p hpar
    rw [hXk] at hle
    set 𝒯 := (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
      (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)) with h𝒯
    have hint0 : 0 ≤ ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁
        (extendConfig (X.biUnion id) y)| ∂plusModel χ N p₀ β lam M ε₀ L V Z X :=
      integral_nonneg fun y => abs_nonneg _
    have hsum : ∑ Ta ∈ 𝒯, jExtIntegral χ p₀ N β lam M ε₀ V Z X Ys Ta Tb ≤
        ENNReal.ofReal (G * B) := by
      by_cases h𝒯ne : 𝒯.Nonempty
      · obtain ⟨Ta₀, hTa₀⟩ := h𝒯ne
        have hne : ∀ l, ((Ys l).subtype (· ∈ X)).Nonempty := by
          intro l
          obtain ⟨e', -⟩ := ((Finset.mem_filter.1 hTa₀).2 l).1.2.1
          induction e' using Sym2.ind with
          | h i j =>
            obtain ⟨B', hB', -⟩ := mem_biUnion_id.1 i.2
            exact ⟨⟨B', hYs l hB'⟩, Finset.mem_subtype.2 hB'⟩
        have hex : ∀ (l : Fin m) (z : X.biUnion id → ℂ × ℂ), ∃ S : X,
            S ∈ (Ys l).subtype (· ∈ X) ∧ ∀ S' ∈ (Ys l).subtype (· ∈ X),
              Peeling.blockRadius hX (fun i => Peeling.dipoleLength (z i)) S' ≤
                Peeling.blockRadius hX (fun i => Peeling.dipoleLength (z i)) S := by
          intro l z
          obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _
            (fun S => Peeling.blockRadius hX (fun i => Peeling.dipoleLength (z i)) S) (hne l)
          exact ⟨S, hS, hmax⟩
        choose hatS hhat using hex
        have hW : (coarsen X (univ.image Ys)).biUnion id = X.biUnion id :=
          biUnion_coarsen fun Y hY => by
            obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
            exact hYs l
        have hJle : ∀ Ta ∈ 𝒯, jExtIntegral χ p₀ N β lam M ε₀ V Z X Ys Ta Tb ≤
            ENNReal.ofReal B := fun Ta hTa =>
          (jExtIntegral_le_integralJext p₀ N V Z hX Ys hYs hYd Ta Tb hW hatS
            (fun l z => hhat l z)).trans
            (hJ X hX h2 hXk Ys hYs hYd _ (fun l => Finset.mem_image.2 ⟨Ta l,
              mem_relTrees.2 ((Finset.mem_filter.1 hTa).2 l), rfl⟩) _
              (Finset.mem_image.2 ⟨Tb, mem_relTrees₀.2 hTb, rfl⟩) hatS (fun l z => hhat l z)
              lam hlam hlε.le N V Z)
        have hcard : (𝒯.card : ℝ) ≤ G := card_trees_family_le hXk Ys hYs hm _
        refine (Finset.sum_le_card_nsmul _ _ _ hJle).trans ?_
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hB0)
      · rw [Finset.not_nonempty_iff_eq_empty.1 h𝒯ne, Finset.sum_empty]
        exact zero_le
    have h1 : ENNReal.ofReal (P * ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁
        (extendConfig (X.biUnion id) y)| ∂plusModel χ N p₀ β lam M ε₀ L V Z X) ≤
        ENNReal.ofReal (K₀ * A ^ k) * ENNReal.ofReal (G * B) :=
      hle.trans (by gcongr)
    rw [← ENNReal.ofReal_mul (mul_nonneg hK₀.le (pow_nonneg hA0 _)),
      ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hK₀.le (pow_nonneg hA0 _))
        (mul_nonneg (by positivity) hB0))] at h1
    rw [hQ, le_div_iff₀ hPpos]
    calc (∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)|
          ∂plusModel χ N p₀ β lam M ε₀ L V Z X) * P
        = P * ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁
          (extendConfig (X.biUnion id) y)| ∂plusModel χ N p₀ β lam M ε₀ L V Z X := mul_comm _ _
      _ ≤ K₀ * A ^ k * (G * B) := h1
      _ = K₀ * A ^ k * G * B := by ring
  -- the sum over the marked terms
  have hpk : (univ.biUnion Es).card ≤ k * k := by
    have hsub : univ.biUnion Es ⊆ pairsOn (X.biUnion id) := Finset.biUnion_subset.2 fun l _ =>
      (hEsi l).trans ((interPairs_subset_of_subset hX (hXs l)).trans interPairs_subset_pairsOn)
    exact (Finset.card_le_card hsub).trans ((card_pairsOn_le _).trans (by rw [hXk]))
  have htot : |∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
        (extendConfig (X.biUnion id) y) *
      ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤ T * Q := by
    refine (abs_integral_clusterTerm_mul_le hχ hlam hε₀ hN1 hM1 hX hXs hEsi hFV hU).trans ?_
    have hin : ∀ E₁ ∈ (univ.biUnion Es).powerset,
        ∑ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
          ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)|
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X ≤ 2 ^ k * Q := by
      intro E₁ hE₁
      refine (Finset.sum_le_card_nsmul _ _ _ (hterm E₁ hE₁)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hQ0
      have : (U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁)).card ≤ 2 ^ k := by
        refine (Finset.card_filter_le _ _).trans ?_
        rw [Finset.card_powerset]
        exact Nat.pow_le_pow_right (by norm_num) (hXk ▸ Finset.card_le_card hU)
      exact_mod_cast this
    refine (Finset.sum_le_card_nsmul _ _ _ hin).trans ?_
    rw [nsmul_eq_mul, hT]
    have : ((univ.biUnion Es).powerset.card : ℝ) ≤ 2 ^ (k * k) := by
      rw [Finset.card_powerset]
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hpk
    calc ((univ.biUnion Es).powerset.card : ℝ) * (2 ^ k * Q) ≤ 2 ^ (k * k) * (2 ^ k * Q) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ (k * k) * 2 ^ k * Q := by ring
  -- the algebra: `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β} / 2`
  have hCN := hNl N (le_trans (le_max_left _ _) hN)
  set ℓ : ℝ := lam ^ (2 - β) with hℓ
  have hℓ0 : 0 < ℓ := Real.rpow_pos_of_pos hlam _
  set D' : ℝ := N * (1 / 2 * Zc * ℓ) with hD'
  have hD'0 : 0 < D' := by positivity
  have hAD : A ≤ D'⁻¹ := by
    rw [hA]
    exact inv_anti₀ hD'0 (mul_le_mul_of_nonneg_left hCN hNpos.le)
  have hΛ : lam ^ ((2 - β) * (k : ℝ)) = ℓ ^ k := by
    rw [hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  have hkey : D'⁻¹ ^ k * N * ℓ ^ k = (2 / Zc) ^ k / (N : ℝ) ^ (k - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, hD', inv_pow, mul_pow, mul_pow, mul_pow, pow_succ (N : ℝ) j]
    field_simp
    rw [← mul_pow, ← mul_pow]
    have : 1 / 2 * Zc * (2 / Zc) = 1 := by field_simp
    rw [this, one_pow]
  have hA' : A ^ k * N * lam ^ ((2 - β) * (k : ℝ)) ≤ (2 / Zc) ^ k / (N : ℝ) ^ (k - 1) := by
    rw [hΛ, ← hkey]
    gcongr
  have hNk : 0 < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  have hnum0 : 0 ≤ CεJ * R2 + CJ * e * (V.card / N) := by positivity
  calc |∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
        (extendConfig (X.biUnion id) y) *
      ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤ T * Q := htot
    _ = T * K₀ * G * (A ^ k * N * lam ^ ((2 - β) * (k : ℝ))) *
          (CεJ * R2 + CJ * e * (V.card / N)) / P := by
        rw [hQ, hB]
        field_simp
    _ ≤ T * K₀ * G * ((2 / Zc) ^ k / (N : ℝ) ^ (k - 1)) *
          (CεJ * R2 + CJ * e * (V.card / N)) / P := by
        gcongr
    _ = (D * CεJ * R2 + D * CJ * e * (V.card / N)) / (P * (N : ℝ) ^ (k - 1)) := by
        rw [hD]
        field_simp

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
