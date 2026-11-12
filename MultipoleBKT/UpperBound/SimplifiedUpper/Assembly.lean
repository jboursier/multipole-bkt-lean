/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.Normalize
public import MultipoleBKT.UpperBound.BoundedUpper.MultipoleBounds

/-!
# Lemma 5.37: `SimplifiedBoundUpper`

The paper: Lemma 5.37, from
Lemmas 5.35 and 5.36:

`simplifiedBoundUpper_holds`: for a mollifier `χ`, `p₀ ≥ 1`, `β > 2` and `L`,
`MultipoleBKT.UpperBound.AbsoluteUpper.SimplifiedBoundUpper χ p₀ β L` holds: there is `C₀ > 0`
(depending on `χ`, `p₀`, `β`) such that for `M > 20` with `3^{p(β)} ≤ M` there is `C ≥ 0`
(depending on `χ`, `p₀`, `β`, `M`, `L`, not on `ε₀`) with, for `ε₀ ∈ (0, 1)`, `λ` small and `N`
large, every frozen configuration `(V, Z)` and every subpartition `X` of the good labels with
blocks of at most `p(β)` labels, `|𝖪^{+,Z}_{ε₀}(X)| ≤ simplifiedMajorant C₀ C X`.

The proof:
1. `|𝖪^{+,Z}_{ε₀}(X)| ≤ 𝔼_{𝖯^{+,ε₀,Z}_X}[actSum]` (`abs_plusActivity_le_integral`: Definition 5.15,
   Corollary 5.24);
2. `(∏_{S ∈ X} 𝖬^{+,Z}(S)) 𝔼_{𝖯^{+,ε₀,Z}_X}[actSum] = 𝔼_{μ^{⊗ V_X}}[∏ 𝖬-weights · actSum]` (density
   of the hierarchical model);
3. on the support, `∏ 𝖬-weights · actSum ≤ K^{|V_X|} majSum` (`pointwise_le`: Lemmas 5.35–5.37);
4. `𝔼_{μ^{⊗ V_X}}[majSum] = (N C_{β,λ,ε₀})^{-|V_X|} ∑_{n ≤ |X|} (1/n!) ∑ J_{large,C₀}`
   (`lintegral_majSum`);
5. `C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β}/2` (Lemma 4.12) and `𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)` uniformly in
   `ε₀` (`blockCmp_uniform`).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Hierarchical Multipole SetPartition AbsoluteLower Parity BoundedUpper AbsoluteUpper

/-! ### The reduced series as a function of the configuration -/

section ActSum

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}

theorem measurable_actSum (hw : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (hs : Measurable s) (X : Finset (Finset ℕ)) : Measurable fun c => actSum β w M lam s X c := by
  unfold actSum
  exact Finset.measurable_sum _ fun U _ => Finset.measurable_sum _ fun n _ =>
    (Finset.measurable_sum _ fun Xs _ => measurable_parAbsSum hw hs X Xs U).const_mul _

theorem actSum_congr {X : Finset (Finset ℕ)} {c c' : ℕ → ℂ × ℂ}
    (hcc' : ∀ i ∈ ((X.biUnion id : Finset ℕ) : Set ℕ), c i = c' i) :
    actSum β w M lam s X c = actSum β w M lam s X c' := by
  unfold actSum
  refine sum_congr rfl fun U hU => sum_congr rfl fun n _ => ?_
  congr 1
  exact sum_congr rfl fun Xs hXs =>
    parAbsSum_congr (mem_tuplesT.1 hXs).1 (mem_powerset.1 hU) hcc'

theorem actSum_nonneg (X : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ actSum β w M lam s X c := by
  unfold actSum
  exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (by positivity)
    (sum_nonneg fun _ _ => parAbsSum_nonneg _ _ _ _ _ _ _ _ _)

end ActSum

/-! ### The expectation, in `[0, ∞]` -/

section Expectation

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L C₀ : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

open scoped Classical in
/-- **Steps 1–4** (internal, from the pointwise bound `hpw` of step 3):
`|𝖪^{+,Z}_{ε₀}(X)| ≤ (∏_{S ∈ X} 𝖬^{+,Z}(S))⁻¹ (N C_{β,λ,ε₀})^{-|V_X|} K^{|V_X|}
∑_{n ≤ |X|} (1/n!) ∑ ∑ ∑ J_{large,C₀}`, in `[0, ∞]`. -/
theorem ofReal_abs_plusActivity_le_of (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    (hP : 0 < ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) {K : ℝ} (hK : 0 ≤ K)
    (hpw : ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, c i ∈ supportSet N p₀ β lam ε₀ ∧
        0 < ‖(c i).1 - (c i).2‖) →
      (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
          actSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X c ≤
        K ^ (X.biUnion id).card * majSum M lam ε₀ (truncationScale p₀ β lam) C₀ X c) :
    ENNReal.ofReal |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
      ENNReal.ofReal ((∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S)⁻¹ *
          ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ (X.biUnion id).card *
          K ^ (X.biUnion id).card) *
        ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
          ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
            ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
              jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb := by
  set W := X.biUnion id with hW
  set μ := cutoffDipoleMeasure χ N p₀ β lam ε₀ with hμ
  set P := ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S with hPdef
  set w := interactionGoodZ χ p₀ β lam ε₀ V Z with hw
  set s := extSumZ χ p₀ β lam ε₀ V Z with hs
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hmA : Measurable fun c => actSum β w M lam s X c :=
    measurable_actSum (measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam)
      (measurable_extSumZ hχ hlam) X
  have hdepA : DependsOn (fun c => actSum β w M lam s X c) (W : Set ℕ) := fun c c' hcc' =>
    actSum_congr hcc'
  set Φ : (ℕ → ℂ × ℂ) → ℝ := fun c =>
    (∏ B ∈ X, blockWeightOf β w (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
      actSum β w M lam s X c with hΦ
  have hΦm : Measurable Φ :=
    (Finset.measurable_prod _ fun B _ => h.measurable_blockWeightOf M lam B).mul hmA
  have hΦdep : DependsOn Φ (W : Set ℕ) := by
    intro c c' hcc'
    simp only [hΦ]
    rw [actSum_congr (β := β) (w := w) (M := M) (lam := lam) (s := s) hcc']
    congr 1
    refine prod_congr rfl fun B hB => dependsOn_blockWeightOf M lam B fun i hi => hcc' i ?_
    exact mem_coe.2 (subset_biUnion_of_mem id hB (mem_coe.1 hi))
  have hΦ0 : ∀ c, 0 ≤ Φ c := fun c => mul_nonneg (prod_nonneg fun B _ =>
    blockWeightOf_nonneg M lam (fun _ => dipoleWeightZ_nonneg _) B c) (actSum_nonneg X c)
  -- step 1
  have h1 := abs_plusActivity_le_integral (p₀ := p₀) (β := β) (L := L) (V := V) (Z := Z) hχ hlam
    hε₀ hN hM hX h2
  -- step 2: the density form
  have e1 := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := X)
    (f := fun y => actSum β w M lam s X (extendConfig W y)) (hmA.comp (measurable_extendConfig _))
  have e2 : ∫ c, (∏ B ∈ X, blockWeightOf β w (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
      actSum β w M lam s X (extendConfig W (W.restrict c)) ∂labelField μ =
      ∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ) := by
    rw [← integral_labelField_eq_pi hΦm hΦdep]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [hΦ]
    rw [apply_extendConfig_restrict hdepA c]
  have hPI : P * ∫ y, actSum β w M lam s X (extendConfig W y)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X =
      ∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ) :=
    e1.trans e2
  -- step 3: the lower integral and the pointwise bound
  have hle1 : ENNReal.ofReal (∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ)) ≤
      ∫⁻ y, ENNReal.ofReal (Φ (extendConfig W y)) ∂Measure.pi (fun _ : W => μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hΦ0 _)
      (hΦm.comp (measurable_extendConfig _)).aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  have hae : ∀ᵐ y ∂Measure.pi (fun _ : W => μ), ENNReal.ofReal (Φ (extendConfig W y)) ≤
      ENNReal.ofReal (K ^ W.card * majSum M lam ε₀ (truncationScale p₀ β lam) C₀ X
        (extendConfig W y)) := by
    filter_upwards [ae_pi_mem (ρ := μ) (ι := W) (ae_cutoffDipoleMeasure_pos χ N p₀ β lam ε₀)]
      with y hy
    refine ENNReal.ofReal_le_ofReal (hpw (extendConfig W y) fun i hi => ?_)
    have : extendConfig W y i = y ⟨i, hi⟩ := by simp [extendConfig, hi]
    rw [this]
    exact hy ⟨i, hi⟩
  have h4 := lintegral_majSum (p₀ := p₀) (β := β) (C₀ := C₀) (M := M) hχ hlam hε₀ hN X
    (K := K ^ W.card)
    (pow_nonneg hK _)
  -- the chain
  have hI0 : 0 ≤ ∫ y, actSum β w M lam s X (extendConfig W y)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X :=
    integral_nonneg fun y => actSum_nonneg X _
  calc ENNReal.ofReal |plusActivity χ N p₀ β lam M ε₀ L V Z X|
      ≤ ENNReal.ofReal (∫ y, actSum β w M lam s X (extendConfig W y)
          ∂plusModel χ N p₀ β lam M ε₀ L V Z X) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal P⁻¹ *
          ENNReal.ofReal (∫ y, Φ (extendConfig W y) ∂Measure.pi (fun _ : W => μ)) := by
        rw [← hPI, ← ENNReal.ofReal_mul (inv_nonneg.2 hP.le), ← mul_assoc, inv_mul_cancel₀ hP.ne',
          one_mul]
    _ ≤ ENNReal.ofReal P⁻¹ *
          (ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ W.card) *
            (ENNReal.ofReal (K ^ W.card) * ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
              ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
                ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
                  jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb)) := by
        exact mul_le_mul_of_nonneg_left (hle1.trans ((lintegral_mono_ae hae).trans (le_of_eq h4)))
          zero_le
    _ = _ := by
        have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hP.le),
          ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.2 hP.le)
            (pow_nonneg (inv_nonneg.2 hC.le) _))]

end Expectation

/-! ### Lemma 5.37 -/

section Main

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}

theorem zeroPartitionFunction_eq_prod' {N : ℕ} {lam M ε₀ : ℝ} (X : Finset (Finset ℕ)) :
    zeroPartitionFunction χ N p₀ β lam M ε₀ X =
      ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
  unfold zeroPartitionFunction
  exact prod_congr rfl fun S _ => (prod_singleton _ S).symm

/-- **The real inequality of step 5**: from `𝖬^0(X) ≤ C_b^{|V_X|} ∏ 𝖬^{+,Z}(S)` and
`C_{β,λ,ε₀} ≥ 𝒵_β λ^{2-β}/2`, `P⁻¹ (N C)^{-k} K^k ≤ (C_b (2/𝒵_β) K)^k / ((N λ^{2-β})^k 𝖬^0(X))`. -/
theorem normalization_le {P M0 A Cb Zc K ℓ Nr : ℝ} {k : ℕ} (hP : 0 < P) (hM0 : 0 < M0)
    (hCb : 0 ≤ Cb) (hZ : 0 < Zc) (hK : 0 ≤ K) (hℓ : 0 < ℓ) (hNr : 0 < Nr)
    (hcmp : M0 ≤ Cb ^ k * P) (hA0 : 0 ≤ A) (hA : A ≤ (Nr * (1 / 2 * Zc * ℓ))⁻¹) :
    P⁻¹ * A ^ k * K ^ k ≤ (Cb * (2 / Zc) * K) ^ k / ((Nr * ℓ) ^ k * M0) := by
  have hD : 0 < (Nr * ℓ) ^ k * M0 := by positivity
  have hP' : P⁻¹ ≤ Cb ^ k / M0 := by
    rw [inv_eq_one_div, div_le_div_iff₀ hP hM0]
    linarith
  have hA' : A ^ k ≤ (2 / Zc) ^ k / (Nr * ℓ) ^ k := by
    rw [← div_pow]
    refine pow_le_pow_left₀ hA0 (hA.trans (le_of_eq ?_)) k
    field_simp
  calc P⁻¹ * A ^ k * K ^ k ≤ Cb ^ k / M0 * ((2 / Zc) ^ k / (Nr * ℓ) ^ k) * K ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul hP' hA' (pow_nonneg hA0 _) (by positivity))
          (pow_nonneg hK _)
    _ = (Cb * (2 / Zc) * K) ^ k / ((Nr * ℓ) ^ k * M0) := by
        rw [mul_pow, mul_pow]
        field_simp
        ring

open scoped Classical in
/-- **Lemma 5.37**: `SimplifiedBoundUpper χ p₀ β L`. -/
theorem simplifiedBoundUpper_holds (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (L : ℝ) :
    SimplifiedBoundUpper χ p₀ β L := by
  obtain ⟨C₀, hC₀, hpt⟩ := pointwise_le hχ hβ p₀ L
  refine ⟨C₀, hC₀, fun M hM hMp => ?_⟩
  obtain ⟨Kf, hKf, hpt'⟩ := hpt hM hMp
  obtain ⟨Cb, hCb, hcmp⟩ := blockCmp_uniform hχ hβ hp₀ L hM
  have hZ : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  set Q := Cb * (2 / dipoleConstant χ β) * Kf with hQ
  refine ⟨Real.log (max Q 1), Real.log_nonneg (le_max_right _ _), fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lc, hlc, hcmp'⟩ := hcmp ε₀ hε₀ hε₁
  obtain ⟨ll, hll, hlow⟩ := lem411_lower hχ hβ hε₀
  refine ⟨min (min lc ll) (min 1 ε₀), lt_min (lt_min hlc hll) (lt_min one_pos hε₀),
    fun lam hlam hlt => ?_⟩
  have hltc : lam < lc := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hltl : lam < ll := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨Nc, hNc⟩ := hcmp' lam hlam hltc
  obtain ⟨Nl, hNl⟩ := Filter.eventually_atTop.1 (hlow p₀ lam hlam hltl)
  refine ⟨max (max Nc Nl) 1, fun N hN V Z hVZ X hX hXgood hXp => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hM1 : 1 ≤ M := by linarith
  have hlamh := lam_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
  have hVZ' : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hVZ.1.symm.subset
  -- `|X| ≤ 1`
  by_cases h2 : 2 ≤ X.card
  swap
  · rw [plusActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z (by omega), abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  -- the blocks
  have hblocks : ∀ S ∈ X, 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
      0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
      zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
        Cb * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := fun S hS =>
    hNc N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) hMp V Z hVZ.1 S
      (card_pos.2 (hX.1 S hS)) (hXp S hS)
  set P := ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S with hPdef
  have hP : 0 < P := prod_pos fun S hS => (hblocks S hS).1
  have hM0 : 0 < zeroPartitionFunction χ N p₀ β lam M ε₀ X := by
    rw [zeroPartitionFunction_eq_prod']
    exact prod_pos fun S hS => (hblocks S hS).2.1
  have hXk : X.card ≤ (X.biUnion id).card := Finset.card_le_card_biUnion hX.2 hX.1
  have hcmpX : zeroPartitionFunction χ N p₀ β lam M ε₀ X ≤ Cb ^ (X.biUnion id).card * P := by
    rw [zeroPartitionFunction_eq_prod']
    calc ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S}
        ≤ ∏ S ∈ X, (Cb * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) :=
          prod_le_prod₀ (fun S hS => (hblocks S hS).2.1.le) fun S hS => (hblocks S hS).2.2
      _ = Cb ^ X.card * P := by rw [prod_mul_distrib, prod_const]
      _ ≤ Cb ^ (X.biUnion id).card * P :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCb hXk) hP.le
  -- the normalization `C_{β,λ,ε₀}`
  have hCN := hNl N ((le_max_right _ _).trans ((le_max_left _ _).trans hN))
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1
  have hA : ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ≤
      ((N : ℝ) * (1 / 2 * dipoleConstant χ β * lam ^ (2 - β)))⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hCN hNpos.le)
  -- steps 1–4
  have hmain := ofReal_abs_plusActivity_le_of (C₀ := C₀) hχ hlam hε₀ hN1 hM1 hX h2 hP
    (K := Kf) (by linarith)
    (hpt' lam ε₀ V Z hlam hlamh hVZ' hX hXp)
  refine hmain.trans ?_
  -- step 5
  have hreal := normalization_le (k := (X.biUnion id).card) hP hM0 (by linarith) hZ
    (by linarith : (0 : ℝ) ≤ Kf) hℓ hNpos hcmpX (inv_nonneg.2 hC.le) hA
  have hexp : (Cb * (2 / dipoleConstant χ β) * Kf) ^ (X.biUnion id).card ≤
      Real.exp (Real.log (max Q 1) * (X.biUnion id).card) := by
    have hQ0 : 0 ≤ Q := mul_nonneg (mul_nonneg (by linarith) (div_nonneg zero_le_two hZ.le))
      (by linarith)
    rw [show Real.log (max Q 1) * ((X.biUnion id).card : ℝ) =
      ((X.biUnion id).card : ℝ) * Real.log (max Q 1) from mul_comm _ _, Real.exp_nat_mul,
      Real.exp_log (lt_of_lt_of_le one_pos (le_max_right _ _))]
    exact pow_le_pow_left₀ hQ0 (le_max_left _ _) _
  have hD : 0 < ((N : ℝ) * lam ^ (2 - β)) ^ (X.biUnion id).card *
      zeroPartitionFunction χ N p₀ β lam M ε₀ X := by positivity
  have hfin : ENNReal.ofReal (P⁻¹ *
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ (X.biUnion id).card *
        Kf ^ (X.biUnion id).card) ≤
      ENNReal.ofReal (Real.exp (Real.log (max Q 1) * (X.biUnion id).card)) /
        ENNReal.ofReal (((N : ℝ) * lam ^ (2 - β)) ^ (X.biUnion id).card *
          zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
    rw [← ENNReal.ofReal_div_of_pos hD]
    exact ENNReal.ofReal_le_ofReal (hreal.trans (div_le_div_of_nonneg_right hexp hD.le))
  unfold simplifiedMajorant
  refine mul_le_mul' hfin ?_
  have hD' : ∀ n, tuplesD X n = (Fintype.piFinset fun _ : Fin n => X.powerset).filter
      (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) := fun n => by
    ext Xs
    simp only [tuplesD, mem_filter]
  simp_rw [hD']
  exact ENNReal.sum_le_tsum _

end Main

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
