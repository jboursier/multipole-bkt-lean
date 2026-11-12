/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Majorant
public import MultipoleBKT.Limits.MultipoleLimit

/-!
# Multipole integrands and their elementary regularity

See (4.50),
 and proof of Lemma 4.26.

The block weights, bond products and reversal average are defined here. Translation invariance, measurability, finite-box reversal
invariance and the uniform bound on internal block factors belong below the
logarithmic tree integration. The integrability theorem is in `MultIntegrable`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Defs

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
/-- The weight `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` of the block `S`. -/
noncomputable def blockW (χ : ℂ → ℝ) (β lam M : ℝ) (blk : ι → β') (S : β')
    (c : ι → ℂ × ℂ) : ℝ :=
  (if ((nearGraph M lam c).induce {i | blk i = S}).Connected then 1 else 0) *
    ∏ i, ∏ j, if blk i = S ∧ blk j = S ∧ i < j then stablePairWeight χ β lam (c i) (c j) else 1

open scoped Classical in
/-- The product of the bonds `∏_{i<j ∈ E} (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)`. -/
noncomputable def bondProd (χ : ℂ → ℝ) (β lam M : ℝ) (E : SimpleGraph ι) (c : ι → ℂ × ℂ) : ℝ :=
  ∏ i, ∏ j, if i < j ∧ E.Adj i j then unlinkedPairWeight χ β lam M (c i) (c j) - 1 else 1

/-- The box integrand of `𝖪^mult` for the edge set `E`. -/
noncomputable def multBox (χ : ℂ → ℝ) (β lam M : ℝ) (blk : ι → β') (E : SimpleGraph ι)
    (c : ι → ℂ × ℂ) : ℝ :=
  bondProd χ β lam M E c * (∏ S, blockW χ β lam M blk S c) * ∏ i, pairDensity χ β lam (c i)

/-- The average of `multBox` over the reversals of sets of blocks. -/
noncomputable def symBox (χ : ℂ → ℝ) (β lam M : ℝ) (blk : ι → β') (E : SimpleGraph ι)
    (c : ι → ℂ × ℂ) : ℝ :=
  (∑ A : Finset β', multBox χ β lam M blk E (flipCfg (blockLabels blk A) c)) /
    2 ^ Fintype.card β'

end Defs

section Props

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

omit [Fintype ι] [LinearOrder ι] in
theorem nearGraph_flipCfg (B : Finset ι) (c : ι → ℂ × ℂ) :
    nearGraph M lam (flipCfg B c) = nearGraph M lam c := by
  ext i j
  simp only [nearGraph_adj, flipCfg_apply]
  refine and_congr_right fun _ => ?_
  split_ifs
  · rw [multipoleLinked_swap_left, multipoleLinked_swap_right]
  · rw [multipoleLinked_swap_left]
  · rw [multipoleLinked_swap_right]
  · rfl

omit [Fintype β'] in
theorem blockW_flip (hχ : IsMollifier χ) (blk : ι → β') (S : β') (A : Finset β')
    (c : ι → ℂ × ℂ) :
    blockW χ β lam M blk S (flipCfg (blockLabels blk A) c) = blockW χ β lam M blk S c := by
  unfold blockW
  rw [nearGraph_flipCfg]
  refine congrArg₂ (· * ·) rfl ?_
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  by_cases h : blk i = S ∧ blk j = S ∧ i < j
  · rw [ite_eq_left h, ite_eq_left h, flipCfg_apply, flipCfg_apply]
    simp only [mem_blockLabels, h.1, h.2.1]
    split_ifs
    · exact stablePairWeight_swap_swap _ _ hχ β lam
    · rfl
  · rw [ite_eq_right h, ite_eq_right h]

omit [Fintype ι] [LinearOrder ι] in
theorem pairDensity_flip (hχ : IsMollifier χ) (B : Finset ι) (c : ι → ℂ × ℂ) (i : ι) :
    pairDensity χ β lam (flipCfg B c i) = pairDensity χ β lam (c i) := by
  rw [flipCfg_apply]
  split_ifs
  · exact pairDensity_swap _ hχ β lam
  · rfl

theorem symBox_translate (blk : ι → β') (E : SimpleGraph ι) (a : ℂ) (c : ι → ℂ × ℂ) :
    symBox χ β lam M blk E (translate a c) = symBox χ β lam M blk E c := by
  unfold symBox
  refine congrArg₂ (· / ·) ?_ rfl
  refine Finset.sum_congr rfl fun A _ => ?_
  have hflip : flipCfg (blockLabels blk A) (translate a c) =
      translate a (flipCfg (blockLabels blk A) c) := by
    funext i
    simp only [flipCfg_apply, translate]
    split_ifs <;> simp [Prod.swap]
  rw [hflip]
  set c' := flipCfg (blockLabels blk A) c
  unfold multBox bondProd blockW translate
  have hG : nearGraph M lam (fun i => c' i + (a, a)) = nearGraph M lam c' := by
    ext i j
    simp only [nearGraph_adj, multipoleLinked_translate]
  rw [hG]
  simp only [unlinkedPairWeight_translate, stablePairWeight_translate, pairDensity_translate]

omit [DecidableEq ι] [Fintype β'] in
theorem measurable_blockW (hχ : IsMollifier χ) (hlam : 0 < lam) (blk : ι → β') (S : β') :
    Measurable (blockW (ι := ι) χ β lam M blk S) := by
  classical
  unfold blockW
  refine Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam
      (fun G => (G.induce {i | blk i = S}).Connected))
    measurable_const measurable_const) ?_
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  split_ifs
  · exact measurable_stablePairWeight_apply hχ hlam β i j
  · exact measurable_const

omit [DecidableEq ι] in
theorem measurable_bondProd (hχ : IsMollifier χ) (hlam : 0 < lam) (E : SimpleGraph ι) :
    Measurable (bondProd (ι := ι) χ β lam M E) := by
  classical
  unfold bondProd
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  split_ifs
  · exact (measurable_unlinkedPairWeight_apply hχ hlam β M i j).sub_const 1
  · exact measurable_const

omit [DecidableEq ι] in
theorem measurable_multBox (hχ : IsMollifier χ) (hlam : 0 < lam) (blk : ι → β')
    (E : SimpleGraph ι) : Measurable (multBox (ι := ι) χ β lam M blk E) :=
  ((measurable_bondProd hχ hlam E).mul (Finset.measurable_prod _ fun S _ =>
    measurable_blockW hχ hlam blk S)).mul (Finset.measurable_prod _ fun i _ =>
      (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i))

theorem measurable_symBox (hχ : IsMollifier χ) (hlam : 0 < lam) (blk : ι → β')
    (E : SimpleGraph ι) : Measurable (symBox (ι := ι) χ β lam M blk E) :=
  (Finset.measurable_sum _ fun _ _ => (measurable_multBox hχ hlam blk E).comp
    (measurable_flipCfg _)).div_const _

omit [DecidableEq ι] in
/-- `multBox` is bounded (for `β ≥ 0`, `λ > 0`, `M ≥ 1`). -/
theorem exists_abs_multBox_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam) (hM : 1 ≤ M)
    (blk : ι → β') (E : SimpleGraph ι) :
    ∃ B : ℝ, ∀ c : ι → ℂ × ℂ, |multBox χ β lam M blk E c| ≤ B := by
  classical
  obtain ⟨C, hC0, hC⟩ := dipoleBond_le hχ
  obtain ⟨C', hC'0, hC'⟩ := multipoleBond_le hχ
  obtain ⟨Cw, hCw0, hCw⟩ := exists_exp_smearedKernel_le hχ hβ0
  set W := Real.exp (β * C) + Real.exp (β * C') + 1
  have hW1 : 1 ≤ W := by have := Real.exp_pos (β * C); have := Real.exp_pos (β * C'); linarith
  set P := Cw * lam ^ (-β)
  have hpd : ∀ d : ℂ × ℂ, pairDensity χ β lam d ≤ P := fun d => by
    refine (hCw lam hlam (d.1 - d.2)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _)
      (by linarith)) hCw0.le
  refine ⟨W ^ (Fintype.card ι * Fintype.card ι) *
    (W ^ (Fintype.card ι * Fintype.card ι)) ^ Fintype.card β' * P ^ Fintype.card ι, fun c => ?_⟩
  unfold multBox
  rw [abs_mul, abs_mul]
  have h1 : |bondProd χ β lam M E c| ≤ W ^ (Fintype.card ι * Fintype.card ι) := by
    unfold bondProd
    refine abs_prod_prod_le _ fun i j => ?_
    split_ifs
    · have h := hC' β hβ0 M hM lam hlam (c i) (c j)
      have h0 := unlinkedPairWeight_nonneg χ β lam M (c i) (c j)
      unfold unlinkedPairWeight at h0 ⊢
      rw [abs_le]
      constructor <;> nlinarith [Real.exp_pos (β * C), Real.exp_pos (β * C')]
    · rw [abs_one]; exact hW1
  have h2 : |∏ S, blockW χ β lam M blk S c| ≤ (W ^ (Fintype.card ι * Fintype.card ι)) ^
      Fintype.card β' := by
    rw [abs_prod]
    rw [← Finset.card_univ (α := β'), ← prod_const]
    refine prod_le_prod₀ (fun S _ => abs_nonneg _) fun S _ => ?_
    unfold blockW
    rw [abs_mul]
    have hind : ∀ (p : Prop) [Decidable p], |(if p then (1 : ℝ) else 0)| ≤ 1 := fun p _ => by
      split_ifs <;> simp
    refine (mul_le_mul_of_nonneg_right (hind _) (abs_nonneg _)).trans ?_
    rw [one_mul]
    refine abs_prod_prod_le _ fun i j => ?_
    split_ifs
    · rw [abs_of_nonneg (stablePairWeight_nonneg _ _ _ _ _)]
      exact (hC β hβ0 lam hlam _ _).trans (by linarith [Real.exp_pos (β * C')])
    · rw [abs_one]; exact hW1
  have h3 : |∏ i, pairDensity χ β lam (c i)| ≤ P ^ Fintype.card ι := by
    rw [abs_of_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le),
      ← Finset.card_univ (α := ι), ← prod_const]
    exact prod_le_prod₀ (fun i _ => (pairDensity_pos _ _ _ _).le) fun i _ => hpd _
  exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)) h3 (abs_nonneg _)
    (by positivity)

/-- The box integrals of `symBox` and `multBox` agree. -/
theorem integral_boxConfig_symBox (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    (hM : 1 ≤ M) (N : ℕ) (blk : ι → β') (E : SimpleGraph ι) :
    ∫ c in boxConfig ι N, symBox χ β lam M blk E c =
      ∫ c in boxConfig ι N, multBox χ β lam M blk E c := by
  obtain ⟨B, hB⟩ := exists_abs_multBox_le hχ hβ0 hlam hM blk E (ι := ι)
  have hfin : volume (boxConfig ι N) ≠ ⊤ := by
    rw [boxConfig, volume_pi, Measure.pi_pi]
    exact ENNReal.prod_ne_top fun _ _ => (volume_box_prod_lt_top N).ne
  have hint : ∀ A : Finset β', IntegrableOn
      (fun c => multBox χ β lam M blk E (flipCfg (blockLabels blk A) c)) (boxConfig ι N) := by
    intro A
    refine Measure.integrableOn_of_bounded hfin
      ((measurable_multBox hχ hlam blk E).comp (measurable_flipCfg _)).aestronglyMeasurable
      (M := B) (Eventually.of_forall fun c => ?_)
    rw [Real.norm_eq_abs]
    exact hB _
  unfold symBox
  rw [integral_div, integral_finsetSum _ fun A _ => hint A]
  simp_rw [integral_boxConfig_flipCfg]
  rw [sum_const, card_univ, Fintype.card_finset, nsmul_eq_mul]
  push_cast
  field_simp

end Props

section Regularity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

omit [Fintype ι] [LinearOrder ι] in
theorem measurable_fold_max (s : Finset ι) (b : ℝ) {f : ι → (ι → ℂ × ℂ) → ℝ}
    (hf : ∀ i, Measurable (f i)) : Measurable fun c => s.fold max b fun i => f i c := by
  induction s using Finset.induction_on with
  | empty => simp only [fold_empty]; exact measurable_const
  | insert a s ha ih =>
    simp only [fold_insert ha]
    exact (hf a).max ih

omit [LinearOrder ι] in
theorem measurable_maxRad (lam : ℝ) : Measurable (maxRad (ι := ι) lam) :=
  measurable_fold_max univ lam fun i =>
    ((continuous_norm.comp (continuous_fst.sub continuous_snd)).max continuous_const).measurable.comp
      (measurable_pi_apply i)

theorem measurable_rhoD (lam : ℝ) : Measurable (rhoD lam) :=
  ((continuous_norm.comp (continuous_fst.sub continuous_snd)).max continuous_const).measurable

theorem measurable_dipoleDist : Measurable fun p : (ℂ × ℂ) × (ℂ × ℂ) => dipoleDist p.1 p.2 := by
  unfold dipoleDist
  fun_prop

theorem measurable_nearW (M lam : ℝ) :
    Measurable fun p : (ℂ × ℂ) × (ℂ × ℂ) => nearW M lam p.1 p.2 := by
  unfold nearW
  have h1 := measurable_dipoleDist
  have h2 : Measurable fun p : (ℂ × ℂ) × (ℂ × ℂ) => min (rhoD lam p.1) (rhoD lam p.2) :=
    ((measurable_rhoD lam).comp measurable_fst).min ((measurable_rhoD lam).comp measurable_snd)
  refine Measurable.div (Measurable.ite ?_ measurable_const measurable_const) (h2.pow_const 2)
  exact measurableSet_le h1 (h2.const_mul M)

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem measurable_nearE (M lam : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => nearE M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    exact (measurable_nearW M lam).comp (f := fun c : ι → ℂ × ℂ => (c i, c j)) (by fun_prop)

theorem pairDensity_mk (hχ : IsMollifier χ) (t u : ℂ) :
    pairDensity χ β lam (t, t + u) = Real.exp (β * smearedKernel χ lam u) := by
  simp only [pairDensity, sub_add_cancel_left, smearedKernel_neg hχ]

omit [DecidableEq ι] [LinearOrder ι] in
theorem maxRad_ofPosVec (lam : ℝ) (x x' u : ι → ℂ) :
    maxRad lam (ofPosVec x u) = maxRad lam (ofPosVec x' u) := by
  unfold maxRad
  congr 1
  funext i
  simp only [ofPosVec_apply, rhoD_mk]

end Regularity

section Integrable

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
omit [DecidableEq ι] in
/-- The block weights vanish unless every block is near-connected, and are bounded. -/
theorem exists_abs_prod_blockW_le_uniform (hχ : IsMollifier χ) (hβ0 : 0 ≤ β)
    (blk : ι → β') :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, ∀ c : ι → ℂ × ℂ, |∏ S, blockW χ β lam M blk S c| ≤
      Cw * (if ∀ S, ((nearGraph M lam c).induce {i | blk i = S}).Connected then 1 else 0) := by
  obtain ⟨C, hC0, hC⟩ := dipoleBond_le hχ
  set W := Real.exp (β * C)
  have hW1 : 1 ≤ W := Real.one_le_exp (mul_nonneg hβ0 hC0)
  refine ⟨(W ^ (Fintype.card ι * Fintype.card ι)) ^ Fintype.card β', by positivity, fun lam hlam M c => ?_⟩
  split_ifs with h
  · rw [mul_one, abs_prod, ← Finset.card_univ (α := β'), ← prod_const]
    refine prod_le_prod₀ (fun S _ => abs_nonneg _) fun S _ => ?_
    unfold blockW
    rw [ite_eq_left (h S), one_mul]
    refine abs_prod_prod_le _ fun i j => ?_
    split_ifs
    · rw [abs_of_nonneg (stablePairWeight_nonneg _ _ _ _ _)]
      exact hC β hβ0 lam hlam _ _
    · rw [abs_one]; exact hW1
  · push Not at h
    obtain ⟨S, hS⟩ := h
    rw [mul_zero, abs_nonpos_iff]
    refine prod_eq_zero (mem_univ S) ?_
    unfold blockW
    rw [ite_eq_right hS, zero_mul]

end Integrable

end Limits

end MultipoleBKT

end
