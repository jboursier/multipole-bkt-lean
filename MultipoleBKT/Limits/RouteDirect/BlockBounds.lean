/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.BlockTerms

/-!
# Bounds and regularity of the merged multipole terms

See Lemma 4.26 of the paper. Internal factors are bounded and vanish unless each
merged part is near connected. Parity is applied only to inter-part edges.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph SmallIntegral
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

omit [Fintype I] [LinearOrder I] in
/-- Measurability of a near indicator. -/
theorem measurable_linkIndE (M lam : ℝ) (e : Sym2 I) :
    Measurable fun c : I → ℂ × ℂ => linkIndE M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    change Measurable fun c : I → ℂ × ℂ => if MultipoleLinked M lam (c i) (c j) then (1 : ℝ) else 0
    exact Measurable.ite (measurableSet_multipoleLinked_apply M lam i j) measurable_const measurable_const

/-- Measurability of the unaveraged near/far term. -/
theorem measurable_blockTerm (hχ : IsMollifier χ) (hlam : 0 < lam)
    (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I)) :
    Measurable (blockTerm χ β lam M blk E F) := by
  unfold blockTerm
  exact (((Finset.measurable_prod _ fun e _ => measurable_farBondE hχ hlam β M e).mul
    (Finset.measurable_prod _ fun e _ => (measurable_linkIndE M lam e).neg)).mul
    (Finset.measurable_prod _ fun b _ => measurable_blockW hχ hlam blk b)).mul
      (Finset.measurable_prod _ fun i _ => (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i))

/-- Measurability of the merged average. -/
theorem measurable_blockAverage (hχ : IsMollifier χ) (hlam : 0 < lam)
    (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I)) :
    Measurable (blockAverage χ β lam M blk E F) :=
  measurable_reversalAverage _ (measurable_blockTerm hχ hlam blk E F)

omit [Fintype B] in
/-- Internal block weights do not change under common translation. -/
theorem blockW_translate (blk : I → B) (b : B) (a : ℂ) (c : I → ℂ × ℂ) :
    blockW χ β lam M blk b (translate a c) = blockW χ β lam M blk b c := by
  unfold blockW translate
  have heq : nearGraph M lam (fun i => c i + (a, a)) = nearGraph M lam c := by
    ext i j
    simp only [nearGraph_adj, multipoleLinked_translate]
  rw [heq]
  simp only [stablePairWeight_translate]

/-- Translation invariance of each merged average. -/
theorem blockAverage_translate (blk : I → B) (E : SimpleGraph I) (F : Finset (Sym2 I))
    (a : ℂ) (c : I → ℂ × ℂ) :
    blockAverage χ β lam M blk E F (translate a c) = blockAverage χ β lam M blk E F c := by
  have ht (c : I → ℂ × ℂ) : blockTerm χ β lam M blk E F (translate a c) =
      blockTerm χ β lam M blk E F c := by
    have hl : (∏ e ∈ E.edgeFinset \ F, -linkIndE M lam (translate a c) e) =
        ∏ e ∈ E.edgeFinset \ F, -linkIndE M lam c e := by
      apply prod_congr rfl
      intro e _
      induction e using Sym2.ind with
      | h i j =>
        change -(if MultipoleLinked M lam (translate a c i) (translate a c j) then (1 : ℝ) else 0) = _
        rw [show MultipoleLinked M lam (translate a c i) (translate a c j) ↔
          MultipoleLinked M lam (c i) (c j) from multipoleLinked_translate a (c i) (c j) M lam]
        rfl
    have hp : (fun i => pairDensity χ β lam (translate a c i)) =
        fun i => pairDensity χ β lam (c i) := funext fun i => pairDensity_translate _ _ _ _ _
    unfold blockTerm
    simp only [farBondE_translate, blockW_translate, hl, hp]
  unfold blockAverage reversalAverage
  simp_rw [flipCfg_translate, ht]

/-- The internal factors of a merged term have a near-connectivity indicator. -/
theorem exists_abs_blockTermWeight_le_uniform (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (blk : I → B) (E : SimpleGraph I) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, ∀ F : Finset (Sym2 I), F ⊆ E.edgeFinset → ∀ c : I → ℂ × ℂ,
      |blockTermWeight χ β lam M blk E F c| ≤ Cw *
        (if ∀ C, ((nearGraph M lam c).induce {i | mergedOf blk E F i = C}).Connected then 1 else 0) := by
  obtain ⟨C, hC, hb⟩ := exists_abs_dipBond_le (ι := I) hχ
  obtain ⟨CW, hCW, hW⟩ := exists_abs_prod_blockW_le_uniform hχ hβ blk
  let Bb := Real.exp (β * C)
  have hBb : 1 ≤ Bb := Real.one_le_exp (mul_nonneg hβ hC)
  refine ⟨Bb ^ E.edgeFinset.card * CW, by positivity, fun lam hlam M F hF c => ?_⟩
  have hfar (e : Sym2 I) : |farBondE χ β lam M c e| ≤ Bb := by
    induction e using Sym2.ind with
    | h i j =>
      change |if MultipoleLinked M lam (c i) (c j) then 0 else dipBond χ β lam c i j| ≤ Bb
      split_ifs
      · simpa only [abs_zero] using zero_le_one.trans hBb
      · exact hb β hβ lam hlam c i j
  have hnear (e : Sym2 I) : |-linkIndE M lam c e| ≤ 1 := by
    induction e using Sym2.ind with
    | h i j => change |-(if MultipoleLinked M lam (c i) (c j) then (1 : ℝ) else 0)| ≤ 1; split_ifs <;> norm_num
  by_cases hblocks : ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected
  · by_cases hedges : ∀ i j, E.Adj i j → s(i, j) ∉ F → MultipoleLinked M lam (c i) (c j)
    · rw [ite_eq_left (merged_near_connected blk E F c hblocks hedges), mul_one]
      have hw := hW lam hlam M c
      rw [ite_eq_left hblocks, mul_one] at hw
      unfold blockTermWeight
      rw [abs_mul, abs_mul]
      have hf : |∏ e ∈ F \ (mergedInter blk E F).edgeFinset, farBondE χ β lam M c e| ≤
          Bb ^ E.edgeFinset.card := abs_prod_le_pow hBb (fun e _ => hfar e)
            ((Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_le_card hF))
      have hn : |∏ e ∈ E.edgeFinset \ F, -linkIndE M lam c e| ≤ 1 := by
        rw [abs_prod]
        exact (prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun e _ => hnear e)).trans_eq (by simp)
      exact mul_le_mul (by simpa only [mul_one] using mul_le_mul hf hn (abs_nonneg _) (by positivity))
        hw (abs_nonneg _) (by positivity)
    · push Not at hedges
      obtain ⟨i, j, hij, he, hn⟩ := hedges
      have hz : ∏ e ∈ E.edgeFinset \ F, -linkIndE M lam c e = 0 := by
        apply prod_eq_zero (i := s(i, j)) (mem_sdiff.mpr ⟨mem_edgeFinset.mpr hij, he⟩)
        change -(if MultipoleLinked M lam (c i) (c j) then (1 : ℝ) else 0) = 0
        simp only [ite_eq_right hn, neg_zero]
      unfold blockTermWeight
      rw [hz, mul_zero, zero_mul, abs_zero]
      positivity
  · have hw := hW lam hlam M c
    rw [ite_eq_right hblocks, mul_zero] at hw
    have hz := abs_nonpos_iff.mp hw
    unfold blockTermWeight
    rw [hz, mul_zero, abs_zero]
    positivity

/-- Parity removes precisely the odd graphs that are not Eulerian relative
to the merged parts. -/
theorem abs_blockAverage_le (hχ : IsMollifier χ) (hM : 1 ≤ M) (blk : I → B)
    (hblk : Function.Surjective blk) (E : SimpleGraph I) {F : Finset (Sym2 I)}
    (hF : F ⊆ E.edgeFinset) (c : I → ℂ × ℂ) :
    |blockAverage χ β lam M blk E F c| ≤
      |blockTermWeight χ β lam M blk E F c| * (∏ i, pairDensity χ β lam (c i)) *
        ∑ A ∈ (mergedInter blk E F).edgeFinset.powerset.filter (CutEven (Sym2.map (mergedOf blk E F))),
          (∏ e ∈ (mergedInter blk E F).edgeFinset \ A, |alphaE hχ β lam M c e|) *
            ∏ e ∈ A, |gammaE hχ β lam M c e| := by
  have hpd : 0 ≤ ∏ i, pairDensity χ β lam (c i) := prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
  have heq : blockAverage χ β lam M blk E F c = blockTermWeight χ β lam M blk E F c *
      (∏ i, pairDensity χ β lam (c i)) *
      ((∑ A : Finset (mergedGraph blk E F).ConnectedComponent,
        ∏ e ∈ (mergedInter blk E F).edgeFinset, (alphaE hχ β lam M c e + linkIndE M lam c e +
          signCross (Sym2.map (mergedOf blk E F)) A e * gammaE hχ β lam M c e)) /
            2 ^ Fintype.card (mergedGraph blk E F).ConnectedComponent) := by
    unfold blockAverage reversalAverage
    simp_rw [blockTerm_flip hχ hM blk hblk E hF]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun A _ => by ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hpd]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) hpd)
  refine (abs_avg_prod_le (Sym2.map (mergedOf blk E F)) (mergedInter blk E F).edgeFinset _ _).trans ?_
  apply sum_le_sum
  intro A _
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun _ _ => abs_nonneg _)
  exact prod_le_prod₀ (fun _ _ => abs_nonneg _) fun e _ => abs_alphaE_add_linkIndE_le hχ c e

end MultipoleBKT.Limits.RouteDirect

end
