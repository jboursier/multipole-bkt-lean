/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.MergedBlocks
public import MultipoleBKT.Limits.RouteDirect.Anchor

/-!
# The near/far expansion of the full multipole block average

See Lemma 4.26 of the paper. Near external bonds are minus their link indicators.
Original block weights are retained, and parity is applied after merging.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph SmallIntegral
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [LinearOrder I] [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- A fixed far-edge term, including all original block weights. -/
noncomputable def blockTerm (χ : ℂ → ℝ) (β lam M : ℝ) (blk : I → B)
    (E : SimpleGraph I) (F : Finset (Sym2 I)) (c : I → ℂ × ℂ) : ℝ :=
  (∏ e ∈ F, farBondE χ β lam M c e) *
    (∏ e ∈ E.edgeFinset \ F, -linkIndE M lam c e) *
    (∏ b, blockW χ β lam M blk b c) * ∏ i, pairDensity χ β lam (c i)

/-- The factors internal to the merged parts. -/
noncomputable def blockTermWeight (χ : ℂ → ℝ) (β lam M : ℝ) (blk : I → B)
    (E : SimpleGraph I) (F : Finset (Sym2 I)) (c : I → ℂ × ℂ) : ℝ :=
  (∏ e ∈ F \ (mergedInter blk E F).edgeFinset, farBondE χ β lam M c e) *
    (∏ e ∈ E.edgeFinset \ F, -linkIndE M lam c e) * ∏ b, blockW χ β lam M blk b c

/-- The reversal average over the merged near parts. -/
noncomputable def blockAverage (χ : ℂ → ℝ) (β lam M : ℝ) (blk : I → B)
    (E : SimpleGraph I) (F : Finset (Sym2 I)) : (I → ℂ × ℂ) → ℝ :=
  reversalAverage (mergedOf blk E F) (blockTerm χ β lam M blk E F)

/-- The external multipole bonds split into their far bond and negative near indicator. -/
theorem bondProd_eq_far_sub_link (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (E : SimpleGraph I) (c : I → ℂ × ℂ) :
    bondProd χ β lam M E c = ∏ e ∈ E.edgeFinset,
      (farBondE χ β lam M c e + -linkIndE M lam c e) := by
  have hc (i j : I) : farBond χ β lam M c i j - linkInd M lam c i j =
      farBond χ β lam M c j i - linkInd M lam c j i := by
    rw [farBond_comm, linkInd_comm]
  have hp : (∏ e ∈ E.edgeFinset, (farBondE χ β lam M c e + -linkIndE M lam c e)) =
      ∏ e ∈ E.edgeFinset, symmLift (fun i j => farBond χ β lam M c i j - linkInd M lam c i j) hc e := by
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => rfl
  rw [hp, ← prod_prod_ite_lt_adj E _ hc]
  unfold bondProd
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j _
  split_ifs
  · rw [farBond_eq hχ hM]
    ring
  · rfl

/-- The pointwise near/far expansion before either reversal average. -/
theorem multBox_eq_sum_blockTerm (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (blk : I → B) (E : SimpleGraph I) (c : I → ℂ × ℂ) :
    multBox χ β lam M blk E c = ∑ F ∈ E.edgeFinset.powerset, blockTerm χ β lam M blk E F c := by
  unfold multBox
  rw [bondProd_eq_far_sub_link hχ hM, prod_add, sum_mul, sum_mul]
  rfl

/-- A term under reversal of its merged parts. Only the far edges between
those parts contribute parity signs. -/
theorem blockTerm_flip (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    {F : Finset (Sym2 I)} (hF : F ⊆ E.edgeFinset)
    (A : Finset (mergedGraph blk E F).ConnectedComponent) (c : I → ℂ × ℂ) :
    blockTerm χ β lam M blk E F (flipCfg (blockLabels (mergedOf blk E F) A) c) =
      blockTermWeight χ β lam M blk E F c *
        (∏ e ∈ (mergedInter blk E F).edgeFinset,
          (alphaE hχ β lam M c e + linkIndE M lam c e +
            signCross (Sym2.map (mergedOf blk E F)) A e * gammaE hχ β lam M c e)) *
        ∏ i, pairDensity χ β lam (c i) := by
  have hD : (mergedInter blk E F).edgeFinset ⊆ F := by
    intro e he
    induction e using Sym2.ind with
    | h i j => exact mem_far_of_mergedInter blk E F (mem_edgeFinset.mp he)
  unfold blockTerm blockTermWeight
  rw [← prod_sdiff hD]
  have h1 : (∏ e ∈ F \ (mergedInter blk E F).edgeFinset,
      farBondE χ β lam M (flipCfg (blockLabels (mergedOf blk E F) A) c) e) =
      ∏ e ∈ F \ (mergedInter blk E F).edgeFinset, farBondE χ β lam M c e := by
    apply prod_congr rfl
    intro e he
    obtain ⟨heF, heD⟩ := mem_sdiff.mp he
    induction e using Sym2.ind with
    | h i j =>
      have hij : E.Adj i j := mem_edgeFinset.mp (hF heF)
      have heq : mergedOf blk E F i = mergedOf blk E F j := by
        by_contra hn
        exact heD (show s(i, j) ∈ (mergedInter blk E F).edgeFinset from mem_edgeFinset.mpr ⟨hij, hn⟩)
      exact farBondE_flip_of_eq hχ hM _ A c heq
  have h2 : (∏ e ∈ (mergedInter blk E F).edgeFinset,
      farBondE χ β lam M (flipCfg (blockLabels (mergedOf blk E F) A) c) e) =
      ∏ e ∈ (mergedInter blk E F).edgeFinset, (alphaE hχ β lam M c e + linkIndE M lam c e +
        signCross (Sym2.map (mergedOf blk E F)) A e * gammaE hχ β lam M c e) :=
    prod_congr rfl fun e _ => farBondE_flip hχ hM _ A c e
  have h3 : (∏ e ∈ E.edgeFinset \ F, -linkIndE M lam (flipCfg (blockLabels (mergedOf blk E F) A) c) e) =
      ∏ e ∈ E.edgeFinset \ F, -linkIndE M lam c e := by
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => change -linkInd M lam _ i j = _; rw [linkInd_flip]; rfl
  have h4 : (∏ i, pairDensity χ β lam (flipCfg (blockLabels (mergedOf blk E F) A) c i)) =
      ∏ i, pairDensity χ β lam (c i) := prod_congr rfl fun i _ => pairDensity_flip hχ _ c i
  have hf : mergedOf blk E F = mergedBlockOf blk hblk E F ∘ blk :=
    funext fun i => (mergedBlockOf_apply blk hblk E F i).symm
  have h5 : (∏ b, blockW χ β lam M blk b (flipCfg (blockLabels (mergedOf blk E F) A) c)) =
      ∏ b, blockW χ β lam M blk b c := by
    rw [hf, blockLabels_comp]
    exact prod_congr rfl fun b _ => blockW_flip hχ blk b _ c
  rw [h1, h2, h3, h4, h5]
  ring

/-- The full original block average is an average of the merged-part averages.
This applies the subgroup identity before integrability is considered. -/
theorem symBox_eq_sum_blockAverage (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I) (c : I → ℂ × ℂ) :
    symBox χ β lam M blk E c = ∑ F ∈ E.edgeFinset.powerset,
      reversalAverage blk (blockAverage χ β lam M blk E F) c := by
  have hsub (F : Finset (Sym2 I)) : reversalAverage blk (blockAverage χ β lam M blk E F) c =
      reversalAverage blk (blockTerm χ β lam M blk E F) c := by
    have hf : mergedOf blk E F = mergedBlockOf blk hblk E F ∘ blk :=
      funext fun i => (mergedBlockOf_apply blk hblk E F i).symm
    unfold blockAverage
    rw [hf]
    exact reversalAverage_subgroup blk (mergedBlockOf blk hblk E F) _ c
  simp_rw [hsub]
  unfold symBox reversalAverage
  simp_rw [multBox_eq_sum_blockTerm hχ hM blk E]
  rw [sum_comm, Finset.sum_div]

end MultipoleBKT.Limits.RouteDirect

end
