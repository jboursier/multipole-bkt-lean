/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.ComponentZ
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Euler
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Marked
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Indicators

/-!
# The frozen-model component estimate as a sum of trees

The paper: Proposition 5.18. Instantiate the two family bounds using support geometry,
then enlarge `B(·, T)` to all relative trees. No tree is selected from an
upper bound on a family sum.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open Finset SimpleGraph Peeling CoreForest Quadratic Parity Hierarchical Multipole
open scoped Classical NNReal

variable {χ : ℂ → ℝ}

/-- Every odd component is bounded by the sum of its quadratic-tail tree terms. -/
theorem component_family_bound_Z_of_indicator (hχ : IsMollifier χ) (p₀ : ℕ) (β M : ℝ) (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ Y : Finset (Finset ℕ), IsSubpartition Y → (Y.biUnion id).card ≤ k →
      ∀ E' : Finset (ℕ × ℕ), E' ⊆ interPairs Y → IsRelConnected Y (pairGraph (Y.biUnion id) E') →
      ∀ W' : Finset ℕ, W' ⊆ Y.biUnion id →
      IsRelEulerianOff Y (marksOn Y W') (pairGraph (Y.biUnion id) E') →
      ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ Y.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) ∧
        0 < ‖(c i).1 - (c i).2‖) →
      (∀ S ∈ Y, ConnOn S (linkedPairs M lam c S)) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ((∏ p ∈ E', |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
          ∏ i ∈ W', |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) * s ≤
        A * (radialExceptMax c Y *
          ∑ T ∈ relTrees Y,
            (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ (truncationScale p₀ β lam) c e) *
              compTail c Y T) := by
  obtain ⟨C₁, hC₁, hab⟩ := bornesabZ_Z hχ β
  obtain ⟨C₂, hC₂, hinf⟩ := bornesabinfty_Z hχ p₀ β
  set K : ℝ := max 6 ((M + 2) ^ k) with hKdef
  have hK : 1 ≤ K := le_max_of_le_left (by norm_num)
  have hM1 : 1 ≤ M := by linarith
  have hB1 : 1 ≤ C₁ ^ 3 * C₂ * K ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC₁) hC₂)
      (one_le_pow₀ hK)
  set A₀ : ℝ := C₁ ^ (k * k) * ((C₁ ^ 3 * C₂ * K ^ 6) ^ k * (4 * (K ^ k) ^ 2)) with hA₀
  have hA₀1 : 1 ≤ A₀ := by
    refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC₁) (one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ hB1) ?_)
    have : 1 ≤ (K ^ k) ^ 2 := one_le_pow₀ (one_le_pow₀ hK)
    linarith
  refine ⟨A₀, hA₀1, ?_⟩
  intro N lam ε₀ V Z hlam hlamh hMp hVZ Y hY hk E' hE' hconn W' hW' heul c hc hS s hs0 hs1
  set W := Y.biUnion id with hWdef
  set R := truncationScale p₀ β lam with hR
  set z : W → ℂ × ℂ := fun i => c i with hz
  set G := pairGraph W E' with hG
  have hsupp' : ∀ i : W, OnSupportZ p₀ β lam M ε₀ V Z (c i) := fun i => (hc i i.2).1
  have hcomm : ∀ i j : ℕ, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c i) (c j)| =
      |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c j) (c i)| :=
    fun i j => abs_oddBondUnlinked_comm hχ hM1 _ _
  set A : Sym2 W → ℝ := Sym2.lift ⟨fun i j : W =>
    |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c i) (c j)|,
    fun i j => hcomm i j⟩ with hAdef
  have hprod : ∏ p ∈ E', |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (c p.1) (c p.2)| = ∏ e ∈ G.edgeFinset, A e :=
    prod_pairs_eq_prod_edgeFinset (hE'.trans interPairs_subset_pairsOn)
      (fun i j => |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c i) (c j)|) hcomm
  have hA0 : ∀ e, 0 ≤ A e := by
    intro e
    induction e using Sym2.ind with
    | h i j => exact abs_nonneg _
  have hAbs : ∀ i j : W, absWeight (radiiOn z) (distOn z) (cutOn M lam ε₀ R z) s(i, j) =
      absOddWeight M lam ε₀ R (c i) (c j) := by
    intro i j
    rw [absWeight_on]
    rfl
  have hA : ∀ e ∈ G.edgeSet, A e ≤ C₁ * absWeight (radiiOn z) (distOn z) (cutOn M lam ε₀ R z) e := by
    intro e _
    induction e using Sym2.ind with
    | h i j =>
      rw [hAbs]
      exact (hab p₀ lam M ε₀ V Z hlam hlamh hMp hVZ (c i) (c j) (hsupp' i) (hsupp' j)).1
  have ha1 : ∀ e ∈ G.edgeSet, absWeight (radiiOn z) (distOn z) (cutOn M lam ε₀ R z) e ≤ 1 := by
    intro e _
    induction e using Sym2.ind with
    | h i j =>
      rw [hAbs]
      exact absOddWeight_le_one' hM1 hlam _ _
  have hr : ∀ v, 0 ≤ radiiOn z v := fun v => norm_nonneg _
  have hd : ∀ e, 0 ≤ distOn z e := distOn_nonneg z
  have hc0 : ∀ e, 0 ≤ cutOn M lam ε₀ R z e := cutOn_nonneg M lam ε₀ R z
  have hc1 : ∀ e, cutOn M lam ε₀ R z e ≤ 1 := by
    intro e
    induction e using Sym2.ind with
    | h i j =>
      simp only [cutOn, Sym2.lift_mk]
      split_ifs <;> norm_num
  -- a block of maximal radius
  have hYne : (univ : Finset Y).Nonempty := by
    obtain ⟨e, -⟩ := hconn.2.1
    induction e using Sym2.ind with
    | h i j => exact ⟨blockOf hY i, mem_univ _⟩
  obtain ⟨Ŝ, -, hŜ⟩ := Finset.exists_max_image (univ : Finset Y)
    (fun S => blockRadius hY (radiiOn z) S) hYne
  have hŜ' : ∀ S, blockRadius hY (radiiOn z) S ≤ blockRadius hY (radiiOn z) Ŝ :=
    fun S => hŜ S (mem_univ S)
  have hŜ'' : ∀ S : Y, blockRad c S ≤ blockRad c Ŝ := by
    intro S
    have := hŜ' S
    rwa [blockRadius_eq_blockRad hY c, blockRadius_eq_blockRad hY c] at this
  have hpos : 0 < blockRad c Ŝ := by
    obtain ⟨i, hi⟩ := hY.1 Ŝ Ŝ.2
    have hiW : i ∈ W := subset_biUnion_of_mem id Ŝ.2 hi
    exact (hc i hiW).2.trans_le (le_blockRad c hi)
  have hrad : ∏ S ∈ univ.erase Ŝ, blockRadius hY (radiiOn z) S ^ 2 = radialExceptMax c Y :=
    prod_erase_blockRadius_eq hY c hŜ'' hpos
  have hRŜ : blockRadius hY (radiiOn z) Ŝ = blockRad c W := by
    rw [blockRadius_eq_blockRad hY c]
    exact blockRad_biUnion_eq c hŜ''
  have htail : ∀ T : SimpleGraph W, treeTail (distOn z) T (blockRadius hY (radiiOn z) Ŝ) =
      compTail c Y T := by
    intro T
    rw [hRŜ]
    rfl
  have hcardW : Fintype.card W ≤ k := by rw [Fintype.card_coe]; exact hk
  have hGcard : G.edgeFinset.card ≤ k * k := card_edgeFinset_le_sq G hcardW
  have hP0 : 0 ≤ radialExceptMax c Y := radialExceptMax_nonneg c Y
  -- the final comparison of constants
  have hfin : ∀ (T : SimpleGraph W) (B : ℝ), 1 ≤ B →
      B ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card * (4 * (K ^ W.card) ^ 2) →
      C₁ ^ G.edgeFinset.card * B * (∏ S ∈ univ.erase Ŝ, blockRadius hY (radiiOn z) S ^ 2) *
          ((∏ e ∈ T.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e) *
            treeTail (distOn z) T (blockRadius hY (radiiOn z) Ŝ)) ≤
        A₀ * (radialExceptMax c Y *
          (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y T) := by
    intro T B hBone hB
    rw [hrad, htail]
    have hK0 : 0 ≤ ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e :=
      prod_nonneg fun e _ => keptWeight_nonneg' hc0 e
    have hX0 : 0 ≤ radialExceptMax c Y * (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) *
        compTail c Y T := mul_nonneg (mul_nonneg hP0 hK0) (compTail_nonneg c Y T)
    have hconst : C₁ ^ G.edgeFinset.card * B ≤ A₀ := by
      refine mul_le_mul (pow_le_pow_right₀ hC₁ hGcard) (hB.trans ?_) (by linarith)
        (by positivity)
      refine mul_le_mul (pow_le_pow_right₀ hB1 hk) ?_ (by positivity) (by positivity)
      have : (K ^ W.card) ^ 2 ≤ (K ^ k) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hK hk) 2
      linarith
    calc C₁ ^ G.edgeFinset.card * B * radialExceptMax c Y *
          ((∏ e ∈ T.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e) * compTail c Y T)
        = (C₁ ^ G.edgeFinset.card * B) * (radialExceptMax c Y *
            (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y T) := by
          unfold keptLift
          ring
      _ ≤ A₀ * (radialExceptMax c Y * (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) *
            compTail c Y T) := mul_le_mul_of_nonneg_right hconst hX0
  have hfin_family : ∀ (T : SimpleGraph W) (B : ℝ), 1 ≤ B →
      B ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card * (4 * (K ^ W.card) ^ 2) →
      C₁ ^ G.edgeFinset.card * B * (∏ S ∈ univ.erase Ŝ, blockRadius hY (radiiOn z) S ^ 2) *
        (∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
          (∏ e ∈ U.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e) *
            treeTail (distOn z) U (blockRadius hY (radiiOn z) Ŝ)) ≤
        A₀ * (radialExceptMax c Y * ∑ U ∈ relTrees Y,
          (∏ e ∈ U.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y U) := by
    intro T B hB1 hB
    rw [Finset.mul_sum]
    calc _ ≤ ∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
          A₀ * (radialExceptMax c Y *
            (∏ e ∈ U.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y U) :=
        sum_le_sum fun U _ => hfin U B hB1 hB
      _ = A₀ * (radialExceptMax c Y *
          ∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
            (∏ e ∈ U.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y U) := by
        simp_rw [← mul_assoc]
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro U _
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hA₀1)
        apply mul_le_mul_of_nonneg_left _ hP0
        apply sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro U _ _
        exact mul_nonneg (prod_nonneg fun e _ => keptWeight_nonneg' hc0 e)
          (compTail_nonneg c Y U)
  -- Carry the full indicator on both sides while proving the tail for
  -- every replacement tree. Only the final comparison removes it.
  have hfamily :
      ((∏ p ∈ E', |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
          (c p.1) (c p.2)|) *
        ∏ i ∈ W', |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) * s ≤
      (A₀ * (radialExceptMax c Y * ∑ T ∈ relTrees Y,
        (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c Y T)) * s := by
    apply mul_le_mul_of_nonneg_right _ hs0
    rw [hprod, ← prod_marksOn hW']
    by_cases hW'e : W' = ∅
    · -- no marks: Corollary 4.47
      have hm : marksOn Y W' = ∅ := by
        subst hW'e
        unfold marksOn
        simp
      rw [hm] at heul ⊢
      rw [Finset.prod_empty, mul_one]
      have hG' : Parity.IsRelEulerianConnected Y G :=
        ⟨hconn, CoreForest.isRelEulerianOff_empty_iff.1 heul⟩
      obtain ⟨T, hT, hbound⟩ := euler_component_family_bound hY hG' hr hd hc0 hc1 hA0 hC₁ hA ha1 hŜ' (by rwa [blockRadius_eq_blockRad hY c])
      apply hbound.trans
      have h1 : (1 : ℝ) ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card * (4 * (K ^ W.card) ^ 2) := by
        refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB1) ?_
        have : 1 ≤ (K ^ W.card) ^ 2 := one_le_pow₀ (one_le_pow₀ hK)
        linarith
      have := hfin_family T 1 le_rfl h1
      rwa [mul_one] at this
    · -- marks: Corollary 5.34
      have hWne : (marksOn Y W').Nonempty := by
        obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hW'e
        refine ⟨⟨a, hW' ha⟩, ?_⟩
        unfold marksOn
        exact Finset.mem_filter.2 ⟨mem_univ _, ha⟩
      set δ : W → ℝ := fun i => badDistZ p₀ β lam ε₀ V Z (c i) with hδdef
      have hδ : ∀ i, 0 < δ i := fun i =>
        hlam.trans_le (lam_le_badDistZ hlam hlamh hMp hVZ (hsupp' i).2 (hsupp' i).norm_le)
      have hrδ : ∀ i, radiiOn z i ≤ δ i := fun i =>
        norm_le_badDistZ hlam hlamh hMp hVZ (hsupp' i).2 (hsupp' i).norm_le
      have hAi0 : ∀ i : W, 0 ≤ |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
        fun _ => abs_nonneg _
      have hAi : ∀ i ∈ marksOn Y W', |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| ≤
          C₂ * (radiiOn z i / δ i) := fun i _ =>
        (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i) (hsupp' i)).1
      have hv : ∀ i j : W, A s(i, j) ≠ 0 → interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) ≠ 0 := by
        intro i j h
        refine interactionGoodZ_ne_zero_of_oddBond (M := M) _ _ fun h0 => h ?_
        show |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c i) (c j)| = 0
        rw [h0, abs_zero]
      have hKE : ∀ i j, G.Adj i j → A s(i, j) ≠ 0 → δ j ≤ K * δ i := by
        intro i j _ hAij
        have := badDistZ_le_six_mul hχ hlam hlamh hMp hVZ (hsupp' i).2 (hsupp' i).norm_le (hv i j hAij)
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hδ i).le)
      have hKS : ∀ i j, blockOf hY i = blockOf hY j → δ j ≤ K * δ i := by
        intro i j hij
        set S := blockOf hY i
        have hiS : (i : ℕ) ∈ (S : Finset ℕ) := mem_blockOf hY i
        have hjS : (j : ℕ) ∈ (S : Finset ℕ) := hij ▸ mem_blockOf hY j
        have hSW : (S : Finset ℕ) ⊆ W := subset_biUnion_of_mem id S.2
        have h1 := badDistZ_le_of_connOn hlam hlamh hMp hVZ
          (fun a ha => (hc a (hSW ha)).1) (hS S S.2) hiS hjS
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hδ i).le)
        refine (pow_le_pow_right₀ (by linarith) ((Finset.card_le_card hSW).trans hk)).trans ?_
        exact le_max_right _ _
      have hsupp : ∀ i j, G.Adj i j → A s(i, j) ≠ 0 → distOn z s(i, j) ≤ δ i + δ j := by
        intro i j _ hAij
        exact dipoleDist_le_of_interactionGoodZ_ne_zero hχ hlam hlamh hMp hVZ (hsupp' i) (hsupp' j)
          (hv i j hAij)
      obtain ⟨T, hT, hbound⟩ := marked_component_family_bound hY ⟨heul, hconn⟩ hWne hr hd hc0 hc1
        (A := A) (Ainf := fun i : W => |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) (δ := δ)
        hC₁ hC₂ hK hA0 hA ha1 hAi0 hAi hδ hrδ hKE hKS hsupp hŜ'
      apply hbound.trans
      have h1 : (1 : ℝ) ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card * (4 * (K ^ W.card) ^ 2) := by
        refine one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB1) ?_
        have : 1 ≤ (K ^ W.card) ^ 2 := one_le_pow₀ (one_le_pow₀ hK)
        linarith
      exact hfin_family T _ h1 le_rfl
  exact hfamily.trans (mul_le_of_le_one_right
    (mul_nonneg (zero_le_one.trans hA₀1) (mul_nonneg hP0
      (sum_nonneg fun T _ => mul_nonneg
        (prod_nonneg fun e _ => keptWeight_nonneg' hc0 e) (compTail_nonneg c Y T)))) hs1)

/-- Full component separation is kept through the replacement-tree tail proof,
then only the indicators already present in each replacement tree remain. -/
theorem component_family_bound_Z (hχ : IsMollifier χ) (p₀ : ℕ) (β M : ℝ) (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ Y : Finset (Finset ℕ), IsSubpartition Y → (Y.biUnion id).card ≤ k →
      ∀ E' : Finset (ℕ × ℕ), E' ⊆ interPairs Y → IsRelConnected Y (pairGraph (Y.biUnion id) E') →
      ∀ W' : Finset ℕ, W' ⊆ Y.biUnion id →
      IsRelEulerianOff Y (marksOn Y W') (pairGraph (Y.biUnion id) E') →
      ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ Y.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) ∧
        0 < ‖(c i).1 - (c i).2‖) →
      (∀ S ∈ Y, ConnOn S (linkedPairs M lam c S)) →
      ((∏ p ∈ E', |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
          ∏ i ∈ W', |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) * componentSeparation M lam Y c ≤
        A * (radialExceptMax c Y *
          ∑ T ∈ relTrees Y,
            (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ (truncationScale p₀ β lam) c e) *
              compTail c Y T) := by
  obtain ⟨A, hA, hbound⟩ := component_family_bound_Z_of_indicator hχ p₀ β M hM3 k
  refine ⟨A, hA, ?_⟩
  intro N lam ε₀ V Z hlam hlamh hMp hVZ Y hY hk E' hE' hconn W' hW' heul c hc hS
  exact hbound lam ε₀ V Z hlam hlamh hMp hVZ Y hY hk E' hE' hconn W' hW' heul c hc hS
    (componentSeparation M lam Y c) (componentSeparation_nonneg M lam Y c)
    (componentSeparation_le_one M lam Y c)

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
