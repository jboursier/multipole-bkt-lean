/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Component

/-!
# The bad-distance gain on a marked replacement-tree family

The paper: (5.106), using (5.89) of Corollary 5.34.

`marked_component_gain` applies `squares_of_bounds_sum` to the
peeled skeleton. At a dipole of maximal radius, the largest block's
square becomes `r_i₀² / δ_i₀²`. The peeled factors are bounded by one.
The retained factor remains a sum over `longAgreeingTrees`.

`component_gain_Z` instantiates the estimate for frozen bad points and
enlarges the replacement family to all relative trees. Full component
separation is carried through that estimate and removed afterward.
Every replacement tree retains its own separation and cutoff indicators.
The prefactor depends on `χ`, `p₀`, `β`, `M` and `k`, before `ε₀` is chosen.
-/

@[expose] public section

open Finset SimpleGraph
open scoped NNReal

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Peeling CoreForest Quadratic Parity Hierarchical Multipole BoundedUpper

/-! ### The abstract component -/

section Marked

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)

open scoped Classical in
/-- The paper quadratic estimate on the complete replacement family,
with `i₀` of largest radius and the factor `r_i₀² / δ_i₀²` retained.
The paper: (5.89), (5.106). -/
theorem marked_component_gain {G : SimpleGraph (Y.biUnion id)} {W : Finset (Y.biUnion id)}
    (hG : IsRelEulerianOffConnected Y W G) (hW : W.Nonempty)
    {r : Y.biUnion id → ℝ} (hr : ∀ v, 0 ≤ r v) {d c : Sym2 (Y.biUnion id) → ℝ}
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {A : Sym2 (Y.biUnion id) → ℝ} {Ainf δ : Y.biUnion id → ℝ} {C₁ C₂ K : ℝ}
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K) (hA0 : ∀ e, 0 ≤ A e)
    (hA : ∀ e ∈ G.edgeSet, A e ≤ C₁ * absWeight r d c e)
    (ha1 : ∀ e ∈ G.edgeSet, absWeight r d c e ≤ 1)
    (hAi0 : ∀ i, 0 ≤ Ainf i) (hAi : ∀ i ∈ W, Ainf i ≤ C₂ * (r i / δ i))
    (hδ : ∀ i, 0 < δ i) (hrδ : ∀ i, r i ≤ δ i)
    (hKE : ∀ i j, G.Adj i j → A s(i, j) ≠ 0 → δ j ≤ K * δ i)
    (hKS : ∀ i j, blockOf hY i = blockOf hY j → δ j ≤ K * δ i)
    {Ŝ : Y} (hŜ : ∀ S, blockRadius hY r S ≤ blockRadius hY r Ŝ) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧ ∃ i₀ : Y.biUnion id,
      r i₀ = blockRadius hY r Ŝ ∧
      (∏ e ∈ G.edgeFinset, A e) * ∏ i ∈ W, Ainf i ≤
        C₁ ^ G.edgeFinset.card * (C₁ ^ 3 * C₂ * K ^ 6) ^ (Y.biUnion id).card *
          (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
          (∑ U ∈ longAgreeingTrees Y r d T, ∏ e ∈ U.edgeFinset, keptWeight d c e) * (r i₀ ^ 2 / δ i₀ ^ 2) := by
  set n := (Y.biUnion id).card
  set b := blockOf hY
  have hcross : G ≤ crossBlockGraph b := interEdges_eq hY ▸ hG.1.1
  obtain ⟨E, hE⟩ := exists_isMinimalSkeleton (b := b) (E := G)
  have hEE := isMinimalSkeleton_self_of_isMinimalSkeleton hcross hE
  have hKs := isMinimalSkeleton_self_iff.1 hEE
  have hcrossE : E ≤ crossBlockGraph b := hE.le.trans hcross
  obtain ⟨v₁, e₀, Ts, Fs, hP⟩ := exists_isPlusPeeling hcrossE hKs r d
  set T := plusTree b E Ts
  have hT : IsRelTree Y T := isRelTree_plusTree_of_peeled hY hG hE hP
  -- a vertex of maximal radius
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (univ : Finset (Y.biUnion id)) r
    (by
      obtain ⟨i, -⟩ := hW
      exact ⟨i, mem_univ i⟩)
  have hRi₀ : blockRadius hY r Ŝ = r i₀ := by
    refine le_antisymm ?_ ((le_blockRadius r i₀).trans (hŜ _))
    unfold blockRadius
    exact Finset.sup'_le _ _ fun i _ => hi₀ i (mem_univ i)
  refine ⟨T, hT, i₀, hRi₀.symm, ?_⟩
  have hmain := squares_of_bounds_sum hY hG hW hE hP hr hd hc (A := A) (Ainf := Ainf) (δ := δ) hC₁ hC₂
    hK hA0 (fun e he => hA e (edgeSet_mono hE.le he)) hAi0 hAi hδ hrδ
    (fun i j hadj hAij => hKE i j (hE.le hadj) hAij) hKS i₀
  rw [← Finset.mul_prod_erase univ (fun S => blockRadius hY r S ^ 2) (mem_univ Ŝ), hRi₀] at hmain
  -- nonnegativity
  have hP0 : 0 ≤ ∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2 := prod_nonneg fun _ _ => sq_nonneg _
  have hKp0 : 0 ≤ ∑ U ∈ longAgreeingTrees Y r d T, ∏ e ∈ U.edgeFinset, keptWeight d c e :=
    sum_nonneg fun U _ => prod_nonneg fun e _ => keptWeight_nonneg' hc e
  have hF1 : ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d c (r (v₁ l)) (e₀ l) e ≤ 1 :=
    prod_le_one₀ (fun l _ => prod_nonneg fun e _ => peelWeight_nonneg' hc _ _ _) fun l _ =>
      prod_le_one₀ (fun e _ => peelWeight_nonneg' hc _ _ _) fun e _ =>
        peelWeight_le_one hr hd hc hc1 (hr _) _ _
  have hAinf0 : 0 ≤ ∏ i ∈ W, Ainf i := prod_nonneg fun i _ => hAi0 i
  have hAE0 : 0 ≤ ∏ e ∈ E.edgeFinset, A e := prod_nonneg fun e _ => hA0 e
  have hC0 : 0 ≤ C₁ ^ 3 * C₂ * K ^ 6 := by positivity
  -- `∏_G A ≤ C₁^{|G|} ∏_E A`
  have hGE : ∏ e ∈ G.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card * ∏ e ∈ E.edgeFinset, A e := by
    have hsub : E.edgeFinset ⊆ G.edgeFinset := edgeFinset_mono hE.le
    rw [← Finset.prod_sdiff hsub]
    have h1 : ∏ e ∈ G.edgeFinset \ E.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card := by
      calc ∏ e ∈ G.edgeFinset \ E.edgeFinset, A e ≤ ∏ _e ∈ G.edgeFinset \ E.edgeFinset, C₁ :=
            Finset.prod_le_prod₀ (fun e _ => hA0 e) fun e he => by
              have he' := mem_edgeFinset.1 (Finset.mem_sdiff.1 he).1
              calc A e ≤ C₁ * absWeight r d c e := hA e he'
                _ ≤ C₁ * 1 := mul_le_mul_of_nonneg_left (ha1 e he') (by linarith)
                _ = C₁ := mul_one C₁
        _ = C₁ ^ (G.edgeFinset \ E.edgeFinset).card := Finset.prod_const _
        _ ≤ C₁ ^ G.edgeFinset.card := pow_le_pow_right₀ hC₁ (Finset.card_le_card sdiff_subset)
    exact mul_le_mul_of_nonneg_right h1 hAE0
  set P := ∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2
  set Kp := ∑ U ∈ longAgreeingTrees Y r d T, ∏ e ∈ U.edgeFinset, keptWeight d c e
  set Fp := ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r d c (r (v₁ l)) (e₀ l) e
  have hq0 : 0 ≤ r i₀ ^ 2 / δ i₀ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmain' : (∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ W, Ainf i ≤
      (C₁ ^ 3 * C₂ * K ^ 6) ^ n * P * Kp * (r i₀ ^ 2 / δ i₀ ^ 2) := by
    refine hmain.trans ?_
    have e1 : (C₁ ^ 3 * C₂ * K ^ 6) ^ n * (r i₀ ^ 2 * P) * Kp * Fp / δ i₀ ^ 2 =
        (C₁ ^ 3 * C₂ * K ^ 6) ^ n * P * Kp * Fp * (r i₀ ^ 2 / δ i₀ ^ 2) := by ring
    rw [e1]
    have hX0 : 0 ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ n * P * Kp :=
      mul_nonneg (mul_nonneg (pow_nonneg hC0 _) hP0) hKp0
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hX0 hF1) hq0
  calc (∏ e ∈ G.edgeFinset, A e) * ∏ i ∈ W, Ainf i
      ≤ (C₁ ^ G.edgeFinset.card * ∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ W, Ainf i :=
        mul_le_mul_of_nonneg_right hGE hAinf0
    _ = C₁ ^ G.edgeFinset.card * ((∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ W, Ainf i) := by ring
    _ ≤ C₁ ^ G.edgeFinset.card * ((C₁ ^ 3 * C₂ * K ^ 6) ^ n * P * Kp * (r i₀ ^ 2 / δ i₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left hmain' (pow_nonneg (zero_le_one.trans hC₁) _)
    _ = _ := by ring

end Marked

/-! ### The model with frozen bad points -/

section Component

variable {χ : ℂ → ℝ}

open scoped Classical in
/-- The frozen-model marked family bound with its bad-distance gain.
Full component separation is retained through the quadratic family estimate.
The coefficient is uniform in `ε₀`.
The paper: (5.106). -/
theorem component_gain_Z (hχ : IsMollifier χ) (p₀ : ℕ) (β M : ℝ) (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ Y : Finset (Finset ℕ), IsSubpartition Y → (Y.biUnion id).card ≤ k →
      ∀ E' : Finset (ℕ × ℕ), E' ⊆ interPairs Y → IsRelConnected Y (pairGraph (Y.biUnion id) E') →
      ∀ W' : Finset ℕ, W' ⊆ Y.biUnion id → W'.Nonempty →
      IsRelEulerianOff Y (marksOn Y W') (pairGraph (Y.biUnion id) E') →
      ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ Y.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) ∧
        0 < ‖(c i).1 - (c i).2‖) →
      (∀ S ∈ Y, ConnOn S (linkedPairs M lam c S)) →
      ∃ i₀ ∈ Y.biUnion id,
        ((∏ p ∈ E', |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
          ∏ i ∈ W', |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
            BoundedUpper.RouteRaw.componentSeparation M lam Y c ≤
        A * (‖(c i₀).1 - (c i₀).2‖ ^ 2 / badDistZ p₀ β lam ε₀ V Z (c i₀) ^ 2) *
          (radialExceptMax c Y *
            ∑ T ∈ relTrees Y, ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ (truncationScale p₀ β lam) c e) := by
  obtain ⟨C₁, hC₁, hab⟩ := bornesabZ_Z hχ β
  obtain ⟨C₂, hC₂, hinf⟩ := bornesabinfty_Z hχ p₀ β
  set K : ℝ := max 6 ((M + 2) ^ k) with hKdef
  have hK : 1 ≤ K := le_max_of_le_left (by norm_num)
  have hM1 : 1 ≤ M := by linarith
  have hB1 : 1 ≤ C₁ ^ 3 * C₂ * K ^ 6 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC₁) hC₂)
      (one_le_pow₀ hK)
  set A₀ : ℝ := C₁ ^ (k * k) * (C₁ ^ 3 * C₂ * K ^ 6) ^ k with hA₀
  have hA₀1 : 1 ≤ A₀ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC₁) (one_le_pow₀ hB1)
  refine ⟨A₀, hA₀1, ?_⟩
  intro N lam ε₀ V Z hlam hlamh hMp hVZ Y hY hk E' hE' hconn W' hW' hW'ne heul c hc hS
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
  have hcardW : Fintype.card W ≤ k := by rw [Fintype.card_coe]; exact hk
  have hGcard : G.edgeFinset.card ≤ k * k := card_edgeFinset_le_sq G hcardW
  have hP0 : 0 ≤ radialExceptMax c Y := radialExceptMax_nonneg c Y
  -- the marks
  rw [hprod, ← prod_marksOn hW']
  have hWne : (marksOn Y W').Nonempty := by
    obtain ⟨a, ha⟩ := hW'ne
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
  obtain ⟨T, hT, i₀, -, hbound⟩ := marked_component_gain hY ⟨heul, hconn⟩ hWne hr hd hc0 hc1
    (A := A) (Ainf := fun i : W => |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) (δ := δ)
    hC₁ hC₂ hK hA0 hA ha1 hAi0 hAi hδ hrδ hKE hKS hŜ'
  refine ⟨i₀, i₀.2, ?_⟩
  rw [hrad] at hbound
  have hq0 : 0 ≤ radiiOn z i₀ ^ 2 / δ i₀ ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hconst : C₁ ^ G.edgeFinset.card * (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card ≤ A₀ :=
    mul_le_mul (pow_le_pow_right₀ hC₁ hGcard) (pow_le_pow_right₀ hB1 hk) (by positivity)
      (by positivity)
  have hsum : (∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
      ∏ e ∈ U.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e) ≤
      ∑ U ∈ relTrees Y, ∏ e ∈ U.edgeFinset, keptLift M lam ε₀ R c e := by
    apply sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro U _ _
    exact prod_nonneg fun e _ => keptWeight_nonneg' hc0 e
  have hsum0 : 0 ≤ ∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
      ∏ e ∈ U.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e :=
    sum_nonneg fun U _ => prod_nonneg fun e _ => keptWeight_nonneg' hc0 e
  have hfinal := calc
    C₁ ^ G.edgeFinset.card * (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card * radialExceptMax c Y *
        (∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
          ∏ e ∈ U.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e) *
        (radiiOn z i₀ ^ 2 / δ i₀ ^ 2) = (C₁ ^ G.edgeFinset.card * (C₁ ^ 3 * C₂ * K ^ 6) ^ W.card) *
        ((radiiOn z i₀ ^ 2 / δ i₀ ^ 2) * (radialExceptMax c Y *
          ∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
            ∏ e ∈ U.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e)) := by ring
    _ ≤ A₀ * ((radiiOn z i₀ ^ 2 / δ i₀ ^ 2) * (radialExceptMax c Y *
          ∑ U ∈ longAgreeingTrees Y (radiiOn z) (distOn z) T,
            ∏ e ∈ U.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e)) :=
      mul_le_mul_of_nonneg_right hconst (mul_nonneg hq0 (mul_nonneg hP0 hsum0))
    _ ≤ A₀ * ((radiiOn z i₀ ^ 2 / δ i₀ ^ 2) * (radialExceptMax c Y *
        ∑ U ∈ relTrees Y, ∏ e ∈ U.edgeFinset, keptLift M lam ε₀ R c e)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hP0) hq0)
        (zero_le_one.trans hA₀1)
    _ = A₀ * (‖(c i₀).1 - (c i₀).2‖ ^ 2 /
        badDistZ p₀ β lam ε₀ V Z (c i₀) ^ 2) * (radialExceptMax c Y *
          ∑ U ∈ relTrees Y, ∏ e ∈ U.edgeFinset, keptLift M lam ε₀ R c e) := by
      dsimp [radiiOn, z, δ]
      ring

  have hle := hbound.trans hfinal
  exact (mul_le_mul_of_nonneg_right hle
    (BoundedUpper.RouteRaw.componentSeparation_nonneg M lam Y c)).trans
      (mul_le_of_le_one_right
        (mul_nonneg (mul_nonneg (zero_le_one.trans hA₀1) hq0)
          (mul_nonneg hP0 (hsum0.trans hsum)))
        (BoundedUpper.RouteRaw.componentSeparation_le_one M lam Y c))

end Component

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
