/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Pointwise
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Component
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Indicators

/-!
# Odd-component tree families before integration

The paper: Proposition 5.18. Extract the odd components and their even quotient tree,
multiply their tree-family bounds, and retain one maximum tail before
integrating. The pointwise estimate is also available.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open Finset SimpleGraph Peeling CoreForest Quadratic Parity Hierarchical Multipole SetPartition
open scoped Classical NNReal

variable {χ : ℂ → ℝ}

/-- The pointwise bound using the paper family estimates on every component. -/
theorem pointwise_separated_family_bound (hχ : IsMollifier χ) {β : ℝ} (hβ : 0 ≤ β) (p₀ : ℕ) (M L : ℝ)
    (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ k →
      ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset, ∀ V₁ ∈ (X.biUnion id).powerset,
      IsParityPair X E₁ V₁ →
      ∃ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), n ≤ k ∧ (∀ l, Xs l ⊆ X) ∧
        (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) ∧
        ∃ Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id),
          IsRelTree₀ (coarsen X (univ.image Xs)) Tb ∧
          ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, c i ∈ supportSet N p₀ β lam ε₀ ∧
              0 < ‖(c i).1 - (c i).2‖) →
            (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
                (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
              (|reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ c| *
                ∏ Y ∈ oddComponents X E₁, componentSeparation M lam Y c) ≤
            K₀ * ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
                (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l)),
              jIntegrand M lam ε₀ (truncationScale p₀ β lam) X Xs Ta Tb c *
                ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
  obtain ⟨A, hA1, hcomp⟩ := component_family_bound_Z hχ p₀ β M hM3 k
  obtain ⟨C₁, hC₁, hab⟩ := bornesabZ_Z hχ β
  obtain ⟨C₂, hC₂, hinf⟩ := bornesabinfty_Z hχ p₀ β
  obtain ⟨Cs, -, hstab⟩ := stableWeightZ_le hχ β hβ
  set Cs' : ℝ := max Cs 1 with hCs'
  have hCs'1 : 1 ≤ Cs' := le_max_right _ _
  set Ew : ℝ := Real.exp (16 * |L|) with hEw
  have hEw1 : 1 ≤ Ew := Real.one_le_exp (by positivity)
  have hbase : 1 ≤ Cs' ^ (k * k) * Ew ^ k :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCs'1) (one_le_pow₀ hEw1)
  set BW : ℝ := (Cs' ^ (k * k) * Ew ^ k) ^ k with hBW
  have hBW1 : 1 ≤ BW := one_le_pow₀ hbase
  set K₀ : ℝ := BW * A ^ k * C₂ ^ k * C₂ ^ k * (2 * C₁) ^ (k * k) with hK₀
  have h2C₁ : 1 ≤ 2 * C₁ := by linarith
  have hK₀1 : 1 ≤ K₀ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hBW1 (one_le_pow₀ hA1))
        (one_le_pow₀ hC₂)) (one_le_pow₀ hC₂)) (one_le_pow₀ h2C₁)
  refine ⟨K₀, by linarith, ?_⟩
  intro N lam ε₀ V Z hlam hlamh hMp hVZ X hX hk E hE E₁ hE₁ V₁ hV₁ hpar
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨hEX, hEconn⟩ := mem_relEdgeSets₀.1 hE
  have hE₁E : E₁ ⊆ E := Finset.mem_powerset.1 hE₁
  have hE₁X : E₁ ⊆ interPairs X := hE₁E.trans hEX
  have hV₁X : V₁ ⊆ X.biUnion id := Finset.mem_powerset.1 hV₁
  set R := truncationScale p₀ β lam with hR
  set odd := oddComponents X E₁ with hodd
  set eqv := odd.equivFin with heqv
  set Xs : Fin odd.card → Finset (Finset ℕ) := fun l => ((eqv.symm l : odd) : Finset (Finset ℕ))
    with hXs
  have hXsmem : ∀ l, Xs l ∈ odd := fun l => (eqv.symm l).2
  have himage : univ.image Xs = odd := by
    ext Y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨l, rfl⟩
      exact hXsmem l
    · intro hY
      refine ⟨eqv ⟨Y, hY⟩, ?_⟩
      simp only [Xs, Equiv.symm_apply_apply]
  have hXsX : ∀ l, Xs l ⊆ X := fun l =>
    subset_of_mem_relComponents (oddComponents_subset _ (hXsmem l))
  have hXsinj : ∀ l l', Xs l = Xs l' → l = l' := fun l l' h =>
    eqv.symm.injective (Subtype.ext h)
  have hXsdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l') := fun l l' h =>
    disjoint_of_mem_relComponents hX (oddComponents_subset _ (hXsmem l))
      (oddComponents_subset _ (hXsmem l')) fun h' => h (hXsinj l l' h')
  obtain ⟨Tb, hTb, hTbE⟩ := exists_isRelTree₀_even hX hE hE₁E himage
  have hXk : X.card ≤ k := (Finset.card_le_card_biUnion hX.2 hX.1).trans hk
  have hoddk : odd.card ≤ k := by
    refine (Finset.card_le_card_biUnion (pairwiseDisjoint_oddComponents hX E₁)
      (fun Y hY => nonempty_of_mem_relComponents (oddComponents_subset _ hY))).trans ?_
    refine (Finset.card_le_card ?_).trans hXk
    intro B hB
    obtain ⟨Y, hY, hBY⟩ := Finset.mem_biUnion.1 hB
    exact subset_of_mem_relComponents (oddComponents_subset _ hY) hBY
  refine ⟨odd.card, Xs, hoddk, hXsX, hXsdisj, Tb, hTb, ?_⟩
  intro c hc
  -- the right side is nonnegative
  have hRHS0 : 0 ≤ K₀ * ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
      (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l)),
        jIntegrand M lam ε₀ R X Xs Ta Tb c *
          ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
    refine mul_nonneg (by linarith) (sum_nonneg fun Ta _ => mul_nonneg
      (jIntegrand_nonneg M lam ε₀ R X Xs Ta Tb c) (prod_nonneg fun S _ => ?_))
    split_ifs <;> norm_num
  -- the degenerate cases
  by_cases hgood : ∀ i ∈ X.biUnion id, IsGoodZ p₀ β lam M ε₀ V Z (c i)
  swap
  · push Not at hgood
    obtain ⟨i, hi, hng⟩ := hgood
    obtain ⟨B, hB, hiB⟩ := mem_biUnion_id.1 hi
    have h0 : blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c = 0 := by
      unfold blockWeightOf
      rw [Finset.prod_eq_zero hiB (by unfold dipoleWeightZ; rw [ite_eq_right hng, mul_zero]),
        mul_zero]
    rw [Finset.prod_eq_zero hB h0, zero_mul]
    exact hRHS0
  by_cases hconn : ∀ S ∈ X, ConnOn S (linkedPairs M lam c S)
  swap
  · push Not at hconn
    obtain ⟨S, hS, hnc⟩ := hconn
    have h0 : blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam S c = 0 := by
      unfold blockWeightOf
      rw [ite_eq_right hnc, zero_mul, zero_mul]
    rw [Finset.prod_eq_zero hS h0, zero_mul]
    exact hRHS0
  -- the main case: on the support
  have hsupp : ∀ i ∈ X.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) := fun i hi =>
    ⟨(hc i hi).1, hgood i hi⟩
  -- the block weights
  have hbw : ∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c ≤ BW := by
    refine prod_le_pow_of_le X hbase hXk (fun B _ => ?_) (fun B hB => ?_)
    · unfold blockWeightOf
      refine mul_nonneg (mul_nonneg ?_ (prod_nonneg fun p _ => stableWeight_nonneg _ _ _ _))
        (prod_nonneg fun i _ => dipoleWeightZ_nonneg _)
      split_ifs <;> norm_num
    · have hBX : B ⊆ X.biUnion id := subset_biUnion_of_mem id hB
      have hBk : B.card ≤ k := (Finset.card_le_card hBX).trans hk
      unfold blockWeightOf
      rw [ite_eq_left (hconn B hB), one_mul]
      refine mul_le_mul ?_ ?_ (prod_nonneg fun i _ => dipoleWeightZ_nonneg _)
        (pow_nonneg (zero_le_one.trans hCs'1) _)
      · refine prod_le_pow_of_le _ hCs'1 ((card_pairsOn_le B).trans (Nat.mul_le_mul hBk hBk))
          (fun p _ => stableWeight_nonneg _ _ _ _) (fun p hp => ?_)
        obtain ⟨h1, h2, -⟩ := mem_pairsOn.1 hp
        exact (hstab p₀ lam M ε₀ V Z hlam hlamh hMp hVZ _ _ (hsupp _ (hBX h1))
          (hsupp _ (hBX h2))).trans (le_max_left _ _)
      · exact prod_le_pow_of_le _ hEw1 hBk (fun i _ => dipoleWeightZ_nonneg _) fun i hi =>
          dipoleWeightZ_le hlam hlamh hMp hVZ L (hsupp i (hBX hi)).norm_le
  -- the odd components
  have hcomp_l : ∀ l,
      ((∏ p ∈ E₁ ∩ interPairs (Xs l),
          |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
        ∏ i ∈ V₁ ∩ (Xs l).biUnion id, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) * componentSeparation M lam (Xs l) c ≤
      A * (radialExceptMax c (Xs l) * ∑ T ∈ relTrees (Xs l),
        (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c (Xs l) T) := by
    intro l
    have hYc : Xs l ∈ relComponents X E₁ := oddComponents_subset _ (hXsmem l)
    have hYs : IsSubpartition (Xs l) := isSubpartition_mono hX (hXsX l)
    have hYV : (Xs l).biUnion id ⊆ X.biUnion id :=
      Finset.biUnion_subset_biUnion_of_subset_left _ (hXsX l)
    have hmk : marksOn (Xs l) (V₁ ∩ (Xs l).biUnion id) = marksOn (Xs l) V₁ := by
      unfold marksOn
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
      exact ⟨fun h => h.1, fun h => ⟨h, i.2⟩⟩
    have heul := isRelEulerianOff_pairGraph hX hE₁X hpar hYc
    rw [← hmk] at heul
    exact hcomp lam ε₀ V Z hlam hlamh hMp hVZ (Xs l) hYs ((Finset.card_le_card hYV).trans hk)
      _ Finset.inter_subset_right (isRelConnected_pairGraph hX hE₁X (hXsmem l)) _
      Finset.inter_subset_right heul c (fun i hi => ⟨hsupp i (hYV hi), (hc i (hYV hi)).2⟩)
      (fun S hS => hconn S (hXsX l hS))
  let 𝒯 := (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
    (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l))
  let oddMaj := fun Ta : ∀ l, SimpleGraph ((Xs l).biUnion id) =>
    (∏ l, radialExceptMax c (Xs l)) *
      (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) * jTail c X Xs Ta
  have oddMaj0 : ∀ Ta, 0 ≤ oddMaj Ta := fun Ta =>
    mul_nonneg (mul_nonneg (prod_nonneg fun l _ => radialExceptMax_nonneg c _)
      (prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e))
      (sq_nonneg _)
  have hpi : Fintype.piFinset (fun l => relTrees (Xs l)) = 𝒯 := by
    ext Ta
    simp only [Fintype.mem_piFinset, mem_relTrees, 𝒯, mem_filter, mem_univ, true_and]
  -- reindexing the odd components
  have hreidx : ∀ f : Finset (Finset ℕ) → ℝ, ∏ Y ∈ odd, f Y = ∏ l, f (Xs l) := by
    intro f
    rw [← Finset.prod_coe_sort odd f]
    exact (Equiv.prod_comp eqv.symm (fun Y : odd => f Y)).symm
  set oddP : ℕ × ℕ → ℝ := fun p =>
    |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)| with hoddP
  set sh : ℕ → ℝ := fun i => |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| with hsh
  set Vodd := odd.biUnion fun Y => Y.biUnion id with hVodd
  have hoddprod : ∏ p ∈ E₁, oddP p = ∏ l, ∏ p ∈ E₁ ∩ interPairs (Xs l), oddP p := by
    rw [prod_eq_prod_oddComponents hX hE₁X oddP]
    exact hreidx fun Y => ∏ p ∈ E₁ ∩ interPairs Y, oddP p
  have hshprod : ∏ i ∈ V₁, sh i =
      (∏ l, ∏ i ∈ V₁ ∩ (Xs l).biUnion id, sh i) * ∏ i ∈ V₁ \ Vodd, sh i := by
    rw [← Finset.prod_inter_mul_prod_sdiff V₁ Vodd sh]
    congr 1
    have hV : V₁ ∩ Vodd = odd.biUnion fun Y => V₁ ∩ Y.biUnion id := by
      ext i
      simp only [hVodd, Finset.mem_inter, Finset.mem_biUnion]
      constructor
      · rintro ⟨h1, Y, hY, h2⟩
        exact ⟨Y, hY, h1, h2⟩
      · rintro ⟨Y, hY, h1, h2⟩
        exact ⟨h1, Y, hY, h2⟩
    rw [hV, Finset.prod_biUnion]
    · exact hreidx fun Y => ∏ i ∈ V₁ ∩ Y.biUnion id, sh i
    · intro Y hY Y' hY' hne
      have hd := disjoint_biUnion_of_disjoint hX
        (subset_of_mem_relComponents (oddComponents_subset _ hY))
        (subset_of_mem_relComponents (oddComponents_subset _ hY'))
        (disjoint_of_mem_relComponents hX (oddComponents_subset _ hY)
          (oddComponents_subset _ hY') hne)
      exact hd.mono Finset.inter_subset_right Finset.inter_subset_right
  -- the radii
  have hXne : (X.biUnion id).Nonempty := hEconn.1
  have hposX : 0 < blockRad c (X.biUnion id) := by
    obtain ⟨i, hi⟩ := hXne
    exact (hc i hi).2.trans_le (le_blockRad c hi)
  -- nonnegativity
  have hoddP0 : ∀ p, 0 ≤ oddP p := fun p => abs_nonneg _
  have hsh0 : ∀ i, 0 ≤ sh i := fun i => abs_nonneg _
  have hrad0 : 0 ≤ ∏ l, radialExceptMax c (Xs l) := prod_nonneg fun l _ => radialExceptMax_nonneg c _
  have hTb0 : 0 ≤ ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e :=
    prod_nonneg fun e _ => absEvenLift_nonneg M lam ε₀ R c e
  -- the marks outside the odd components
  have hshout : ∏ i ∈ V₁ \ Vodd, sh i ≤ C₂ ^ k := by
    refine prod_le_pow_of_le _ hC₂ ((Finset.card_le_card (Finset.sdiff_subset.trans hV₁X)).trans
      hk) (fun i _ => hsh0 i) (fun i hi => ?_)
    have hiX := hV₁X (Finset.sdiff_subset hi)
    have h := (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i) (hsupp i hiX)).1
    have hrδ := norm_le_badDistZ hlam hlamh hMp hVZ (hsupp i hiX).2 (hsupp i hiX).norm_le
    have hδ := hlam.trans_le (lam_le_badDistZ hlam hlamh hMp hVZ (hsupp i hiX).2
      (hsupp i hiX).norm_le)
    calc sh i ≤ C₂ * (‖(c i).1 - (c i).2‖ / badDistZ p₀ β lam ε₀ V Z (c i)) := h
      _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left (div_le_one_of_le₀ hrδ hδ.le) (by linarith)
      _ = C₂ := mul_one C₂
  -- Multiply the family sums, then attach the single maximum tail.
  have hOM : ((∏ p ∈ E₁, oddP p) * ∏ i ∈ V₁, sh i) *
      (∏ Y ∈ odd, componentSeparation M lam Y c) ≤
      A ^ k * (∑ Ta ∈ 𝒯, oddMaj Ta) * C₂ ^ k := by
    rw [hoddprod, hshprod, hreidx]
    have hsplit : (∏ l, ∏ p ∈ E₁ ∩ interPairs (Xs l), oddP p) *
        ((∏ l, ∏ i ∈ V₁ ∩ (Xs l).biUnion id, sh i) * ∏ i ∈ V₁ \ Vodd, sh i) =
        (∏ l, ((∏ p ∈ E₁ ∩ interPairs (Xs l), oddP p) *
          ∏ i ∈ V₁ ∩ (Xs l).biUnion id, sh i)) * ∏ i ∈ V₁ \ Vodd, sh i := by
      rw [Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    rw [mul_right_comm _ _ (∏ l, componentSeparation M lam (Xs l) c), ← Finset.prod_mul_distrib]
    have hl := Finset.prod_le_prod₀
      (fun l (_ : l ∈ (univ : Finset (Fin odd.card))) =>
        mul_nonneg (mul_nonneg (prod_nonneg fun p _ => hoddP0 p)
          (prod_nonneg fun i _ => hsh0 i)) (componentSeparation_nonneg M lam _ c))
      (fun l _ => hcomp_l l)
    have hsum : (∏ l, radialExceptMax c (Xs l) * ∑ T ∈ relTrees (Xs l),
        (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c (Xs l) T) ≤
        ∑ Ta ∈ 𝒯, oddMaj Ta := by
      simp_rw [Finset.mul_sum]
      rw [Finset.prod_univ_sum, hpi]
      apply sum_le_sum
      intro Ta _
      simp_rw [Finset.prod_mul_distrib]
      change (∏ l, radialExceptMax c (Xs l)) *
        ((∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) *
          ∏ l, compTail c (Xs l) (Ta l)) ≤ _
      have hkept0 : 0 ≤ ∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e :=
        prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e
      dsimp only [oddMaj]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (prod_compTail_le_jTail c X Xs hXsX Ta hposX) hkept0) hrad0
    have hP1 : ∏ l, (((∏ p ∈ E₁ ∩ interPairs (Xs l), oddP p) *
        ∏ i ∈ V₁ ∩ (Xs l).biUnion id, sh i) * componentSeparation M lam (Xs l) c) ≤ A ^ k * ∑ Ta ∈ 𝒯, oddMaj Ta := by
      apply hl.trans
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (pow_le_pow_right₀ hA1 hoddk) hsum
        (prod_nonneg fun l _ => mul_nonneg (radialExceptMax_nonneg c _)
          (sum_nonneg fun T _ => mul_nonneg
            (prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e) (compTail_nonneg c _ _)))
        (pow_nonneg (zero_le_one.trans hA1) _)
    exact mul_le_mul hP1 hshout (prod_nonneg fun i _ => hsh0 i)
      (mul_nonneg (pow_nonneg (zero_le_one.trans hA1) _) (sum_nonneg fun Ta _ => oddMaj0 Ta))
  -- the even bonds
  have hev : ∏ p ∈ E \ E₁,
      |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)| ≤
      (2 * C₁) ^ (k * k) * ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e := by
    have hEk : (E \ E₁).card ≤ k * k :=
      (Finset.card_le_card (Finset.sdiff_subset.trans (hEX.trans interPairs_subset_pairsOn))).trans
        ((card_pairsOn_le _).trans (Nat.mul_le_mul hk hk))
    have hpX : ∀ p ∈ E \ E₁, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp =>
      ⟨(mem_pairsOn.1 (interPairs_subset_pairsOn (hEX (Finset.sdiff_subset hp)))).1,
        (mem_pairsOn.1 (interPairs_subset_pairsOn (hEX (Finset.sdiff_subset hp)))).2.1⟩
    have h1 : ∏ p ∈ E \ E₁,
        |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)| ≤
        ∏ p ∈ E \ E₁, (C₁ * absEvenWeight M lam ε₀ R (c p.1) (c p.2)) :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p hp =>
        (hab p₀ lam M ε₀ V Z hlam hlamh hMp hVZ _ _ (hsupp _ (hpX p hp).1)
          (hsupp _ (hpX p hp).2)).2
    rw [Finset.prod_mul_distrib, Finset.prod_const] at h1
    have h2 : ∏ p ∈ E \ E₁, absEvenWeight M lam ε₀ R (c p.1) (c p.2) ≤
        2 ^ (E \ E₁).card * ∏ p ∈ graphPairs Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2) := by
      rw [← Finset.prod_sdiff hTbE]
      exact mul_le_mul_of_nonneg_right (prod_le_pow_of_le _ (by norm_num)
        (Finset.card_le_card Finset.sdiff_subset) (fun p _ => absEvenWeight_nonneg _ _ _ _ _ _)
        fun p _ => absEvenWeight_le_two' hM1 hlam _ _)
        (prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _)
    have h3 : ∏ p ∈ graphPairs Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2) =
        ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e :=
      prod_graphPairs Tb (fun i j => absEvenWeight M lam ε₀ R (c i) (c j))
        fun i j => absEvenWeight_comm M lam ε₀ R _ _
    rw [h3] at h2
    calc ∏ p ∈ E \ E₁,
          |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|
        ≤ C₁ ^ (E \ E₁).card * (2 ^ (E \ E₁).card *
            ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _))
      _ = (2 * C₁) ^ (E \ E₁).card * ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e := by
          rw [mul_pow]
          ring
      _ ≤ (2 * C₁) ^ (k * k) * ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h2C₁ hEk) hTb0
  -- the cosh factors
  have hch : ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) ≤ C₂ ^ k :=
    prod_le_pow_of_le _ hC₂ ((Finset.card_le_card Finset.sdiff_subset).trans hk)
      (fun i _ => (Real.cosh_pos _).le) fun i hi =>
        (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i) (hsupp i (Finset.sdiff_subset hi))).2
  -- assembling
  have hind : ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) = 1 :=
    Finset.prod_eq_one fun S hS => ite_eq_left (hconn S hS)
  rw [hind]
  simp only [mul_one]
  rw [abs_reducedTerm_eq]
  have hOM0 : 0 ≤ (∏ p ∈ E₁, oddP p) * ∏ i ∈ V₁, sh i :=
    mul_nonneg (prod_nonneg fun p _ => hoddP0 p) (prod_nonneg fun i _ => hsh0 i)
  have hOMsep0 : 0 ≤ ((∏ p ∈ E₁, oddP p) * ∏ i ∈ V₁, sh i) *
      ∏ Y ∈ odd, componentSeparation M lam Y c := mul_nonneg hOM0 (prod_nonneg fun Y _ => componentSeparation_nonneg M lam Y c)
  have hev0 : 0 ≤ ∏ p ∈ E \ E₁,
      |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)| :=
    prod_nonneg fun p _ => abs_nonneg _
  have hch0 : 0 ≤ ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) :=
    prod_nonneg fun i _ => (Real.cosh_pos _).le
  have hbw0 : 0 ≤ ∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c :=
    prod_nonneg fun B _ => blockWeightOf_nonneg M lam (fun _ => dipoleWeightZ_nonneg _) B c
  have hR1 : 0 ≤ A ^ k * (∑ Ta ∈ 𝒯, oddMaj Ta) * C₂ ^ k := by
    exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hA1) _)
      (sum_nonneg fun Ta _ => oddMaj0 Ta)) (pow_nonneg (zero_le_one.trans hC₂) _)
  have hstep := mul_le_mul hbw
    (mul_le_mul (mul_le_mul hOM hev hev0 hR1) hch hch0
      (mul_nonneg hR1 (mul_nonneg (pow_nonneg (by linarith) _) hTb0)))
    (mul_nonneg (mul_nonneg hOMsep0 hev0) hch0) (by linarith : 0 ≤ BW)
  calc _ = (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
        ((((∏ p ∈ E₁, oddP p) * ∏ i ∈ V₁, sh i) * ∏ Y ∈ odd, componentSeparation M lam Y c) *
          (∏ p ∈ E \ E₁, |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
            (c p.1) (c p.2)|) *
          ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))) := by ring
    _ ≤ _ := hstep
    _ = _ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro Ta _
      dsimp [oddMaj, jIntegrand, K₀]
      ring

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
