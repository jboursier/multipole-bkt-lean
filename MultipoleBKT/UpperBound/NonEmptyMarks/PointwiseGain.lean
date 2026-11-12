/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.ComponentGain
public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Pointwise
public import MultipoleBKT.Appendix.SmallIntegral.LemmaA6J2

/-!
# A marked odd component supplies the gain of `J_ext`

The paper: (5.106).

`ratio_le_gainRoot` compares each bad-distance ratio with the common
gain. `cosh_sub_one_le_Z` provides the even external-mark estimate.
`pointwise_bound_gain` attaches the gain to one marked odd component
using `component_gain_Z`. The remaining components use the
`component_family_bound_Z`, which proves replacement-tree tails before
separation is removed. Their tails are then bounded by one.

The component family sums are multiplied by `Finset.prod_univ_sum`.
There is exactly one gain factor. The resulting sum is the integrand of
`J_ext`, including the block-connectivity indicators. No tree is selected
from an upper bound on a family sum.
-/

@[expose] public section

open Finset SimpleGraph
open scoped NNReal

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Peeling CoreForest Quadratic Parity Hierarchical Multipole SetPartition BoundedUpper BoundedUpper.RouteRaw

/-! ### The integrand of `J` without its tail -/

section NT

variable (M lam ε₀ R : ℝ)

open scoped Classical in
/-- The integrand of `J` without the tail and without `∏_{S ∈ X} 𝟙_{𝓑_S}` and the densities:
`∏_l ∏_{S ∈ X_l, S ≠ Ŝ_l} r_S² ∏_l ∏_{ij ∈ T_l^a} d_ij^{-2} 𝟙 𝟙_{𝓑^c} ∏_{ij ∈ T^b} b^abs_ij`. -/
noncomputable def jIntegrandNT (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ l, radialExceptMax c (Xs l)) * (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) *
    ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e

theorem jIntegrandNT_nonneg (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ) :
    0 ≤ jIntegrandNT M lam ε₀ R X Xs Ta Tb c := by
  classical
  unfold jIntegrandNT
  refine mul_nonneg (mul_nonneg ?_ ?_) ?_
  · exact prod_nonneg fun l _ => radialExceptMax_nonneg c _
  · exact prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e
  · exact prod_nonneg fun e _ => absEvenLift_nonneg M lam ε₀ R c e

end NT

/-! ### The gain -/

section Gain

variable {N p₀ : ℕ} {β lam ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

theorem extGain_eq {X : Finset (Finset ℕ)} (c : ℕ → ℂ × ℂ) :
    SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) =
      min (univ.fold max 0 (fun j : X.biUnion id => dipoleLength (c j)) /
        SmallIntegral.minBadDist p₀ β lam ε₀ V Z (fun j : X.biUnion id => c j)) 1 ^ 2 := rfl

/-- **The ratio of one dipole is at most the root of the gain**: if every dipole of `V_X` has
`d_{j,bad} ≥ λ` and `r_i ≤ d_{i,bad}`, then `r_i/d_{i,bad} ≤ min(max_j r_j / min_j d_{j,bad}, 1)`. -/
theorem ratio_le_gainRoot {X : Finset (Finset ℕ)} {c : ℕ → ℂ × ℂ} (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hδ : ∀ j ∈ X.biUnion id, lam ≤ badDistZ p₀ β lam ε₀ V Z (c j)) {i : ℕ}
    (hi : i ∈ X.biUnion id) (hri : ‖(c i).1 - (c i).2‖ ≤ badDistZ p₀ β lam ε₀ V Z (c i)) :
    ‖(c i).1 - (c i).2‖ / badDistZ p₀ β lam ε₀ V Z (c i) ≤
      min (univ.fold max 0 (fun j : X.biUnion id => dipoleLength (c j)) /
        SmallIntegral.minBadDist p₀ β lam ε₀ V Z (fun j : X.biUnion id => c j)) 1 := by
  set F := univ.fold max 0 (fun j : X.biUnion id => dipoleLength (c j))
  set m := SmallIntegral.minBadDist p₀ β lam ε₀ V Z (fun j : X.biUnion id => c j)
  have hδi : 0 < badDistZ p₀ β lam ε₀ V Z (c i) := hlam.trans_le (hδ i hi)
  have hm : lam ≤ m := (le_fold_min _).2 ⟨by linarith, fun j _ => hδ j j.2⟩
  have hm0 : 0 < m := hlam.trans_le hm
  have hmi : m ≤ badDistZ p₀ β lam ε₀ V Z (c i) :=
    (fold_min_le _).2 (Or.inr ⟨⟨i, hi⟩, mem_univ _, le_rfl⟩)
  have hF0 : 0 ≤ F := (le_fold_max _).2 (Or.inl le_rfl)
  have hrF : ‖(c i).1 - (c i).2‖ ≤ F :=
    (le_fold_max _).2 (Or.inr ⟨⟨i, hi⟩, mem_univ _, le_rfl⟩)
  exact le_min (div_le_div₀ hF0 hrF hm0 hmi) (div_le_one_of_le₀ hri hδi.le)

variable {χ : ℂ → ℝ}

/-- **Eq. (5.72) for the even part of the external bond**: on the support,
`cosh(β S_e) - 1 ≤ C (r_e/d_{e,bad})²`, `S_e = ∑_{j ∈ V_bad} v^Z_{ej}`. -/
theorem cosh_sub_one_le_Z (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {N : ℕ} (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ e : ℂ × ℂ, OnSupportZ p₀ β lam M ε₀ V Z e →
        Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z e) - 1 ≤
          C * (‖e.1 - e.2‖ / badDistZ p₀ β lam ε₀ V Z e) ^ 2 := by
  obtain ⟨C₁, hC₁, hgb⟩ := sum_abs_interactionExtZ_le hχ p₀ β
  set C := 1 + |β| * C₁ * Real.exp (|β| * C₁) + (|β| * C₁) ^ 2 * Real.exp (|β| * C₁) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |β| * C₁ * Real.exp (|β| * C₁) + (|β| * C₁) ^ 2 * Real.exp (|β| * C₁) := by
      positivity
    linarith
  refine ⟨C, hC1, fun lam M ε₀ V Z hlam hlamh hM hM3 hVZ e he => ?_⟩
  set D := badDistZ p₀ β lam ε₀ V Z e
  have hrD := norm_le_badDistZ hlam hlamh hM hVZ he.2 he.norm_le
  have hD : 0 < D := hlam.trans_le (lam_le_badDistZ hlam hlamh hM hVZ he.2 he.norm_le)
  have ha0 : 0 ≤ ‖e.1 - e.2‖ / D := div_nonneg (norm_nonneg _) hD.le
  have ha1 : ‖e.1 - e.2‖ / D ≤ 1 := by rwa [div_le_one hD]
  have hS : |extSumZ χ p₀ β lam ε₀ V Z e| ≤ C₁ * (‖e.1 - e.2‖ / D) := by
    unfold extSumZ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← mul_div_assoc]
    exact hgb lam M ε₀ V Z hlam hlamh hM hM3 hVZ e he.2 he.norm_le
  obtain ⟨-, h2⟩ := abs_sinh_cosh_le hC₁.le ha0 ha1 hS (β := β)
  exact (le_abs_self _).trans h2

end Gain

/-! ### The pointwise bound -/

section Pointwise

variable {χ : ℂ → ℝ}


open scoped Classical in
/-- A marked odd component supplies the common quadratic gain while all
odd components are bounded by paper tree families with full separation.
The paper: (5.106). -/
theorem pointwise_bound_gain (hχ : IsMollifier χ) {β : ℝ} (hβ : 0 ≤ β) (p₀ : ℕ) (M L : ℝ)
    (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ k →
      ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset, ∀ V₁ ∈ (X.biUnion id).powerset,
      IsParityPair X E₁ V₁ → (∃ Y ∈ oddComponents X E₁, (V₁ ∩ Y.biUnion id).Nonempty) →
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
              (SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
                jIntegrandNT M lam ε₀ (truncationScale p₀ β lam) X Xs Ta Tb c) *
                ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
  obtain ⟨A₁, hA₁1, hcomp⟩ := component_family_bound_Z hχ p₀ β M hM3 k
  obtain ⟨Ag, hAg1, hgain⟩ := component_gain_Z hχ p₀ β M hM3 k
  set A : ℝ := max A₁ Ag with hAdef
  have hA1 : 1 ≤ A := le_max_of_le_left hA₁1
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
  intro N lam ε₀ V Z hlam hlamh hMp hVZ X hX hk E hE E₁ hE₁ V₁ hV₁ hpar hmark
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
        (SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
          jIntegrandNT M lam ε₀ R X Xs Ta Tb c) *
          ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
    refine mul_nonneg (by linarith) (sum_nonneg fun Ta _ => mul_nonneg
      (mul_nonneg (sq_nonneg _) (jIntegrandNT_nonneg M lam ε₀ R X Xs Ta Tb c))
      (prod_nonneg fun S _ => ?_))
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
          BoundedUpper.dipoleWeightZ_le hlam hlamh hMp hVZ L (hsupp i (hBX hi)).norm_le
  -- the gain
  obtain ⟨Y₀, hY₀, hY₀m⟩ := hmark
  set G := SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) with hGdef
  have hG0 : 0 ≤ G := sq_nonneg _
  have hδX : ∀ j ∈ X.biUnion id, lam ≤ badDistZ p₀ β lam ε₀ V Z (c j) := fun j hj =>
    lam_le_badDistZ hlam hlamh hMp hVZ (hsupp j hj).2 (hsupp j hj).norm_le
  set gl : Fin odd.card → ℝ := fun l => if Xs l = Y₀ then G else 1 with hgl
  have hgl0 : ∀ l, 0 ≤ gl l := fun l => by
    simp only [hgl]
    split_ifs
    · exact hG0
    · exact zero_le_one
  -- Keep full separation while each component is replaced by its tree family.
  have hcomp_l : ∀ l,
      ((∏ p ∈ E₁ ∩ interPairs (Xs l),
          |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
        ∏ i ∈ V₁ ∩ (Xs l).biUnion id, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
          componentSeparation M lam (Xs l) c ≤
      A * (radialExceptMax c (Xs l) *
        (∑ T ∈ relTrees (Xs l), ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * gl l) := by
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
    have hrk0 : 0 ≤ radialExceptMax c (Xs l) := radialExceptMax_nonneg c _
    by_cases hl : Xs l = Y₀
    · -- the marked component carries the gain
      have hW'ne : (V₁ ∩ (Xs l).biUnion id).Nonempty := hl ▸ hY₀m
      obtain ⟨i₀, hi₀, hb⟩ := hgain lam ε₀ V Z hlam hlamh hMp hVZ (Xs l) hYs
        ((Finset.card_le_card hYV).trans hk) _ Finset.inter_subset_right
        (isRelConnected_pairGraph hX hE₁X (hXsmem l)) _ Finset.inter_subset_right hW'ne heul c
        (fun i hi => ⟨hsupp i (hYV hi), (hc i (hYV hi)).2⟩) fun S hS => hconn S (hXsX l hS)
      have hi₀X := hYV hi₀
      have hratio := ratio_le_gainRoot (p₀ := p₀) (β := β) (V := V) (Z := Z) hlam hlamh hδX hi₀X
        (norm_le_badDistZ hlam hlamh hMp hVZ (hsupp _ hi₀X).2 (hsupp _ hi₀X).norm_le)
      have hq0 : 0 ≤ ‖(c i₀).1 - (c i₀).2‖ / badDistZ p₀ β lam ε₀ V Z (c i₀) :=
        div_nonneg (norm_nonneg _) (hlam.trans_le (hδX _ hi₀X)).le
      have hgain' : ‖(c i₀).1 - (c i₀).2‖ ^ 2 / badDistZ p₀ β lam ε₀ V Z (c i₀) ^ 2 ≤ G := by
        rw [← div_pow, hGdef, extGain_eq]
        exact pow_le_pow_left₀ hq0 hratio 2
      have hsum0 : 0 ≤ ∑ T ∈ relTrees (Xs l),
          ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e :=
        sum_nonneg fun T _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e
      have hfinal : Ag * (‖(c i₀).1 - (c i₀).2‖ ^ 2 /
          badDistZ p₀ β lam ε₀ V Z (c i₀) ^ 2) * (radialExceptMax c (Xs l) *
            ∑ T ∈ relTrees (Xs l), ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) ≤
          A * (radialExceptMax c (Xs l) *
            (∑ T ∈ relTrees (Xs l), ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * gl l) := by
        simp only [hgl, ite_eq_left hl]
        calc _ ≤ A * G * (radialExceptMax c (Xs l) *
              ∑ T ∈ relTrees (Xs l), ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) :=
            mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) hgain'
              (div_nonneg (sq_nonneg _) (sq_nonneg _)) (zero_le_one.trans hA1))
              (mul_nonneg hrk0 hsum0)
          _ = _ := by ring
      exact hb.trans hfinal
    · have hb := hcomp lam ε₀ V Z hlam hlamh hMp hVZ (Xs l) hYs
        ((Finset.card_le_card hYV).trans hk) _ Finset.inter_subset_right
        (isRelConnected_pairGraph hX hE₁X (hXsmem l)) _ Finset.inter_subset_right heul c
        (fun i hi => ⟨hsupp i (hYV hi), (hc i (hYV hi)).2⟩) fun S hS => hconn S (hXsX l hS)
      apply hb.trans
      simp only [hgl, ite_eq_right hl, mul_one]
      have hs : (∑ T ∈ relTrees (Xs l),
          (∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * compTail c (Xs l) T) ≤
          ∑ T ∈ relTrees (Xs l), ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e :=
        sum_le_sum fun T _ => mul_le_of_le_one_right
          (prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e) (compTail_le_one c _ T)
      exact mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_left hs hrk0)
        (mul_nonneg hrk0 (sum_nonneg fun T _ => mul_nonneg
          (prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e) (compTail_nonneg c _ T)))
        (zero_le_one.trans hA1)
  let 𝒯 := (univ : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))).filter
    (fun Ta => ∀ l, IsRelTree (Xs l) (Ta l))
  let oddMaj := fun Ta : ∀ l, SimpleGraph ((Xs l).biUnion id) =>
    (∏ l, radialExceptMax c (Xs l)) *
      (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) * G
  have oddMaj0 : ∀ Ta, 0 ≤ oddMaj Ta := fun Ta =>
    mul_nonneg (mul_nonneg (prod_nonneg fun l _ => radialExceptMax_nonneg c _)
      (prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e))
      hG0
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
      have hd := BoundedUpper.disjoint_biUnion_of_disjoint hX
        (subset_of_mem_relComponents (oddComponents_subset _ hY))
        (subset_of_mem_relComponents (oddComponents_subset _ hY'))
        (disjoint_of_mem_relComponents hX (oddComponents_subset _ hY)
          (oddComponents_subset _ hY') hne)
      exact hd.mono Finset.inter_subset_right Finset.inter_subset_right
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
  -- The gain occurs once, on the chosen marked odd component.
  have htl : ∏ l, gl l ≤ G := by
    set l₀ := eqv ⟨Y₀, hY₀⟩
    have hl₀ : Xs l₀ = Y₀ := by simp only [Xs, l₀, Equiv.symm_apply_apply]
    have hiff : ∀ l, Xs l = Y₀ ↔ l = l₀ := fun l =>
      ⟨fun h => hXsinj l l₀ (h.trans hl₀.symm), fun h => h ▸ hl₀⟩
    have : ∏ l, gl l = ∏ l, if l = l₀ then G else 1 :=
      Finset.prod_congr rfl fun l _ => by simp only [hgl, hiff l]
    rw [this, Finset.prod_ite_eq' univ l₀ (fun _ => G), ite_eq_left (mem_univ _)]
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
    have hsum : (∏ l, radialExceptMax c (Xs l) *
        (∑ T ∈ relTrees (Xs l), ∏ e ∈ T.edgeFinset, keptLift M lam ε₀ R c e) * gl l) ≤
        ∑ Ta ∈ 𝒯, oddMaj Ta := by
      simp_rw [Finset.prod_mul_distrib]
      rw [Finset.prod_univ_sum, hpi]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply sum_le_sum
      intro Ta _
      exact mul_le_mul_of_nonneg_left htl (mul_nonneg hrad0
        (prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e))
    have hP1 : ∏ l, (((∏ p ∈ E₁ ∩ interPairs (Xs l), oddP p) *
        ∏ i ∈ V₁ ∩ (Xs l).biUnion id, sh i) * componentSeparation M lam (Xs l) c) ≤
        A ^ k * ∑ Ta ∈ 𝒯, oddMaj Ta := by
      apply hl.trans
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul (pow_le_pow_right₀ hA1 hoddk) hsum
        (prod_nonneg fun l _ => mul_nonneg (mul_nonneg (radialExceptMax_nonneg c _)
          (sum_nonneg fun T _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e)) (hgl0 l))
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
      dsimp [oddMaj, jIntegrandNT, K₀]
      ring

end Pointwise

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
