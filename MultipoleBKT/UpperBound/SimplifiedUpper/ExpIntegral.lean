/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.Expansion
public import MultipoleBKT.LowerBound.Hierarchical.ActivityIntegral

/-!
# The parity reduction of one term of `𝖪^{+,Z}_{ε₀}` (Corollary 5.24)

The paper: Corollary 5.24,
used at the start of the proof of Lemma 5.35. For disjoint groups
`X₁, …, Xₙ ⊆ X` and a set `U ⊆ V_X` of external bonds, the sum over `Eₗ ∈ 𝖤^{Xₗ}` and
`F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}` of the expectations of Definition 5.15 is bounded by the
expectation of the sum of `|expTerm|` over the marks `U₁ ⊆ U` and the odd edge sets
`E₁ₗ ⊆ ℰ^inter(Xₗ)` such that `∑ₗ deg_{E₁ₗ}(S) + |S ∩ U₁|` is even for every `S ∈ X`
(`abs_sum_integral_le`): the other terms vanish by the reversal of a block (`expTerm_flipOn`).

The integrands are measurable, bounded on the support of `μ_{β,λ,ε₀}` and depend only on the
labels of `V_X` (`measurable_expTerm`, `boundedOn_expTerm`, `expTerm_congr`), hence integrable.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Hierarchical Multipole SetPartition AbsoluteLower Parity BoundedUpper

/-! ### The parity condition and the reduced sum -/

section Defs

open scoped Classical

/-- The sum of `|expTerm|` over the marks `U₁ ⊆ U` and the odd edge sets `E₁ₗ ⊆ ℰ^inter(Xₗ)` with
`∑ₗ deg_{E₁ₗ}(S) + |S ∩ U₁|` even for every `S ∈ X`. -/
noncomputable def parAbsSum (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (s : ℂ × ℂ → ℝ)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (U : Finset ℕ)
    (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ U₁ ∈ U.powerset, ∑ E₁s ∈ (Fintype.piFinset fun l => (interPairs (Xs l)).powerset).filter
      (fun E₁s => ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card)),
    |expTerm β w M lam s X Xs U U₁ E₁s c|

theorem parAbsSum_nonneg (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (s : ℂ × ℂ → ℝ)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (U : Finset ℕ)
    (c : ℕ → ℂ × ℂ) : 0 ≤ parAbsSum β w M lam s X Xs U c :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

end Defs

/-! ### Measurability, boundedness, locality -/

section Generic

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}

section Measurable

variable (hw : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2) (hs : Measurable s)
include hw

theorem measurable_evenSum (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) :
    Measurable fun c => evenSum β w M lam Y E₁ c := by
  unfold evenSum
  exact (Finset.measurable_sum _ fun E₂ _ => measurable_prod_pair
    (measurable_evenBondUnlinked hw β M lam)).mul
    (measurable_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
      (measurable_unlinkedIndicator M lam))

theorem measurable_groupTerm (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) :
    Measurable fun c => groupTerm β w M lam Y E₁ c := by
  unfold groupTerm
  exact (measurable_prod_pair (measurable_oddBondUnlinked hw β M lam)).mul
    (measurable_evenSum hw Y E₁)

omit hw in
theorem measurable_treeF (Y : Finset (Finset ℕ)) : Measurable fun c => treeF M lam Y c := by
  unfold treeF
  exact Finset.measurable_sum _ fun F _ => measurable_prod_pair
    (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
    (measurable_negLinkedIndicator M lam)

include hs in
theorem measurable_expTerm (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (U U₁ : Finset ℕ) (E₁s : Fin n → Finset (ℕ × ℕ)) :
    Measurable fun c => expTerm β w M lam s X Xs U U₁ E₁s c := by
  unfold expTerm
  refine (((Finset.measurable_prod _ fun l _ => measurable_groupTerm hw (Xs l) (E₁s l)).mul
    (measurable_treeF _)).mul (Finset.measurable_prod _ fun i _ => ?_)).mul
    (Finset.measurable_prod _ fun i _ => ?_)
  · exact (Real.continuous_sinh.measurable.comp (measurable_const.mul
      (hs.comp (measurable_pi_apply i)))).neg
  · exact (Real.continuous_cosh.measurable.comp (measurable_const.mul
      (hs.comp (measurable_pi_apply i)))).sub_const 1

include hs in
theorem measurable_parAbsSum (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (U : Finset ℕ) : Measurable fun c => parAbsSum β w M lam s X Xs U c := by
  unfold parAbsSum
  exact Finset.measurable_sum _ fun U₁ _ => Finset.measurable_sum _ fun E₁s _ =>
    continuous_abs.measurable.comp (measurable_expTerm hw hs X Xs U U₁ E₁s)

end Measurable

section Bounded

variable {K : Set (ℂ × ℂ)} (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C)
  (hsb : ∃ C, ∀ d ∈ K, |s d| ≤ C)
include hwb

theorem boundedOn_groupTerm (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) :
    BoundedOn K fun c => groupTerm β w M lam Y E₁ c := by
  unfold groupTerm evenSum
  exact (boundedOn_prod_pair (exists_abs_oddBondUnlinked_le hwb β M lam)).mul
    ((BoundedOn.sum _ fun E₂ _ => boundedOn_prod_pair
      (exists_abs_evenBondUnlinked_le hwb β M lam)).mul
      (boundedOn_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
        (exists_abs_unlinkedIndicator_le M lam)))

omit hwb in
theorem boundedOn_treeF (Y : Finset (Finset ℕ)) : BoundedOn K fun c => treeF M lam Y c := by
  unfold treeF
  exact BoundedOn.sum _ fun F _ => boundedOn_prod_pair
    (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
    (exists_abs_negLinkedIndicator_le M lam)

include hsb in
theorem boundedOn_expTerm (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (U U₁ : Finset ℕ) (E₁s : Fin n → Finset (ℕ × ℕ)) :
    BoundedOn K fun c => expTerm β w M lam s X Xs U U₁ E₁s c := by
  obtain ⟨C, hC⟩ := hsb
  have hS : ∀ d ∈ K, |β * s d| ≤ |β| * C := fun d hd => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC d hd) (abs_nonneg β)
  unfold expTerm
  refine (((BoundedOn.prod _ fun l _ => boundedOn_groupTerm hwb (Xs l) (E₁s l)).mul
    (boundedOn_treeF _)).mul (BoundedOn.prod _ fun i _ => BoundedOn.single
      (ψ := fun d => -Real.sinh (β * s d)) ⟨Real.exp (|β| * C), fun d hd => ?_⟩ i)).mul
    (BoundedOn.prod _ fun i _ => BoundedOn.single
      (ψ := fun d => Real.cosh (β * s d) - 1) ⟨Real.exp (|β| * C) + 1, fun d hd => ?_⟩ i)
  · simp only [abs_neg]
    exact (abs_sinh_le_exp_abs _).trans (Real.exp_le_exp.2 (hS d hd))
  · refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.cosh_pos _), abs_one]
    exact add_le_add_left ((cosh_le_exp_abs' _).trans (Real.exp_le_exp.2 (hS d hd))) 1

end Bounded

section Congr

variable {c c' : ℕ → ℂ × ℂ}

theorem evenSum_congr {Y : Finset (Finset ℕ)} (E₁ : Finset (ℕ × ℕ))
    (hcc' : ∀ i ∈ ((Y.biUnion id : Finset ℕ) : Set ℕ), c i = c' i) :
    evenSum β w M lam Y E₁ c = evenSum β w M lam Y E₁ c' := by
  have hI : ∀ p ∈ interPairs Y, p.1 ∈ Y.biUnion id ∧ p.2 ∈ Y.biUnion id := fun p hp =>
    interPairs_subset_pairsOn_biUnion _ hp
  unfold evenSum
  rw [prod_pair_congr hI (fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1) hcc']
  congr 1
  refine sum_congr rfl fun E₂ hE₂ => ?_
  have hE₂ : E₂ ⊆ interPairs Y := mem_powerset.1 (mem_filter.1 hE₂).1
  exact prod_pair_congr (fun p hp => hI p (hE₂ hp)) _ hcc'

theorem groupTerm_congr {Y : Finset (Finset ℕ)} {E₁ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ interPairs Y)
    (hcc' : ∀ i ∈ ((Y.biUnion id : Finset ℕ) : Set ℕ), c i = c' i) :
    groupTerm β w M lam Y E₁ c = groupTerm β w M lam Y E₁ c' := by
  unfold groupTerm
  rw [evenSum_congr E₁ hcc', prod_pair_congr
    (fun p hp => interPairs_subset_pairsOn_biUnion _ (hE₁ hp)) _ hcc']

theorem treeF_congr {Y : Finset (Finset ℕ)}
    (hcc' : ∀ i ∈ ((Y.biUnion id : Finset ℕ) : Set ℕ), c i = c' i) :
    treeF M lam Y c = treeF M lam Y c' := by
  unfold treeF
  refine sum_congr rfl fun F hF => ?_
  have hF' := (mem_relEdgeSets₀.1 hF).1
  exact prod_pair_congr (fun p hp => interPairs_subset_pairsOn_biUnion _ (hF' hp))
    (fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0)) hcc'

/-- `expTerm` depends only on the labels of `V_X`. -/
theorem expTerm_congr {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) {U U₁ : Finset ℕ} (hU : U ⊆ X.biUnion id) (hU₁ : U₁ ⊆ U)
    {E₁s : Fin n → Finset (ℕ × ℕ)} (hE₁s : ∀ l, E₁s l ⊆ interPairs (Xs l))
    (hcc' : ∀ i ∈ ((X.biUnion id : Finset ℕ) : Set ℕ), c i = c' i) :
    expTerm β w M lam s X Xs U U₁ E₁s c = expTerm β w M lam s X Xs U U₁ E₁s c' := by
  have hXl : ∀ l, ∀ i ∈ (((Xs l).biUnion id : Finset ℕ) : Set ℕ), c i = c' i := fun l i hi =>
    hcc' i (mem_coe.2 (biUnion_subset_biUnion_of_subset_left id (hXs l) (mem_coe.1 hi)))
  have hco : ∀ i ∈ (((coarsen X (univ.image Xs)).biUnion id : Finset ℕ) : Set ℕ),
      c i = c' i := by
    intro i hi
    rw [biUnion_coarsen fun Y hY => by
      obtain ⟨l, -, rfl⟩ := mem_image.1 hY
      exact hXs l] at hi
    exact hcc' i hi
  unfold expTerm
  have h1 : ∏ l, groupTerm β w M lam (Xs l) (E₁s l) c =
      ∏ l, groupTerm β w M lam (Xs l) (E₁s l) c' :=
    prod_congr rfl fun l _ => groupTerm_congr (hE₁s l) (hXl l)
  have h3 : ∏ i ∈ U₁, -Real.sinh (β * s (c i)) = ∏ i ∈ U₁, -Real.sinh (β * s (c' i)) :=
    prod_congr rfl fun i hi => by rw [hcc' i (mem_coe.2 (hU (hU₁ hi)))]
  have h4 : ∏ i ∈ U \ U₁, (Real.cosh (β * s (c i)) - 1) =
      ∏ i ∈ U \ U₁, (Real.cosh (β * s (c' i)) - 1) :=
    prod_congr rfl fun i hi => by rw [hcc' i (mem_coe.2 (hU (sdiff_subset hi)))]
  rw [h1, treeF_congr hco, h3, h4]

theorem parAbsSum_congr {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) {U : Finset ℕ} (hU : U ⊆ X.biUnion id)
    (hcc' : ∀ i ∈ ((X.biUnion id : Finset ℕ) : Set ℕ), c i = c' i) :
    parAbsSum β w M lam s X Xs U c = parAbsSum β w M lam s X Xs U c' := by
  unfold parAbsSum
  refine sum_congr rfl fun U₁ hU₁ => sum_congr rfl fun E₁s hE₁s => ?_
  have hE := Fintype.mem_piFinset.1 (mem_filter.1 hE₁s).1
  rw [expTerm_congr hXs hU (mem_powerset.1 hU₁) (fun l => mem_powerset.1 (hE l)) hcc']

end Congr

end Generic

/-! ### The frozen model -/

section Frozen

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

theorem externalBondZ_eq (e : ℂ × ℂ) :
    externalBondZ χ p₀ β lam ε₀ V Z e = Real.exp (-β * extSumZ χ p₀ β lam ε₀ V Z e) - 1 := by
  have h := one_add_externalBondZ_eq (χ := χ) (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀)
    (V := V) (Z := Z) e
  rw [neg_mul, ← Real.cosh_sub_sinh]
  linarith

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

omit hε₀ hN in
theorem exists_abs_extSumZ_le :
    ∃ C, ∀ d ∈ supportSet N p₀ β lam ε₀, |extSumZ χ p₀ β lam ε₀ V Z d| ≤ C := by
  obtain ⟨Bx, hBx⟩ := exists_abs_interactionExtZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
    (Z := Z) hχ hlam
  exact ⟨∑ _j ∈ V, Bx, fun d hd => (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun j hj => hBx d hd j hj)⟩

open scoped Classical in
/-- **An integrand without parity vanishes** (Corollary 5.24). -/
theorem integral_expTerm_eq_zero (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (U U₁ : Finset ℕ) (E₁s : Fin n → Finset (ℕ × ℕ))
    {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X) (hodd : Odd (∑ l, blockDeg (E₁s l) S₀ + (S₀ ∩ U₁).card)) :
    ∫ y, expTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X Xs U
        U₁ E₁s (extendConfig (X.biUnion id) y) ∂plusModel χ N p₀ β lam M ε₀ L V Z X = 0 := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  set f : (X.biUnion id → ℂ × ℂ) → ℝ := fun y =>
    expTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X Xs U U₁
      E₁s (extendConfig (X.biUnion id) y) with hf
  have hmp := measurePreserving_flipOn_modelHierarchical (β := β) (M := M) (lam := lam)
    (w := interactionGoodZ χ p₀ β lam ε₀ V Z) (ψ := dipoleWeightZ p₀ β lam M ε₀ L V Z)
    (fun d e => interactionGoodZ_swap_left d e) (fun d e => interactionGoodZ_swap_right d e)
    (fun d => dipoleWeightZ_swap d) (measurePreserving_swap_cutoffDipoleMeasure hχ N p₀ β lam ε₀)
    hX hS₀
  have hcomp : ∫ y, f (flipOn Prod.swap (blockSet X S₀) y) ∂plusModel χ N p₀ β lam M ε₀ L V Z X =
      ∫ y, f y ∂plusModel χ N p₀ β lam M ε₀ L V Z X :=
    hmp.integral_comp (flipOnEquiv measurable_swap Prod.swap_swap _).measurableEmbedding f
  have hneg : ∀ y, f (flipOn Prod.swap (blockSet X S₀) y) = -f y := by
    intro y
    simp only [hf, extendConfig_flipOn hS₀,
      expTerm_flipOn hM (fun d e => interactionGoodZ_swap_left d e)
        (fun d e => interactionGoodZ_swap_right d e) (fun d => extSumZ_swap d),
      hodd.neg_one_pow]
    ring
  simp_rw [hneg, integral_neg] at hcomp
  linarith

open scoped Classical in
theorem integrable_expTerm {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) {U U₁ : Finset ℕ} (hU : U ⊆ X.biUnion id) (hU₁ : U₁ ⊆ U)
    {E₁s : Fin n → Finset (ℕ × ℕ)} (hE₁s : ∀ l, E₁s l ⊆ interPairs (Xs l)) :
    Integrable (fun y => expTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (extSumZ χ p₀ β lam ε₀ V Z) X Xs U U₁ E₁s (extendConfig (X.biUnion id) y))
      (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  exact h.integrable_comp_extendConfig
    (measurable_expTerm (measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam)
      (measurable_extSumZ hχ hlam) X Xs U U₁ E₁s)
    (boundedOn_expTerm (exists_abs_interactionGoodZ_le hχ hlam) (exists_abs_extSumZ_le hχ hlam)
      X Xs U U₁ E₁s)
    fun c c' hcc' => expTerm_congr hXs hU hU₁ hE₁s hcc'

open scoped Classical in
theorem integrable_parAbsSum {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) {U : Finset ℕ} (hU : U ⊆ X.biUnion id) :
    Integrable (fun y => parAbsSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (extSumZ χ p₀ β lam ε₀ V Z) X Xs U (extendConfig (X.biUnion id) y))
      (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
  unfold parAbsSum
  refine integrable_finsetSum _ fun U₁ hU₁ => integrable_finsetSum _ fun E₁s hE₁s => ?_
  have hE := Fintype.mem_piFinset.1 (mem_filter.1 hE₁s).1
  exact (integrable_expTerm hχ hlam hε₀ hN hXs hU (mem_powerset.1 hU₁)
    fun l => mem_powerset.1 (hE l)).abs

open scoped Classical in
/-- **The parity reduction of one term** (Definition 5.15 with Corollary 5.24): for disjoint
groups `Xₗ ⊆ X` and `U ⊆ V_X`,
`|∑_{Eₗ ∈ 𝖤^{Xₗ}} ∑_F 𝔼_{𝖯^{+,ε₀,Z}_X}[clusterTerm ∏_{i ∈ U} f^{v^Z}_{i∞}]|
≤ 𝔼_{𝖯^{+,ε₀,Z}_X}[parAbsSum]`. -/
theorem abs_sum_integral_le (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) {U : Finset ℕ} (hU : U ⊆ X.biUnion id) :
    |∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
          ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
              (extendConfig (X.biUnion id) y) *
            ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤
      ∫ y, parAbsSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X
        Xs U (extendConfig (X.biUnion id) y) ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  set W := X.biUnion id with hW
  set w := interactionGoodZ χ p₀ β lam ε₀ V Z with hwdef
  set s := extSumZ χ p₀ β lam ε₀ V Z with hsdef
  set P := plusModel χ N p₀ β lam M ε₀ L V Z X with hP
  have hext : ∃ B, ∀ d ∈ supportSet N p₀ β lam ε₀,
      |externalBondZ χ p₀ β lam ε₀ V Z d| ≤ B := by
    obtain ⟨C, hC⟩ := exists_abs_extSumZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (Z := Z)
      hχ hlam
    refine ⟨Real.exp (|β| * C) + 1, fun d hd => ?_⟩
    rw [externalBondZ_eq]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.exp_pos _), abs_one]
    refine add_le_add_left (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)) 1
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hC d hd) (abs_nonneg β)
  -- the integrability of the terms of the series
  have hint1 : ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      Integrable (fun y => clusterTerm β w M lam Xs Es F (extendConfig W y) *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig W y i)) P := by
    intro Es hEs F hF
    have hEs' : ∀ l, Es l ⊆ interPairs (Xs l) := fun l =>
      (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1
    refine h.integrable_comp_extendConfig
      (g := fun c => clusterTerm β w M lam Xs Es F c *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (c i)) ?_ ?_ ?_
    · exact (measurable_clusterTerm β w M lam h Xs Es F).mul (Finset.measurable_prod _ fun i _ =>
        (measurable_externalBondZ hχ hlam).comp (measurable_pi_apply i))
    · exact (boundedOn_clusterTerm β w M lam h Xs Es F).mul
        (BoundedOn.prod _ fun i _ => BoundedOn.single hext i)
    · intro c c' hcc'
      simp only
      rw [dependsOn_clusterTerm β w M lam hXs hEs' (mem_relEdgeSets₀.1 hF).1 hcc']
      congr 1
      exact prod_congr rfl fun i hi => by rw [hcc' i (mem_coe.2 (hU hi))]
  have hint2 : ∀ U₁ ∈ U.powerset,
      ∀ E₁s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset),
      Integrable (fun y => expTerm β w M lam s X Xs U U₁ E₁s (extendConfig W y)) P := by
    intro U₁ hU₁ E₁s hE₁s
    exact integrable_expTerm hχ hlam hε₀ hN hXs hU (mem_powerset.1 hU₁)
      fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hE₁s l)
  -- the sum of the integrals is the integral of the expanded sum
  have e1 : ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
        ∫ y, clusterTerm β w M lam Xs Es F (extendConfig W y) *
          ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig W y i) ∂P =
      ∑ U₁ ∈ U.powerset, ∑ E₁s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset),
        ∫ y, expTerm β w M lam s X Xs U U₁ E₁s (extendConfig W y) ∂P := by
    rw [sum_congr rfl fun Es hEs => (integral_finsetSum _ fun F hF => hint1 Es hEs F hF).symm,
      ← integral_finsetSum _ fun Es hEs => integrable_finsetSum _ fun F hF => hint1 Es hEs F hF]
    simp_rw [externalBondZ_eq]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun y =>
      sum_clusterTerm_eq_sum_expTerm hX hXs hdisj U (extendConfig W y))]
    rw [integral_finsetSum _ fun U₁ hU₁ => integrable_finsetSum _ fun E₁s hE₁s =>
      hint2 U₁ hU₁ E₁s hE₁s]
    exact sum_congr rfl fun U₁ hU₁ => integral_finsetSum _ fun E₁s hE₁s => hint2 U₁ hU₁ E₁s hE₁s
  rw [e1]
  -- the terms without parity vanish
  have e2 : ∀ U₁ ∈ U.powerset,
      ∑ E₁s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset),
        ∫ y, expTerm β w M lam s X Xs U U₁ E₁s (extendConfig W y) ∂P =
      ∑ E₁s ∈ (Fintype.piFinset fun l => (interPairs (Xs l)).powerset).filter
          (fun E₁s => ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card)),
        ∫ y, expTerm β w M lam s X Xs U U₁ E₁s (extendConfig W y) ∂P := by
    intro U₁ _
    rw [← sum_filter_add_sum_filter_not _
      (fun E₁s => ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card))]
    rw [add_eq_left]
    refine sum_eq_zero fun E₁s hE₁s => ?_
    have hnp := (mem_filter.1 hE₁s).2
    push Not at hnp
    obtain ⟨S₀, hS₀, hodd⟩ := hnp
    exact integral_expTerm_eq_zero hχ hlam hε₀ hN hM hX U U₁ E₁s hS₀
      (Nat.not_even_iff_odd.1 hodd)
  rw [sum_congr rfl e2]
  -- the absolute values
  unfold parAbsSum
  rw [integral_finsetSum _ fun U₁ hU₁ => integrable_finsetSum _ fun E₁s hE₁s =>
    (hint2 U₁ hU₁ E₁s (mem_filter.1 hE₁s).1).abs]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun U₁ hU₁ => ?_)
  rw [integral_finsetSum _ fun E₁s hE₁s => (hint2 U₁ hU₁ E₁s (mem_filter.1 hE₁s).1).abs]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun E₁s _ => ?_)
  exact abs_integral_le_integral_abs

end Frozen

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
