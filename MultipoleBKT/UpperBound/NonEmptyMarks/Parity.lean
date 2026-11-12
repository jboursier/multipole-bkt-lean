/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Pointwise
public import MultipoleBKT.Appendix.SmallIntegral.JGraphs

/-!
# Expansion and parity cancellation for one raw marked term

The paper: (5.106), and Corollary 5.24.

`markedTerm` expands the Mayer bonds into odd and even factors while
retaining the full separation product `sepFactor`. External factors split
as `-sinh(β S_i) + (cosh(β S_i) - 1)`.

Reversing every dipole in a block preserves the hierarchical measure.
Its sign on each expanded term is determined by the number of incident
odd edges plus the number of odd marks. Terms without block parity
therefore integrate to zero. `abs_integral_clusterTerm_mul_le` bounds the
raw expectation by the surviving marked absolute integrals.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Hierarchical Multipole Parity BoundedUpper SetPartition

open scoped Classical

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-! ### The marked terms -/

section Defs

/-- The separation factor `∏_{ij ∈ ∪ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})`. -/
noncomputable def sepFactor (M lam : ℝ) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (F : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ univ.biUnion fun l => interPairs (Xs l),
      if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1) *
    ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)

/-- **A marked term** of the expansion of one term of Definition 5.15 with marks `U`: odd edges
`E₁ ⊆ ∪ Eₗ`, odd marks `U₁ ⊆ U`,
`∏_{E₁} a^{v^Z} 𝟙_{𝓑^c} ∏_{∪ Eₗ ∖ E₁} b^{v^Z} 𝟙_{𝓑^c} · sepFactor · ∏_{U₁} (-sinh(β S_i))
∏_{U ∖ U₁} (cosh(β S_i) - 1)`. -/
noncomputable def markedTerm (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
    (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ) (E₁ : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ E₁, oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)) *
    (∏ p ∈ univ.biUnion Es \ E₁,
      evenBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)) *
    sepFactor M lam Xs F c *
    (∏ i ∈ U₁, -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))) *
    ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1)

end Defs

/-! ### The expansion -/

theorem externalBondZ_eq_sinh_cosh (e : ℂ × ℂ) :
    externalBondZ χ p₀ β lam ε₀ V Z e =
      -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z e) +
        (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z e) - 1) := by
  have h := one_add_externalBondZ_eq (χ := χ) (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀)
    (V := V) (Z := Z) e
  linarith

/-- **The expansion of one marked term** into odd and even parts. -/
theorem clusterTerm_mul_eq_sum {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) (F : Finset (ℕ × ℕ))
    (U : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F c *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (c i) =
      ∑ E₁ ∈ (univ.biUnion Es).powerset, ∑ U₁ ∈ U.powerset,
        markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c := by
  rw [clusterTerm_eq_prod_add_mul hEs F c]
  simp_rw [externalBondZ_eq_sinh_cosh]
  rw [Finset.prod_add, Finset.prod_add, Finset.sum_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun E₁ _ => Finset.sum_congr rfl fun U₁ _ => ?_
  unfold markedTerm sepFactor
  ring

/-! ### The reversal of a block -/

theorem sepFactor_flipOn {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (F : Finset (ℕ × ℕ))
    (S : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    sepFactor M lam Xs F (flipOn Prod.swap S c) = sepFactor M lam Xs F c := by
  unfold sepFactor
  congr 1
  · refine Finset.prod_congr rfl fun p _ => ?_
    exact if_congr (linkedIndicator_flipOn S c p) rfl rfl
  · refine Finset.prod_congr rfl fun p _ => ?_
    rw [if_congr (linkedIndicator_flipOn S c p) rfl rfl]

/-- The marked term at the configuration with the dipoles of `S` reversed. -/
theorem markedTerm_flipOn (hM : 1 ≤ M) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ) (E₁ : Finset (ℕ × ℕ))
    (S : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (flipOn Prod.swap S c) =
      (-1) ^ (blockDeg E₁ S + (S ∩ U₁).card) *
        markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c := by
  unfold markedTerm
  rw [prod_flipOn_of_odd' (fun d e => oddBondUnlinked_swap_left hM
      (fun d e => interactionGoodZ_swap_left d e) d e)
      (fun d e => oddBondUnlinked_swap_right hM (fun d e => interactionGoodZ_swap_right d e) d e),
    prod_flipOn_of_even' (fun d e => evenBondUnlinked_swap_left hM
      (fun d e => interactionGoodZ_swap_left d e) d e)
      (fun d e => evenBondUnlinked_swap_right hM (fun d e => interactionGoodZ_swap_right d e) d e),
    sepFactor_flipOn,
    prod_flipOn_vertex_odd (u := fun d => -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z d))
      (fun d => by simp only [extSumZ_swap, mul_neg, Real.sinh_neg, neg_neg]),
    prod_flipOn_vertex_even (v := fun d => Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z d) - 1)
      (fun d => by simp only [extSumZ_swap, mul_neg, Real.cosh_neg]), pow_add]
  ring

/-! ### Measurability, boundedness, integrability -/

section Integral

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam

omit hχ hlam in
theorem measurable_sepFactor {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (F : Finset (ℕ × ℕ)) :
    Measurable (sepFactor M lam Xs F) := by
  unfold sepFactor
  exact (measurable_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
    (measurable_unlinkedIndicator M lam)).mul (measurable_prod_pair
      (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
      (measurable_negLinkedIndicator M lam))

theorem measurable_markedTerm {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ)
    (E₁ : Finset (ℕ × ℕ)) :
    Measurable (markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁) := by
  have hw := measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam
  have hS := measurable_extSumZ (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (Z := Z) hχ hlam
  unfold markedTerm
  refine ((((Finset.measurable_prod _ fun p _ => measurable_pairWeight
    (measurable_oddBondUnlinked hw β M lam) p).mul (Finset.measurable_prod _ fun p _ =>
      measurable_pairWeight (measurable_evenBondUnlinked hw β M lam) p)).mul
    (measurable_sepFactor Xs F)).mul (Finset.measurable_prod _ fun i _ => ?_)).mul
    (Finset.measurable_prod _ fun i _ => ?_)
  · exact (Real.continuous_sinh.measurable.comp (measurable_const.mul
      (hS.comp (measurable_pi_apply i)))).neg
  · exact (Real.continuous_cosh.measurable.comp (measurable_const.mul
      (hS.comp (measurable_pi_apply i)))).sub_const 1

omit hχ hlam in
theorem boundedOn_sepFactor {K : Set (ℂ × ℂ)} {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (F : Finset (ℕ × ℕ)) : BoundedOn K (sepFactor M lam Xs F) := by
  unfold sepFactor
  exact (boundedOn_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
    (exists_abs_unlinkedIndicator_le M lam)).mul (boundedOn_prod_pair
      (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
      (exists_abs_negLinkedIndicator_le M lam))

theorem boundedOn_markedTerm {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ)
    (E₁ : Finset (ℕ × ℕ)) :
    BoundedOn (supportSet N p₀ β lam ε₀) (markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁) := by
  classical
  obtain ⟨Bw, hBw⟩ := exists_abs_interactionGoodZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
    (Z := Z) hχ hlam
  obtain ⟨Bx, hBx⟩ := exists_abs_interactionExtZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
    (Z := Z) hχ hlam
  have hS : ∀ d ∈ supportSet N p₀ β lam ε₀, |β * extSumZ χ p₀ β lam ε₀ V Z d| ≤
      |β| * ∑ _j ∈ V, Bx := by
    intro d hd
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => hBx d hd j hj)) (abs_nonneg β)
  have h3 : BoundedOn (supportSet N p₀ β lam ε₀) fun c : ℕ → ℂ × ℂ =>
      ∏ i ∈ U₁, -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) := by
    refine BoundedOn.prod _ fun i _ => BoundedOn.single
      (ψ := fun d => -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z d))
      ⟨Real.exp (|β| * ∑ _j ∈ V, Bx), fun d hd => ?_⟩ i
    simp only [abs_neg]
    exact (abs_sinh_le_exp_abs _).trans (Real.exp_le_exp.2 (hS d hd))
  have h4 : BoundedOn (supportSet N p₀ β lam ε₀) fun c : ℕ → ℂ × ℂ =>
      ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1) := by
    refine BoundedOn.prod _ fun i _ => BoundedOn.single
      (ψ := fun d => Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z d) - 1)
      ⟨Real.exp (|β| * ∑ _j ∈ V, Bx) + 1, fun d hd => ?_⟩ i
    refine (abs_sub _ _).trans ?_
    rw [abs_of_pos (Real.cosh_pos _), abs_one]
    exact add_le_add ((cosh_le_exp_abs' _).trans (Real.exp_le_exp.2 (hS d hd))) le_rfl
  unfold markedTerm
  exact ((((boundedOn_prod_pair (g := oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam)
    (exists_abs_oddBondUnlinked_le ⟨Bw, hBw⟩ β M lam)).mul
    (boundedOn_prod_pair (g := evenBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam)
      (exists_abs_evenBondUnlinked_le ⟨Bw, hBw⟩ β M lam))).mul
    (boundedOn_sepFactor Xs F)).mul h3).mul h4

omit hχ hlam in
theorem dependsOn_markedTerm {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {F : Finset (ℕ × ℕ)} (hF : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id)
    {U U₁ : Finset ℕ} (hU : U ⊆ X.biUnion id) (hU₁ : U₁ ⊆ U) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ⊆ univ.biUnion Es) :
    DependsOn (markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁)
      ((X.biUnion id : Finset ℕ) : Set ℕ) := by
  intro c c' hcc'
  have hIV : ∀ p ∈ univ.biUnion fun l => interPairs (Xs l),
      p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => by
    obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
    exact mem_biUnion_of_mem_interPairs (hXs l) hpl
  have hEV : ∀ p ∈ univ.biUnion Es, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => by
    obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
    exact mem_biUnion_of_mem_interPairs (hXs l) (hEs l hpl)
  have hc : ∀ i ∈ X.biUnion id, c i = c' i := fun i hi => hcc' i (Finset.mem_coe.2 hi)
  unfold markedTerm sepFactor
  rw [prod_pair_congr (fun p hp => hEV p (hE₁ hp)) _ hcc',
    prod_pair_congr (fun p hp => hEV p (Finset.sdiff_subset hp)) _ hcc',
    prod_pair_congr hIV (fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1) hcc',
    prod_pair_congr hF (fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0)) hcc']
  congr 1
  · congr 1
    exact Finset.prod_congr rfl fun i hi => by rw [hc i (hU (hU₁ hi))]
  · exact Finset.prod_congr rfl fun i hi => by rw [hc i (hU (Finset.sdiff_subset hi))]

include hε₀ hN

/-- **The marked terms without parity vanish** (Corollary 5.24): if `deg_{E₁}(S₀) + |S₀ ∩ U₁|` is
odd for some `S₀ ∈ X`, then `𝔼_{𝖯^{+,ε₀,Z}_X}[markedTerm U U₁ E₁] = 0`. -/
theorem integral_markedTerm_eq_zero (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ))
    (U U₁ : Finset ℕ) (E₁ : Finset (ℕ × ℕ)) {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X)
    (hodd : Odd (blockDeg E₁ S₀ + (S₀ ∩ U₁).card)) :
    ∫ y, markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X = 0 := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  set f : (X.biUnion id → ℂ × ℂ) → ℝ := fun y =>
    markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y) with hf
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
    simp only [hf, extendConfig_flipOn hS₀, markedTerm_flipOn hM, hodd.neg_one_pow]
    ring
  simp_rw [hneg, integral_neg] at hcomp
  linarith

/-- **The parity reduction of one marked term** (Corollary 5.24 for the claim (5.106)): for
`M ≥ 1`, a subpartition `X`, groups `Xₗ ⊆ X`, `Eₗ ⊆ ℰ^inter(Xₗ)`, `F` with pairs in `V_X` and marks
`U ⊆ V_X`,
`|𝔼[clusterTerm ∏_{i ∈ U} f_{i∞}]| ≤ ∑_{E₁ ⊆ ∪ Eₗ} ∑_{U₁ ⊆ U, E₁ ∈ Eul^X(U₁)} 𝔼[|markedTerm U U₁ E₁|]`. -/
theorem abs_integral_clusterTerm_mul_le (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) {F : Finset (ℕ × ℕ)}
    (hF : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id) {U : Finset ℕ}
    (hU : U ⊆ X.biUnion id) :
    |∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
          (extendConfig (X.biUnion id) y) *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
      ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤
      ∑ E₁ ∈ (univ.biUnion Es).powerset,
        ∑ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
          ∫ y, |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)|
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  classical
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hint : ∀ E₁ ∈ (univ.biUnion Es).powerset, ∀ U₁ ∈ U.powerset,
      Integrable (fun y => markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁
        (extendConfig (X.biUnion id) y)) (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
    intro E₁ hE₁ U₁ hU₁
    exact h.integrable_comp_extendConfig (measurable_markedTerm hχ hlam Xs Es F U U₁ E₁)
      (boundedOn_markedTerm hχ hlam Xs Es F U U₁ E₁)
      (dependsOn_markedTerm hXs hEs hF hU (Finset.mem_powerset.1 hU₁)
        (Finset.mem_powerset.1 hE₁))
  simp_rw [clusterTerm_mul_eq_sum hEs F U]
  rw [integral_finsetSum _ fun E₁ hE₁ => integrable_finsetSum _ fun U₁ hU₁ => hint E₁ hE₁ U₁ hU₁]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun E₁ hE₁ => ?_)
  rw [integral_finsetSum _ fun U₁ hU₁ => hint E₁ hE₁ U₁ hU₁,
    ← Finset.sum_filter_add_sum_filter_not U.powerset (IsParityPair X E₁)]
  have hzero : ∑ U₁ ∈ U.powerset.filter (fun U₁ => ¬ IsParityPair X E₁ U₁),
      ∫ y, markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ (extendConfig (X.biUnion id) y)
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X = 0 := by
    refine Finset.sum_eq_zero fun U₁ hU₁ => ?_
    have hnp := (Finset.mem_filter.1 hU₁).2
    unfold IsParityPair at hnp
    push Not at hnp
    obtain ⟨S₀, hS₀, hodd⟩ := hnp
    exact integral_markedTerm_eq_zero hχ hlam hε₀ hN hM hX Xs Es F U U₁ E₁ hS₀
      (Nat.not_even_iff_odd.1 hodd)
  rw [hzero, add_zero]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun U₁ _ => ?_)
  exact abs_integral_le_integral_abs

end Integral

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
