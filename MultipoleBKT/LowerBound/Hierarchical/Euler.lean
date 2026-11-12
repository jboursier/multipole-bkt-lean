/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Instances
public import MultipoleBKT.LowerBound.Parity.Hierarchical

/-!
# Integrability against the hierarchical model; the parity reduction

Section 4.9: Lemma 4.32 and Corollary 4.34 (eq. (4.61), Corollary 4.34), for the
hierarchical models of `MultipoleBKT.LowerBound.Hierarchical.Model`.

* `ModelHyp.isFiniteMeasure_modelHierarchical`, `ModelHyp.integrable_modelHierarchical`,
  `ModelHyp.integrable_comp_extendConfig`: `𝖯_X` is a finite measure, and functions bounded on
  the configurations with all dipoles in `K` are integrable against it.
* `measurePreserving_flipOn_modelHierarchical`: if `ρ` is invariant under the reversal
  `(x, y) ↦ (y, x)` of a dipole, `w` is odd in each dipole and `ψ` is invariant under the
  reversal, then `𝖯_X` is invariant under the simultaneous reversal of the dipoles of any block
  `S₀ ∈ X` (proof of Corollary 4.34: `𝟙_{𝓑_S}` is invariant under every reversal, `e^{-β w_ij} 𝟙_{𝒜_ij}`
  under the reversal of both dipoles).
* `blockDeg E S`, `relEulerianPairs X`: the degree `deg_E(S) = ∑_{i ∈ S} deg_E(i)` of a block and
  the set `Eul^X` (Definition 4.33) of the edge sets `E ⊆ ℰ^inter(X)` all of whose
  block degrees are even, for edge sets of pairs `i < j`.
* `integral_prod_add_mul_eq_sum_relEulerian` (**the parity reduction**, Lemma 4.32 and the proof
  of Corollary 4.34): for `E ⊆ ℰ^inter(X)`, odd parts `a_ij` and even parts `b_ij` of the bonds
  and a reversal-invariant factor `G`,
  `𝔼_{𝖯_X}[∏_{ij ∈ E} (a_ij + b_ij) G] = ∑_{E₁ ⊆ E, E₁ ∈ Eul^X} 𝔼_{𝖯_X}[∏_{E₁} a ∏_{E ∖ E₁} b G]`.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

/-! ### Integrability against the hierarchical model -/

/-- The extension of a configuration of the labels of `U` by a fixed dipole `k₀`. -/
def extendDefault (k₀ : ℂ × ℂ) (U : Finset ℕ) (y : U → ℂ × ℂ) : ℕ → ℂ × ℂ :=
  fun i => if h : i ∈ U then y ⟨i, h⟩ else k₀

theorem restrict_extendDefault (k₀ : ℂ × ℂ) (U : Finset ℕ) (y : U → ℂ × ℂ) :
    U.restrict (extendDefault k₀ U y) = y := by
  funext i
  simp [extendDefault, Finset.restrict]

theorem extendDefault_mem {k₀ : ℂ × ℂ} (hk₀ : k₀ ∈ K) {U : Finset ℕ} {y : U → ℂ × ℂ}
    (hy : ∀ i, y i ∈ K) (i : ℕ) : extendDefault k₀ U y i ∈ K := by
  unfold extendDefault
  split_ifs
  · exact hy _
  · exact hk₀

theorem apply_extendConfig_eq_extendDefault {U : Finset ℕ} {g : (ℕ → ℂ × ℂ) → ℝ}
    (hdep : DependsOn g (U : Set ℕ)) (k₀ : ℂ × ℂ) (y : U → ℂ × ℂ) :
    g (extendConfig U y) = g (extendDefault k₀ U y) :=
  hdep fun i hi => by
    have hi' : i ∈ U := Finset.mem_coe.1 hi
    simp [extendConfig, extendDefault, hi']

theorem ModelHyp.nonempty (h : ModelHyp ρ β w ψ K) : K.Nonempty := by
  have := h.isProbabilityMeasure
  by_contra hK
  rw [Set.not_nonempty_iff_eq_empty] at hK
  have h0 := h.ae_mem
  rw [hK] at h0
  simp only [Set.mem_empty_iff_false, Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h0
  exact IsProbabilityMeasure.ne_zero ρ h0

/-- The density factors of `𝖯_X` are bounded on the configurations with all dipoles in `K`. -/
theorem ModelHyp.exists_bound_hierBlockWeight (h : ModelHyp ρ β w ψ K) (X : Finset (Finset ℕ)) :
    ∃ C, ∀ S ∈ X, ∀ y : X.biUnion id → ℂ × ℂ, (∀ i, y i ∈ K) →
      |hierBlockWeight β w ψ M lam X S y| ≤ C := by
  obtain ⟨k₀, hk₀⟩ := h.nonempty
  have hb : ∀ S ∈ X, ∃ C, ∀ c : ℕ → ℂ × ℂ, (∀ i, c i ∈ K) →
      |blockWeightOf β w ψ M lam S c| ≤ C := fun S _ => h.boundedOn_blockWeightOf M lam S
  choose! C hC using hb
  refine ⟨∑ S ∈ X, |C S|, fun S hS y hy => ?_⟩
  rw [← restrict_extendDefault k₀ _ y, hierBlockWeight_restrict β w ψ M lam hS]
  calc |blockWeightOf β w ψ M lam S (extendDefault k₀ (X.biUnion id) y)| ≤ C S :=
        hC S hS _ (extendDefault_mem hk₀ hy)
    _ ≤ |C S| := le_abs_self _
    _ ≤ ∑ S ∈ X, |C S| := Finset.single_le_sum (fun S _ => abs_nonneg (C S)) hS

theorem ModelHyp.measurable_modelHierarchicalDensity (h : ModelHyp ρ β w ψ K)
    (X : Finset (Finset ℕ)) :
    Measurable fun y : X.biUnion id → ℂ × ℂ =>
      ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        hierBlockWeight β w ψ M lam X S y) :=
  Finset.measurable_prod _ fun S _ => ENNReal.measurable_ofReal.comp
    ((h.measurable_hierBlockWeight M lam X S).const_mul _)

/-- `𝖯_X` is a finite measure. -/
theorem ModelHyp.isFiniteMeasure_modelHierarchical (h : ModelHyp ρ β w ψ K)
    (X : Finset (Finset ℕ)) : IsFiniteMeasure (modelHierarchical ρ β w ψ M lam X) := by
  have := h.isProbabilityMeasure
  obtain ⟨C, hC⟩ := h.exists_bound_hierBlockWeight (M := M) (lam := lam) X
  rw [modelHierarchical_eq]
  refine isFiniteMeasure_withDensity ?_
  have hle : ∀ᵐ y ∂(Measure.pi fun _ : X.biUnion id => ρ),
      ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        hierBlockWeight β w ψ M lam X S y) ≤
        ∏ S ∈ X, ENNReal.ofReal (|(modelPartitionFunction ρ β w ψ M lam S)⁻¹| * C) := by
    filter_upwards [ae_pi_mem (ι := X.biUnion id) h.ae_mem] with y hy
    refine Finset.prod_le_prod fun S hS => ENNReal.ofReal_le_ofReal ?_
    calc (modelPartitionFunction ρ β w ψ M lam S)⁻¹ * hierBlockWeight β w ψ M lam X S y
        ≤ |(modelPartitionFunction ρ β w ψ M lam S)⁻¹ * hierBlockWeight β w ψ M lam X S y| :=
          le_abs_self _
      _ = |(modelPartitionFunction ρ β w ψ M lam S)⁻¹| *
            |hierBlockWeight β w ψ M lam X S y| := abs_mul _ _
      _ ≤ |(modelPartitionFunction ρ β w ψ M lam S)⁻¹| * C := by
        gcongr
        exact hC S hS y hy
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hle) ?_)
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.prod_lt_top fun S _ => ENNReal.ofReal_lt_top

/-- A measurable function bounded on the configurations with all dipoles in `K` is integrable
against `𝖯_X`. -/
theorem ModelHyp.integrable_modelHierarchical (h : ModelHyp ρ β w ψ K)
    {X : Finset (Finset ℕ)} {f : (X.biUnion id → ℂ × ℂ) → ℝ} (hf : Measurable f)
    (hb : ∃ C, ∀ y : X.biUnion id → ℂ × ℂ, (∀ i, y i ∈ K) → |f y| ≤ C) :
    Integrable f (modelHierarchical ρ β w ψ M lam X) := by
  have := h.isProbabilityMeasure
  have := h.isFiniteMeasure_modelHierarchical (M := M) (lam := lam) X
  obtain ⟨C, hC⟩ := hb
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  have hac : modelHierarchical ρ β w ψ M lam X ≪ Measure.pi fun _ : X.biUnion id => ρ := by
    rw [modelHierarchical_eq]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le (ae_pi_mem (ι := X.biUnion id) h.ae_mem)] with y hy
  rw [Real.norm_eq_abs]
  exact hC y hy

/-- A function of the configurations of all labels, measurable, bounded on `K^ℕ` and depending
only on the labels of `V_X`, read on `V_X`, is integrable against `𝖯_X`. -/
theorem ModelHyp.integrable_comp_extendConfig (h : ModelHyp ρ β w ψ K)
    {X : Finset (Finset ℕ)} {g : (ℕ → ℂ × ℂ) → ℝ} (hg : Measurable g) (hgb : BoundedOn K g)
    (hdep : DependsOn g ((X.biUnion id : Finset ℕ) : Set ℕ)) :
    Integrable (fun y => g (extendConfig (X.biUnion id) y))
      (modelHierarchical ρ β w ψ M lam X) := by
  obtain ⟨k₀, hk₀⟩ := h.nonempty
  obtain ⟨C, hC⟩ := hgb
  refine h.integrable_modelHierarchical (hg.comp (measurable_extendConfig _)) ⟨C, fun y hy => ?_⟩
  rw [apply_extendConfig_eq_extendDefault hdep k₀ y]
  exact hC _ (extendDefault_mem hk₀ hy)

/-! ### Invariance under the reversal of a block -/

section Flip

variable (hw₁ : ∀ d e, w d.swap e = -w d e) (hw₂ : ∀ d e, w d e.swap = -w d e)
  (hψ : ∀ d, ψ d.swap = ψ d)
include hw₁ hw₂ hψ

open scoped Classical in
/-- The density factor of a block `S ∈ X` is invariant under the reversal of the dipoles of a
block `S₀ ∈ X`. -/
theorem hierBlockWeight_flipOn {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {S₀ S : Finset ℕ} (hS₀ : S₀ ∈ X) (hS : S ∈ X) (y : X.biUnion id → ℂ × ℂ) :
    hierBlockWeight β w ψ M lam X S (flipOn Prod.swap (blockSet X S₀) y) =
      hierBlockWeight β w ψ M lam X S y := by
  have hgraph : (SimpleGraph.fromRel fun i j : X.biUnion id =>
      MultipoleLinked M lam (flipOn Prod.swap (blockSet X S₀) y i)
        (flipOn Prod.swap (blockSet X S₀) y j)) =
      SimpleGraph.fromRel fun i j : X.biUnion id => MultipoleLinked M lam (y i) (y j) :=
    congrArg SimpleGraph.fromRel
      (funext fun i => funext fun j => propext (multipoleLinked_flipOn _ y i j))
  have hprod : (∏ i : X.biUnion id, ∏ j : X.biUnion id,
      if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
        (if IsStableDipolePair (flipOn Prod.swap (blockSet X S₀) y i)
            (flipOn Prod.swap (blockSet X S₀) y j) then
          Real.exp (-β * w (flipOn Prod.swap (blockSet X S₀) y i)
            (flipOn Prod.swap (blockSet X S₀) y j)) else 0) else 1) =
      ∏ i : X.biUnion id, ∏ j : X.biUnion id,
        if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
          (if IsStableDipolePair (y i) (y j) then Real.exp (-β * w (y i) (y j)) else 0)
        else 1 := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    by_cases hij : (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j
    · rw [ite_eq_left hij, ite_eq_left hij]
      by_cases hSS : S = S₀
      · subst hSS
        rw [flipOn_apply_of_mem (mem_blockSet.2 hij.1),
          flipOn_apply_of_mem (mem_blockSet.2 hij.2.1), stableExp_swap_swap hw₁ hw₂]
      · have hd : Disjoint S S₀ := hX.2 (Finset.mem_coe.2 hS) (Finset.mem_coe.2 hS₀) hSS
        rw [flipOn_apply_of_notMem fun h => Finset.disjoint_left.1 hd hij.1 (mem_blockSet.1 h),
          flipOn_apply_of_notMem fun h => Finset.disjoint_left.1 hd hij.2.1 (mem_blockSet.1 h)]
    · rw [ite_eq_right hij, ite_eq_right hij]
  have hψprod : (∏ i : X.biUnion id,
      if (i : ℕ) ∈ S then ψ (flipOn Prod.swap (blockSet X S₀) y i) else 1) =
      ∏ i : X.biUnion id, if (i : ℕ) ∈ S then ψ (y i) else 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [flipOn_apply]
    split_ifs <;> simp [hψ]
  unfold hierBlockWeight
  rw [hgraph, hprod, hψprod]

/-- **The hierarchical model is invariant under the reversal of a block** (proof of Corollary 4.34). -/
theorem measurePreserving_flipOn_modelHierarchical (hρ : MeasurePreserving Prod.swap ρ ρ)
    [IsProbabilityMeasure ρ] {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {S₀ : Finset ℕ}
    (hS₀ : S₀ ∈ X) :
    MeasurePreserving (flipOn Prod.swap (blockSet X S₀)) (modelHierarchical ρ β w ψ M lam X)
      (modelHierarchical ρ β w ψ M lam X) := by
  rw [modelHierarchical_eq]
  refine measurePreserving_withDensity_flipOn measurable_swap Prod.swap_swap
    (measurePreserving_flipOn_pi hρ _) fun y => ?_
  exact Finset.prod_congr rfl fun S hS => by
    rw [hierBlockWeight_flipOn hw₁ hw₂ hψ hX hS₀ hS]

end Flip

/-! ### Eulerian edge sets and the parity reduction -/

section Euler

/-- The degree `deg_E(S) = ∑_{i ∈ S} deg_E(i)` of a block `S` in the edge set `E` (Definition
4.10(7)): the number of pairs of `E` with an endpoint in `S`, counted with multiplicity. -/
def blockDeg (E : Finset (ℕ × ℕ)) (S : Finset ℕ) : ℕ :=
  (E.filter fun p => p.1 ∈ S).card + (E.filter fun p => p.2 ∈ S).card

open scoped Classical in
/-- `Eul^X` (Definition 4.33): the edge sets
`E ⊆ ℰ^inter(X)` such that `deg_E(S)` is even for every block `S ∈ X`. -/
noncomputable def relEulerianPairs (X : Finset (Finset ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (interPairs X).powerset.filter fun E => ∀ S ∈ X, Even (blockDeg E S)

theorem mem_relEulerianPairs {X : Finset (Finset ℕ)} {E : Finset (ℕ × ℕ)} :
    E ∈ relEulerianPairs X ↔ E ⊆ interPairs X ∧ ∀ S ∈ X, Even (blockDeg E S) := by
  rw [relEulerianPairs, Finset.mem_filter, Finset.mem_powerset]

/-- Reversing the dipoles of `S` turns `∏_{ij ∈ E} a_ij` into `(-1)^{deg_E(S)} ∏_{ij ∈ E} a_ij`
for `a` odd in each dipole. -/
theorem prod_flipOn_of_odd' {a : ℂ × ℂ → ℂ × ℂ → ℝ} (ha₁ : ∀ d e, a d.swap e = -a d e)
    (ha₂ : ∀ d e, a d e.swap = -a d e) (E : Finset (ℕ × ℕ)) (S : Finset ℕ)
    (c : ℕ → ℂ × ℂ) :
    ∏ p ∈ E, a (flipOn Prod.swap S c p.1) (flipOn Prod.swap S c p.2) =
      (-1) ^ blockDeg E S * ∏ p ∈ E, a (c p.1) (c p.2) := by
  have hpt : ∀ p : ℕ × ℕ, a (flipOn Prod.swap S c p.1) (flipOn Prod.swap S c p.2) =
      ((if p.1 ∈ S then (-1 : ℝ) else 1) * (if p.2 ∈ S then (-1 : ℝ) else 1)) *
        a (c p.1) (c p.2) := by
    intro p
    simp only [flipOn_apply]
    split_ifs <;> simp [ha₁, ha₂]
  rw [Finset.prod_congr rfl fun p _ => hpt p, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_ite, Finset.prod_ite, Finset.prod_const_one, Finset.prod_const_one,
    Finset.prod_const, Finset.prod_const, mul_one, mul_one, blockDeg, pow_add]

/-- Reversing the dipoles of `S` does not change `∏_{ij ∈ E} b_ij` for `b` even in each dipole. -/
theorem prod_flipOn_of_even' {b : ℂ × ℂ → ℂ × ℂ → ℝ} (hb₁ : ∀ d e, b d.swap e = b d e)
    (hb₂ : ∀ d e, b d e.swap = b d e) (E : Finset (ℕ × ℕ)) (S : Finset ℕ)
    (c : ℕ → ℂ × ℂ) :
    ∏ p ∈ E, b (flipOn Prod.swap S c p.1) (flipOn Prod.swap S c p.2) =
      ∏ p ∈ E, b (c p.1) (c p.2) := by
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [flipOn_apply]
  split_ifs <;> simp [hb₁, hb₂]

/-- Reading a configuration of `V_X` on all labels commutes with the reversal of a block. -/
theorem extendConfig_flipOn {X : Finset (Finset ℕ)} {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X)
    (y : X.biUnion id → ℂ × ℂ) :
    extendConfig (X.biUnion id) (flipOn Prod.swap (blockSet X S₀) y) =
      flipOn Prod.swap S₀ (extendConfig (X.biUnion id) y) := by
  funext i
  simp only [extendConfig, flipOn_apply, mem_blockSet]
  by_cases hi : i ∈ X.biUnion id
  · simp [hi]
  · have : i ∉ S₀ := fun h => hi (subset_biUnion_of_mem hS₀ h)
    simp [hi, this]

variable (hw₁ : ∀ d e, w d.swap e = -w d e) (hw₂ : ∀ d e, w d e.swap = -w d e)
  (hψ : ∀ d, ψ d.swap = ψ d) (hρ : MeasurePreserving Prod.swap ρ ρ)
include hw₁ hw₂ hψ hρ

/-- **Lemma 4.32 for the hierarchical model**: if some block `S₀ ∈ X` has odd degree in `E₁`, the
expectation of `∏_{E₁} a ∏_{E₂} b G` vanishes (`a` odd, `b` even, `G` invariant). -/
theorem integral_eq_zero_of_odd_blockDeg [IsProbabilityMeasure ρ] {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X) {E₁ E₂ : Finset (ℕ × ℕ)}
    (hodd : Odd (blockDeg E₁ S₀)) {a b : ℂ × ℂ → ℂ × ℂ → ℝ}
    (ha₁ : ∀ d e, a d.swap e = -a d e) (ha₂ : ∀ d e, a d e.swap = -a d e)
    (hb₁ : ∀ d e, b d.swap e = b d e) (hb₂ : ∀ d e, b d e.swap = b d e)
    {G : (ℕ → ℂ × ℂ) → ℝ} (hG : ∀ c, G (flipOn Prod.swap S₀ c) = G c) :
    ∫ y, (∏ p ∈ E₁, a (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
        (∏ p ∈ E₂, b (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
        G (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X = 0 := by
  set f : (X.biUnion id → ℂ × ℂ) → ℝ := fun y =>
    (∏ p ∈ E₁, a (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
      (∏ p ∈ E₂, b (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
      G (extendConfig (X.biUnion id) y) with hf
  have hmp := measurePreserving_flipOn_modelHierarchical (β := β) (M := M) (lam := lam) hw₁ hw₂
    hψ hρ hX hS₀
  have hcomp : ∫ y, f (flipOn Prod.swap (blockSet X S₀) y) ∂modelHierarchical ρ β w ψ M lam X =
      ∫ y, f y ∂modelHierarchical ρ β w ψ M lam X :=
    hmp.integral_comp (flipOnEquiv measurable_swap Prod.swap_swap _).measurableEmbedding f
  have hneg : ∀ y, f (flipOn Prod.swap (blockSet X S₀) y) = -f y := by
    intro y
    simp only [hf, extendConfig_flipOn hS₀, prod_flipOn_of_odd' ha₁ ha₂,
      prod_flipOn_of_even' hb₁ hb₂, hG, hodd.neg_one_pow]
    ring
  simp_rw [hneg, integral_neg] at hcomp
  linarith

/-- **The parity reduction** (Lemma 4.32, Corollary 4.34): for `E ⊆ ℰ^inter(X)`, odd parts `a`
and even parts `b` of the bonds, and a factor `G` invariant under the reversal of each block,
`𝔼_{𝖯_X}[∏_{ij ∈ E} (a_ij + b_ij) G] = ∑_{E₁ ⊆ E, E₁ ∈ Eul^X} 𝔼_{𝖯_X}[∏_{E₁} a ∏_{E ∖ E₁} b G]`. -/
theorem integral_prod_add_mul_eq_sum_relEulerian [IsProbabilityMeasure ρ]
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {E : Finset (ℕ × ℕ)}
    (hE : E ⊆ interPairs X) {a b : ℂ × ℂ → ℂ × ℂ → ℝ}
    (ha₁ : ∀ d e, a d.swap e = -a d e) (ha₂ : ∀ d e, a d e.swap = -a d e)
    (hb₁ : ∀ d e, b d.swap e = b d e) (hb₂ : ∀ d e, b d e.swap = b d e)
    {G : (ℕ → ℂ × ℂ) → ℝ} (hG : ∀ S ∈ X, ∀ c, G (flipOn Prod.swap S c) = G c)
    (hint : ∀ E₁ ⊆ E, Integrable (fun y =>
      (∏ p ∈ E₁, a (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
        (∏ p ∈ E \ E₁,
          b (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
        G (extendConfig (X.biUnion id) y)) (modelHierarchical ρ β w ψ M lam X)) :
    ∫ y, (∏ p ∈ E, (a (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2) +
        b (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2))) *
        G (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X =
      ∑ E₁ ∈ E.powerset.filter (· ∈ relEulerianPairs X),
        ∫ y, (∏ p ∈ E₁,
            a (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
          (∏ p ∈ E \ E₁,
            b (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
          G (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X := by
  classical
  simp_rw [Finset.prod_add, Finset.sum_mul]
  rw [integral_finsetSum _ fun E₁ hE₁ => hint E₁ (Finset.mem_powerset.1 hE₁)]
  rw [← Finset.sum_filter_add_sum_filter_not E.powerset (· ∈ relEulerianPairs X)]
  rw [Finset.sum_eq_zero (s := E.powerset.filter fun E₁ => E₁ ∉ relEulerianPairs X)
    fun E₁ hE₁ => ?_, add_zero]
  rw [Finset.mem_filter, Finset.mem_powerset] at hE₁
  have hE₁X : E₁ ⊆ interPairs X := hE₁.1.trans hE
  rw [mem_relEulerianPairs] at hE₁
  push Not at hE₁
  obtain ⟨S₀, hS₀, hodd⟩ := hE₁.2 hE₁X
  rw [Nat.not_even_iff_odd] at hodd
  exact integral_eq_zero_of_odd_blockDeg hw₁ hw₂ hψ hρ hX hS₀ hodd ha₁ ha₂ hb₁ hb₂ (hG S₀ hS₀)

end Euler

end Hierarchical

end MultipoleBKT

end
