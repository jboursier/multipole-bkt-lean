/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Field

/-!
# The activities as integrals, and the cluster expansion of a hierarchical model

Definition 4.15,
Steps 4–8 of the proof of Lemma 4.18 and the proof of
Corollary 4.61 (proof of Corollary 4.61), for a general model `(ρ, w, ψ)` (`MultipoleBKT.Hierarchical.Model`)
satisfying `ModelHyp` (a probability measure `ρ` concentrated on a set `K` of dipoles on which
`e^{-β w}` and `ψ ≥ 0` are bounded).

With the block weight `bw_B(c) = 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ B} ψ(c_i)`
(`blockWeightOf`) and the bond `u_ij = e^{-β w_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c} - 1` (`unlinkedBondOf`):

* `modelPartitionFunction_eq_integral_labelField`: `𝖬(S) = 𝔼_{ρ^{⊗ ℕ}}[bw_S]`;
* `prod_mul_integral_modelHierarchical` (density form): `(∏_{S ∈ X} 𝖬(S)) 𝔼_{𝖯_X}[f]
  = 𝔼_{ρ^{⊗ ℕ}}[(∏_{B ∈ X} bw_B) f]` (no positivity of `𝖬` is needed: if some `𝖬(S) = 0`, then
  `bw_S = 0` almost everywhere);
* `prod_mul_modelActivity`: for `|X| ≥ 2`, `(∏_{S ∈ X} 𝖬(S)) 𝖪(X)
  = 𝔼_{ρ^{⊗ ℕ}}[(∏_{B ∈ X} bw_B) ∑_{E ∈ 𝖤^X} ∏_{ij ∈ E} u_ij]`: the series of Definition 4.15 has
  finitely many nonzero terms, may be integrated termwise, and its integrand is the compact form
  (`MultipoleBKT.Hierarchical.clusterSeries_eq_sum_relEdgeSets`);
* `clusterIntegralOf_eq_tsum` (**the cluster expansion of the hierarchical model**, Steps 4–8 of
  Lemma 4.18): for a subpartition `π`,
  `𝔼_{ρ^{⊗ ℕ}}[(∏_{S ∈ π} bw_S) ∏_{ij ∈ ℰ^inter(π)} e^{-β w_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c}]
  = (∏_{S ∈ π} 𝖬(S)) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪(Xₗ)`.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

/-! ### Hypotheses on a model -/

/-- The hypotheses under which the integrals of the model `(ρ, w, ψ)` are well behaved: `ρ` is a
probability measure concentrated on a set `K` of dipoles; `w` and `ψ` are measurable, `ψ ≥ 0`,
and `-β w` and `ψ` are bounded above on `K`. -/
structure ModelHyp (ρ : Measure (ℂ × ℂ)) (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ)
    (K : Set (ℂ × ℂ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ρ
  ae_mem : ∀ᵐ p ∂ρ, p ∈ K
  measurable_w : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2
  measurable_ψ : Measurable ψ
  nonneg_ψ : ∀ d, 0 ≤ ψ d
  bdd_w : ∃ C, ∀ d ∈ K, ∀ e ∈ K, -β * w d e ≤ C
  bdd_ψ : ∃ C, ∀ d ∈ K, ψ d ≤ C

/-! ### Pair and block weights -/

section Weights

variable (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)

open scoped Classical in
/-- The pair weight `e^{-β w_ij} 𝟙_{𝒜_ij}` of two dipoles (the lower label first). -/
noncomputable def stableWeight (d e : ℂ × ℂ) : ℝ :=
  if IsStableDipolePair d e then Real.exp (-β * w d e) else 0

open scoped Classical in
/-- The bond `e^{-β w_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c} - 1 = (1 + f^w_ij)(1 - 𝟙_{𝓑_ij}) - 1`. -/
noncomputable def unlinkedBondOf (d e : ℂ × ℂ) : ℝ :=
  (if MultipoleLinked M lam d e then 0 else stableWeight β w d e) - 1

open scoped Classical in
/-- The block weight `𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ B} ψ(c_i)` at a
configuration of all labels. -/
noncomputable def blockWeightOf (B : Finset ℕ) (c : ℕ → ℂ × ℂ) : ℝ :=
  (if ConnOn B (linkedPairs M lam c B) then 1 else 0) *
    (∏ p ∈ pairsOn B, stableWeight β w (c p.1) (c p.2)) * ∏ i ∈ B, ψ (c i)

open scoped Classical in
/-- The integrand of `modelPartitionFunction`. -/
noncomputable def partitionIntegrand {S : Finset ℕ} (y : S → ℂ × ℂ) : ℝ :=
  (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (y i) (y j)).Connected
    then 1 else 0) *
  (∏ i : S, ∏ j : S,
    if i < j then
      (if IsStableDipolePair (y i) (y j) then Real.exp (-β * w (y i) (y j)) else 0)
    else 1) *
  ∏ i : S, ψ (y i)

open scoped Classical in
/-- The factor of the block `S ∈ X` in the density of `modelHierarchical`. -/
noncomputable def hierBlockWeight (X : Finset (Finset ℕ)) (S : Finset ℕ)
    (y : X.biUnion id → ℂ × ℂ) : ℝ :=
  (if ((SimpleGraph.fromRel fun i j : X.biUnion id =>
        MultipoleLinked M lam (y i) (y j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected
      then 1 else 0) *
    (∏ i : X.biUnion id, ∏ j : X.biUnion id,
      if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
        (if IsStableDipolePair (y i) (y j) then Real.exp (-β * w (y i) (y j)) else 0)
      else 1) *
    ∏ i : X.biUnion id, if (i : ℕ) ∈ S then ψ (y i) else 1

theorem modelPartitionFunction_eq (ρ : Measure (ℂ × ℂ)) (S : Finset ℕ) :
    modelPartitionFunction ρ β w ψ M lam S =
      ∫ y, partitionIntegrand β w ψ M lam (S := S) y ∂Measure.pi fun _ : S => ρ := rfl

theorem modelHierarchical_eq (ρ : Measure (ℂ × ℂ)) (X : Finset (Finset ℕ)) :
    modelHierarchical ρ β w ψ M lam X =
      (Measure.pi fun _ : X.biUnion id => ρ).withDensity fun y =>
        ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
          hierBlockWeight β w ψ M lam X S y) := rfl

theorem mayerBondOf_eq (d e : ℂ × ℂ) : mayerBondOf β w d e = stableWeight β w d e - 1 := rfl

open scoped Classical in
/-- `(1 + f^w_ij)(1 - 𝟙_{𝓑_ij}) - 1 = e^{-β w_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c} - 1`. -/
theorem one_add_mayerBondOf_mul_sub (d e : ℂ × ℂ) :
    (1 + mayerBondOf β w d e) * (1 - if MultipoleLinked M lam d e then 1 else 0) - 1 =
      unlinkedBondOf β w M lam d e := by
  rw [mayerBondOf_eq, unlinkedBondOf]
  split_ifs <;> ring

theorem stableWeight_nonneg (d e : ℂ × ℂ) : 0 ≤ stableWeight β w d e := by
  unfold stableWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

open scoped Classical in
theorem blockWeightOf_eq (B : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    blockWeightOf β w ψ M lam B c = partitionIntegrand β w ψ M lam (B.restrict c) := by
  unfold blockWeightOf partitionIntegrand
  congr 1
  · congr 1
    · exact if_congr (connected_fromRel_iff c B).symm rfl rfl
    · exact (prod_prod_ite_lt (U := B) fun i j => stableWeight β w (c i) (c j)).symm
  · exact (Finset.prod_coe_sort B fun i => ψ (c i)).symm

open scoped Classical in
theorem hierBlockWeight_restrict {X : Finset (Finset ℕ)} {S : Finset ℕ} (hS : S ∈ X)
    (c : ℕ → ℂ × ℂ) :
    hierBlockWeight β w ψ M lam X S ((X.biUnion id).restrict c) = blockWeightOf β w ψ M lam S c := by
  have hSV : S ⊆ X.biUnion id := subset_biUnion_of_mem hS
  unfold hierBlockWeight blockWeightOf
  congr 1
  · congr 1
    · exact if_congr (connected_induce_iff c hSV) rfl rfl
    · exact prod_prod_ite_mem_lt hSV fun i j => stableWeight β w (c i) (c j)
  · have h1 : ∏ i : X.biUnion id, (if (i : ℕ) ∈ S then ψ (c i) else 1) =
        ∏ i ∈ X.biUnion id, (if i ∈ S then ψ (c i) else 1) :=
      Finset.prod_coe_sort (X.biUnion id) fun i => if i ∈ S then ψ (c i) else 1
    simp only [Finset.restrict]
    rw [h1, ← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hSV]

end Weights

/-! ### Measurability, bounds, nonnegativity -/

section Bounds

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} (M lam : ℝ)

theorem ModelHyp.measurable_stableWeight (h : ModelHyp ρ β w ψ K) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => stableWeight β w q.1 q.2 := by
  unfold stableWeight
  exact Measurable.ite measurableSet_isStableDipolePair
    (Real.measurable_exp.comp (measurable_const.mul h.measurable_w)) measurable_const

theorem ModelHyp.measurable_stableWeight_apply (h : ModelHyp ρ β w ψ K) {ι : Type*} (i j : ι) :
    Measurable fun y : ι → ℂ × ℂ => stableWeight β w (y i) (y j) :=
  Measurable.comp (g := fun q : (ℂ × ℂ) × (ℂ × ℂ) => stableWeight β w q.1 q.2)
    (f := fun y : ι → ℂ × ℂ => (y i, y j)) h.measurable_stableWeight
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

theorem ModelHyp.measurable_unlinkedBondOf (h : ModelHyp ρ β w ψ K) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => unlinkedBondOf β w M lam q.1 q.2 := by
  unfold unlinkedBondOf
  exact (Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const
    h.measurable_stableWeight).sub_const 1

theorem ModelHyp.measurable_partitionIntegrand (h : ModelHyp ρ β w ψ K) {S : Finset ℕ} :
    Measurable (partitionIntegrand β w ψ M lam (S := S)) := by
  unfold partitionIntegrand
  refine Measurable.mul (Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
    measurable_const measurable_const) ?_) ?_
  · refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases hij : i < j
    · simp only [hij, ite_true]
      exact h.measurable_stableWeight_apply i j
    · simp only [hij, ite_false]
      exact measurable_const
  · exact Finset.measurable_prod _ fun i _ => h.measurable_ψ.comp (measurable_pi_apply i)

theorem ModelHyp.measurable_blockWeightOf (h : ModelHyp ρ β w ψ K) (B : Finset ℕ) :
    Measurable (blockWeightOf β w ψ M lam B) := by
  have := (h.measurable_partitionIntegrand M lam (S := B)).comp
    (Finset.measurable_restrict (X := fun _ : ℕ => ℂ × ℂ) B)
  convert this using 1
  funext c
  exact blockWeightOf_eq β w ψ M lam B c

theorem ModelHyp.measurable_hierBlockWeight (h : ModelHyp ρ β w ψ K) (X : Finset (Finset ℕ))
    (S : Finset ℕ) : Measurable (hierBlockWeight β w ψ M lam X S) := by
  unfold hierBlockWeight
  refine Measurable.mul (Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam
      (fun G => (G.induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected))
    measurable_const measurable_const) ?_) ?_
  · refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases hij : (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j
    · simp only [hij, and_self, ite_true]
      exact h.measurable_stableWeight_apply i j
    · simp only [hij, ite_false]
      exact measurable_const
  · refine Finset.measurable_prod _ fun i _ => ?_
    by_cases hi : (i : ℕ) ∈ S
    · simp only [hi, ite_true]
      exact h.measurable_ψ.comp (measurable_pi_apply i)
    · simp only [hi, ite_false]
      exact measurable_const

theorem dependsOn_blockWeightOf (B : Finset ℕ) :
    DependsOn (blockWeightOf β w ψ M lam B) (B : Set ℕ) := by
  intro c c' hcc'
  rw [blockWeightOf_eq, blockWeightOf_eq]
  congr 1
  funext i
  exact hcc' i (Finset.mem_coe.2 i.2)

theorem blockWeightOf_nonneg (hψ : ∀ d, 0 ≤ ψ d) (B : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    0 ≤ blockWeightOf β w ψ M lam B c := by
  unfold blockWeightOf
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun p _ =>
    stableWeight_nonneg β w _ _)) (Finset.prod_nonneg fun i _ => hψ _)

theorem partitionIntegrand_nonneg (hψ : ∀ d, 0 ≤ ψ d) {S : Finset ℕ} (y : S → ℂ × ℂ) :
    0 ≤ partitionIntegrand β w ψ M lam y := by
  unfold partitionIntegrand
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => ?_)) (Finset.prod_nonneg fun i _ => hψ _)
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl
  · exact zero_le_one

theorem hierBlockWeight_nonneg (hψ : ∀ d, 0 ≤ ψ d) (X : Finset (Finset ℕ)) (S : Finset ℕ)
    (y : X.biUnion id → ℂ × ℂ) : 0 ≤ hierBlockWeight β w ψ M lam X S y := by
  unfold hierBlockWeight
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => ?_)) (Finset.prod_nonneg fun i _ => ?_)
  · split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
    · exact zero_le_one
  · split_ifs
    · exact hψ _
    · exact zero_le_one

theorem ModelHyp.exists_stableWeight_le (h : ModelHyp ρ β w ψ K) :
    ∃ C, ∀ d ∈ K, ∀ e ∈ K, |stableWeight β w d e| ≤ C := by
  obtain ⟨C, hC⟩ := h.bdd_w
  refine ⟨Real.exp C, fun d hd e he => ?_⟩
  rw [abs_of_nonneg (stableWeight_nonneg β w d e)]
  unfold stableWeight
  split_ifs
  · exact Real.exp_le_exp.2 (hC d hd e he)
  · exact (Real.exp_pos _).le

theorem ModelHyp.exists_abs_ψ_le (h : ModelHyp ρ β w ψ K) : ∃ C, ∀ d ∈ K, |ψ d| ≤ C := by
  obtain ⟨C, hC⟩ := h.bdd_ψ
  exact ⟨C, fun d hd => by rw [abs_of_nonneg (h.nonneg_ψ d)]; exact hC d hd⟩

open scoped Classical in
theorem ModelHyp.boundedOn_blockWeightOf (h : ModelHyp ρ β w ψ K) (B : Finset ℕ) :
    BoundedOn K (blockWeightOf β w ψ M lam B) := by
  unfold blockWeightOf
  exact ((BoundedOn.ite (BoundedOn.const K 1) (BoundedOn.const K 0)).mul
    (BoundedOn.prod _ fun p _ => BoundedOn.pair h.exists_stableWeight_le p.1 p.2)).mul
    (BoundedOn.prod _ fun i _ => BoundedOn.single h.exists_abs_ψ_le i)

open scoped Classical in
theorem ModelHyp.boundedOn_unlinkedBondOf (h : ModelHyp ρ β w ψ K) (i j : ℕ) :
    BoundedOn K fun c => unlinkedBondOf β w M lam (c i) (c j) := by
  unfold unlinkedBondOf
  exact (BoundedOn.ite (BoundedOn.const K 0)
    (BoundedOn.pair h.exists_stableWeight_le i j)).sub (BoundedOn.const K 1)

theorem ModelHyp.integrable_blockWeightOf (h : ModelHyp ρ β w ψ K) (B : Finset ℕ) :
    Integrable (blockWeightOf β w ψ M lam B) (labelField ρ) := by
  have := h.isProbabilityMeasure
  exact integrable_of_boundedOn h.ae_mem (h.measurable_blockWeightOf M lam B)
    (h.boundedOn_blockWeightOf M lam B)

/-- `𝖬(S) = 𝔼_{ρ^{⊗ ℕ}}[bw_S]`. -/
theorem ModelHyp.modelPartitionFunction_eq_integral_labelField (h : ModelHyp ρ β w ψ K)
    (S : Finset ℕ) :
    modelPartitionFunction ρ β w ψ M lam S = ∫ c, blockWeightOf β w ψ M lam S c ∂labelField ρ := by
  have := h.isProbabilityMeasure
  rw [modelPartitionFunction_eq, integral_pi_eq_integral_labelField
    (h.measurable_partitionIntegrand M lam)]
  simp_rw [blockWeightOf_eq]

theorem ModelHyp.modelPartitionFunction_nonneg (h : ModelHyp ρ β w ψ K) (S : Finset ℕ) :
    0 ≤ modelPartitionFunction ρ β w ψ M lam S :=
  integral_nonneg fun y => partitionIntegrand_nonneg M lam h.nonneg_ψ y

end Bounds

/-! ### The density form of the hierarchical model -/

section Density

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

/-- **The hierarchical model in density form**: for a family of blocks `X` and a measurable `f`,
`(∏_{S ∈ X} 𝖬(S)) 𝔼_{𝖯_X}[f] = 𝔼_{ρ^{⊗ ℕ}}[(∏_{B ∈ X} bw_B) f]`. -/
theorem ModelHyp.prod_mul_integral_modelHierarchical (h : ModelHyp ρ β w ψ K)
    {X : Finset (Finset ℕ)} {f : (X.biUnion id → ℂ × ℂ) → ℝ} (hf : Measurable f) :
    (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) *
        ∫ y, f y ∂modelHierarchical ρ β w ψ M lam X =
      ∫ c, (∏ B ∈ X, blockWeightOf β w ψ M lam B c) * f ((X.biUnion id).restrict c)
        ∂labelField ρ := by
  have := h.isProbabilityMeasure
  have hMnn := h.modelPartitionFunction_nonneg M lam
  have hdm : Measurable fun y : X.biUnion id → ℂ × ℂ =>
      ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        hierBlockWeight β w ψ M lam X S y) :=
    Finset.measurable_prod _ fun S _ => ENNReal.measurable_ofReal.comp
      ((h.measurable_hierBlockWeight M lam X S).const_mul _)
  rw [modelHierarchical_eq, integral_withDensity_eq_integral_toReal_smul hdm
    (Filter.Eventually.of_forall fun y => ENNReal.prod_lt_top fun S _ => ENNReal.ofReal_lt_top)]
  have hdens : ∀ y : X.biUnion id → ℂ × ℂ,
      (∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        hierBlockWeight β w ψ M lam X S y)).toReal =
      ∏ S ∈ X, ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
        hierBlockWeight β w ψ M lam X S y) := by
    intro y
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun S _ => ENNReal.toReal_ofReal (mul_nonneg ?_ ?_)
    · exact inv_nonneg.2 (hMnn S)
    · exact hierBlockWeight_nonneg M lam h.nonneg_ψ X S y
  simp_rw [hdens, smul_eq_mul, Finset.prod_mul_distrib]
  rw [← integral_const_mul]
  have hg : Measurable fun y : X.biUnion id → ℂ × ℂ =>
      (∏ S ∈ X, hierBlockWeight β w ψ M lam X S y) * f y :=
    (Finset.measurable_prod _ fun S _ => h.measurable_hierBlockWeight M lam X S).mul hf
  by_cases hM0 : ∀ S ∈ X, modelPartitionFunction ρ β w ψ M lam S ≠ 0
  · have hcancel : ∀ y : X.biUnion id → ℂ × ℂ,
        (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) *
          ((∏ S ∈ X, (modelPartitionFunction ρ β w ψ M lam S)⁻¹) *
            (∏ S ∈ X, hierBlockWeight β w ψ M lam X S y) * f y) =
          (∏ S ∈ X, hierBlockWeight β w ψ M lam X S y) * f y := by
      intro y
      rw [← mul_assoc, ← mul_assoc, ← Finset.prod_mul_distrib,
        Finset.prod_congr rfl fun S hS => mul_inv_cancel₀ (hM0 S hS), Finset.prod_const_one,
        one_mul]
    simp_rw [hcancel]
    rw [integral_pi_eq_integral_labelField hg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only
    rw [Finset.prod_congr rfl fun S hS => hierBlockWeight_restrict β w ψ M lam hS c]
  · push Not at hM0
    obtain ⟨S₀, hS₀, hS₀0⟩ := hM0
    rw [Finset.prod_eq_zero hS₀ hS₀0]
    simp only [zero_mul, integral_zero]
    symm
    have hae : blockWeightOf β w ψ M lam S₀ =ᵐ[labelField ρ] 0 := by
      have hint := h.integrable_blockWeightOf M lam S₀
      have h0 : ∫ c, blockWeightOf β w ψ M lam S₀ c ∂labelField ρ = 0 := by
        rw [← h.modelPartitionFunction_eq_integral_labelField M lam S₀, hS₀0]
      exact (integral_eq_zero_iff_of_nonneg
        (fun c => blockWeightOf_nonneg M lam h.nonneg_ψ S₀ c) hint).1 h0
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with c hc
    rw [Finset.prod_eq_zero hS₀ hc, zero_mul]
    rfl

end Density

end Hierarchical

end MultipoleBKT

end
