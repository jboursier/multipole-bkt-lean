/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.PlusModel
public import MultipoleBKT.Multipole.RouteGrouping.Marks

/-!
# Direct marked expansion of the good part

The paper: Step 5 of Lemma 5.16. Expand the Mayer edges, the separation factors between their
components, and the external marks. Group the two edge families by the components
of their union, retaining marks on unused multipoles.

* `prod_mul_markedSeries_grouped` integrates each marked term with the density
  of the original hierarchical model, before any external normalization.
* `prod_plusPartitionFunction_mul_plusActivity_grouped` sums the retained marks
  inside a nontrivial union component, giving the paper's `𝒰(X)`.
* `clusterIntegralOf_hat_eq_partitionSum_grouped` groups the full marked
  integrand and integrates independently over all union components.
* `clusterIntegralOf_hat_eq` reads a singleton component as its unused external
  normalization and a nontrivial component as its marked activity. Factoring
  `𝖬̂^{+,Z}` and ordering the components yields `W(Z)`.

`hatPartitionFunction_eq` identifies the external normalization with the block
integral, and the positivity results justify its use in later bounds.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

open Hierarchical Multipole SetPartition Parity

/-! ### The marked series of a generic model -/

section Marked

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

open scoped Classical in
/-- **The marked series as a directly grouped integral**: for a subpartition `X` with `|X| ≥ 2` and a
bounded measurable factor `m` depending on the dipoles of `V_X`,
`(∏_{S ∈ X} 𝖬(S)) ∑_{n} (1/n!) ∑_{Xₗ, Eₗ, F} 𝔼_{𝖯_X}[(term) m]
= 𝔼_{ρ^{⊗ ℕ}}[(∏_{B ∈ X} bw_B) groupWeight(X) m]`. -/
theorem prod_mul_markedSeries_grouped (h : ModelHyp ρ β w ψ K) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (_h2 : 2 ≤ X.card) {m : (ℕ → ℂ × ℂ) → ℝ} (hmm : Measurable m)
    (hmb : BoundedOn K m) (hmd : DependsOn m ((X.biUnion id : Finset ℕ) : Set ℕ)) :
    (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) *
        ∑' n : ℕ, 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
              (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
            ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
              ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
                ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) *
                    m (extendConfig (X.biUnion id) y)
                  ∂modelHierarchical ρ β w ψ M lam X =
      ∫ c, (∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
          groupWeight (fun p => mayerBondOf β w (c p.1) (c p.2))
            (fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) X * m c
        ∂labelField ρ := by
  classical
  have := h.isProbabilityMeasure
  have hbwm : Measurable fun c => ∏ B ∈ X, blockWeightOf β w ψ M lam B c :=
    Finset.measurable_prod _ fun B _ => h.measurable_blockWeightOf M lam B
  have hbwb : BoundedOn K fun c => ∏ B ∈ X, blockWeightOf β w ψ M lam B c :=
    BoundedOn.prod _ fun B _ => h.boundedOn_blockWeightOf M lam B
  -- each term of the series, integrated in density form
  have hterm : ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)),
      Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
      (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) *
          ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) *
              m (extendConfig (X.biUnion id) y)
            ∂modelHierarchical ρ β w ψ M lam X =
        ∫ c, (∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
            (clusterTerm β w M lam Xs Es F c * m c) ∂labelField ρ := by
    intro n Xs hXs Es hEs F hF
    rw [Finset.mem_filter] at hXs
    have hXsX : ∀ l, Xs l ⊆ X := fun l => Finset.mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)
    have hEsX : ∀ l, Es l ⊆ interPairs (Xs l) := fun l =>
      (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1
    have hFX := (mem_relEdgeSets₀.1 hF).1
    have hdep : DependsOn (fun c => clusterTerm β w M lam Xs Es F c * m c)
        ((X.biUnion id : Finset ℕ) : Set ℕ) := by
      intro c c' hcc'
      simp only
      rw [dependsOn_clusterTerm β w M lam hXsX hEsX hFX hcc', hmd hcc']
    have key := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := X)
      (f := fun y => clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) *
        m (extendConfig (X.biUnion id) y))
      (((measurable_clusterTerm β w M lam h Xs Es F).mul hmm).comp (measurable_extendConfig _))
    rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only
    rw [apply_extendConfig_restrict hdep c]
  -- integrability of the integrands
  have hint : ∀ {n : ℕ} (a : ℝ) (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
      (F : Finset (ℕ × ℕ)), Integrable (fun c => a *
        ((∏ B ∈ X, blockWeightOf β w ψ M lam B c) * (clusterTerm β w M lam Xs Es F c * m c)))
        (labelField ρ) :=
    fun a Xs Es F => (integrable_of_boundedOn h.ae_mem
      (hbwm.mul ((measurable_clusterTerm β w M lam h Xs Es F).mul hmm))
      (hbwb.mul ((boundedOn_clusterTerm β w M lam h Xs Es F).mul hmb))).const_mul a
  -- the series has finitely many terms
  have hfin : ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) *
                  m (extendConfig (X.biUnion id) y)
                ∂modelHierarchical ρ β w ψ M lam X =
      ∑ n ∈ Finset.range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) *
                  m (extendConfig (X.biUnion id) y)
                ∂modelHierarchical ρ β w ψ M lam X := by
    refine tsum_eq_sum fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]
  -- the series, integrated termwise
  rw [hfin, Finset.mul_sum]
  have hseries : ∀ n ∈ Finset.range (X.card + 1),
      (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) * (1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) *
                  m (extendConfig (X.biUnion id) y)
                ∂modelHierarchical ρ β w ψ M lam X) =
      ∫ c, ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              1 / (n.factorial : ℝ) * ((∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
                (clusterTerm β w M lam Xs Es F c * m c)) ∂labelField ρ := by
    intro n _
    rw [integral_finsetSum _ fun Xs _ => integrable_finsetSum _ fun Es _ =>
      integrable_finsetSum _ fun F _ => hint _ Xs Es F, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Xs hXs => ?_
    rw [integral_finsetSum _ fun Es _ => integrable_finsetSum _ fun F _ => hint _ Xs Es F,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Es hEs => ?_
    rw [integral_finsetSum _ fun F _ => hint _ Xs Es F, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [integral_const_mul, ← hterm n Xs hXs Es hEs F hF]
    ring
  rw [Finset.sum_congr rfl hseries, ← integral_finsetSum _ fun n _ =>
    integrable_finsetSum _ fun Xs _ => integrable_finsetSum _ fun Es _ =>
      integrable_finsetSum _ fun F _ => hint _ Xs Es F]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  -- the pointwise identity
  set f : ℕ × ℕ → ℝ := fun p => mayerBondOf β w (c p.1) (c p.2) with hf
  set b : ℕ × ℕ → ℝ := fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0 with hb
  have hcs := clusterSeries_eq_groupWeight (f := f) (b := b) hX
  rw [clusterSeries, tsum_eq_sum (s := Finset.range (X.card + 1)) fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]] at hcs
  change _ = (∏ B ∈ X, blockWeightOf β w ψ M lam B c) * groupWeight f b X * m c
  rw [← hcs]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun Xs _ =>
    Finset.sum_congr rfl fun Es _ => Finset.sum_congr rfl fun F _ => ?_
  rw [clusterTerm_eq]
  ring

end Marked

/-! ### The frozen-bad-point model -/

section Plus

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-- The block weight of the model `ψ̂` is that of the model `ψ` times `∏_{i ∈ B} (1 + f_{i∞})`. -/
theorem blockWeightOf_hat (B : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z)
        M lam B c =
      blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z)
          M lam B c * ∏ i ∈ B, (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i)) := by
  unfold blockWeightOf
  simp_rw [hatDipoleWeightZ_eq, Finset.prod_mul_distrib]
  ring

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

/-- **`𝖬̂^{+,Z}_{ε₀}(S)`** is the partition function of the model `(μ_{β,λ,ε₀}, v^Z, ψ̂)`. -/
theorem hatPartitionFunction_eq (S : Finset ℕ) :
    hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S =
      modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
        (interactionGoodZ χ p₀ β lam ε₀ V Z) (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam S := by
  classical
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have h' := modelHyp_hat (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have hf : Measurable fun y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ =>
      Real.exp (-β * ∑ i : ({S} : Finset (Finset ℕ)).biUnion id,
        ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j) :=
    Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ =>
        (measurable_interactionExtZ p₀ β lam ε₀ V Z hχ hlam j).comp (measurable_pi_apply i)))
  have key := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := {S}) hf
  rw [Finset.prod_singleton] at key
  unfold hatPartitionFunction externalNormalization plusModel plusPartitionFunction
  rw [key, h'.modelPartitionFunction_eq_integral_labelField]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [Finset.prod_singleton]
  rw [blockWeightOf_hat]
  congr 1
  have hsum : ∑ i : ({S} : Finset (Finset ℕ)).biUnion id,
      ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (((({S} : Finset (Finset ℕ)).biUnion id).restrict
        c) i) j = ∑ i ∈ S, ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (c i) j := by
    have hr : ∀ i : ({S} : Finset (Finset ℕ)).biUnion id,
        (({S} : Finset (Finset ℕ)).biUnion id).restrict c i = c i := fun i => rfl
    simp_rw [hr]
    rw [Finset.sum_coe_sort (({S} : Finset (Finset ℕ)).biUnion id)
      (fun i => ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (c i) j)]
    simp
  rw [hsum, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [one_add_externalBondZ, Finset.mul_sum, Real.exp_sum]

/-- Measurability and a bound for the external bond on the good-dipole carrier. -/
theorem externalBondZ_regular : Measurable (externalBondZ χ p₀ β lam ε₀ V Z) ∧
    ∃ B, ∀ d ∈ supportSet N p₀ β lam ε₀, |externalBondZ χ p₀ β lam ε₀ V Z d| ≤ B := by
  have hext : ∃ B, ∀ d ∈ supportSet N p₀ β lam ε₀, |externalBondZ χ p₀ β lam ε₀ V Z d| ≤ B := by
    obtain ⟨C, hC⟩ := (modelHyp_hat (p₀ := p₀) (β := β) (M := 0) (L := 0) (V := V) (Z := Z)
      hχ hlam hε₀ hN).bdd_ψ
    obtain ⟨B, hB⟩ := exists_abs_interactionExtZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
      (Z := Z) hχ hlam
    refine ⟨∏ _j ∈ V, Real.exp (|β| * B) + 1, fun d hd => ?_⟩
    unfold externalBondZ
    have hp : 0 ≤ ∏ j ∈ V, Real.exp (-β * interactionExtZ χ p₀ β lam ε₀ V Z d j) :=
      Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
    have hle : ∏ j ∈ V, Real.exp (-β * interactionExtZ χ p₀ β lam ε₀ V Z d j) ≤
        ∏ _j ∈ V, Real.exp (|β| * B) := by
      refine Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun j hj =>
        Real.exp_le_exp.2 ?_
      calc -β * interactionExtZ χ p₀ β lam ε₀ V Z d j
          ≤ |-β * interactionExtZ χ p₀ β lam ε₀ V Z d j| := le_abs_self _
        _ = |β| * |interactionExtZ χ p₀ β lam ε₀ V Z d j| := by rw [abs_mul, abs_neg]
        _ ≤ |β| * B := mul_le_mul_of_nonneg_left (hB d hd j hj) (abs_nonneg β)
    rw [abs_le]
    constructor <;> linarith
  have hextm : Measurable (externalBondZ χ p₀ β lam ε₀ V Z) := by
    unfold externalBondZ
    exact (Finset.measurable_prod _ fun j _ => Real.measurable_exp.comp (measurable_const.mul
      (measurable_interactionExtZ p₀ β lam ε₀ V Z hχ hlam j))).sub_const 1
  exact ⟨hextm, hext⟩

open scoped Classical in
/-- The marked activity integral with both edge families retained, Step 5 of
Lemma 5.16, the paper. -/
theorem prod_plusPartitionFunction_mul_plusActivity_grouped {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card) :
    (∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
        plusActivity χ N p₀ β lam M ε₀ L V Z X =
      ∫ c, (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
        groupWeight (fun p => mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c p.1) (c p.2))
          (fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) X *
        ∏ i ∈ X.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i))
        ∂labelField (cutoffDipoleMeasure χ N p₀ β lam ε₀) := by
  classical
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  set K := supportSet N p₀ β lam ε₀
  obtain ⟨hextm, hext⟩ := externalBondZ_regular (p₀ := p₀) (β := β)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  have hmark : ∀ U ⊆ X.biUnion id,
      (∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
          ∑' n : ℕ, 1 / (n.factorial : ℝ) *
            ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
                (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
              ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
                ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
                  ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
                      (extendConfig (X.biUnion id) y) *
                    ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
                    ∂plusModel χ N p₀ β lam M ε₀ L V Z X =
        ∫ c, (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
            (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
          groupWeight (fun p => mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
            (c p.1) (c p.2)) (fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) X *
          ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (c i)
          ∂labelField (cutoffDipoleMeasure χ N p₀ β lam ε₀) := by
    intro U hU
    refine prod_mul_markedSeries_grouped h hX h2 (m := fun c => ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z
      (c i)) (Finset.measurable_prod _ fun i _ => hextm.comp (measurable_pi_apply i))
      (BoundedOn.prod _ fun i _ => BoundedOn.single hext i) ?_
    intro c c' hcc'
    simp only
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hcc' i (Finset.mem_coe.2 (hU hi))]
  have hint : ∀ U ∈ (X.biUnion id).powerset, Integrable (fun c =>
      (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
        groupWeight (fun p => mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (c p.1) (c p.2)) (fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) X *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (c i))
      (labelField (cutoffDipoleMeasure χ N p₀ β lam ε₀)) := by
    intro U _
    have hfm := measurable_mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) h
    have hbm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
        if MultipoleLinked M lam q.1 q.2 then (1 : ℝ) else 0 :=
      Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const
    have hfb : ∀ i j, BoundedOn K fun c =>
        mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c i) (c j) := fun i j =>
      (BoundedOn.pair h.exists_stableWeight_le i j).sub (BoundedOn.const K 1)
    have hbb : ∀ i j, BoundedOn K fun c =>
        if MultipoleLinked M lam (c i) (c j) then (1 : ℝ) else 0 := fun i j =>
      BoundedOn.ite (P := fun c => MultipoleLinked M lam (c i) (c j))
        (BoundedOn.const K 1) (BoundedOn.const K 0)
    exact integrable_of_boundedOn h.ae_mem
      (((Finset.measurable_prod _ fun B _ => h.measurable_blockWeightOf M lam B).mul
        (RouteGrouping.measurable_groupWeight
          (f := mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z))
          (b := fun d e => if MultipoleLinked M lam d e then 1 else 0) hfm hbm X)).mul
        (Finset.measurable_prod _ fun i _ => hextm.comp (measurable_pi_apply i)))
      (((BoundedOn.prod _ fun B _ => h.boundedOn_blockWeightOf M lam B).mul
        (RouteGrouping.boundedOn_groupWeight
          (f := mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z))
          (b := fun d e => if MultipoleLinked M lam d e then 1 else 0) hfb hbb X)).mul
        (BoundedOn.prod _ fun i _ => BoundedOn.single hext i))
  rw [plusActivity, ite_eq_right (by omega), Finset.mul_sum,
    Finset.sum_congr rfl fun U hU => hmark U (Finset.mem_powerset.1 hU),
    ← integral_finsetSum _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  dsimp only
  rw [← Finset.mul_sum, ← Finset.prod_one_add]

open scoped Classical in
/-- Direct marked grouping of `W'(Z)` by the components of `E ∪ F`, retaining the
marks on unused singleton blocks. This is Step 5 of Lemma 5.16,
the paper. -/
theorem clusterIntegralOf_hat_eq_partitionSum_grouped {π : Finset (Finset ℕ)}
    (hπ : IsSubpartition π) :
    clusterIntegralOf (cutoffDipoleMeasure χ N p₀ β lam ε₀)
        (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam)
        (unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam) π =
      partitionSum (RouteGrouping.markedComponentIntegral (cutoffDipoleMeasure χ N p₀ β lam ε₀)
        (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam)
        (mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z))
        (fun d e => if MultipoleLinked M lam d e then 1 else 0)
        (externalBondZ χ p₀ β lam ε₀ V Z)) π := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  let f := mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
  let b : ℂ × ℂ → ℂ × ℂ → ℝ := fun d e => if MultipoleLinked M lam d e then 1 else 0
  have hfm := measurable_mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) h
  have hbm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => b q.1 q.2 :=
    Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const
  have hfb : ∀ i j, BoundedOn (supportSet N p₀ β lam ε₀) fun c => f (c i) (c j) := fun i j =>
    (BoundedOn.pair h.exists_stableWeight_le i j).sub (BoundedOn.const _ 1)
  have hbb : ∀ i j, BoundedOn (supportSet N p₀ β lam ε₀) fun c => b (c i) (c j) := fun i j =>
    BoundedOn.ite (P := fun c => MultipoleLinked M lam (c i) (c j))
      (BoundedOn.const _ 1) (BoundedOn.const _ 0)
  obtain ⟨hmm, hmb⟩ := externalBondZ_regular (p₀ := p₀) (β := β) (V := V) (Z := Z) hχ hlam hε₀ hN
  have hpoint : ∀ c, clusterWeight
      (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam)
      (unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam) π c =
      ((∏ B ∈ π, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
        ∏ p ∈ interPairs π, ((1 + f (c p.1) (c p.2)) * (1 - b (c p.1) (c p.2)))) *
        ∏ i ∈ π.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i)) := by
    intro c
    unfold clusterWeight
    simp_rw [blockWeightOf_hat, Finset.prod_mul_distrib]
    have he := Finset.prod_biUnion
      (f := fun i => 1 + externalBondZ χ p₀ β lam ε₀ V Z (c i)) hπ.2
    dsimp only [id_eq] at he
    rw [← he]
    have hp : ∏ p ∈ interPairs π, (1 + unlinkedBondOf β
        (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)) =
        ∏ p ∈ interPairs π, ((1 + f (c p.1) (c p.2)) * (1 - b (c p.1) (c p.2))) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      have ht := one_add_mayerBondOf_mul_sub β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        M lam (c p.1) (c p.2)
      dsimp only [f, b]
      linarith
    rw [hp, Finset.prod_mul_distrib]
    ring
  unfold clusterIntegralOf
  simp_rw [hpoint]
  exact RouteGrouping.marked_grouping_integral (f := f) (b := b)
    (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam)
    (externalBondZ χ p₀ β lam ε₀ V Z) h.ae_mem (h.measurable_blockWeightOf M lam)
    (h.boundedOn_blockWeightOf M lam) (dependsOn_blockWeightOf M lam) hfm hbm hfb hbb hmm hmb hπ

/-- **The expansion of `W'(Z)`** (Step 5 of Lemma 5.16): for a subpartition `π`,
`𝔼_{μ^{⊗ ℕ}}[(∏_{S ∈ π} bŵ_S) ∏_{ij ∈ ℰ^inter(π)} e^{-β v^Z_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c}]
= 𝖬̂^{+,Z}_{ε₀}(π) W(Z)`. -/
theorem clusterIntegralOf_hat_eq {π : Finset (Finset ℕ)} (hπ : IsSubpartition π) :
    clusterIntegralOf (cutoffDipoleMeasure χ N p₀ β lam ε₀)
        (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam)
        (unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam) π =
      hatPartitionFunctions χ N p₀ β lam M ε₀ L V Z π * clusterSeriesW χ N p₀ β lam M ε₀ L V Z π := by
  classical
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have h' := modelHyp_hat (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  by_cases h0 : ∀ S ∈ π, hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≠ 0
  · let A := RouteGrouping.markedComponentIntegral (cutoffDipoleMeasure χ N p₀ β lam ε₀)
      (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam)
      (mayerBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z))
      (fun d e => if MultipoleLinked M lam d e then 1 else 0)
      (externalBondZ χ p₀ β lam ε₀ V Z)
    let Kₐ := hatActivity χ N p₀ β lam M ε₀ L V Z
    let w' := fun Y => if 2 ≤ Y.card then Kₐ Y else if Y.card = 1 then 1 else 0
    have h1 : partitionSum A π =
        hatPartitionFunctions χ N p₀ β lam M ε₀ L V Z π * partitionSum w' π := by
      unfold partitionSum hatPartitionFunctions
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun 𝒴 h𝒴 => ?_
      have heq : ∀ Y ∈ 𝒴, A Y =
          (∏ S ∈ Y, hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S) * w' Y := by
        intro Y hY
        have hYπ := subset_of_mem_partitions h𝒴 hY
        have hYs := isSubpartition_mono hπ hYπ
        have hne := (mem_partitions.1 h𝒴).1.1 Y hY
        by_cases h2 : 2 ≤ Y.card
        · have hg : ∏ S ∈ Y, externalNormalization χ N p₀ β lam M ε₀ L V Z S ≠ 0 :=
            Finset.prod_ne_zero_iff.2 fun S hS => right_ne_zero_of_mul (h0 S (hYπ hS))
          change _ = (∏ S ∈ Y, hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S) *
            (if 2 ≤ Y.card then hatActivity χ N p₀ β lam M ε₀ L V Z Y else _)
          rw [ite_eq_left h2]
          dsimp only [A, RouteGrouping.markedComponentIntegral]
          rw [← prod_plusPartitionFunction_mul_plusActivity_grouped hχ hlam hε₀ hN hYs h2]
          simp only [hatPartitionFunction, Finset.prod_mul_distrib, hatActivity]
          field_simp
        · have hcard : Y.card = 1 := by have := Finset.card_pos.2 hne; omega
          obtain ⟨S, rfl⟩ := Finset.card_eq_one.1 hcard
          have hS := hYs.1 S (Finset.mem_singleton_self S)
          dsimp only [A, w', Kₐ]
          rw [ite_eq_right h2, ite_eq_left hcard, mul_one, Finset.prod_singleton]
          unfold RouteGrouping.markedComponentIntegral
          simp_rw [groupWeight_singleton hS, Finset.prod_singleton, mul_one,
            Finset.singleton_biUnion, id_eq]
          rw [hatPartitionFunction_eq hχ hlam hε₀ hN,
            h'.modelPartitionFunction_eq_integral_labelField]
          exact integral_congr_ae (Filter.Eventually.of_forall fun c => (blockWeightOf_hat S c).symm)
      rw [Finset.prod_congr rfl heq, Finset.prod_mul_distrib]
      congr 1
      have hp := Finset.prod_biUnion
        (f := fun S => hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S) (mem_partitions.1 h𝒴).1.2
      rw [(mem_partitions.1 h𝒴).2] at hp
      exact hp.symm
    -- step 2: disjoint families
    have h3 : partitionSum w' π =
        ∑ 𝒱 ∈ disjointFamilies π (fun Y => 2 ≤ Y.card), ∏ Y ∈ 𝒱, Kₐ Y :=
      (sum_disjointFamilies π (fun Y => 2 ≤ Y.card) (fun _ h => h) Kₐ).symm
    -- step 3: the tuples
    have h4 : ∀ n : ℕ, ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)), ∏ i, Kₐ (Xs i) =
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card),
          ∏ i, Kₐ (Xs i) := by
      intro n
      rw [← Finset.filter_filter]
      refine (Finset.sum_filter_of_ne fun Xs _ hne => fun i => ?_).symm
      by_contra hlt
      exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
        (hatActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z (by omega)))
    have h5 := tsum_tuples_eq_sum π.powerset (fun Y => 2 ≤ Y.card)
      (fun Y h => Finset.card_pos.1 (by omega)) Kₐ
    rw [biUnion_powerset_id] at h5
    have hfilt : (disjointFamilies π (fun Y => 2 ≤ Y.card)).filter (· ⊆ π.powerset) =
        disjointFamilies π (fun Y => 2 ≤ Y.card) := by
      refine Finset.filter_true_of_mem fun 𝒱 h𝒱 Y hY => ?_
      exact Finset.mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)
    rw [hfilt] at h5
    rw [clusterIntegralOf_hat_eq_partitionSum_grouped hχ hlam hε₀ hN hπ, h1]
    unfold clusterSeriesW
    rw [h3, ← h5]
    congr 1
    refine tsum_congr fun n => ?_
    congr 1
    rw [h4 n]
    congr 1
    ext Xs
    simp only [Finset.mem_filter]

  · -- The total definitions also cover a vanishing normalization.
    push Not at h0
    obtain ⟨S, hS, hS0⟩ := h0
    rw [h'.clusterIntegralOf_eq_tsum hπ]
    simp_rw [← hatPartitionFunction_eq hχ hlam hε₀ hN]
    unfold hatPartitionFunctions
    rw [Finset.prod_eq_zero hS hS0, zero_mul, zero_mul]

end Plus

/-! ### Positivity -/

section Positivity

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}
variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

theorem plusPartitionFunction_nonneg (S : Finset ℕ) :
    0 ≤ plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
  (modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN).modelPartitionFunction_nonneg
    M lam S

theorem hatPartitionFunction_nonneg (S : Finset ℕ) :
    0 ≤ hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
  rw [hatPartitionFunction_eq hχ hlam hε₀ hN]
  exact (modelHyp_hat (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀
    hN).modelPartitionFunction_nonneg M lam S

end Positivity

end UpperBound

end MultipoleBKT

end
