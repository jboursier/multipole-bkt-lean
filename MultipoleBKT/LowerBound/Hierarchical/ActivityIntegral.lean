/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Activity
public import MultipoleBKT.Multipole.RouteGrouping.Integral

/-!
# Directly grouped activity integrals and the cluster expansion

Definition 4.15 and Steps 4–8 of proof of Lemma 4.18, for a model `(ρ, w, ψ)` satisfying `ModelHyp`.

`ModelHyp.prod_mul_modelActivity_grouped` integrates the finite expanded series
against the density of the hierarchical measure. Its coefficient is `groupWeight`,
with both edge families retained. `ModelHyp.clusterIntegralOf_eq_tsum` applies
`RouteGrouping.weighted_grouping_integral`, the direct component expansion
(4.36), and factors the integral over disjoint union components. Singleton
components contribute their multipole partition functions. Normalization gives
the activity series, including its empty-family term.

`ModelHyp.prod_mul_modelActivity` retains the compact connected-integral interface
for estimates. The starting-bound expansion uses the grouped formula directly.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

/-! ### Finiteness of the series -/

/-- More than `|X|` pairwise disjoint subfamilies of `X` contain one with at most one block. -/
theorem exists_card_le_one_of_card_lt {X : Finset (Finset ℕ)} {n : ℕ} (hn : X.card < n)
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) : ∃ l, (Xs l).card ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hpd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Xs :=
    fun i _ j _ hij => hdisj i j hij
  have h1 : (Finset.univ.biUnion Xs).card = ∑ l, (Xs l).card := Finset.card_biUnion hpd
  have h2 : (Finset.univ.biUnion Xs).card ≤ X.card :=
    Finset.card_le_card (Finset.biUnion_subset.2 fun l _ => hXs l)
  have h3 : ∑ l : Fin n, 2 ≤ ∑ l, (Xs l).card :=
    Finset.sum_le_sum fun l _ => hcon l
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
  omega

/-- The terms of the series of Definition 4.15 with more than `|X|` groups vanish: one group has
at most one block, and `𝖤^Y = ∅` for `|Y| ≤ 1`. -/
theorem sum_piFinset_relEdgeSets_eq_zero {X : Finset (Finset ℕ)} {n : ℕ} (hn : X.card < n)
    {R : Type*} [AddCommMonoid R]
    (g : (Fin n → Finset (Finset ℕ)) → (Fin n → Finset (ℕ × ℕ)) → R) :
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)), g Xs Es = 0 := by
  refine Finset.sum_eq_zero fun Xs hXs => ?_
  rw [Finset.mem_filter] at hXs
  obtain ⟨l, hl⟩ := exists_card_le_one_of_card_lt hn
    (fun l => Finset.mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)) hXs.2
  have : Fintype.piFinset (fun l => relEdgeSets (Xs l)) = ∅ :=
    Fintype.piFinset_eq_empty.2 ⟨l, relEdgeSets_eq_empty_of_card_le_one hl⟩
  rw [this, Finset.sum_empty]

/-! ### The terms of the series -/

section Terms

variable (β w M lam)

theorem measurable_mayerBondOf (h : ModelHyp ρ β w ψ K) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => mayerBondOf β w q.1 q.2 :=
  h.measurable_stableWeight.sub_const 1

open scoped Classical in
theorem measurable_clusterTerm (h : ModelHyp ρ β w ψ K) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) :
    Measurable (clusterTerm β w M lam Xs Es F) := by
  have hb : ∀ p : ℕ × ℕ, Measurable fun c : ℕ → ℂ × ℂ =>
      (if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0) := fun p =>
    Measurable.ite (measurableSet_setOf_multipoleLinked M lam p.1 p.2)
      measurable_const measurable_const
  have hb' : ∀ p : ℕ × ℕ, Measurable fun c : ℕ → ℂ × ℂ =>
      (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) := fun p =>
    Measurable.ite (measurableSet_setOf_multipoleLinked M lam p.1 p.2)
      measurable_const measurable_const
  unfold clusterTerm
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact Finset.measurable_prod _ fun p _ =>
      measurable_pairWeight (measurable_mayerBondOf β w h) p
  · exact Finset.measurable_prod _ fun p _ => hb' p
  · exact Finset.measurable_prod _ fun p _ => (hb p).neg

open scoped Classical in
theorem boundedOn_clusterTerm (h : ModelHyp ρ β w ψ K) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) :
    BoundedOn K (clusterTerm β w M lam Xs Es F) := by
  unfold clusterTerm
  refine BoundedOn.mul (BoundedOn.mul ?_ ?_) ?_
  · refine BoundedOn.prod _ fun p _ => ?_
    simp only [mayerBondOf_eq]
    exact (BoundedOn.pair h.exists_stableWeight_le p.1 p.2).sub (BoundedOn.const K 1)
  · exact BoundedOn.prod _ fun p _ => BoundedOn.ite
      (P := fun c => MultipoleLinked M lam (c p.1) (c p.2)) (BoundedOn.const K 0)
      (BoundedOn.const K 1)
  · exact BoundedOn.prod _ fun p _ => (BoundedOn.ite
      (P := fun c => MultipoleLinked M lam (c p.1) (c p.2)) (BoundedOn.const K 1)
      (BoundedOn.const K 0)).neg

/-- The pairs of a term of the series lie in `V_X`. -/
theorem dependsOn_clusterTerm {X : Finset (Finset ℕ)} {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X) {Es : Fin n → Finset (ℕ × ℕ)}
    (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) {F : Finset (ℕ × ℕ)}
    (hF : F ⊆ interPairs (coarsen X (Finset.univ.image Xs))) :
    DependsOn (clusterTerm β w M lam Xs Es F) ((X.biUnion id : Finset ℕ) : Set ℕ) := by
  have hpair : ∀ {Y : Finset (Finset ℕ)}, Y.biUnion id ⊆ X.biUnion id → ∀ p ∈ interPairs Y,
      p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun hY p hp =>
    ⟨hY (interPairs_subset_pairsOn_biUnion _ hp).1, hY (interPairs_subset_pairsOn_biUnion _ hp).2⟩
  have hXl : ∀ l, (Xs l).biUnion id ⊆ X.biUnion id := fun l =>
    Finset.biUnion_subset_biUnion_of_subset_left id (hXs l)
  have hcoarse : (coarsen X (Finset.univ.image Xs)).biUnion id ⊆ X.biUnion id := by
    rw [biUnion_coarsen fun Y hY => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
      exact hXs l]
  intro c c' hcc'
  have hc : ∀ p : ℕ × ℕ, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id →
      c p.1 = c' p.1 ∧ c p.2 = c' p.2 := fun p hp =>
    ⟨hcc' _ (Finset.mem_coe.2 hp.1), hcc' _ (Finset.mem_coe.2 hp.2)⟩
  unfold clusterTerm
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨h1, h2⟩ := hc p (hpair (hXl l) p (hEs l hpl))
    rw [h1, h2]
  · refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
    obtain ⟨h1, h2⟩ := hc p (hpair (hXl l) p hpl)
    rw [h1, h2]
  · refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := hc p (hpair hcoarse p (hF hp))
    rw [h1, h2]

open scoped Classical in
/-- A term of the series in the notation of `clusterSeries`, with `f_ij = f^w_ij` and
`b_ij = 𝟙_{𝓑_ij}`. -/
theorem clusterTerm_eq {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
    (F : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) :
    clusterTerm β w M lam Xs Es F c =
      (∏ p ∈ Finset.univ.biUnion Es, mayerBondOf β w (c p.1) (c p.2)) *
        (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
          (1 - if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)) *
        ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) := by
  unfold clusterTerm
  congr 2
  refine Finset.prod_congr rfl fun p _ => ?_
  split_ifs <;> norm_num

end Terms

/-! ### The activity as a connected integral -/

open scoped Classical in
/-- The directly grouped activity integral, (4.36) and Step 8 of the proof of Lemma 4.18. The inner sums stay expanded. -/
theorem ModelHyp.prod_mul_modelActivity_grouped (h : ModelHyp ρ β w ψ K) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card) :
    (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) * modelActivity ρ β w ψ M lam X =
      ∫ c, (∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
        groupWeight (fun p => mayerBondOf β w (c p.1) (c p.2))
          (fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) X
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
          ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
            ∂modelHierarchical ρ β w ψ M lam X =
        ∫ c, (∏ B ∈ X, blockWeightOf β w ψ M lam B c) * clusterTerm β w M lam Xs Es F c
          ∂labelField ρ := by
    intro n Xs hXs Es hEs F hF
    rw [Finset.mem_filter] at hXs
    have hXsX : ∀ l, Xs l ⊆ X := fun l => Finset.mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)
    have hEsX : ∀ l, Es l ⊆ interPairs (Xs l) := fun l =>
      (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1
    have hFX := (mem_relEdgeSets₀.1 hF).1
    have key := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := X)
      (f := fun y => clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y))
      ((measurable_clusterTerm β w M lam h Xs Es F).comp (measurable_extendConfig _))
    rw [key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only
    rw [apply_extendConfig_restrict (dependsOn_clusterTerm β w M lam hXsX hEsX hFX) c]
  -- integrability of the integrands
  have hint : ∀ {n : ℕ} (a : ℝ) (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
      (F : Finset (ℕ × ℕ)), Integrable (fun c => a *
        ((∏ B ∈ X, blockWeightOf β w ψ M lam B c) * clusterTerm β w M lam Xs Es F c))
        (labelField ρ) :=
    fun a Xs Es F => (integrable_of_boundedOn h.ae_mem
      (hbwm.mul (measurable_clusterTerm β w M lam h Xs Es F))
      (hbwb.mul (boundedOn_clusterTerm β w M lam h Xs Es F))).const_mul a
  -- the series has finitely many terms
  have hfin : modelActivity ρ β w ψ M lam X =
      ∑ n ∈ Finset.range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
                ∂modelHierarchical ρ β w ψ M lam X := by
    rw [modelActivity, ite_eq_right (by omega : ¬ X.card ≤ 1)]
    refine tsum_eq_sum fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]
  -- the series, integrated termwise
  have hseries : (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) *
        modelActivity ρ β w ψ M lam X =
      ∫ c, ∑ n ∈ Finset.range (X.card + 1),
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              1 / (n.factorial : ℝ) * ((∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
                clusterTerm β w M lam Xs Es F c) ∂labelField ρ := by
    rw [hfin, integral_finsetSum _ fun n _ => integrable_finsetSum _ fun Xs _ =>
      integrable_finsetSum _ fun Es _ => integrable_finsetSum _ fun F _ => hint _ Xs Es F,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
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
  rw [hseries]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  -- the pointwise identity
  set f : ℕ × ℕ → ℝ := fun p => mayerBondOf β w (c p.1) (c p.2) with hf
  set b : ℕ × ℕ → ℝ := fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0 with hb
  have hcs := clusterSeries_eq_groupWeight (f := f) (b := b) hX
  rw [clusterSeries, tsum_eq_sum (s := Finset.range (X.card + 1)) fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]] at hcs
  change _ = (∏ B ∈ X, blockWeightOf β w ψ M lam B c) * groupWeight f b X
  rw [← hcs]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun Xs _ =>
    Finset.sum_congr rfl fun Es _ => Finset.sum_congr rfl fun F _ => ?_
  rw [clusterTerm_eq]
  ring

/-- The compact connected integral, retained as an interface for activity estimates. -/
theorem ModelHyp.prod_mul_modelActivity (h : ModelHyp ρ β w ψ K) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card) :
    (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) * modelActivity ρ β w ψ M lam X =
      connIntegralOf ρ (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam) X := by
  classical
  rw [h.prod_mul_modelActivity_grouped hX h2, connIntegralOf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  dsimp only
  unfold connWeight
  congr 1
  rw [← relConnSum_eq_groupWeight
    (f := fun p => mayerBondOf β w (c p.1) (c p.2))
    (b := fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)
    hX le_rfl (Finset.card_pos.1 (by omega))]
  exact congrArg (fun g => relConnSum g X) (funext fun p =>
    one_add_mayerBondOf_mul_sub β w M lam (c p.1) (c p.2))

/-! ### The cluster expansion of the hierarchical model -/

open scoped Classical in
/-- Normalization of a grouped union component. Singleton components contribute their
multipole partition function, as in Step 8 of the proof of Lemma 4.18. -/
theorem ModelHyp.integral_groupWeight_eq_prod_mul (h : ModelHyp ρ β w ψ K)
    {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) (hne : Y.Nonempty) :
    (∫ c, (∏ B ∈ Y, blockWeightOf β w ψ M lam B c) *
      groupWeight (fun p => mayerBondOf β w (c p.1) (c p.2))
        (fun p => if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0) Y ∂labelField ρ) =
      (∏ S ∈ Y, modelPartitionFunction ρ β w ψ M lam S) *
        (if 2 ≤ Y.card then modelActivity ρ β w ψ M lam Y else if Y.card = 1 then 1 else 0) := by
  by_cases h2 : 2 ≤ Y.card
  · rw [ite_eq_left h2, h.prod_mul_modelActivity_grouped hY h2]
  · have h1 : Y.card = 1 := by
      have := Finset.card_pos.2 hne
      omega
    obtain ⟨B, rfl⟩ := Finset.card_eq_one.1 h1
    rw [ite_eq_right h2, ite_eq_left h1, mul_one, Finset.prod_singleton]
    simp_rw [groupWeight_singleton (hY.1 B (Finset.mem_singleton_self B)), mul_one,
      Finset.prod_singleton]
    exact (h.modelPartitionFunction_eq_integral_labelField M lam B).symm

/-- **The cluster expansion of the hierarchical model** (Steps 4–8 of proof of Lemma 4.18): for a subpartition `π`,
`𝔼_{ρ^{⊗ ℕ}}[(∏_{S ∈ π} bw_S) ∏_{ij ∈ ℰ^inter(π)} e^{-β w_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c}]
= (∏_{S ∈ π} 𝖬(S)) ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} ∏ₗ 𝖪(Xₗ)`. -/
theorem ModelHyp.clusterIntegralOf_eq_tsum (h : ModelHyp ρ β w ψ K) {π : Finset (Finset ℕ)}
    (hπ : IsSubpartition π) :
    clusterIntegralOf ρ (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam) π =
      (∏ S ∈ π, modelPartitionFunction ρ β w ψ M lam S) *
        ∑' n : ℕ, 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
              (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
            ∏ i, modelActivity ρ β w ψ M lam (Xs i) := by
  classical
  have := h.isProbabilityMeasure
  set Kₐ := modelActivity ρ β w ψ M lam
  set w' : Finset (Finset ℕ) → ℝ :=
    fun Y => if 2 ≤ Y.card then Kₐ Y else if Y.card = 1 then 1 else 0 with hw'
  -- Step 7: group the expanded pairs by their union components.
  have h1 : clusterIntegralOf ρ (blockWeightOf β w ψ M lam) (unlinkedBondOf β w M lam) π =
      (∏ S ∈ π, modelPartitionFunction ρ β w ψ M lam S) * partitionSum w' π := by
    let f := mayerBondOf β w
    let b : ℂ × ℂ → ℂ × ℂ → ℝ := fun d e => if MultipoleLinked M lam d e then 1 else 0
    have hfm := measurable_mayerBondOf β w h
    have hbm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => b q.1 q.2 :=
      Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const
    have hfb : ∀ i j, BoundedOn K fun c => f (c i) (c j) := fun i j =>
      (BoundedOn.pair h.exists_stableWeight_le i j).sub (BoundedOn.const K 1)
    have hbb : ∀ i j, BoundedOn K fun c => b (c i) (c j) := fun i j =>
      BoundedOn.ite (P := fun c => MultipoleLinked M lam (c i) (c j))
        (BoundedOn.const K 1) (BoundedOn.const K 0)
    have hpoint : ∀ c, clusterWeight (blockWeightOf β w ψ M lam)
        (unlinkedBondOf β w M lam) π c =
        (∏ B ∈ π, blockWeightOf β w ψ M lam B c) *
          ∏ p ∈ interPairs π, ((1 + f (c p.1) (c p.2)) * (1 - b (c p.1) (c p.2))) := by
      intro c
      unfold clusterWeight
      congr 1
      exact Finset.prod_congr rfl fun p _ => by
        have hp := one_add_mayerBondOf_mul_sub β w M lam (c p.1) (c p.2)
        dsimp only [f, b]
        linarith
    unfold clusterIntegralOf
    simp_rw [hpoint]
    rw [RouteGrouping.weighted_grouping_integral (f := f) (b := b)
      (blockWeightOf β w ψ M lam) h.ae_mem (h.measurable_blockWeightOf M lam)
      (h.boundedOn_blockWeightOf M lam) (dependsOn_blockWeightOf M lam)
      hfm hbm hfb hbb hπ]
    unfold partitionSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝒴 h𝒴 => ?_
    have h𝒴s := (mem_partitions.1 h𝒴).1
    have hY : ∀ Y ∈ 𝒴,
        (∫ c, (∏ B ∈ Y, blockWeightOf β w ψ M lam B c) *
          groupWeight (fun p => f (c p.1) (c p.2)) (fun p => b (c p.1) (c p.2)) Y ∂labelField ρ) =
          (∏ S ∈ Y, modelPartitionFunction ρ β w ψ M lam S) * w' Y := fun Y hY =>
      h.integral_groupWeight_eq_prod_mul (isSubpartition_mono hπ (subset_of_mem_partitions h𝒴 hY))
        (h𝒴s.1 Y hY)
    rw [Finset.prod_congr rfl hY, Finset.prod_mul_distrib]
    congr 1
    have := Finset.prod_biUnion (f := fun S => modelPartitionFunction ρ β w ψ M lam S) h𝒴s.2
    rw [(mem_partitions.1 h𝒴).2] at this
    exact this.symm
  -- Step 8: remove singleton components after factoring their normalizations.
  have h3 : partitionSum w' π =
      ∑ 𝒱 ∈ disjointFamilies π (fun Y => 2 ≤ Y.card), ∏ Y ∈ 𝒱, Kₐ Y :=
    (sum_disjointFamilies π (fun Y => 2 ≤ Y.card) (fun _ h => h) Kₐ).symm
  -- Order the nontrivial components and divide by their factorial.
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
      (modelActivity_eq_zero_of_card_le_one ρ β w ψ M lam (by omega)))
  have h5 := tsum_tuples_eq_sum π.powerset (fun Y => 2 ≤ Y.card)
    (fun Y h => Finset.card_pos.1 (by omega)) Kₐ
  rw [biUnion_powerset_id] at h5
  have hfilt : (disjointFamilies π (fun Y => 2 ≤ Y.card)).filter (· ⊆ π.powerset) =
      disjointFamilies π (fun Y => 2 ≤ Y.card) := by
    refine Finset.filter_true_of_mem fun 𝒱 h𝒱 Y hY => ?_
    exact Finset.mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)
  rw [hfilt] at h5
  rw [h1, h3, ← h5]
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  rw [h4 n]
  congr 1
  ext Xs
  simp only [Finset.mem_filter]

end Hierarchical

end MultipoleBKT

end
