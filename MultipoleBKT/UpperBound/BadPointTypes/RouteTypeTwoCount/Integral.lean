/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.ClassRecursion
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Profiles

/-!
# Decomposition by the actual multipole partition

The paper: (5.135),
and (5.141). The actual component partition is retained
in the decomposition. Dropping links between distinct blocks gives a product
of connected block integrals.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset TheoremTwo SetPartition
open scoped ENNReal Classical

variable {n : ℕ} {M lam : ℝ}

/-- The partition into the connected components on `s`. -/
noncomputable def componentPartition (M lam : ℝ) (s : Finset (Fin n))
    (c : Fin n → ℂ × ℂ) : Finset (Finset (Fin n)) := by
  classical
  exact s.image (multipoleClassOn M lam c s)

/-- The actual component family is a partition, also on the empty label set. -/
theorem componentPartition_mem (s : Finset (Fin n)) (c : Fin n → ℂ × ℂ) :
    componentPartition M lam s c ∈ partitions s := by
  classical
  rw [mem_partitions]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro T hT
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hT
    exact ⟨i, mem_classOn_self s i⟩
  · intro T hT U hU hTU
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hT
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hU
    rw [Function.onFun, disjoint_left]
    intro a ha hb
    exact hTU ((classOn_eq_of_mem ha).symm.trans (classOn_eq_of_mem hb))
  · ext i
    simp only [mem_biUnion, id_eq]
    constructor
    · rintro ⟨T, hT, hi⟩
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hT
      exact classOn_subset hj hi
    · intro hi
      exact ⟨_, mem_image_of_mem _ hi, mem_classOn_self s i⟩

/-- The exact integrand decomposition, keeping the actual component partition. -/
theorem classWeight_eq_sum_partitions (A : ℕ → Prop) (w : ℂ × ℂ → ℝ≥0∞)
    (s : Finset (Fin n)) (c : Fin n → ℂ × ℂ) :
    classWeight M lam A w s c = ∑ π ∈ partitions s,
      (if componentPartition M lam s c = π then 1 else 0) *
        (if ∀ T ∈ π, A T.card then 1 else 0) * ∏ i ∈ s, w (c i) := by
  classical
  rw [sum_eq_single (componentPartition M lam s c)]
  · simp only [ite_true, one_mul]
    unfold classWeight
    congr 2
    simp only [componentPartition, forall_mem_image]
  · intro π _ hπ
    rw [ite_eq_right (Ne.symm hπ), zero_mul, zero_mul]
  · exact fun h => (h (componentPartition_mem s c)).elim

/-- The actual component-partition sectors are measurable. -/
theorem measurableSet_componentPartition_eq (s : Finset (Fin n)) (π : Finset (Finset (Fin n))) :
    MeasurableSet {c : Fin n → ℂ × ℂ | componentPartition M lam s c = π} := by
  have h := measurableSet_setOf_graph (fun c : Fin n → ℂ × ℂ => classGraph M lam c s)
    (measurableSet_classGraph_adj M lam s)
    (fun G => s.image (fun i => univ.filter (fun j => G.Reachable i j)) = π)
  convert h using 1
  ext c
  simp only [Set.mem_ofPred_eq, componentPartition]
  suffices he : s.image (multipoleClassOn M lam c s) =
      s.image (fun i => univ.filter (fun j => (classGraph M lam c s).Reachable i j)) by
    rw [he]
    simp only [Finset.ext_iff, mem_image, mem_filter, mem_univ, true_and]
  apply image_congr
  intro i _
  ext j
  simp only [mem_classOn_iff, mem_filter, mem_univ, true_and]

/-- Split any nonnegative configuration integral into its exact component
sectors. No regularity of the weight is needed for this measurable partition. -/
theorem lintegral_eq_sum_componentPartition (s : Finset (Fin n))
    (f : (Fin n → ℂ × ℂ) → ℝ≥0∞) (μ : Measure (Fin n → ℂ × ℂ)) :
    ∫⁻ c, f c ∂μ = ∑ π ∈ partitions s, ∫⁻ c,
      (if componentPartition M lam s c = π then 1 else 0) * f c ∂μ := by
  have hc : (⋃ π ∈ partitions s, {c : Fin n → ℂ × ℂ | componentPartition M lam s c = π}) =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨componentPartition_mem s c, rfl⟩⟩
  have hd : Set.PairwiseDisjoint (↑(partitions s))
      (fun π => {c : Fin n → ℂ × ℂ | componentPartition M lam s c = π}) := by
    intro π _ ρ _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro c hπ hρ
    exact hne (hπ.symm.trans hρ)
  calc ∫⁻ c, f c ∂μ = ∫⁻ c in ⋃ π ∈ partitions s,
        {c : Fin n → ℂ × ℂ | componentPartition M lam s c = π}, f c ∂μ := by
          rw [hc, Measure.restrict_univ]
    _ = ∑ π ∈ partitions s, ∫⁻ c in
        {c : Fin n → ℂ × ℂ | componentPartition M lam s c = π}, f c ∂μ :=
          lintegral_biUnion_finset hd (fun π _ => measurableSet_componentPartition_eq s π) f
    _ = _ := by
      apply sum_congr rfl
      intro π _
      rw [← lintegral_indicator (measurableSet_componentPartition_eq s π)]
      apply lintegral_congr
      intro c
      by_cases h : componentPartition M lam s c = π <;> simp [h]

/-- Dropping the requirement that distinct blocks have no links leaves the
product of their connected weights. -/
theorem classWeight_le_partitions (A : ℕ → Prop) (w : ℂ × ℂ → ℝ≥0∞)
    (s : Finset (Fin n)) (c : Fin n → ℂ × ℂ) :
    classWeight M lam A w s c ≤ ∑ π ∈ partitions s,
      ∏ T ∈ π, (if A T.card then blockWeight M lam w (fun i : T => c i) else 0) := by
  classical
  unfold classWeight
  split_ifs with hA
  · set π := componentPartition M lam s c
    have hπ : π ∈ partitions s := componentPartition_mem s c
    refine (le_of_eq ?_).trans (single_le_sum (fun _ _ => zero_le) hπ)
    have hterm : ∀ T ∈ π,
        (if A T.card then blockWeight M lam w (fun i : T => c i) else 0) = ∏ i ∈ T, w (c i) := by
      intro T hT
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hT
      rw [ite_eq_left (hA i hi), blockWeight, ite_eq_left connected_classOn, one_mul, prod_coe_sort _ (fun i => w (c i))]
    rw [prod_congr rfl hterm, one_mul]
    symm
    calc (∏ T ∈ π, ∏ i ∈ T, w (c i)) = ∏ i ∈ π.biUnion id, w (c i) :=
          (prod_biUnion (mem_partitions.1 hπ).1.2).symm
      _ = _ := by rw [(mem_partitions.1 hπ).2]
  · rw [zero_mul]
    exact zero_le

/-- Tonelli for a fixed disjoint family of blocks. This induction integrates
fixed blocks and does not enumerate partitions recursively. -/
theorem lmarginal_prod_blocks {w : ℂ × ℂ → ℝ≥0∞} (hw : Measurable w)
    (π : Finset (Finset (Fin n))) (hπ : IsSubpartition π) (x : Fin n → ℂ × ℂ) :
    (∫⋯∫⁻_(π.biUnion id),
      (fun c => ∏ T ∈ π, blockWeight M lam w (fun i : T => c i)) ∂fun _ => volume) x =
        ∏ T ∈ π, ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y := by
  classical
  have hm (T : Finset (Fin n)) :
      Measurable fun c : Fin n → ℂ × ℂ => blockWeight M lam w (fun i : T => c i) :=
    (measurable_blockWeight M lam hw).comp
      (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  induction π using Finset.induction_on with
  | empty => simp
  | @insert T π hT ih =>
    have hπ' := isSubpartition_mono hπ (subset_insert T π)
    have hd : Disjoint (π.biUnion id) T := by
      rw [disjoint_left]
      intro i hi hiT
      obtain ⟨U, hU, hiU⟩ := mem_biUnion.1 hi
      exact disjoint_left.1 (hπ.2 (mem_insert_of_mem hU) (mem_insert_self _ _)
        (fun h => hT (h ▸ hU))) hiU hiT
    have hmπ : Measurable fun c : Fin n → ℂ × ℂ =>
        ∏ U ∈ π, blockWeight M lam w (fun i : U => c i) :=
      Finset.measurable_prod _ fun U _ => hm U
    have hmfull : Measurable (fun c : Fin n → ℂ × ℂ =>
        ∏ U ∈ insert T π, blockWeight M lam w (fun i : U => c i)) :=
      Finset.measurable_prod _ fun U _ => hm U
    rw [biUnion_insert, union_comm]
    change (∫⋯∫⁻_(π.biUnion id ∪ T), _ ∂fun _ => volume) x = _
    rw [lmarginal_union (fun _ : Fin n => (volume : Measure (ℂ × ℂ))) _ hmfull hd]
    have hint : ∀ z : Fin n → ℂ × ℂ,
        (∫⋯∫⁻_T, (fun c => ∏ U ∈ insert T π,
          blockWeight M lam w (fun i : U => c i)) ∂fun _ => volume) z =
        (∏ U ∈ π, blockWeight M lam w (fun i : U => z i)) *
          ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y := by
      intro z
      simp_rw [prod_insert hT]
      rw [show (fun c : Fin n → ℂ × ℂ => blockWeight M lam w (fun i : T => c i) *
        ∏ U ∈ π, blockWeight M lam w (fun i : U => c i)) =
        (fun c => (∏ U ∈ π, blockWeight M lam w (fun i : U => c i)) *
          blockWeight M lam w (fun i : T => c i)) from funext fun _ => mul_comm _ _]
      rw [MultipoleIntegral.lmarginal_mul_left_of_indep _ _ (hm T) ?_, lmarginal_blockWeight]
      intro a b hab
      apply prod_congr rfl
      intro U hU
      congr 1
      funext i
      exact hab i (fun hi => disjoint_left.1 hd (mem_biUnion.2 ⟨U, hU, i.2⟩) hi)
    rw [funext hint]
    have hpull : (∫⋯∫⁻_(π.biUnion id),
        (fun z => (∏ U ∈ π, blockWeight M lam w (fun i : U => z i)) *
          ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y) ∂fun _ => volume) x =
        (∫⋯∫⁻_(π.biUnion id), (fun z => ∏ U ∈ π,
          blockWeight M lam w (fun i : U => z i)) ∂fun _ => volume) x *
            ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y := by
      exact lintegral_mul_const _ (hmπ.comp
        (measurable_updateFinset (s := π.biUnion id) (x := x)))
    rw [hpull]
    rw [ih hπ', prod_insert hT, mul_comm]

/-- The integral partition decomposition after dropping interblock constraints. -/
theorem lintegral_classWeight_le_partitions (A : ℕ → Prop) {w : ℂ × ℂ → ℝ≥0∞}
    (hw : Measurable w) (B : ℕ → ℝ≥0∞)
    (hB : ∀ T : Finset (Fin n), A T.card →
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y ≤ B T.card) :
    ∫⁻ c : Fin n → ℂ × ℂ, classWeight M lam A w univ c ≤
      ∑ π ∈ partitions (univ : Finset (Fin n)), ∏ T ∈ π, if A T.card then B T.card else 0 := by
  classical
  refine (lintegral_mono fun c => classWeight_le_partitions A w univ c).trans ?_
  rw [lintegral_finsetSum _ (fun (π : Finset (Finset (Fin n))) _ => Finset.measurable_prod _ fun (T : Finset (Fin n)) _ =>
    (by
      by_cases h : A T.card
      · simp only [h, ite_true]
        exact (measurable_blockWeight M lam hw).comp
          (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
      · simp only [h, ite_false]
        exact measurable_const : Measurable fun c : Fin n → ℂ × ℂ =>
          if A T.card then blockWeight M lam w (fun i : T => c i) else 0))]
  refine sum_le_sum fun π hπ => ?_
  by_cases hA : ∀ T ∈ π, A T.card
  · simp_rw [prod_congr rfl (fun T hT => ite_eq_left (hA T hT))]
    rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => ((0 : ℂ), (0 : ℂ))),
      ← (mem_partitions.1 hπ).2, lmarginal_prod_blocks hw π (mem_partitions.1 hπ).1]
    exact prod_le_prod fun T hT => hB T (hA T hT)
  · obtain ⟨T, hT, hAT⟩ := not_forall₂.1 hA
    have hz : ∀ c : Fin n → ℂ × ℂ, (∏ U ∈ π,
        if A U.card then blockWeight M lam w (fun i : U => c i) else 0) = 0 :=
      fun c => prod_eq_zero hT (ite_eq_right hAT)
    simp_rw [hz, lintegral_zero]
    exact zero_le

end MultipoleBKT.BadPointTypes

end
