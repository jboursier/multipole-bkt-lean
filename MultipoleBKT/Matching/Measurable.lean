/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Matching.Pair
public import MultipoleBKT.Matching.RouteGeneric.Distance

/-!
# Measurability of the stable matching; distinct distances almost everywhere

Section 4.1 of the paper discusses measurability and polynomial exceptional sets.
Lemmas 4.3 and 4.5 hold almost everywhere.

* `measurableSet_stableMatching_eq`: `{c | σ_N(c) = σ}` is Borel for every permutation `σ`.
* `measurableSet_isStableDipolePair`, `measurableSet_setOf_isStableDipolePair`: the event `𝒜_ij`
  is Borel.
* `volume_setOf_not_injective_norm_sub`, `ae_injective_norm_sub`: Lebesgue-almost every
  configuration `c : ι → ℂ × ℂ` has pairwise distinct opposite-sign distances `|x_i - y_j|`
  (`ι` any finite type), so the hypothesis of Lemma 4.3 holds almost everywhere.
* `ae_nodup_norm_sub`: Lebesgue-almost every pair of dipoles has four distinct opposite-sign
  distances (the hypothesis of Lemma 4.5).
* `ae_stableMatching_eq_refl_iff`: Lemma 4.3 almost everywhere.
-/

@[expose] public section

open MeasureTheory

namespace MultipoleBKT

variable {N : ℕ}

/-! ### Measurability -/

section Measurability

theorem measurableSet_matchKey_lt (p q : Fin N × Fin N) :
    MeasurableSet {c : Fin N → ℂ × ℂ | matchKey c p < matchKey c q} := by
  simp only [matchKey_lt_matchKey_iff]
  refine measurableSet_setOfPred.2 ?_
  fun_prop

theorem measurableSet_isLexStable (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {c : Fin N → ℂ × ℂ | IsLexStable c σ} := by
  simp only [IsLexStable, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    ((measurableSet_matchKey_lt _ _).inter (measurableSet_matchKey_lt _ _)).compl

/-- The stable matching is a random variable: `{c | σ_N(c) = σ}` is Borel for every
permutation `σ` (Definition 4.1). -/
theorem measurableSet_stableMatching_eq (σ : Equiv.Perm (Fin N)) :
    MeasurableSet {c : Fin N → ℂ × ℂ | stableMatching c = σ} := by
  simp only [stableMatching_eq_iff]
  exact measurableSet_isLexStable σ

/-- The event `𝒜_ij` is Borel, as a set of pairs of dipoles. -/
theorem measurableSet_isStableDipolePair :
    MeasurableSet {p : (ℂ × ℂ) × (ℂ × ℂ) | IsStableDipolePair p.1 p.2} := by
  simp only [isStableDipolePair_iff]
  refine measurableSet_setOfPred.2 ?_
  fun_prop

/-- The event `𝒜_ij` (equation (4.2)) is Borel, as a set of
configurations. -/
theorem measurableSet_setOf_isStableDipolePair {ι : Type*} (i j : ι) :
    MeasurableSet {c : ι → ℂ × ℂ | IsStableDipolePair (c i) (c j)} := by
  simp only [isStableDipolePair_iff]
  refine measurableSet_setOfPred.2 ?_
  fun_prop

end Measurability

/-! ### Distinct distances almost everywhere -/

section AE

/-- The measurable equivalence `c ↦ (x, y)` from configurations `ι → ℂ × ℂ` to
`ι ⊕ ι → ℂ` (`inl i ↦ x_i`, `inr i ↦ y_i`). -/
noncomputable def configEquivSum (ι : Type*) [Fintype ι] : (ι → ℂ × ℂ) ≃ᵐ (ι ⊕ ι → ℂ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ ι).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℂ).symm

theorem configEquivSum_apply_inl {ι : Type*} [Fintype ι] (c : ι → ℂ × ℂ) (i : ι) :
    configEquivSum ι c (Sum.inl i) = (c i).1 :=
  rfl

theorem configEquivSum_apply_inr {ι : Type*} [Fintype ι] (c : ι → ℂ × ℂ) (i : ι) :
    configEquivSum ι c (Sum.inr i) = (c i).2 :=
  rfl

theorem measurePreserving_configEquivSum (ι : Type*) [Fintype ι] :
    MeasurePreserving (configEquivSum ι) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm _).comp
    (volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ ι)

/-- Two distinct opposite-sign pairs are at the same distance only on a Lebesgue-null set. -/
theorem volume_setOf_norm_sub_eq_norm_sub_pair {ι : Type*} [Fintype ι] {p q : ι × ι}
    (hpq : p ≠ q) :
    volume {c : ι → ℂ × ℂ | ‖(c p.1).1 - (c p.2).2‖ = ‖(c q.1).1 - (c q.2).2‖} = 0 := by
  have h : {c : ι → ℂ × ℂ | ‖(c p.1).1 - (c p.2).2‖ = ‖(c q.1).1 - (c q.2).2‖} =
      configEquivSum ι ⁻¹' {Z : ι ⊕ ι → ℂ |
        ‖Z (Sum.inl p.1) - Z (Sum.inr p.2)‖ = ‖Z (Sum.inl q.1) - Z (Sum.inr q.2)‖} := by
    ext c
    rfl
  rw [h, (measurePreserving_configEquivSum ι).measure_preimage_equiv]
  refine RouteGeneric.volume_distance_eq Sum.inl_ne_inr Sum.inl_ne_inr ?_
  rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
  · exact hpq (Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2))
  · exact Sum.inl_ne_inr h1

/-- Lebesgue-almost every configuration has pairwise distinct opposite-sign distances
`|x_i - y_j|`: the exceptional set is null. -/
theorem volume_setOf_not_injective_norm_sub {ι : Type*} [Fintype ι] :
    volume {c : ι → ℂ × ℂ |
      ¬ Function.Injective fun p : ι × ι => ‖(c p.1).1 - (c p.2).2‖} = 0 := by
  have hsub : {c : ι → ℂ × ℂ |
      ¬ Function.Injective fun p : ι × ι => ‖(c p.1).1 - (c p.2).2‖} ⊆
      ⋃ p : ι × ι, ⋃ q : ι × ι, ⋃ (_ : p ≠ q),
        {c : ι → ℂ × ℂ | ‖(c p.1).1 - (c p.2).2‖ = ‖(c q.1).1 - (c q.2).2‖} := by
    intro c hc
    simp only [Function.Injective, not_forall, Set.mem_ofPred_eq] at hc
    obtain ⟨p, q, hpq, hne⟩ := hc
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨q, Set.mem_iUnion.2 ⟨hne, hpq⟩⟩⟩
  exact measure_mono_null hsub <| measure_iUnion_null fun p => measure_iUnion_null fun q =>
    measure_iUnion_null fun hpq => volume_setOf_norm_sub_eq_norm_sub_pair hpq

theorem ae_injective_norm_sub {ι : Type*} [Fintype ι] :
    ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)),
      Function.Injective fun p : ι × ι => ‖(c p.1).1 - (c p.2).2‖ :=
  ae_iff.2 volume_setOf_not_injective_norm_sub

/-- Lebesgue-almost every pair of dipoles has four distinct opposite-sign distances (the
hypothesis of Lemma 4.5). -/
theorem ae_nodup_norm_sub :
    ∀ᵐ p ∂(volume : Measure ((ℂ × ℂ) × (ℂ × ℂ))),
      [‖p.1.1 - p.1.2‖, ‖p.1.1 - p.2.2‖, ‖p.2.1 - p.1.2‖, ‖p.2.1 - p.2.2‖].Nodup := by
  have he := volume_preserving_piFinTwo fun _ : Fin 2 => ℂ × ℂ
  rw [← he.map_eq]
  refine (ae_map_iff he.measurable.aemeasurable ?_).2 ?_
  · refine measurableSet_setOfPred.2 ?_
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    fun_prop
  · filter_upwards [ae_injective_norm_sub (ι := Fin 2)] with c hc
    exact nodup_norm_sub_of_injective hc (i := 0) (j := 1) Fin.zero_ne_one

/-- **Lemma 4.3 almost everywhere**: for Lebesgue-almost every configuration, `σ_N = Id` if and
only if `σ₂[(x_i, x_j), (y_i, y_j)] = Id` for every `i ≠ j`. -/
theorem ae_stableMatching_eq_refl_iff :
    ∀ᵐ c ∂(volume : Measure (Fin N → ℂ × ℂ)),
      stableMatching c = Equiv.refl _ ↔ ∀ i j : Fin N, i ≠ j → IsStableDipolePair (c i) (c j) := by
  filter_upwards [ae_injective_norm_sub] with c hc
  exact lemma_4_3' hc

end AE

end MultipoleBKT

end
