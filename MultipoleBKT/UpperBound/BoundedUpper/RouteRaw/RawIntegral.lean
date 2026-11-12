/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Regroup

/-!
# Integrating the raw parity expansion

The paper: Corollary 5.24, and Proposition 5.18. Begin with the nested raw identity, apply block reversal
inside its terms and integrate the surviving marked terms. The extra
regrouping is used only by the coefficient-one sum bound.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity NonEmptyMarks
open scoped Classical

/-- Successive measure-preserving averages keep the integral unchanged. -/
theorem integral_reversalAverage {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (τ : ι → α → α) (Ss : List ι)
    (hτ : ∀ S ∈ Ss, MeasurePreserving (τ S) μ μ)
    (he : ∀ S ∈ Ss, MeasurableEmbedding (τ S))
    (f : α → ℝ) (hf : Integrable f μ) :
    Integrable (reversalAverage τ Ss f) μ ∧
      ∫ c, reversalAverage τ Ss f c ∂μ = ∫ c, f c ∂μ := by
  induction Ss generalizing f with
  | nil => exact ⟨hf, rfl⟩
  | cons S Ss ih =>
    have hmp := hτ S (List.mem_cons_self ..)
    have hfc : Integrable (fun c => f (τ S c)) μ := hmp.integrable_comp_of_integrable hf
    have hg := (hf.add hfc).div_const 2
    obtain ⟨hgi, hge⟩ := ih
      (fun T hT => hτ T (List.mem_cons_of_mem S hT))
      (fun T hT => he T (List.mem_cons_of_mem S hT)) _ hg
    simp only [Pi.add_apply] at hge
    refine ⟨hgi, hge.trans ?_⟩
    rw [integral_div]
    change (∫ c, f c + f (τ S c) ∂μ) / 2 = _
    rw [integral_add hf hfc, hmp.integral_comp (he S (List.mem_cons_self ..))]
    ring

/-- Extending a configuration intertwines the same block reversals. -/
theorem reversalAverage_extend (X : Finset (Finset ℕ)) (Ss : List (Finset ℕ))
    (hSs : ∀ S ∈ Ss, S ∈ X) (f : (ℕ → ℂ × ℂ) → ℝ) :
    (fun y => reversalAverage (flipOn Prod.swap) Ss f (extendConfig (X.biUnion id) y)) =
      reversalAverage (fun S => flipOn Prod.swap (blockSet X S)) Ss
        (fun y => f (extendConfig (X.biUnion id) y)) := by
  induction Ss generalizing f with
  | nil => rfl
  | cons S Ss ih =>
    simp only [reversalAverage]
    rw [ih (fun T hT => hSs T (List.mem_cons_of_mem S hT))]
    have hc : (fun y => (f (extendConfig (X.biUnion id) y) +
        f (extendConfig (X.biUnion id) (flipOn Prod.swap (blockSet X S) y))) / 2) =
        (fun y => (f (extendConfig (X.biUnion id) y) +
          f (flipOn Prod.swap S (extendConfig (X.biUnion id) y))) / 2) := by
      funext y
      rw [extendConfig_flipOn (hSs S (List.mem_cons_self ..))]
    rw [hc]

variable {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ L : ℝ}
  {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- Integrability of one raw term under the original model. -/
theorem integrable_rawTerm (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {X : Finset (Finset ℕ)} {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {F : Finset (ℕ × ℕ)} (hF : F ⊆ interPairs (coarsen X (univ.image Xs))) :
    Integrable (fun y => clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
        (extendConfig (X.biUnion id) y) *
      ∏ i ∈ X.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)))
      (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  obtain ⟨hm, hb⟩ := externalBondZ_regular (p₀ := p₀) (β := β)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  apply h.integrable_comp_extendConfig
    ((measurable_clusterTerm β _ M lam h Xs Es F).mul
      (measurable_prod _ fun i _ => measurable_const.add (hm.comp (measurable_pi_apply i))))
    ((boundedOn_clusterTerm β _ M lam h Xs Es F).mul
      (BoundedOn.prod _ fun i _ => (BoundedOn.const _ 1).add (BoundedOn.single hb i)))
  intro c c' hcc'
  simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  rw [dependsOn_clusterTerm β _ M lam hXs hEs hF hcc']
  congr 1
  exact prod_congr rfl fun i hi => by rw [hcc' i hi]

/-- The activity starts with the raw integrand and its marked reversal projection. -/
theorem plusActivity_eq_integral_rawProjectedSum (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card)
    (hM0 : ∀ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≠ 0) :
    plusActivity χ N p₀ β lam M ε₀ L V Z X =
      ∫ y, rawProjectedSum χ p₀ β lam M ε₀ V Z X (extendConfig (X.biUnion id) y)
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  let μ := plusModel χ N p₀ β lam M ε₀ L V Z X
  have hint : ∀ (n : ℕ) Xs,
      Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      Integrable (fun y => clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
          (extendConfig (X.biUnion id) y) *
        ∏ i ∈ X.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z
          (extendConfig (X.biUnion id) y i))) μ := by
    intro n Xs hXs Es hEs F hF
    exact integrable_rawTerm hχ hlam hε₀ hN
      (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hXs).1 l))
      (fun l => (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1) (mem_relEdgeSets₀.1 hF).1
  have hi : Integrable (fun y => rawIntegrand χ p₀ β lam M ε₀ V Z X
      (extendConfig (X.biUnion id) y)) μ :=
    integrable_finsetSum _ fun n _ => (integrable_finsetSum _ fun Xs hXs =>
      integrable_finsetSum _ fun Es hEs => integrable_finsetSum _ fun F hF =>
        hint n Xs hXs Es hEs F hF).const_mul _
  have hraw : plusActivity χ N p₀ β lam M ε₀ L V Z X =
      ∫ y, rawIntegrand χ p₀ β lam M ε₀ V Z X (extendConfig (X.biUnion id) y) ∂μ := by
    rw [plusActivity_eq_raw hχ hlam hε₀ hN hX h2 hM0]
    unfold rawIntegrand
    rw [integral_finsetSum _ fun n _ => (integrable_finsetSum _ fun Xs hXs =>
      integrable_finsetSum _ fun Es hEs => integrable_finsetSum _ fun F hF =>
        hint n Xs hXs Es hEs F hF).const_mul _]
    apply sum_congr rfl
    intro n _
    rw [integral_const_mul]
    apply congrArg (fun a : ℝ => 1 / (n.factorial : ℝ) * a)
    rw [integral_finsetSum _ fun Xs hXs => integrable_finsetSum _ fun Es hEs =>
      integrable_finsetSum _ fun F hF => hint n Xs hXs Es hEs F hF]
    apply sum_congr rfl
    intro Xs hXs
    rw [integral_finsetSum _ fun Es hEs => integrable_finsetSum _ fun F hF =>
      hint n Xs hXs Es hEs F hF]
    apply sum_congr rfl
    intro Es hEs
    rw [integral_finsetSum _ fun F hF => hint n Xs hXs Es hEs F hF]
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hmp : ∀ S ∈ X.toList, MeasurePreserving
      (flipOn Prod.swap (blockSet X S)) μ μ := by
    intro S hS
    exact measurePreserving_flipOn_modelHierarchical
      (fun d e => interactionGoodZ_swap_left d e) (fun d e => interactionGoodZ_swap_right d e)
      (fun d => dipoleWeightZ_swap d) (measurePreserving_swap_cutoffDipoleMeasure hχ N p₀ β lam ε₀)
      hX (Finset.mem_toList.1 hS)
  have hproj := (integral_reversalAverage μ _ X.toList hmp
    (fun S _ => (flipOnEquiv measurable_swap Prod.swap_swap _).measurableEmbedding) _ hi).2
  rw [← reversalAverage_extend X X.toList (fun S hS => Finset.mem_toList.1 hS)] at hproj
  simp only [reversalAverage_rawIntegrand hM X] at hproj
  exact hraw.trans hproj.symm

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
