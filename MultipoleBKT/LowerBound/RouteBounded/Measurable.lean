/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.RawBounds
public import MultipoleBKT.UpperBound.BoundedUpper.Proposition

/-!
# Measurability and null sets for the grouped lower reduction

The proof of Proposition 4.23. The finite tree sum is measurable and dipole radii are
positive outside the diagonal null set.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical

/-- The separate hatted tree expression is measurable. -/
theorem measurable_hatTreeCore (M lam : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id)) :
    Measurable (hatTreeCore M lam X Xs Ta Tb) := by
  unfold hatTreeCore
  refine (((measurable_jTail X Xs Ta).mul
    (Finset.measurable_prod _ fun l _ => measurable_radialExceptMax _)).mul ?_).mul ?_
  · apply Finset.measurable_prod
    intro l _
    apply Finset.measurable_prod
    intro e _
    induction e using Sym2.ind with
    | h i j =>
      change Measurable fun c : ℕ → ℂ × ℂ =>
        if MultipoleLinked M lam (c i) (c j) then 0 else (dipoleDist (c i) (c j) ^ 2)⁻¹
      exact Measurable.ite (measurableSet_setOf_multipoleLinked M lam (i : ℕ) (j : ℕ)) measurable_const
        ((measurable_dipoleDist_apply i j).pow_const 2).inv
  · apply Finset.measurable_prod
    intro e _
    induction e using Sym2.ind with
    | h i j =>
      change Measurable fun c : ℕ → ℂ × ℂ => hatEven M lam (c i) (c j)
      unfold hatEven
      apply Measurable.ite (measurableSet_setOf_multipoleLinked M lam (i : ℕ) (j : ℕ)) measurable_const
      unfold ahat
      apply Measurable.pow_const
      exact (((measurable_pi_apply (i : ℕ)).fst.sub (measurable_pi_apply (i : ℕ)).snd).norm.mul
        ((measurable_pi_apply (j : ℕ)).fst.sub (measurable_pi_apply (j : ℕ)).snd).norm).div
        ((measurable_dipoleDist_apply i j).mul ((measurable_dipoleDist_apply i j).max
          (((measurable_pi_apply (i : ℕ)).fst.sub (measurable_pi_apply (i : ℕ)).snd).norm.max
            ((measurable_pi_apply (j : ℕ)).fst.sub (measurable_pi_apply (j : ℕ)).snd).norm)))

/-- The grouped parity term is a measurable function of the labels. -/
theorem measurable_eulerTerm {ρ : Measure (ℂ × ℂ)} {β : ℝ}
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}
    (h : ModelHyp ρ β w ψ K) (M lam : ℝ) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (A B F : Finset (ℕ × ℕ)) :
    Measurable (eulerTerm β w M lam Xs A B F) := by
  have ho : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => oddBond β w q.1 q.2 := by
    unfold oddBond
    exact Measurable.ite measurableSet_isStableDipolePair
      (Real.continuous_sinh.measurable.comp (measurable_const.mul h.measurable_w)).neg measurable_const
  have he : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => evenBond β w q.1 q.2 := by
    unfold evenBond
    exact Measurable.ite measurableSet_isStableDipolePair
      ((Real.continuous_cosh.measurable.comp (measurable_const.mul h.measurable_w)).sub_const 1) measurable_const
  have hs := measurable_prod_pair (s := univ.biUnion fun l => interPairs (Xs l))
    (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
    (measurable_unlinkedIndicator M lam)
  have hf := measurable_prod_pair (s := F)
    (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
    (measurable_negLinkedIndicator M lam)
  exact (((measurable_prod_pair (s := A) ho).mul (measurable_prod_pair (s := B) he)).mul hs).mul hf

/-- Almost every dipole has a positive radius. -/
theorem ae_radius_pos : ∀ᵐ p : ℂ × ℂ, 0 < ‖p.1 - p.2‖ := by
  have h0 : (volume : Measure (ℂ × ℂ)) {p | p.1 - p.2 = 0} = 0 := by
    have hm : MeasurableSet {p : ℂ × ℂ | p.1 - p.2 = 0} :=
      (measurable_fst.sub measurable_snd) (measurableSet_singleton 0)
    rw [Measure.volume_eq_prod, Measure.prod_apply hm]
    have h1 : ∀ x : ℂ, Prod.mk x ⁻¹' {p : ℂ × ℂ | p.1 - p.2 = 0} = {x} := by
      intro x
      ext y
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, sub_eq_zero]
      exact eq_comm
    simp_rw [h1, measure_singleton, lintegral_zero]
  rw [ae_iff]
  exact measure_mono_null (fun p hp => by
    simpa only [Set.mem_ofPred_eq, not_lt, norm_le_zero_iff] using hp) h0

/-- All dipole radii are positive almost everywhere on a finite carrier. -/
theorem ae_radii_pos (I : Type*) [Fintype I] :
    ∀ᵐ y : I → ℂ × ℂ, ∀ i, 0 < ‖(y i).1 - (y i).2‖ := by
  rw [volume_pi]
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval (fun _ : I => (volume : Measure (ℂ × ℂ))) i).ae ae_radius_pos

end MultipoleBKT.LowerBound.RouteBounded

end
