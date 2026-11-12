/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.GoodPoints
public import MultipoleBKT.Appendix.MultipoleIntegral.UpperBound

/-!
# Connected block weights and component classes

The paper: (5.135).
The components of the linking graph give the actual multipole partition.
`RouteTypeTwoCount/Integral.lean` decomposes the integral by that partition.
This module supplies the connected weight and its measurability.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset TheoremTwo
open scoped ENNReal

variable {n : ℕ} {M lam : ℝ}

/-! ### Classes on a set of labels -/

section Classes

variable {c : Fin n → ℂ × ℂ}

theorem classOn_subset {s : Finset (Fin n)} {a : Fin n} (ha : a ∈ s) :
    multipoleClassOn M lam c s a ⊆ s := fun _ hj =>
  mem_of_classGraph_reachable ha (mem_classOn_iff.1 hj)

/-- The class of `a` is closed under the links inside `s`. -/
theorem mem_classOn_of_adj {s : Finset (Fin n)} {a u v : Fin n}
    (hu : u ∈ multipoleClassOn M lam c s a) (huv : (classGraph M lam c s).Adj u v) :
    v ∈ multipoleClassOn M lam c s a :=
  mem_classOn_iff.2 ((mem_classOn_iff.1 hu).trans huv.reachable)

/-- The linking graph induced on the class of `a ∈ s` is connected. -/
theorem connected_classOn {s : Finset (Fin n)} {a : Fin n} :
    (SimpleGraph.fromRel fun i j : multipoleClassOn M lam c s a =>
      MultipoleLinked M lam (c i) (c j)).Connected := by
  set T := multipoleClassOn M lam c s a
  set G := SimpleGraph.fromRel fun i j : T => MultipoleLinked M lam (c i) (c j)
  have ha : a ∈ T := mem_classOn_self s a
  -- every vertex reachable from `a` is reachable from `a` inside `T`
  have key : ∀ v, (classGraph M lam c s).Reachable a v →
      ∃ hv : v ∈ T, G.Reachable ⟨a, ha⟩ ⟨v, hv⟩ := by
    intro v hv
    refine mem_of_reachable_of_closed
      (T := fun v => ∃ hv : v ∈ T, G.Reachable ⟨a, ha⟩ ⟨v, hv⟩)
      (fun u v ⟨hu, hreach⟩ huv => ?_) ⟨ha, SimpleGraph.Reachable.refl _⟩ hv
    have hvT : v ∈ T := mem_classOn_of_adj hu huv
    refine ⟨hvT, hreach.trans (SimpleGraph.Adj.reachable ?_)⟩
    rw [SimpleGraph.fromRel_adj] at huv ⊢
    refine ⟨fun h => huv.1 (congrArg Subtype.val h), ?_⟩
    rcases huv.2 with h' | h'
    · exact Or.inl h'.2.2
    · exact Or.inr h'.2.2
  have : Nonempty T := ⟨⟨a, ha⟩⟩
  refine ⟨fun u v => ?_⟩
  obtain ⟨_, hu⟩ := key u (mem_classOn_iff.1 u.2)
  obtain ⟨_, hv⟩ := key v (mem_classOn_iff.1 v.2)
  exact hu.symm.trans hv

end Classes

/-! ### The weights -/

/-- The weight of one block: `𝟙{the linking graph is connected} ∏_i w(y_i)`. -/
noncomputable def blockWeight (M lam : ℝ) (w : ℂ × ℂ → ℝ≥0∞) {ι : Type*} [Fintype ι]
    (y : ι → ℂ × ℂ) : ℝ≥0∞ := by
  classical
  exact (if (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (y i) (y j)).Connected then 1
    else 0) * ∏ i, w (y i)

/-- The weight of a set `s` of labels: `𝟙{every class computed on s has an allowed size}
∏_{i ∈ s} w(c_i)`. -/
noncomputable def classWeight (M lam : ℝ) (A : ℕ → Prop) (w : ℂ × ℂ → ℝ≥0∞)
    (s : Finset (Fin n)) (c : Fin n → ℂ × ℂ) : ℝ≥0∞ := by
  classical
  exact (if ∀ i ∈ s, A (multipoleClassOn M lam c s i).card then 1 else 0) * ∏ i ∈ s, w (c i)

/-! ### Measurability -/

theorem measurableSet_classGraph_adj (M lam : ℝ) (s : Finset (Fin n)) (i j : Fin n) :
    MeasurableSet {c : Fin n → ℂ × ℂ | (classGraph M lam c s).Adj i j} := by
  simp only [SimpleGraph.fromRel_adj]
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.union ?_ ?_)
  · exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_setOf_multipoleLinked M lam i j))
  · exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_setOf_multipoleLinked M lam j i))

theorem measurable_blockWeight (M lam : ℝ) {w : ℂ × ℂ → ℝ≥0∞} (hw : Measurable w) {ι : Type*}
    [Fintype ι] : Measurable (blockWeight (ι := ι) M lam w) := by
  classical
  unfold blockWeight
  refine Measurable.mul (Measurable.ite ?_ measurable_const measurable_const) ?_
  · exact measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected)
  · exact Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)

/-- The marginal integral of a block weight is the integral over the block. -/
theorem lmarginal_blockWeight (M lam : ℝ) {w : ℂ × ℂ → ℝ≥0∞} (T : Finset (Fin n)) (x : Fin n → ℂ × ℂ) :
    (∫⋯∫⁻_T, (fun c => blockWeight M lam w (fun i : T => c i)) ∂fun _ => volume) x =
      ∫⁻ y : T → ℂ × ℂ, blockWeight M lam w y := by
  unfold lmarginal
  rw [← volume_pi]
  refine lintegral_congr fun y => ?_
  show blockWeight M lam w (fun i : T => Function.updateFinset x T y i) = _
  congr 1
  funext i
  simp [Function.updateFinset_def, i.2]

end BadPointTypes

end MultipoleBKT

end
