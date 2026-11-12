/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.Transport
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Data.Fin.VecNotation

/-!
# Endpoint-realization cells

See (A.7),
(A.8) and (A.9). Each of the four measurable cells
records which endpoint difference realizes the minimum distance. As in the
paper, cells overlap on ties. We use a finite union bound, so no
null-set assertion about ties is needed, even for fixed dipole vectors.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Finset Set
open scoped ENNReal

/-- The four differences, in the order `xx`, `xy`, `yx`, `yy` of (A.9). -/
def endpointDifference (d e : ℂ × ℂ) (l : Fin 4) : ℂ :=
  ![d.1 - e.1, d.1 - e.2, d.2 - e.1, d.2 - e.2] l

/-- The closed realization cell `D^l`, including all ties for the minimum. -/
def endpointCell (l : Fin 4) : Set ((ℂ × ℂ) × (ℂ × ℂ)) :=
  {p | ∀ j, ‖endpointDifference p.1 p.2 l‖ ≤ ‖endpointDifference p.1 p.2 j‖}

theorem continuous_endpointDifference (l : Fin 4) :
    Continuous (fun p : (ℂ × ℂ) × (ℂ × ℂ) => endpointDifference p.1 p.2 l) := by
  fin_cases l <;> simp [endpointDifference] <;> fun_prop

/-- Measurability holds on the whole configuration space, including ties. -/
theorem measurableSet_endpointCell (l : Fin 4) : MeasurableSet (endpointCell l) := by
  simp only [endpointCell, ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact measurableSet_le (continuous_endpointDifference l).norm.measurable
    (continuous_endpointDifference j).norm.measurable

/-- At least one of the four endpoint differences realizes the distance. -/
theorem exists_endpointCell (d e : ℂ × ℂ) : ∃ l, (d, e) ∈ endpointCell l := by
  obtain ⟨l, hl⟩ := Finite.exists_min (fun l : Fin 4 => ‖endpointDifference d e l‖)
  exact ⟨l, hl⟩

/-- On a realization cell, the selected norm is the literal minimum of
all four endpoint distances appearing in `MultipoleLinked`. -/
theorem endpointCell_min {d e : ℂ × ℂ} {l : Fin 4} (hl : (d, e) ∈ endpointCell l) :
    min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) =
      ‖endpointDifference d e l‖ := by
  have hle : ‖endpointDifference d e l‖ ≤
      min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) := by
    exact le_min (le_min (hl 0) (hl 1)) (le_min (hl 2) (hl 3))
  apply le_antisymm _ hle
  fin_cases l <;> simp [endpointDifference]

/-- The link condition on a cell confines its selected coordinate to the
disc of radius `M max(min(r_i,r_j),λ)` in (A.11). -/
theorem endpointCell_linked_iff {M lam : ℝ} {d e : ℂ × ℂ} {l : Fin 4}
    (hl : (d, e) ∈ endpointCell l) :
    MultipoleLinked M lam d e ↔
      ‖endpointDifference d e l‖ ≤
        M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) := by
  unfold MultipoleLinked
  rw [endpointCell_min hl]

/-- The finite union bound for the four realization cells. This is valid
pointwise, with no exceptional set. -/
theorem one_le_sum_endpointCells (d e : ℂ × ℂ) :
    (1 : ℝ≥0∞) ≤ ∑ l : Fin 4, (endpointCell l).indicator (1 : ((ℂ × ℂ) × (ℂ × ℂ)) → ℝ≥0∞) (d, e) := by
  obtain ⟨l, hl⟩ := exists_endpointCell d e
  calc
    (1 : ℝ≥0∞) = (endpointCell l).indicator (1 : ((ℂ × ℂ) × (ℂ × ℂ)) → ℝ≥0∞) (d, e) := by
      rw [indicator_of_mem hl]
      rfl
    _ ≤ _ := Finset.single_le_sum (f := fun l : Fin 4 =>
      (endpointCell l).indicator (1 : ((ℂ × ℂ) × (ℂ × ℂ)) → ℝ≥0∞) (d, e))
      (fun _ _ => zero_le) (Finset.mem_univ l)

/-- Endpoint offsets in coordinates `(x,y)=(a+u,a)`. -/
def endpointOffset (u v : ℂ) (l : Fin 4) : ℂ := ![u - v, u, -v, 0] l

/-- For fixed dipole vectors the selected endpoint coordinate is an affine
tree difference with unit coefficient on the child position. -/
theorem endpointDifference_eq (a b u v : ℂ) (l : Fin 4) :
    endpointDifference (a + u, a) (b + v, b) l = a - b + endpointOffset u v l := by
  fin_cases l <;> simp [endpointDifference, endpointOffset] <;> ring

open scoped Classical in
/-- The full phase-space split (A.8), for any finite collection of
oriented edges. Assigning a type to each edge is the same as splitting
it into the four possibly empty forests. -/
theorem one_le_sum_endpointAssignments {E : Type*} [Fintype E]
    (d e : E → ℂ × ℂ) :
    (1 : ℝ≥0∞) ≤ ∑ l : E → Fin 4,
      ∏ i, (endpointCell (l i)).indicator (1 : ((ℂ × ℂ) × (ℂ × ℂ)) → ℝ≥0∞) (d i, e i) := by
  classical
  choose l hl using fun i => exists_endpointCell (d i) (e i)
  calc
    (1 : ℝ≥0∞) = ∏ i, (endpointCell (l i)).indicator (1 : ((ℂ × ℂ) × (ℂ × ℂ)) → ℝ≥0∞) (d i, e i) := by
      symm
      apply prod_eq_one
      intro i _
      rw [indicator_of_mem (hl i)]
      rfl
    _ ≤ _ := Finset.single_le_sum (f := fun l : E → Fin 4 =>
      ∏ i, (endpointCell (l i)).indicator (1 : ((ℂ × ℂ) × (ℂ × ℂ)) → ℝ≥0∞) (d i, e i))
      (fun _ _ => zero_le) (Finset.mem_univ l)

end MultipoleBKT.MultipoleIntegral

end
