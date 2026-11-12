/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Ear
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Algebra.CharP.Two
public import MultipoleBKT.Limits.Majorant
public import MultipoleBKT.Appendix.GeneralExpansionK.TreeSharp

/-!
# Geometry of far pairs

See Lemma A.7. The far relation bounds the absolute bond weight by one. Distance,
weight and relation lifts on unordered pairs support the paper's estimates.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open Finset SimpleGraph
open Limits

variable {M lam : ℝ}

/-! ### Far pairs -/

theorem ahat_comm (d e : ℂ × ℂ) : ahat d e = ahat e d := by
  unfold ahat
  rw [dipoleDist_comm, mul_comm ‖d.1 - d.2‖, max_comm ‖d.1 - d.2‖]

/-- On `𝓑_ij^c` (`M ≥ 1`, `λ > 0`): `λ < d_ij`, `min(ρ_i, ρ_j) < d_ij` and `â ≤ 1`. -/
theorem far_facts (hlam : 0 < lam) (hM : 1 ≤ M) {d e : ℂ × ℂ}
    (hnl : ¬ MultipoleLinked M lam d e) :
    lam < dipoleDist d e ∧ M * min (rhoD lam d) (rhoD lam e) < dipoleDist d e ∧ ahat d e ≤ 1 := by
  set dd := dipoleDist d e
  set r₁ := ‖d.1 - d.2‖
  set r₂ := ‖e.1 - e.2‖
  have hnl' : M * min (max r₁ lam) (max r₂ lam) < dd := by
    rw [MultipoleLinked, not_le] at hnl
    exact hnl
  have hmin : min (max r₁ lam) (max r₂ lam) ≤ M * min (max r₁ lam) (max r₂ lam) :=
    le_mul_of_one_le_left (le_min (le_max_of_le_right hlam.le) (le_max_of_le_right hlam.le)) hM
  have hlamd : lam < dd :=
    lt_of_le_of_lt ((le_min (le_max_right _ _) (le_max_right _ _)).trans hmin) hnl'
  have hdd : 0 < dd := hlam.trans hlamd
  have hrmin : min r₁ r₂ ≤ dd :=
    ((min_le_min (le_max_left _ _) (le_max_left _ _)).trans hmin).trans hnl'.le
  refine ⟨hlamd, hnl', ?_⟩
  unfold ahat
  rw [div_le_one (mul_pos hdd (lt_max_of_lt_left hdd))]
  rcases le_total r₁ r₂ with h | h
  · calc r₁ * r₂ ≤ dd * r₂ := by
          gcongr
          exact (min_eq_left h ▸ hrmin)
      _ ≤ dd * max dd (max r₁ r₂) := by
          gcongr; exact (le_max_right _ _).trans (le_max_right _ _)
  · calc r₁ * r₂ ≤ r₁ * dd := by
          gcongr
          exact (min_eq_right h ▸ hrmin)
      _ = dd * r₁ := by ring
      _ ≤ dd * max dd (max r₁ r₂) := by
          gcongr; exact (le_max_left _ _).trans (le_max_right _ _)

section Majorant

variable {ι β ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
  [DecidableEq ε]

/-- The dipole distance as a function of unordered pairs of labels. -/
noncomputable def distE (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => dipoleDist (c i) (c j)) fun _ _ => dipoleDist_comm _ _

/-- The weight `â` as a function of unordered pairs of labels. -/
noncomputable def ahatE (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => ahat (c i) (c j)) fun _ _ => ahat_comm _ _

/-- The far relation as a function of unordered pairs of labels. -/
def FarE (M lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) : Prop :=
  Sym2.lift ⟨fun i j => ¬ MultipoleLinked M lam (c i) (c j), fun i j => by
    simp only [eq_iff_iff]; exact not_congr multipoleLinked_comm⟩ e

end Majorant

end ExpansionK

end MultipoleBKT

end
