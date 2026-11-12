/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Weights
public import MultipoleBKT.LowerBound.Parity.MayerBond

/-!
# The peeling weights of dipole configurations

The estimates of the peeling (`MultipoleBKT.Peeling.ear_estimate`,
`MultipoleBKT.Peeling.quadratic_estimate`, …) are stated for abstract radii `r`, distances `d` and
indicator factors `c`. Here we instantiate them at a dipole configuration `z : V → ℂ × ℂ`,
`z i = (x_i, y_i)` (Definition 4.29):

* `MultipoleBKT.Peeling.dipoleLength (z i) = r_i = |x_i - y_i|`;
* `MultipoleBKT.Peeling.dipoleDistOn z ij = d_ij = dist({x_i, y_i}, {x_j, y_j})`
  (`MultipoleBKT.dipoleDist`);
* `MultipoleBKT.Peeling.absIndicator M lam ε₀ R z ij = 1_{𝓑_ij^c} 1_{d_ij ≤ 17 ε₀ R}`, with `R` the
  truncation scale `R̄_{β,λ}`.

Then `absWeight` is the weight `a^abs_ij` of Definition 4.29
(`MultipoleBKT.Peeling.absWeight_dipole`: it equals `MultipoleBKT.Parity.absOddWeight`), and
`keptWeight`, `peelWeight` are the factors `d_ij^{-2} 1_{d_ij ≤ 17 ε₀ R̄} 1_{𝓑_ij^c}` and `g_ij` of
(4.65) and (4.66).
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

variable {V : Type*}

/-- The size `r = |x - y|` of a dipole `(x, y)`. -/
noncomputable def dipoleLength (z : ℂ × ℂ) : ℝ := ‖z.1 - z.2‖

/-- The distances `d_ij = dist({x_i, y_i}, {x_j, y_j})` as a function of unordered pairs. -/
noncomputable def dipoleDistOn (z : V → ℂ × ℂ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => dipoleDist (z i) (z j), fun _ _ => dipoleDist_comm _ _⟩

theorem dipoleDistOn_mk (z : V → ℂ × ℂ) (i j : V) :
    dipoleDistOn z s(i, j) = dipoleDist (z i) (z j) := rfl

theorem dipoleDistOn_nonneg (z : V → ℂ × ℂ) (e : Sym2 V) : 0 ≤ dipoleDistOn z e := by
  induction e using Sym2.ind with
  | h i j =>
    exact le_min (le_min (norm_nonneg _) (norm_nonneg _)) (le_min (norm_nonneg _) (norm_nonneg _))

theorem multipoleLinked_iff_dipoleDist_le {M lam : ℝ} {d e : ℂ × ℂ} :
    MultipoleLinked M lam d e ↔
      dipoleDist d e ≤ M * min (max (dipoleLength d) lam) (max (dipoleLength e) lam) := Iff.rfl

theorem multipoleLinked_swap {M lam : ℝ} {d e : ℂ × ℂ} :
    MultipoleLinked M lam d e ↔ MultipoleLinked M lam e d := by
  rw [multipoleLinked_iff_dipoleDist_le, multipoleLinked_iff_dipoleDist_le, dipoleDist_comm,
    min_comm]

open scoped Classical in
/-- The indicator factor `1_{𝓑_ij^c} 1_{d_ij ≤ 17 ε₀ R}` of `a^abs_ij` (Definition 4.29). -/
noncomputable def absIndicator (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => (if MultipoleLinked M lam (z i) (z j) then 0 else 1) *
      (if dipoleDist (z i) (z j) ≤ 17 * ε₀ * R then 1 else 0), fun i j => by
    simp only [dipoleDist_comm (z i) (z j), propext (multipoleLinked_swap (d := z i))]⟩

theorem absIndicator_nonneg (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (e : Sym2 V) :
    0 ≤ absIndicator M lam ε₀ R z e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [absIndicator, Sym2.lift_mk]
    split_ifs <;> norm_num

theorem absIndicator_le_one (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (e : Sym2 V) :
    absIndicator M lam ε₀ R z e ≤ 1 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [absIndicator, Sym2.lift_mk]
    split_ifs <;> norm_num

/-- `absWeight` at a dipole configuration is the weight `a^abs_ij` of Definition 4.29
(`MultipoleBKT.Parity.absOddWeight`). -/
theorem absWeight_dipole (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (i j : V) :
    absWeight (fun i => dipoleLength (z i)) (dipoleDistOn z) (absIndicator M lam ε₀ R z) s(i, j) =
      Parity.absOddWeight M lam ε₀ R (z i) (z j) := by
  classical
  simp only [absWeight, radProd_mk, radMax_mk, dipoleDistOn_mk, absIndicator, Sym2.lift_mk,
    Parity.absOddWeight, dipoleLength]
  rw [max_comm (max _ _) (dipoleDist (z i) (z j))]
  split_ifs <;> ring

end Peeling

end MultipoleBKT

end
