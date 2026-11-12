/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MultipoleBKT.Frozen.DipoleNormalization
public import MultipoleBKT.Frozen.MultipolePartitionFunction
public import MultipoleBKT.Frozen.MultipoleActivity

/-!
# Frozen: `MultipoleBKT.truncatedPartitionWeight`

See the paper, equation (5.160).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- takes `χ` explicitly. total in
-- `p` (the paper has `p = p(β)`).
-- the series over `n` is a `tsum`; its terms vanish for `2n > |π|`, so it is
-- a finite sum and needs no summability conjunct.
open scoped Classical in
/-- `Ẑ(π)`, eq. (5.160), for `p = p(β)` and
`π ∈ 𝚷_p([N])`:
`(N C_{β,λ})^N 𝖬^0_∞(π) ∑_{n ≥ 0} (1/n!) ∑_{X_1, …, X_n ⊂ π disjoint, 2 ≤ |X_i|, |V_{X_i}| ≤ p}
∏ᵢ 𝖪^mult_{β,λ}(X_i)`, with `𝖬^0_∞(π) = ∏_{S ∈ π} 𝖬_{β,λ}(S)` (eq. (4.17)). -/
noncomputable def truncatedPartitionWeight (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (p : ℕ)
    (π : Finset (Finset ℕ)) : ℝ :=
  ((N : ℝ) * dipoleNormalization χ N β lam) ^ N *
    (∏ S ∈ π, multipolePartitionFunction χ N β lam M S) *
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter (fun X =>
            (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
              ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p),
          ∏ i, multipoleActivity χ N β lam M (X i)

end MultipoleBKT

end
