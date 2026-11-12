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
public import MultipoleBKT.Frozen.Hypertrees
public import MultipoleBKT.Frozen.HypertreeWeight

/-!
# Frozen: `MultipoleBKT.mayerTerm`

See the paper, equation (2.36).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- `[k]` as `Finset.range k`, 0-based.
-- the `(n, k)` term of the double series (2.36), named so that the
-- theorems can assert its absolute summability.
-- a function of the coefficient function `kdip : ℕ → ℝ`.
-- the size cutoff is applied to each factor in the product.
/-- The `(n, k)` term of the truncated Mayer series (2.36), Definition 2.7, for coefficients `kdip` (the paper's `𝗄^dip_{β,λ}`):
`((-1)ⁿ/n!) (1/k!) ∑_{V ∈ Htrees_n([k]), V_1 ∪ ⋯ ∪ V_n = [k]} ω(V) ∏ᵢ 𝗄^dip(|V_i|) 𝟙_{|V_i| ≤ p}`,
with `[k]` relabelled as `{0, …, k-1}`. -/
noncomputable def mayerTerm (p : ℕ) (kdip : ℕ → ℝ) (n k : ℕ+) : ℝ :=
  (-1) ^ (n : ℕ) / (n : ℕ).factorial *
    (1 / (k : ℕ).factorial *
      ∑ V ∈ (hypertrees n (Finset.range k)).filter
          (fun V => Finset.univ.biUnion V = Finset.range k),
        hypertreeWeight V * if ∀ i, (V i).card ≤ p then ∏ i, kdip (V i).card else 0)

end MultipoleBKT

end
