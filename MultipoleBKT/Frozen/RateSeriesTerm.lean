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
public import MultipoleBKT.Frozen.BlockProfile
public import MultipoleBKT.Frozen.CanonicalPartition

/-!
# Frozen: `MultipoleBKT.rateSeriesTerm`

See the paper, Definition 2.15.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- the `(n, m)` term of the series in `ℐ`, named so that the theorems
-- can assert its absolute summability.
-- a function of the coefficient function `kmult`.
-- the size cutoff is applied to each factor in the product.
/-- The `(n, (m_1, …, m_p))` term of the cluster series in the rate function, Definition 2.15, for coefficients `kmult` (the paper's
`𝗄^mult_{β,λ}`, a function of block profiles):
`((-1)ⁿ/n!) ∏ᵢ (γᵢ^{mᵢ}/mᵢ!) ∑_{X ∈ Htrees_n(Y(m)), X_1 ∪ ⋯ ∪ X_n = Y(m)} ω(X)
∏ᵢ 𝗄^mult((#_k X_i)_k) 𝟙_{|V_{X_i}| ≤ p}`, where each `X_i` is a set of blocks of `Y(m)`. -/
noncomputable def rateSeriesTerm (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) (n : ℕ+)
    (m : Fin p → ℕ) : ℝ :=
  (-1) ^ (n : ℕ) / (n : ℕ).factorial *
    ((∏ i, γ i ^ m i / (m i).factorial) *
      ∑ X ∈ (hypertrees n (canonicalPartition m)).filter
          (fun X => Finset.univ.biUnion X = canonicalPartition m),
        hypertreeWeight X *
          if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, kmult (blockProfile (X i)) else 0)

end MultipoleBKT

end
