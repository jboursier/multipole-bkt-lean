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

/-!
# Frozen: `MultipoleBKT.canonicalPartition`

See the paper, Definition 2.14.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- `[k]` as `{0, …, k-1}`; `m : Fin p → ℕ`.
/-- The canonical partition `Y(m_1, …, m_p)` of `[k]`, `k = ∑ᵢ i mᵢ`, Definition 2.14, with `[k]` relabelled as `{0, …, k-1}` and the paper's
`m_{i+1}` (the number of blocks of size `i + 1`) written `m i` for `i : Fin p`: cut
`0, 1, …, k-1` in order into `m_1` singletons, then `m_2` consecutive pairs, …, then `m_p`
consecutive `p`-tuples. With `o_i = ∑_{l < i} (l + 1) m l` the number of elements used by the
smaller blocks, the `j`-th block of size `i + 1` (`j < m i`) is
`[o_i + j (i + 1), o_i + (j + 1)(i + 1))`. -/
def canonicalPartition {p : ℕ} (m : Fin p → ℕ) : Finset (Finset ℕ) :=
  Finset.univ.biUnion fun i : Fin p =>
    (Finset.range (m i)).image fun j =>
      Finset.Ico (∑ l with l < i, ((l : ℕ) + 1) * m l + j * ((i : ℕ) + 1))
        (∑ l with l < i, ((l : ℕ) + 1) * m l + (j + 1) * ((i : ℕ) + 1))

end MultipoleBKT

end
