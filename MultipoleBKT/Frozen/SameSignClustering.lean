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
# Frozen: `MultipoleBKT.sameSignClustering`

See the paper, Definition 5.1.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT

-- the iteration of Definition 5.1 as a recursion on the set `I` of
-- remaining labels; the output is the set of clusters, each paired with the value of `τ` at which
-- it was removed (the paper's radius is `τ_i^± = max(λ, that value)`, not part of this output).
-- ties. Singleton step: the smallest index `i` with `τ = ¼ r_i`.
-- Overcrowding step: the centre minimising `(i ∉ crowded(τ), r_i, i)` lexicographically, i.e.
-- (since some centre is crowded at that step) the crowded centre with smallest `r_i`, ties by index.
-- `J` is written `insert i (…)`, which is the paper's `J` ("Notice that `i ∈ J`").
open scoped Classical in
/-- One run of the `q`-clustering of same-sign charges, Definition 5.1, on the remaining labels `I`, for charges
`z` (`z i = x_i` for the positive, `z i = y_i` for the negative clustering), dipole lengths
`r` (`r i = |x_i - y_i|`) and cutoff `h = ε₀ R̄_{β,λ}`. All balls are closed. With
`crowded(t)` the centres `i ∈ I` whose ball `B(z_i, t)` meets at least `q` other balls
`B(z_j, t)`, `j ∈ I`, let `τ = min(h, ¼ min_{i ∈ I} r_i, t*)`, where `t*` is the minimal
`t ≥ 0` with `crowded(t) ≠ ∅` (omitted, i.e. `+∞`, if there is none). Then:
* if `τ = h`, every remaining label becomes a singleton cluster (removed at `h`) and the run stops;
* otherwise, if `τ = ¼ r_i` for some `i ∈ I`, `{i}` is a cluster (removed at `¼ r_i`);
* otherwise a crowded centre `i` with smallest `r_i` is chosen and
  `J = {j ∈ I : B(z_j, τ) ∩ B(z_i, τ) ≠ ∅}` is a cluster (removed at `τ`).
The result is the set of pairs (cluster, removal value); its first components form
`Clus_N^±` when `I = [N]`. -/
noncomputable def sameSignClustering {N : ℕ} (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (I : Finset (Fin N)) : Finset (Finset (Fin N) × ℝ) :=
  if hI : I.Nonempty then
    -- the centres whose closed ball of radius `t` meets at least `q` other balls
    let crowded : ℝ → Finset (Fin N) := fun t => I.filter fun i =>
      q ≤ (I.filter fun j => j ≠ i ∧
        (Metric.closedBall (z i) t ∩ Metric.closedBall (z j) t).Nonempty).card
    -- `τ = min(h, ¼ min r, t*)`, with `t* = +∞` if no ball is ever overcrowded
    let τ : ℝ :=
      if {t : ℝ | 0 ≤ t ∧ (crowded t).Nonempty}.Nonempty then
        min (min h (I.inf' hI r / 4)) (sInf {t : ℝ | 0 ≤ t ∧ (crowded t).Nonempty})
      else min h (I.inf' hI r / 4)
    if τ = h then
      I.image fun i => ({i}, h)
    else if hs : (I.filter fun i => r i / 4 = τ).Nonempty then
      let i := (I.filter fun i => r i / 4 = τ).min' hs
      have hi : i ∈ I := (Finset.mem_filter.1 (Finset.min'_mem _ hs)).1
      insert ({i}, τ) (sameSignClustering q h z r (I.erase i))
    else
      let keys := I.image fun j => toLex (decide (j ∉ crowded τ), toLex (r j, j))
      have hk : keys.Nonempty := hI.image _
      let i : Fin N := (ofLex (ofLex (keys.min' hk)).2).2
      have hi : i ∈ I := by
        obtain ⟨j, hj, hjk⟩ := Finset.mem_image.1 (keys.min'_mem hk)
        have : i = j := by simp only [i, ← hjk]; rfl
        exact this ▸ hj
      let J := insert i (I.filter fun j =>
        (Metric.closedBall (z j) τ ∩ Metric.closedBall (z i) τ).Nonempty)
      insert (J, τ) (sameSignClustering q h z r (I \ J))
  else ∅
termination_by I.card
decreasing_by
  · exact Finset.card_erase_lt_of_mem hi
  · exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.subset_iff.2 fun x hx => by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hi
      · exact (Finset.mem_filter.1 hx).1) ⟨i, Finset.mem_insert_self _ _⟩)

end MultipoleBKT

end
