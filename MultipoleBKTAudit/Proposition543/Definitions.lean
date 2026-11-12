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
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Proposition 5.43 (large deviations upper bound): the definitions

These definitions specify the objects in Proposition 5.43 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

The definitions of the smeared Coulomb model, its finite combinatorial objects and
its parameter-dependent quantities below are shared by the challenge and solution.
Only the definitions used by the statement, including their dependencies, are included.
The original namespaces are retained inside `MultipoleBKTAudit.Proposition543`;
for example, `TwoComponentCoulomb.box` specifies the companion paper's square.
This module imports Mathlib only.
-/

@[expose] public section

namespace MultipoleBKTAudit.Proposition543

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- general mollifier as in the paper.
/-- `χ` is an admissible mollifier: measurable, nonnegative, radial, bounded,
vanishing outside the closed unit ball ("supported in `B(0,1)`"), with `∫ χ = 1`. -/
def IsMollifier (χ : ℂ → ℝ) : Prop :=
  Measurable χ ∧ (∀ x, 0 ≤ χ x) ∧ (∀ x y, ‖x‖ = ‖y‖ → χ x = χ y) ∧ BddAbove (Set.range χ) ∧
    (∀ x, 1 < ‖x‖ → χ x = 0) ∧ ∫ x, χ x = 1

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- subpartitions as `Finset (Finset α)`.
/-- `X` is a subpartition: a partition of some finite set `C`, i.e.
a finite family of nonempty, pairwise disjoint finite sets. -/
def IsSubpartition {α : Type*} (X : Finset (Finset α)) : Prop :=
  (∀ S ∈ X, S.Nonempty) ∧ (X : Set (Finset α)).PairwiseDisjoint id

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total in `β`; used for `β > 2`.
/-- The exponent `α(β)`, eq. (4.23): `(4 - β)/2` if `β ∈ (2,4)` and `1/2` if `β ≥ 4`. -/
noncomputable def alphaExponent (β : ℝ) : ℝ :=
  if β < 4 then (4 - β) / 2 else 1 / 2

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total in `β`; used for `β > 2` (then `q(β) ≥ 3`).
/-- The clustering parameter `q(β)`, eq. (5.1): `⌊3/(2 - β/2)⌋` if `β ∈ (2,4)` and `2p₀ + 1` if `β ≥ 4`. -/
noncomputable def clusterThreshold (p₀ : ℕ) (β : ℝ) : ℕ :=
  if β < 4 then ⌊3 / (2 - β / 2)⌋₊ else 2 * p₀ + 1

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

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

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total; the value `+∞` lives in `ℝ≥0∞`.
/-- The critical length scale `R_{β,λ}`, eq. (1.4):
`λ^{-(β-2)/(4-β)}` if `β < 4` and `+∞` if `β ≥ 4`. -/
noncomputable def criticalScale (β lam : ℝ) : ℝ≥0∞ :=
  if β < 4 then ENNReal.ofReal (lam ^ (-(β - 2) / (4 - β))) else ⊤

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total in `β`, `λ`; used for `β > 2`, `λ ∈ (0,1)`.
/-- The truncation scale `R̄_{β,λ}`, Definition 2.18: `R_{β,λ}` if `β ∈ (2,4)` and `λ^{-2p₀}` if `β ≥ 4`.
For `β < 4`, `R_{β,λ} < ∞` and `toReal` is exact. -/
noncomputable def truncationScale (p₀ : ℕ) (β lam : ℝ) : ℝ :=
  if β < 4 then (criticalScale β lam).toReal else lam ^ (-(2 * (p₀ : ℤ)))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- on a dipole configuration `d` (the paper's event `{σ_N = Id}`).
-- clusters of cardinality exactly `q(β) + 1`, as written; the
-- larger clusters occur only on the null set excluded after Definition 5.1.
open scoped Classical in
/-- Bad points of type 1, Definition 5.2, for the dipoles
`d i = (x_i, y_i)`, `r_i = |x_i - y_i|`:
`J^{1,±} = {i : r_i > ε₀ R̄_{β,λ}} ∪ ⋃_{S ∈ Clus_N^±, |S| = q(β)+1} S`, with `Clus_N^±` the
`q(β)`-clusterings (Definition 5.1, cutoff `ε₀ R̄_{β,λ}`) of the positive and of the negative
charges; `I^1_bad = J^{1,+} ∪ J^{1,-}`. -/
noncomputable def badPointsTypeOne {N : ℕ} (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  -- `J^{1,±}` for the clustering of the charges `z`
  let J : (Fin N → ℂ) → Finset (Fin N) := fun z =>
    Finset.univ.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) ∪
      ((sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
          (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).filter
        (fun Sτ => Sτ.1.card = clusterThreshold p₀ β + 1)).biUnion Prod.fst
  J (fun i => (d i).1) ∪ J (fun i => (d i).2)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- closed `≤`; the distance of two two-point sets is the minimum of
-- the four distances.
/-- The multipole relation between two dipoles `d = (x, y)` and `e = (x', y')` (Definition 2.2; Definition 2.3):
`dist({x, y}, {x', y'}) ≤ M min(max(|x - y|, λ), max(|x' - y'|, λ))`. Applied to
`(x_i, y_{σ_N(i)})` it is `i ↔_{σ_N} j` (event `𝖡_ij`); applied to `(x_i, y_i)` it is
`i ↔ j` (event `𝓑_ij`). -/
def MultipoleLinked (M lam : ℝ) (d e : ℂ × ℂ) : Prop :=
  min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) ≤
    M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- `Π_mult^U` is "the partition of `U` into multipoles (computed among
-- points in `U` only)"; on dipole
-- configurations this is the partition of `U` into the connected components of the graph that
-- `↔` (Definition 2.3, i.e. `MultipoleLinked` on the dipoles `d i`) induces on `U`.
open scoped Classical in
/-- The class `[i]^{Π_mult^U}` of `i ∈ U` in the multipoles computed among points of `U` only
("We compute multipoles on `U`"): the labels reachable from `i` in the
graph on `[N]` whose edges are the pairs `a ↔ b` (Definition 2.3, with the dipoles `d a`, `d b`)
with `a, b ∈ U`. For `i ∈ U` this is the connected component of `i` in the graph induced on
`U`. -/
noncomputable def multipoleClassOn {N : ℕ} (M lam : ℝ) (d : Fin N → ℂ × ℂ) (U : Finset (Fin N))
    (i : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun j =>
    (SimpleGraph.fromRel fun a b : Fin N =>
      a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (d a) (d b)).Reachable i j

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total in `q` (`q = 0` gives `4`, never consumed).
/-- `β_q = 4 - 2/q`, eq. (1.3); used for `q ∈ ℕ*`. -/
noncomputable def transitionBeta (q : ℕ) : ℝ := 4 - 2 / q

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total in `β` (the empty supremum, for `β ≤ 2`, is `0`).
/-- `p*(β) = sup {q ∈ ℕ* : β > β_q} ∈ ℕ* ∪ {+∞}`, eq. (2.33). -/
noncomputable def pStar (β : ℝ) : ℕ∞ :=
  ⨆ (q : ℕ) (_ : 1 ≤ q ∧ transitionBeta q < β), (q : ℕ∞)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total in `β`; `ENat.toNat` is exact on `(2, 4)`, where `p*(β) < ∞`.
-- `p₀ : ℕ` explicit.
/-- The series truncation parameter `p(β)`, Definition 2.8:
`p*(β)` if `β ∈ (2, 4)` (where `p*(β)` is finite) and `p₀` if `β ≥ 4`. -/
noncomputable def pBeta (p₀ : ℕ) (β : ℝ) : ℕ :=
  if β < 4 then (pStar β).toNat else p₀

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- on a dipole configuration `d`.
-- `[i]^{Π_mult^U}` is `multipoleClassOn M lam d U i`.
open scoped Classical in
/-- Bad points of type 2, Definition 5.3, with
`U = [N] ∖ I^1_bad` and multipoles computed on `U`: `I^{2,1}_bad` is the set of `i ∈ U` with
`|[i]^{Π_mult^U}| > p(β)`; for `k ∈ [p(β)]`, `I^{2,2,k}_bad` is `{i ∈ U : |[i]^{Π_mult^U}| = k}`
if this set has more than `ε₀^{-α(β)} N λ^{2(k-1)}` elements and `∅` otherwise;
`I^2_bad = I^{2,1}_bad ∪ ⋃_{k ∈ [p(β)]} I^{2,2,k}_bad`. -/
noncomputable def badPointsTypeTwo {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  -- `I^{2,1}_bad`
  U.filter (fun i => pBeta p₀ β < (multipoleClassOn M lam d U i).card) ∪
    -- `I^{2,2}_bad = ⋃_{k ∈ [p(β)]} I^{2,2,k}_bad`
    (Finset.Icc 1 (pBeta p₀ β)).biUnion fun k =>
      if ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) <
          ((U.filter fun i => (multipoleClassOn M lam d U i).card = k).card : ℝ)
      then U.filter fun i => (multipoleClassOn M lam d U i).card = k
      else ∅

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- on a dipole configuration `d`.
-- `[i]^{Π_mult^U}` is `multipoleClassOn M lam d U i`, `U = [N] ∖ I^1_bad`.
-- `d_ij` is the minimum of the four distances.
open scoped Classical in
/-- Bad points of type 3, Definition 5.4: `J^3_bad` is the set
of `i ∉ I^1_bad ∪ I^2_bad` such that `d_ij ≤ M max(r_i, λ)` (eq. (5.2)) for some
`j ∈ I^1_bad ∪ I^2_bad`, where `d_ij = dist({x_i, y_i}, {x_j, y_j})`; and
`I^3_bad = {i ∉ I^1_bad ∪ I^2_bad : [i]^{Π_mult^U} ∩ J^3_bad ≠ ∅}`. -/
noncomputable def badPointsTypeThree {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  let I₁₂ := badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  -- `J^3_bad`
  let J₃ := (Finset.univ \ I₁₂).filter fun i => ∃ j ∈ I₁₂,
    min (min ‖(d i).1 - (d j).1‖ ‖(d i).1 - (d j).2‖) (min ‖(d i).2 - (d j).1‖ ‖(d i).2 - (d j).2‖)
      ≤ M * max ‖(d i).1 - (d i).2‖ lam
  (Finset.univ \ I₁₂).filter fun i => (multipoleClassOn M lam d U i ∩ J₃).Nonempty

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- on a dipole configuration `d`.
/-- The bad points `I_bad = I^1_bad ∪ I^2_bad ∪ I^3_bad`, Definition 5.5. -/
noncomputable def badPoints {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d ∪
    badPointsTypeThree p₀ β lam M ε₀ d

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- profiles as `ℕ →₀ ℕ`, indexed by block size.
/-- The block profile `(#_k X)_{k}` of a family of blocks, `#_k X = |{S ∈ X : |S| = k}|`
, as a finitely supported function: the multiset of block
sizes. -/
def blockProfile {α : Type*} (X : Finset (Finset α)) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (X.val.map Finset.card)

end MultipoleBKT

end

section

namespace TwoComponentCoulomb

/-- The box `Λ = [0, √N]²`, copied from `TwoComponentCoulomb.box`. -/
def box (N : ℕ) : Set ℂ := Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N))

end TwoComponentCoulomb

end

section

namespace TwoComponentCoulomb

/-- `g(x) = -log |x|` on `ℝ² = ℂ`, copied from `TwoComponentCoulomb.logKernel`. -/
noncomputable def logKernel (x : ℂ) : ℝ := -Real.log ‖x‖

end TwoComponentCoulomb

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- takes `χ` explicitly.
/-- The smeared charge `δ_z^{(λ)} = λ⁻² χ((· - z)/λ)`, as a measure on `ℂ`. -/
noncomputable def smearedCharge (χ : ℂ → ℝ) (z : ℂ) (lam : ℝ) : Measure ℂ :=
  volume.withDensity fun x => ENNReal.ofReal ((lam ^ 2)⁻¹ * χ ((x - z) / lam))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

-- takes `χ` explicitly.
/-- `g_λ(z) = ∬ g(x - y) dδ₀^{(λ)}(x) dδ_z^{(λ)}(y)`, eq. (2.6). -/
noncomputable def smearedKernel (χ : ℂ → ℝ) (lam : ℝ) (z : ℂ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge χ 0 lam).prod (smearedCharge χ z lam)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- takes `χ` explicitly. total in `β`.
/-- `𝒵_β = 2π ∫₀^∞ e^{β g₁(r)} r dr`, eq. (2.19). -/
noncomputable def dipoleConstant (χ : ℂ → ℝ) (β : ℝ) : ℝ :=
  2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), Real.exp (β * smearedKernel χ 1 r) * r

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

-- takes `χ` explicitly.
/-- `κ = ∬ g(x - y) dδ₀^{(1)}(x) dδ₀^{(1)}(y)`, eq. (2.3). -/
noncomputable def kappa (χ : ℂ → ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, logKernel (p.1 - p.2) ∂(smearedCharge χ 0 1).prod (smearedCharge χ 0 1)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

-- takes `χ` explicitly.
-- configuration `c : Fin N → ℂ × ℂ`, `c i = (x_i, y_i)`.
/-- The energy `F_λ(X_N, Y_N)`, eq. (2.5): the double integral of
`g(x - y)` against `∑ᵢ (δ_{xᵢ}^{(λ)} - δ_{yᵢ}^{(λ)})` twice, expanded bilinearly (each pair
term a Bochner integral against the product measure), minus
`N (g(λ) + κ)`. -/
noncomputable def energy (χ : ℂ → ℝ) {N : ℕ} (lam : ℝ) (c : Fin N → ℂ × ℂ) : ℝ :=
  (1 / 2) * ∑ i, ∑ j,
      ((∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
          ∂(smearedCharge χ (c i).1 lam).prod (smearedCharge χ (c j).1 lam))
        - (∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
          ∂(smearedCharge χ (c i).1 lam).prod (smearedCharge χ (c j).2 lam))
        - (∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
          ∂(smearedCharge χ (c i).2 lam).prod (smearedCharge χ (c j).1 lam))
        + (∫ p : ℂ × ℂ, logKernel (p.1 - p.2)
          ∂(smearedCharge χ (c i).2 lam).prod (smearedCharge χ (c j).2 lam)))
    - N * (logKernel lam + kappa χ)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total; the `∑'` has at most one nonzero term.
-- `p₀ : ℕ` explicit.
/-- The error rate `δ_{β,λ}`, Definition 2.9 (eq. (2.37)):
`R_{β,λ}^{-2} 𝟙_{β∈(2,4)} (1 + ∑_{p ≥ 2} |log λ| 𝟙_{β = β_p}) + λ^{2p₀} 𝟙_{β ≥ 4}`. -/
noncomputable def errorRate (p₀ : ℕ) (β lam : ℝ) : ℝ :=
  (if 2 < β ∧ β < 4 then
      (criticalScale β lam).toReal ^ (-2 : ℤ) *
        (1 + ∑' q : ℕ, if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0)
    else 0)
  + if 4 ≤ β then lam ^ (2 * p₀) else 0

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- on a dipole configuration `d`.
/-- The good points `I_good = [N] ∖ I_bad`, Definition 5.5. -/
noncomputable def goodPoints {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    Finset (Fin N) :=
  Finset.univ \ badPoints p₀ β lam M ε₀ d

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- labels `Fin N` (0-based, order preserving), so the lexicographic
-- tie-break is the paper's.
-- the literal greedy rule; helper of `stableMatching` (the recursion
-- needs the general state `(A, B)` of remaining labels).
/-- One run of the stable-matching procedure (Definitions 2.1 and 4.1) on the remaining positive labels `A` and negative labels `B`, `|A| = |B| = k`: match
the pair `(i, j) ∈ A × B` that minimises `(|x_i - y_j|, i, j)` lexicographically (the first
contact, simultaneous contacts broken by the lexicographically smallest `(i, j)`), remove
`x_i` and `y_j`, and repeat on `A ∖ {i}`, `B ∖ {j}`. The result is the bijection `A ≃ B`,
`i ↦ σ(i)`. -/
noncomputable def greedyMatching {N : ℕ} (c : Fin N → ℂ × ℂ) :
    (k : ℕ) → (A B : Finset (Fin N)) → A.card = k → B.card = k → (A ≃ B)
  | 0, A, B, hA, hB =>
    haveI : IsEmpty A := ⟨fun a => by simpa [Finset.card_eq_zero.1 hA] using a.2⟩
    haveI : IsEmpty B := ⟨fun b => by simpa [Finset.card_eq_zero.1 hB] using b.2⟩
    Equiv.equivOfIsEmpty A B
  | k + 1, A, B, hA, hB =>
    let keys : Finset (ℝ ×ₗ (Fin N ×ₗ Fin N)) :=
      (A ×ˢ B).image fun ij => toLex (‖(c ij.1).1 - (c ij.2).2‖, toLex ij)
    have hkeys : keys.Nonempty :=
      ((Finset.card_pos.1 (by omega)).product (Finset.card_pos.1 (by omega))).image _
    -- the matched pair of this iteration
    let ij : Fin N × Fin N := ofLex (ofLex (keys.min' hkeys)).2
    have hij : ij ∈ A ×ˢ B := by
      obtain ⟨ij', hmem, heq⟩ := Finset.mem_image.1 (keys.min'_mem hkeys)
      have : ij = ij' := by simp only [ij, ← heq]; rfl
      exact this ▸ hmem
    have hi : ij.1 ∈ A := (Finset.mem_product.1 hij).1
    have hj : ij.2 ∈ B := (Finset.mem_product.1 hij).2
    -- the later iterations
    let e := greedyMatching c k (A.erase ij.1) (B.erase ij.2)
      (by rw [Finset.card_erase_of_mem hi, hA]; rfl) (by rw [Finset.card_erase_of_mem hj, hB]; rfl)
    { toFun := fun a =>
        if h : (a : Fin N) = ij.1 then ⟨ij.2, hj⟩
        else ⟨e ⟨a, Finset.mem_erase.2 ⟨h, a.2⟩⟩, (Finset.mem_erase.1 (e _).2).2⟩
      invFun := fun b =>
        if h : (b : Fin N) = ij.2 then ⟨ij.1, hi⟩
        else ⟨e.symm ⟨b, Finset.mem_erase.2 ⟨h, b.2⟩⟩, (Finset.mem_erase.1 (e.symm _).2).2⟩
      left_inv := by
        intro a
        by_cases h : (a : Fin N) = ij.1
        · simp [h]; exact Subtype.ext h.symm
        · have hne : (e ⟨a, Finset.mem_erase.2 ⟨h, a.2⟩⟩ : Fin N) ≠ ij.2 :=
            (Finset.mem_erase.1 (e _).2).1
          simp [h, hne]
      right_inv := by
        intro b
        by_cases h : (b : Fin N) = ij.2
        · simp [h]; exact Subtype.ext h.symm
        · have hne : (e.symm ⟨b, Finset.mem_erase.2 ⟨h, b.2⟩⟩ : Fin N) ≠ ij.1 :=
            (Finset.mem_erase.1 (e.symm _).2).1
          simp [h, hne] }

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- configurations `c : Fin N → ℂ × ℂ`.
-- `σ_N` literal, `N` rounds of `greedyMatching`, a permutation.
/-- The stable matching `σ_N` (Definition 2.1; Definition 4.1): `N` rounds of the greedy procedure, starting from all labels. -/
noncomputable def stableMatching {N : ℕ} (c : Fin N → ℂ × ℂ) : Equiv.Perm (Fin N) :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans
    ((greedyMatching c N Finset.univ Finset.univ (by simp) (by simp)).trans
      (Equiv.subtypeUnivEquiv Finset.mem_univ))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- vertices `Fin N`, dipoles `(x_i, y_{σ_N(i)})`.
-- the literal relation `MultipoleLinked`.
/-- The multipole graph (Definition 2.2 (1)–(2)): the graph on `[N]` with
`i ~ j` iff `i ≠ j` and `i ↔_{σ_N} j`, computed on the dipoles `(x_i, y_{σ_N(i)})`. Its
connected components are the multipoles. -/
noncomputable def multipoleGraph {N : ℕ} (M lam : ℝ) (c : Fin N → ℂ × ℂ) :
    SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j =>
    MultipoleLinked M lam ((c i).1, (c (stableMatching c i)).2)
      ((c j).1, (c (stableMatching c j)).2)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- the good points of a configuration `c` are those of its matched dipoles
-- `(x_i, y_{σ_N(i)})`, the dipoles of Definition 2.2.
-- "multipoles of cardinality `k` in `I_good`" are the
-- multipoles of Definition 2.2 (components of `multipoleGraph`) contained in `I_good`; by
-- Remark 5.6(1) these are also the `Π_mult^U`-classes contained in `I_good`.
-- counted as connected components with `k` vertices.
/-- `𝒩_k^good`, the number of multipoles of cardinality `k` in `I_good` (Proposition 5.43; proof of Theorem 2): the connected components of the multipole graph
(Definition 2.2) with `k` vertices, all of them good. -/
noncomputable def goodMultipoleCount {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (c : Fin N → ℂ × ℂ)
    (k : ℕ) : ℕ :=
  Nat.card {C : (multipoleGraph M lam c).ConnectedComponent // Nat.card C.supp = k ∧
    C.supp ⊆ ↑(goodPoints p₀ β lam M ε₀ fun i => ((c i).1, (c (stableMatching c i)).2))}

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- takes `χ` explicitly.
/-- The dipole–dipole interaction `v_ij = g_λ(x_i - x_j) + g_λ(y_i - y_j) - g_λ(x_i - y_j)
- g_λ(x_j - y_i)` of `d = (x_i, y_i)` and `e = (x_j, y_j)`. -/
noncomputable def dipoleInteraction (χ : ℂ → ℝ) (lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  smearedKernel χ lam (d.1 - e.1) + smearedKernel χ lam (d.2 - e.2)
    - smearedKernel χ lam (d.1 - e.2) - smearedKernel χ lam (e.1 - d.2)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- the pair is passed in increasing label order (`i < j`), so `𝒜_ij`
-- is symmetric in `i, j` by construction.
/-- The event `𝒜_ij` (Definition 4.4, eq. (4.2)), for the dipoles
`d = (x_i, y_i)` and `e = (x_j, y_j)` with `i < j`: the stable matching of `x_i, x_j` with
`y_i, y_j` alone is the identity, `σ₂[(x_i, x_j), (y_i, y_j)] = Id_{i,j}`. -/
def IsStableDipolePair (d e : ℂ × ℂ) : Prop :=
  stableMatching ![d, e] = Equiv.refl (Fin 2)

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

-- total in `N` (`1 / 0 = 0`).
-- takes `χ` explicitly.
/-- `C_{β,λ} = (1/N) ∫_{Λ²} e^{β g_λ(x - y)} dx dy`, eq. (2.31). -/
noncomputable def dipoleNormalization (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : ℝ :=
  (1 / N) * ∫ p in box N ×ˢ box N, Real.exp (β * smearedKernel χ lam (p.1 - p.2))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

-- total; `(N C)⁻¹ = 0` when `N C = 0`.
-- takes `χ` explicitly.
/-- The dipole measure `dμ_{β,λ}(x, y) = (N C_{β,λ})⁻¹ e^{β g_λ(x - y)} dx dy` on `Λ²`,
eq. (2.30). -/
noncomputable def dipoleMeasure (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : Measure (ℂ × ℂ) :=
  (volume.restrict (box N ×ˢ box N)).withDensity fun p =>
    ENNReal.ofReal
      ((N * dipoleNormalization χ N β lam)⁻¹ * Real.exp (β * smearedKernel χ lam (p.1 - p.2)))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- takes `χ` explicitly. `S : Finset ℕ`.
-- `𝒜_ij` evaluated with `i < j`.
open scoped Classical in
/-- The multipole partition function `𝖬_{β,λ}(S) = 𝔼_{μ^{⊗|S|}} [𝟙_{𝓑_S} ∏_{i<j ∈ S}
e^{-β v_ij} 𝟙_{𝒜_ij}]`, eq. (2.41), where `𝓑_S` says that the graph
induced on `S` by `↔` (with the pairs `(x_i, y_i)`) is connected (eq. (2.14)). -/
noncomputable def multipolePartitionFunction (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (S : Finset ℕ) : ℝ :=
  ∫ c : S → ℂ × ℂ,
    (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
      then 1 else 0) *
    ∏ i : S, ∏ j : S,
      if i < j then
        (if IsStableDipolePair (c i) (c j) then
          Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0)
      else 1
    ∂Measure.pi fun _ : S => dipoleMeasure χ N β lam

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- takes `χ` explicitly.
-- density form, with the normalisation `∏_{S ∈ X} 𝖬(S)` divided
-- out (Mathlib's `x⁻¹ = 0` at `𝖬(S) = 0`, which does not occur for `N ≥ 1`, `λ > 0`, `S ≠ ∅`).
open scoped Classical in
/-- The hierarchical multipole model `𝖯^X_{β,λ} = ⨂_{S ∈ X} 𝖯^S_{β,λ}` on `(Λ²)^{V_X}`
(eq. (2.42) and the line after it), written, as in eq. (4.16)
(with `ε₀ = ∞`), as the measure with density
`∏_{S ∈ X} 𝖬(S)⁻¹ 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` with respect to
`μ^{⊗ V_X}`, `V_X = ⋃_{S ∈ X} S`. -/
noncomputable def hierarchicalModel (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) : Measure (X.biUnion id → ℂ × ℂ) :=
  (Measure.pi fun _ : X.biUnion id => dipoleMeasure χ N β lam).withDensity fun c =>
    ∏ S ∈ X, ENNReal.ofReal ((multipolePartitionFunction χ N β lam M S)⁻¹ *
      ((if ((SimpleGraph.fromRel fun i j : X.biUnion id =>
            MultipoleLinked M lam (c i) (c j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected
          then 1 else 0) *
        ∏ i : X.biUnion id, ∏ j : X.biUnion id,
          if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
            (if IsStableDipolePair (c i) (c j) then
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0)
          else 1))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- takes `χ` explicitly.
-- `X : Finset (Finset ℕ)`, configurations `V_X → ℂ × ℂ`.
open scoped Classical in
/-- The multipole activity `𝖪^mult_{β,λ}(X)`, Definition 2.13 (eq. (2.44)): the sum over `E ∈ 𝖤^X` of `𝔼_{𝖯^X} ∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)`.
Here `𝖤^X` is the set of edge sets `E ⊂ ℰ^inter(X)` (edges between
distinct blocks) with at least one edge such that `(V_X, E ∪ ℰ^intra(X))` is connected,
`ℰ^intra(X)` being the edges inside the blocks. -/
noncomputable def multipoleActivity (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) : ℝ :=
  ∑ E ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
      (∀ i j : X.biUnion id, E.Adj i j →
          ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
        E.edgeSet.Nonempty ∧
        (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
          ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected),
    ∫ c : X.biUnion id → ℂ × ℂ,
      ∏ i : X.biUnion id, ∏ j : X.biUnion id,
        if i < j ∧ E.Adj i j then
          (if MultipoleLinked M lam (c i) (c j) then 0 else
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j))) - 1
        else 1
      ∂hierarchicalModel χ N β lam M X

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

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

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

/-- The hypertree weight `ω(X) = ∏_{a ∈ ⋃ᵢ X_i} (|{i ∈ [n] : a ∈ X_i}| - 1)!`. -/
def hypertreeWeight {α : Type*} [DecidableEq α] {n : ℕ} (X : Fin n → Finset α) : ℕ :=
  ∏ a ∈ Finset.univ.biUnion X, ((Finset.univ.filter fun i => a ∈ X i).card - 1).factorial

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

/-- The connection graph `G(X_1, …, X_n)`: the graph on `[n]` with an
edge `ij` (`i ≠ j`) if `X_i` and `X_j` intersect. -/
def connectionGraph {α : Type*} [DecidableEq α] {n : ℕ} (X : Fin n → Finset α) :
    SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => (X i ∩ X j).Nonempty

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

open scoped Classical in
/-- `Htrees_n(A)`, eq. (2.35): the tuples `(X_1, …, X_n)` of subsets
of `A` with `|X_i| ≥ 2` for every `i`, `G(X_1, …, X_n)` connected, and
`|⋃ᵢ X_i| + n - ∑ᵢ |X_i| = 1`. -/
noncomputable def hypertrees {α : Type*} [DecidableEq α] (n : ℕ) (A : Finset α) :
    Finset (Fin n → Finset α) :=
  (Fintype.piFinset fun _ : Fin n => A.powerset).filter fun X =>
    (∀ i, 2 ≤ (X i).card) ∧ (connectionGraph X).Connected ∧
      ((Finset.univ.biUnion X).card : ℤ) + n - ∑ i, ((X i).card : ℤ) = 1

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

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

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- total on `Fin p → ℝ`; the theorems use it on `Δ_{p,0}` only.
-- `tsum`s; summability is asserted by the theorems.
-- a function of the coefficient functions `msf` and `kmult`.
/-- The multipole rate function `ℐ_{β,p,λ}(γ)`, Definition 2.15, for coefficients `msf` (the paper's `𝗆_{β,λ}`) and `kmult`:
`∑_{i=1}^p γᵢ (log i! - 1 + log γᵢ - log 𝗆(i)) + 1 + ∑_{n ≥ 1} ∑_{m ∈ ℕ^p}` of
`rateSeriesTerm`. The convention `0 log 0 = 0` holds since `Real.log 0 = 0`. -/
noncomputable def rateFunction (p : ℕ) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ)
    (γ : Fin p → ℝ) : ℝ :=
  ∑ i, γ i * (Real.log ((i : ℕ) + 1).factorial - 1 + Real.log (γ i) - Real.log (msf ((i : ℕ) + 1)))
    + 1 + ∑' n : ℕ+, ∑' m : Fin p → ℕ, rateSeriesTerm p kmult γ n m

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- `Fin p`, coordinate `i` carrying weight `i + 1`.
/-- `Δ_{p,x} = {(γ_1, …, γ_p) ∈ [0,1]^p : γ_1 + 2γ_2 + ⋯ + pγ_p = 1 - x}`, Definition 2.15, with `γ i = γ_{i+1}`. -/
def simplex (p : ℕ) (x : ℝ) : Set (Fin p → ℝ) :=
  {γ | (∀ i, γ i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * γ i = 1 - x}

end MultipoleBKT

end

end MultipoleBKTAudit.Proposition543

end
