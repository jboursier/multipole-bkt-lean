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
# Lemma 5.46 (disjoint-cluster expansion): the definitions

These definitions specify the objects in Lemma 5.46 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

The definitions of the smeared Coulomb model, its finite combinatorial objects and
its parameter-dependent quantities below are shared by the challenge and solution.
Only the definitions used by the statement, including their dependencies, are included.
The original namespaces are retained inside `MultipoleBKTAudit.Lemma546`;
for example, `TwoComponentCoulomb.box` specifies the companion paper's square.
This module imports Mathlib only.
-/

@[expose] public section

namespace MultipoleBKTAudit.Lemma546

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

-- `[N]` as `Finset.range N`; partitions as `Finset (Finset ℕ)`.
open scoped Classical in
/-- `𝚷_p([N])`, the partitions of `[N]` whose blocks have cardinality at most `p` (the
Definition 5.44). -/
noncomputable def boundedBlockPartitions (N p : ℕ) : Finset (Finset (Finset ℕ)) :=
  (Finset.range N).powerset.powerset.filter fun π =>
    IsSubpartition π ∧ π.biUnion id = Finset.range N ∧ ∀ S ∈ π, S.card ≤ p

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

-- takes `χ` explicitly.
/-- The dipole–dipole interaction `v_ij = g_λ(x_i - x_j) + g_λ(y_i - y_j) - g_λ(x_i - y_j)
- g_λ(x_j - y_i)` of `d = (x_i, y_i)` and `e = (x_j, y_j)`. -/
noncomputable def dipoleInteraction (χ : ℂ → ℝ) (lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  smearedKernel χ lam (d.1 - e.1) + smearedKernel χ lam (d.2 - e.2)
    - smearedKernel χ lam (d.1 - e.2) - smearedKernel χ lam (e.1 - d.2)

end MultipoleBKT

end

section

namespace TwoComponentCoulomb

/-- The box `Λ = [0, √N]²`, copied from `TwoComponentCoulomb.box`. -/
def box (N : ℕ) : Set ℂ := Complex.reProdIm (Set.Icc 0 (Real.sqrt N)) (Set.Icc 0 (Real.sqrt N))

end TwoComponentCoulomb

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

-- takes `χ` explicitly.
-- `V : Finset ℕ` (any finite label set), configurations `V → ℂ × ℂ`.
-- `𝒜_ij` evaluated with `i < j`.
open scoped Classical in
/-- The dipole activity `K^dip_{β,λ}(V)`, Definition 2.5: the sum over `E ∈ 𝒢_c(V)` (edge sets on `V`, i.e. simple graphs on `V`, that are
connected and have at least one edge) of `𝔼_{μ^{⊗|V|}} ∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝒜_ij} - 1)`. -/
noncomputable def dipoleActivity (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (V : Finset ℕ) : ℝ :=
  ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty),
    ∫ c : V → ℂ × ℂ,
      ∏ i : V, ∏ j : V,
        if i < j ∧ E.Adj i j then
          (if IsStableDipolePair (c i) (c j) then
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0) - 1
        else 1
      ∂Measure.pi fun _ : V => dipoleMeasure χ N β lam

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

end MultipoleBKTAudit.Lemma546

end
