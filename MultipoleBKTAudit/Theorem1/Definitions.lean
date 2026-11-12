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
# Theorem 1 (free energy expansion): the definitions

These definitions specify the objects in Theorem 1 of J. Boursier and S. Serfaty,
*Multipole and Berezinskii–Kosterlitz–Thouless Transitions in the Two-component Plasma*
(arXiv:2509.09449, revised version 2026).

The definitions of the smeared Coulomb model, its finite combinatorial objects and
its parameter-dependent quantities below are shared by the challenge and solution.
Only the definitions used by the statement, including their dependencies, are included.
The original namespaces are retained inside `MultipoleBKTAudit.Theorem1`;
for example, `TwoComponentCoulomb.box` specifies the companion paper's square.
This module imports Mathlib only.
-/

@[expose] public section

namespace MultipoleBKTAudit.Theorem1

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

-- takes `χ` explicitly. total in `β`.
/-- `𝒵_β = 2π ∫₀^∞ e^{β g₁(r)} r dr`, eq. (2.19). -/
noncomputable def dipoleConstant (χ : ℂ → ℝ) (β : ℝ) : ℝ :=
  2 * Real.pi * ∫ r in Set.Ioi (0 : ℝ), Real.exp (β * smearedKernel χ 1 r) * r

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

-- total in `q` (`q = 0` gives `4`, never consumed).
/-- `β_q = 4 - 2/q`, eq. (1.3); used for `q ∈ ℕ*`. -/
noncomputable def transitionBeta (q : ℕ) : ℝ := 4 - 2 / q

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

/-- The hypertree weight `ω(X) = ∏_{a ∈ ⋃ᵢ X_i} (|{i ∈ [n] : a ∈ X_i}| - 1)!`. -/
def hypertreeWeight {α : Type*} [DecidableEq α] {n : ℕ} (X : Fin n → Finset α) : ℕ :=
  ∏ a ∈ Finset.univ.biUnion X, ((Finset.univ.filter fun i => a ∈ X i).card - 1).factorial

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

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

-- `tsum`s; summability is asserted by the theorems.
-- a function of the coefficient function `kdip : ℕ → ℝ`.
/-- The truncated Mayer series `Mayer_{β,p,λ}`, eq. (2.36):
`∑_{n ≥ 1} ∑_{k ≥ 1}` of `mayerTerm`, evaluated at the coefficients `kdip`. -/
noncomputable def mayer (p : ℕ) (kdip : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, ∑' k : ℕ+, mayerTerm p kdip n k

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
open TwoComponentCoulomb (box)

namespace MultipoleBKT

-- integration over `(Λ²)^N` as `c : Fin N → ℂ × ℂ`, `c i = (x_i, y_i)`.
-- takes `χ` explicitly. value in `[0, ∞]`.
/-- `Z_{N,β}^λ = ∫_{(Λ²)^N} exp(-β F_λ) dX_N dY_N`, eq. (2.9). -/
noncomputable def partitionFunction (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : ℝ≥0∞ :=
  ∫⁻ c in Set.univ.pi fun _ : Fin N => box N ×ˢ box N,
    ENNReal.ofReal (Real.exp (-β * energy χ lam c))

end MultipoleBKT

end

section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MultipoleBKT

open scoped Classical in
/-- The Ursell function `I(G) = ∑_{H ⊂ G} (-1)^{|E(H)|}`, Definition 2.4 (Definition 2.4,
eq. (2.29)), the sum over connected spanning subgraphs `H` of `G`. -/
noncomputable def ursell {V : Type*} [Fintype V] (G : SimpleGraph V) : ℤ :=
  ∑ H ∈ (Finset.univ : Finset (SimpleGraph V)).filter (fun H => H ≤ G ∧ H.Connected),
    (-1) ^ H.edgeFinset.card

end MultipoleBKT

end

end MultipoleBKTAudit.Theorem1

end
