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
public import MultipoleBKT.Frozen.IsMollifier
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.DipoleNormalization
public import MultipoleBKT.Frozen.DipoleActivity
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import MultipoleBKT.Frozen.TruncatedPartitionWeight
public import MultipoleBKT.Multipole.Switch

/-!
# Provider for the frozen statement `MultipoleBKT.lemma_5_46`

Registered implementation module of `MultipoleBKT/Frozen/Lemma546.lean`. Its export
`MultipoleBKT.Main.lemma_5_46` states and proves exactly the frozen statement.

The frozen statement imports this provider; this module never imports the frozen statement.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

@[expose] public section

namespace MultipoleBKT.Main

open scoped Classical in
/-- **Lemma 5.46**, eq. (5.164):
`(N C_{β,λ})^{-N} ∑_{π ∈ 𝚷_p([N])} Ẑ(π) = ∑_{n ≥ 0} (1/n!) ∑_{V_1, …, V_n ⊂ [N] disjoint,
2 ≤ |V_i| ≤ p} ∏ᵢ 𝖪^dip_{β,λ}(V_i)`. The statement equals the frozen statement
`MultipoleBKT.lemma_5_46`; the proof is `MultipoleBKT.Multipole.lemma_5_46_identity` with
`p = p(β) ≥ 1` (`MultipoleBKT.Multipole.one_le_pBeta`). -/
theorem lemma_5_46
    -- `χ` and `p₀` outermost
    {χ : ℂ → ℝ} (hχ : IsMollifier χ := by assumption) {p₀ : ℕ} (hp₀ : 1 ≤ p₀ := by assumption)
    {β : ℝ} (hβ : 2 < β := by assumption) :
    let p := pBeta p₀ β
    -- an exact identity for every `M > 20` (Definition 2.2), every
    -- `λ ∈ (0,1)` and every `N`
    ∀ M : ℝ, 20 < M → ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ N : ℕ,
      (((N : ℝ) * dipoleNormalization χ N β lam) ^ N)⁻¹ *
          ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π
        -- the series over `n` is a `tsum` with finitely many nonzero terms
        = ∑' n : ℕ, 1 / (n.factorial : ℝ) *
            ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter (fun V =>
                (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
              ∏ i, dipoleActivity χ N β lam (V i) := by
  intro p M hM lam hlam _ N
  exact Multipole.lemma_5_46_identity hχ hlam (by linarith) (Multipole.one_le_pBeta hp₀ hβ) N

end MultipoleBKT.Main

end
