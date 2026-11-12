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
public import TwoComponentCoulomb.Frozen.Box
public import MultipoleBKT.Frozen.IsMollifier
public import MultipoleBKT.Frozen.Energy
public import MultipoleBKT.Frozen.PBeta
public import MultipoleBKT.Frozen.ErrorRate
public import MultipoleBKT.Frozen.StableMatching
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import MultipoleBKT.Frozen.TruncatedPartitionWeight
import MultipoleBKT.Main.Proposition545

/-!
# Frozen: `MultipoleBKT.proposition_5_45`

See the paper, Proposition 5.45.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

namespace MultipoleBKT

open scoped Classical in
/-- **Proposition 5.45**, eq. (5.161):
`log ∫_{σ_N = Id} e^{-βF_λ} = log ∑_{π ∈ 𝚷_p([N])} Ẑ(π) + O_{β,p,M}(Nδ_{β,λ})`. -/
theorem proposition_5_45
    -- `χ` and `p₀` outermost
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- "For `M` large enough with respect to `β, p`"
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      -- "`λ` small enough and `N` large enough depending on `λ`";
      -- `O_{β,p,M}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          -- `∫_{σ_N = Id}` as `∫⁻` over `(Λ²)^N ∩ {σ_N = Id}`
          let zId : ℝ≥0∞ := ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
              {c | stableMatching c = Equiv.refl (Fin N)},
            ENNReal.ofReal (Real.exp (-β * energy χ lam c))
          let zHat : ℝ := ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π
          -- both logarithms are of positive finite
          -- quantities, asserted; then the two-sided bound
          0 < zId ∧ zId < ∞ ∧ 0 < zHat ∧
            |Real.log zId.toReal - Real.log zHat| ≤ C * N * errorRate p₀ β lam :=
  by exact MultipoleBKT.Main.proposition_5_45

end MultipoleBKT

end
