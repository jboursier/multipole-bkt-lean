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
public import TwoComponentCoulomb.Frozen.LogKernel
public import MultipoleBKT.Frozen.SmearedCharge
public import MultipoleBKT.Frozen.Kappa

/-!
# Frozen: `MultipoleBKT.energy`

See the paper, equation (2.5).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (logKernel)

@[expose] public section

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
