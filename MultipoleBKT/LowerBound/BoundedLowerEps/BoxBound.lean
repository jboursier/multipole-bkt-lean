/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.BoundedLowerEps.Pointwise

/-!
# Density and cardinality interfaces for the lower activities

The proof of Proposition 4.23. The radial cutoff is written as
its literal density. The grouped route bounds the number of possible pairs.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLowerEps

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits SmallIntegral Hierarchical Parity
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {X : Finset (Finset ℕ)}

/-- The density of `μ_{β,λ,ε₀}` is `(N C_{β,λ,ε₀})^{-1} cutDens`. -/
theorem indicator_exp_eq_cutDens (R : ℝ) (p : ℂ × ℂ) :
    (Metric.closedBall (0 : ℂ) R).indicator (fun w => Real.exp (β * smearedKernel χ lam w))
      (p.1 - p.2) = cutDens χ β lam R p := by
  unfold cutDens pairDensity
  by_cases h : ‖p.1 - p.2‖ ≤ R
  · rw [Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right]),
      Set.indicator_of_mem (show ‖p.1 - p.2‖ ∈ Set.Iic R from h), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (by rwa [Metric.mem_closedBall, dist_zero_right]),
      Set.indicator_of_notMem (show ‖p.1 - p.2‖ ∉ Set.Iic R from h), mul_zero]
theorem card_pairsOn_le (V : Finset ℕ) : (pairsOn V).card ≤ V.card ^ 2 :=
  calc (pairsOn V).card ≤ (V ×ˢ V).card := card_filter_le _ _
    _ = V.card ^ 2 := by rw [card_product, sq]

end BoundedLowerEps

end MultipoleBKT

end
