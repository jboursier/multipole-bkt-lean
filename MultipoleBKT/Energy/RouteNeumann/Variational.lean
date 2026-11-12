/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.RouteNeumann.WeakBase
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The energy class for the Neumann problem

In (3.16), solutions have finite energy and their gradients are unique.
We use the energy completion of functions of class C¹ near the closed disc.
Both the potential and its gradient converge in L². The weak equation is
initially tested on those functions. Continuity extends it to the completion,
so testing the difference of two solutions requires no unstated testing step.
-/

@[expose] public section

open MeasureTheory Metric Set InnerProductSpace

namespace MultipoleBKT.RouteNeumann

/-- Potential and gradient in L² on the screening disc. -/
abbrev EnergyPair (z : ℂ) (τ : ℝ) :=
  Lp ℝ 2 (volume.restrict (ball z τ)) × Lp ℂ 2 (volume.restrict (ball z τ))

/-- Classical potential-gradient pairs on a neighborhood of the closed disc.
The L² witnesses only construct the equivalence classes. -/
def classicalPairs (z : ℂ) (τ : ℝ) : Set (EnergyPair z τ) :=
  {U | ∃ (u : ℂ → ℝ) (F : ℂ → ℂ) (ρ : ℝ), τ < ρ ∧
    ContDiffOn ℝ 1 u (ball z ρ) ∧
    (∀ w ∈ ball z ρ, HasGradientAt u (F w) w) ∧
    ∃ (hu : MemLp u 2 (volume.restrict (ball z τ)))
      (hF : MemLp F 2 (volume.restrict (ball z τ))),
      U = (hu.toLp u, hF.toLp F)}

/-- The finite-energy space is the closure of classical potential-gradient
pairs for simultaneous L² convergence. This definition explicitly records the
approximating class used in the variational Neumann problem. -/
def energySpace (z : ℂ) (τ : ℝ) : Set (EnergyPair z τ) := closure (classicalPairs z τ)

/-- A finite-energy weak Neumann solution with L² density `f`.
Tests may reach the boundary and impose the zero normal data variationally. -/
def IsWeakSolution (z : ℂ) (τ : ℝ)
    (f : Lp ℝ 2 (volume.restrict (ball z τ))) (U : EnergyPair z τ) : Prop :=
  U ∈ energySpace z τ ∧ ∀ V ∈ classicalPairs z τ,
    inner ℝ U.2 V.2 = inner ℝ f V.1

/-- The weak equation holds for every energy test. The proof is exactly the
continuous extension from the specified dense classical class. -/
theorem IsWeakSolution.test {z : ℂ} {τ : ℝ}
    {f : Lp ℝ 2 (volume.restrict (ball z τ))} {U : EnergyPair z τ}
    (hU : IsWeakSolution z τ f U) {V : EnergyPair z τ} (hV : V ∈ energySpace z τ) :
    inner ℝ U.2 V.2 = inner ℝ f V.1 := by
  have hc : IsClosed {V : EnergyPair z τ | inner ℝ U.2 V.2 = inner ℝ f V.1} :=
    isClosed_eq (continuous_const.inner continuous_snd) (continuous_const.inner continuous_fst)
  exact closure_minimal hU.2 hc hV

/-- The difference of two weak solutions has zero gradient, by using both
solutions as energy tests and subtracting. This is the harmonic zero Neumann
uniqueness argument after (3.19). -/
theorem gradient_unique {z : ℂ} {τ : ℝ}
    {f : Lp ℝ 2 (volume.restrict (ball z τ))} {U V : EnergyPair z τ}
    (hU : IsWeakSolution z τ f U) (hV : IsWeakSolution z τ f V) : U.2 = V.2 := by
  have hUU := hU.test hU.1
  have hUV := hU.test hV.1
  have hVU := hV.test hU.1
  have hVV := hV.test hV.1
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hUU, hUV, hVU, hVV]
  ring

/-- A continuous function on the closed disc belongs to L² on the open disc. -/
theorem memLp_of_continuousOn_closedBall {E : Type*} [NormedAddCommGroup E]
    {z : ℂ} {τ : ℝ} {u : ℂ → E} (hu : ContinuousOn u (closedBall z τ)) :
    MemLp u 2 (volume.restrict (ball z τ)) := by
  let : IsFiniteMeasure (volume.restrict (ball z τ)) :=
    ⟨by simpa using (measure_ball_lt_top (μ := volume) (x := z) (r := τ))⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall z τ).exists_bound_of_continuousOn hu
  refine MemLp.of_bound ((hu.mono ball_subset_closedBall).aestronglyMeasurable
    measurableSet_ball) C ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
  exact hC w (ball_subset_closedBall hw)

end MultipoleBKT.RouteNeumann
