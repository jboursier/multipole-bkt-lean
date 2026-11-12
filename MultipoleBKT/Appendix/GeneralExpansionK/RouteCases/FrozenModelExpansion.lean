/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.FrozenMixed

/-!
# The concrete five-subset expansion of the original frozen model

See (A.51). The original cluster integrand is transported to the
extended screening model before reversal averaging and expansion.
All common density and support factors multiply the resulting terms.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Hierarchical UpperBound BoundedUpper SmallIntegral

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ L : ℝ}
variable {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- The extended radius is invariant under a dipole reversal. -/
theorem routeFrozenRadius_swap (d : ℂ × ℂ) :
    routeFrozenRadius p₀ β lam ε₀ V Z d.swap = routeFrozenRadius p₀ β lam ε₀ V Z d := by
  unfold routeFrozenRadius
  rw [goodRadiusZ_swap, norm_swap_sub]

section Expansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- The concrete original expansion, with the original frozen integrands on the
left and the extended correction functions on the right. This identity explains
which correction functions a termwise pointwise bound must control. -/
theorem clusterQ_frozen_five_subset_error {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (hlam : 0 < lam) (hlh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V)
    (blk : ι → κ) (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ)
    (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    ((∑ A : Finset κ,
        (clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
            (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df
            (flipCfg (blockLabels blk A) c) -
          clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
            (flipCfg (blockLabels blk A) c))) / 2 ^ Fintype.card κ) *
        mixedDensity χ β lam (ε₀ * truncationScale p₀ β lam) Df c =
      ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        ∑ P ∈ (fiveSubsets O (Df \ O) (intraEdges blk) univ).erase (∅, ∅, ∅, ∅, ∅),
          clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
            fiveTerm O (Df \ O) (intraEdges blk)
              (gammaW β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) M lam c)
              (gammaW β (dipoleInteraction χ lam) M lam c)
              (fun e => alphaW β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) M lam c e + linkIndE M lam c e)
              (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
              (intraRatio β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) (dipoleInteraction χ lam) c)
              (routeFrozenQuadratic p₀ β lam ε₀ L V Z ∘ c)
              (routeFrozenBad p₀ β lam M ε₀ V Z ∘ c) P *
                mixedDensity χ β lam (ε₀ * truncationScale p₀ β lam) Df c := by
  have hcut' : ∀ A : Finset κ, ∀ i,
      ‖(flipCfg (blockLabels blk A) c i).1 - (flipCfg (blockLabels blk A) c i).2‖ ≤
        ε₀ * truncationScale p₀ β lam := by
    intro A i
    rw [flipCfg_apply]
    split_ifs
    · rw [norm_swap_sub]
      exact hcut i
    · exact hcut i
  have htransport : ∀ A : Finset κ,
      clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df
          (flipCfg (blockLabels blk A) c) =
        clusterQ β (routeFrozenInteraction χ p₀ β lam ε₀ V Z)
          (fun d => (1 + routeFrozenQuadratic p₀ β lam ε₀ L V Z d) *
            (1 + routeFrozenBad p₀ β lam M ε₀ V Z d)) M lam blk Dn Dz Df
          (flipCfg (blockLabels blk A) c) :=
    fun A => clusterQ_frozen_extension hlam hlh hM hV blk Dn Dz Df _ (hcut' A)
  simp_rw [htransport]
  have hwl : ∀ d e, routeFrozenInteraction χ p₀ β lam ε₀ V Z d.swap e =
      -routeFrozenInteraction χ p₀ β lam ε₀ V Z d e := by
    intro d e
    unfold routeFrozenInteraction
    rw [routeFrozenRadius_swap, pairInteraction_swap_left]
  have hwr : ∀ d e, routeFrozenInteraction χ p₀ β lam ε₀ V Z d e.swap =
      -routeFrozenInteraction χ p₀ β lam ε₀ V Z d e := by
    intro d e
    unfold routeFrozenInteraction
    rw [routeFrozenRadius_swap, pairInteraction_swap_right]
  have hu : ∀ d, routeFrozenQuadratic p₀ β lam ε₀ L V Z d.swap =
      routeFrozenQuadratic p₀ β lam ε₀ L V Z d := by
    intro d
    unfold routeFrozenQuadratic
    rw [routeFrozenRadius_swap, norm_swap_sub]
  have hv : ∀ d, routeFrozenBad p₀ β lam M ε₀ V Z d.swap =
      routeFrozenBad p₀ β lam M ε₀ V Z d := by
    intro d
    simp only [routeFrozenBad, isGoodZ_swap]
  rw [clusterQ_five_subset_error ((one_le_pow₀ (a := (3 : ℝ)) (by norm_num)).trans hM)
    _ _ _ _ hwl hwr
    (fun d e => Limits.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Limits.dipoleInteraction_swap_right d e hχ lam) hu hv]
  simp_rw [sum_mul]

end Expansion

end MultipoleBKT.ExpansionK.RouteCases

end
