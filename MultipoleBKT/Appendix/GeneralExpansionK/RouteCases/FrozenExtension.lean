/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ModelExpansion
public import MultipoleBKT.Appendix.GeneralExpansionK.ZPointwise

/-!
# The frozen screening extension used before expanding

See the proof of
Lemma A.6 and the opening paragraph of
Lemma A.7. The radius is extended by its maximum
with one quarter of the dipole length. The full model integrand is unchanged
on the cutoff support. Individual mixed terms use this extended interaction.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Hierarchical UpperBound BoundedUpper MultipoleIntegralZ SmallIntegral

variable {N : ℕ}

/-- The paper's whole-carrier extension of the frozen screening radius. -/
noncomputable def routeFrozenRadius (p₀ : ℕ) (β lam ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ) : ℝ :=
  max (goodRadiusZ p₀ β lam ε₀ V Z d) (‖d.1 - d.2‖ / 4)

/-- The frozen interaction with the extended endpoint radii. -/
noncomputable def routeFrozenInteraction (χ : ℂ → ℝ) (p₀ : ℕ) (β lam ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d e : ℂ × ℂ) : ℝ :=
  pairInteraction χ lam d e
    (routeFrozenRadius p₀ β lam ε₀ V Z d, routeFrozenRadius p₀ β lam ε₀ V Z d)
    (routeFrozenRadius p₀ β lam ε₀ V Z e, routeFrozenRadius p₀ β lam ε₀ V Z e)

/-- The quadratic correction in the five-subset expansion of the frozen model. -/
noncomputable def routeFrozenQuadratic (p₀ : ℕ) (β lam ε₀ L : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ) : ℝ :=
  Real.exp (L * (‖d.1 - d.2‖ / routeFrozenRadius p₀ β lam ε₀ V Z d) ^ 2) - 1

open scoped Classical in
/-- The second vertex correction is minus the bad-label indicator. -/
noncomputable def routeFrozenBad (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ) : ℝ :=
  if IsGoodZ p₀ β lam M ε₀ V Z d then 0 else -1

/-- The extension is bounded below by both geometric lower bounds. -/
theorem routeFrozenRadius_lower (p₀ : ℕ) (β lam ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (d : ℂ × ℂ) :
    lam ≤ routeFrozenRadius p₀ β lam ε₀ V Z d ∧
      ‖d.1 - d.2‖ / 4 ≤ routeFrozenRadius p₀ β lam ε₀ V Z d :=
  ⟨(lam_le_goodRadiusZ d).trans (le_max_left _ _), le_max_right _ _⟩

/-- On the good-point cutoff support the extended radius is the original one. -/
theorem routeFrozenRadius_eq {p₀ : ℕ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hlam : 0 < lam) (hlh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V)
    {d : ℂ × ℂ} (hgood : IsGoodZ p₀ β lam M ε₀ V Z d)
    (hcut : ‖d.1 - d.2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    routeFrozenRadius p₀ β lam ε₀ V Z d = goodRadiusZ p₀ β lam ε₀ V Z d := by
  exact max_eq_left (div_four_le_goodRadiusZ hlam hlh hM (hV.symm ▸ subset_rfl) hgood hcut)

section Transport

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- The actual cluster integrand equals the extended model before expanding.
A bad vertex annihilates both integrands. On the all-good support every
interaction and one-body factor agrees separately. -/
theorem clusterQ_frozen_extension {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hlam : 0 < lam) (hlh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hV : badPointsOn p₀ β lam M ε₀ V Z = V)
    (blk : ι → κ) (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ)
    (hcut : ∀ i, ‖(c i).1 - (c i).2‖ ≤ ε₀ * truncationScale p₀ β lam) :
    clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df c =
      clusterQ β (routeFrozenInteraction χ p₀ β lam ε₀ V Z)
        (fun d => (1 + routeFrozenQuadratic p₀ β lam ε₀ L V Z d) *
          (1 + routeFrozenBad p₀ β lam M ε₀ V Z d)) M lam blk Dn Dz Df c := by
  by_cases hg : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (c i)
  · have hτ : ∀ i, routeFrozenRadius p₀ β lam ε₀ V Z (c i) =
        goodRadiusZ p₀ β lam ε₀ V Z (c i) :=
      fun i => routeFrozenRadius_eq hlam hlh hM hV (hg i) (hcut i)
    have hw : ∀ i j, routeFrozenInteraction χ p₀ β lam ε₀ V Z (c i) (c j) =
        interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) := by
      intro i j
      simp only [routeFrozenInteraction, hτ, interactionGoodZ]
    have hψ : ∀ i, (1 + routeFrozenQuadratic p₀ β lam ε₀ L V Z (c i)) *
        (1 + routeFrozenBad p₀ β lam M ε₀ V Z (c i)) =
        dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) := by
      intro i
      simp [routeFrozenQuadratic, routeFrozenBad, dipoleWeightZ, hg i, hτ i]
    have hf : farBondW β (routeFrozenInteraction χ p₀ β lam ε₀ V Z) M lam c =
        farBondW β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam c := by
      funext e
      induction e using Sym2.ind with
      | h i j => simp only [farBondW, symmLift_mk, farBondWij, sOrd, stableWeight, hw]
    unfold clusterQ clusterG
    simp only [prod_blockWW_eq, hψ, hf, stableWeight, hw]
  · push Not at hg
    obtain ⟨i, hi⟩ := hg
    have hψ₀ : dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) = 0 := by
      simp [dipoleWeightZ, hi]
    have hψ₁ : (1 + routeFrozenQuadratic p₀ β lam ε₀ L V Z (c i)) *
        (1 + routeFrozenBad p₀ β lam M ε₀ V Z (c i)) = 0 := by
      simp [routeFrozenBad, hi]
    have hp₀ : (∏ j, dipoleWeightZ p₀ β lam M ε₀ L V Z (c j)) = 0 :=
      prod_eq_zero (f := fun j => dipoleWeightZ p₀ β lam M ε₀ L V Z (c j)) (mem_univ i) hψ₀
    have hp₁ : (∏ j, (1 + routeFrozenQuadratic p₀ β lam ε₀ L V Z (c j)) *
        (1 + routeFrozenBad p₀ β lam M ε₀ V Z (c j))) = 0 :=
      prod_eq_zero (f := fun j => (1 + routeFrozenQuadratic p₀ β lam ε₀ L V Z (c j)) *
        (1 + routeFrozenBad p₀ β lam M ε₀ V Z (c j))) (mem_univ i) hψ₁
    unfold clusterQ clusterG
    simp only [prod_blockWW_eq, hp₀, hp₁, mul_zero, zero_mul]

end Transport

end MultipoleBKT.ExpansionK.RouteCases

end
