/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.MarkedNormalization

/-!
# The common support and density in the original integral

See Lemma A.7, Step 3 of the proof of Lemma A.7. Nonzero common support
supplies connected blocks. Nonzero mixed density supplies the radial and
short-edge restrictions. All zero branches are treated before tree selection.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Hierarchical SmallIntegral RouteCases
open SmallIntegral.RouteJ SmallIntegral.RouteJext
open scoped Classical ENNReal

variable {W B : Type*} [Fintype W] [DecidableEq W] [Fintype B] [DecidableEq B]

/-- Every spatial support indicator is at most one. -/
theorem clusterSupport_le_one (M lam : ℝ) (blk : W → B)
    (Dn Dz : Finset (Sym2 W)) (c : W → ℂ × ℂ) :
    clusterSupport M lam blk Dn Dz c ≤ 1 := by
  have hb : (∏ S, nearConnInd M lam blk S c) ≤ 1 :=
    prod_le_one₀ (fun _ _ => by unfold nearConnInd; split_ifs <;> norm_num)
      (fun _ _ => by unfold nearConnInd; split_ifs <;> norm_num)
  have hf : (∏ e ∈ Dz, farInd M lam c e) ≤ 1 :=
    prod_le_one₀ (fun _ _ => farInd_nonneg c _) (fun _ _ => farInd_le_one c _)
  have hn : (∏ e ∈ Dn, linkIndE M lam c e) ≤ 1 :=
    prod_le_one₀ (fun _ _ => linkIndE_nonneg c _) (fun _ _ => linkIndE_le_one c _)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hb (prod_nonneg fun _ _ => farInd_nonneg c _))
    (prod_nonneg fun _ _ => linkIndE_nonneg c _)).trans (by simpa using
      (mul_le_mul_of_nonneg_right hf (prod_nonneg fun _ _ => linkIndE_nonneg c _)).trans (by simpa using hn))

/-- Nonzero common support gives exactly the connected blocks used in st3. -/
theorem connected_of_clusterSupport_ne_zero (M lam : ℝ) (blk : W → B)
    (Dn Dz : Finset (Sym2 W)) (c : W → ℂ × ℂ)
    (hc : clusterSupport M lam blk Dn Dz c ≠ 0) :
    ∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected := by
  intro b
  by_contra hb
  apply hc
  unfold clusterSupport
  rw [prod_eq_zero (mem_univ b) (show nearConnInd M lam blk b c = 0 from ite_eq_right hb),
    zero_mul,zero_mul]

/-- Off the radial or short-edge support the mixed density vanishes. -/
theorem mixedDensity_support (χ : ℂ → ℝ) (β lam h : ℝ)
    (Df : Finset (Sym2 W)) (c : W → ℂ × ℂ)
    (hc : mixedDensity χ β lam h Df c ≠ 0) :
    (∀ i, ‖(c i).1 - (c i).2‖ ≤ h) ∧ (∀ e ∈ Df, distE c e ≤ 17 * h) := by
  constructor
  · rcases cutInd_eq_one_or h c with hcut | hz
    · exact hcut.2
    · exact False.elim (hc (by unfold mixedDensity; rw [hz,mul_zero,zero_mul]))
  · rcases shortInd_eq_one_or (17 * h) Df c with hs | hz
    · exact hs.2
    · exact False.elim (hc (by unfold mixedDensity; rw [hz.1,mul_zero]))

omit [DecidableEq W] in
/-- The original density is below the product of literal cut dipole densities. -/
theorem mixedDensity_le_cutDens (χ : ℂ → ℝ) (β lam h : ℝ)
    (Df : Finset (Sym2 W)) (c : W → ℂ × ℂ) :
    mixedDensity χ β lam h Df c ≤ ∏ i, cutDens χ β lam h (c i) := by
  have he : (∏ i, cutDens χ β lam h (c i)) =
      (∏ i, pairDensity χ β lam (c i)) * cutInd h c := by
    unfold cutDens cutInd
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    by_cases hi : ‖(c i).1 - (c i).2‖ ≤ h
    · rw [indicator_of_mem (show ‖(c i).1 - (c i).2‖ ∈ Iic h from hi),ite_eq_left hi]; rfl
    · rw [indicator_of_notMem (show ‖(c i).1 - (c i).2‖ ∉ Iic h from hi),ite_eq_right hi]
  rw [he]
  exact mul_le_of_le_one_right
    (mul_nonneg (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le) (cutInd_nonneg h c))
    (shortInd_le_one _ _ _)

omit [DecidableEq W] in
/-- The squared radii and the cut dipole densities assemble into activityDensity. -/
theorem radial_mul_density (χ : ℂ → ℝ) (β lam h : ℝ) (c : W → ℂ × ℂ) :
    ENNReal.ofReal (∏ i, rhoD lam (c i) ^ 2) *
      ENNReal.ofReal (∏ i, cutDens χ β lam h (c i)) = activityDensity χ β lam h c := by
  rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => sq_nonneg _),
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => cutDens_nonneg _ _), ← prod_mul_distrib]
  rfl

end MultipoleBKT.ExpansionK.RouteSpatial

end
