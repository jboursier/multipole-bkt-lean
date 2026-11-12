/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Sectors
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ProductCoordinates
public import MultipoleBKT.LowerBound.Peeling.Dipole

/-!
# Independent endpoint coordinates for a fixed spatial tree

The proof of Lemma 4.58. Keep the tree fixed, split
into the four endpoint sectors on each edge, and apply the Jacobian-one
change of variables of (A.9). Tonelli separates the root and the edges.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RoutePosition

open MeasureTheory Finset SimpleGraph Limits
open SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- Spatial integration along a fixed tree through endpoint coordinates.
The edge profiles may have cutoffs and need not be monotone. -/
theorem lintegral_endpoint_product_le {V : Type*} [Fintype V] [DecidableEq V]
    {T : SimpleGraph V} (hT : T.IsTree) (root : V) (u : V → ℂ)
    (φ : Sym2 V → ℝ → ℝ≥0∞) (hφ : ∀ e, Measurable (φ e))
    (H : ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x : V → ℂ, H (x root) * ∏ e ∈ T.edgeFinset,
      φ e (Peeling.dipoleDistOn (ofPosVec x u) e)) ≤
      (∫⁻ t : ℂ, H t) * ∏ e ∈ T.edgeFinset, (4 * ∫⁻ z : ℂ, φ e ‖z‖) := by
  obtain ⟨par, hpar, hinj, himg⟩ := exists_parent_of_isTree hT root
  let I := {i : V // i ≠ root}
  let eOf (i : I) : Sym2 V := s(i.val, par i.val)
  have hre (f : Sym2 V → ℝ≥0∞) : (∏ i : I, f (eOf i)) = ∏ e ∈ T.edgeFinset, f e := by
    apply prod_bij (fun i _ => eOf i)
    · intro i _
      exact mem_edgeFinset.mpr (hpar i.val i.property).1
    · intro i _ j _ hij
      exact Subtype.ext (hinj (mem_erase.mpr ⟨i.property, mem_univ _⟩)
        (mem_erase.mpr ⟨j.property, mem_univ _⟩) hij)
    · intro e he
      rw [← himg] at he
      obtain ⟨i, hi, he⟩ := mem_image.mp he
      exact ⟨⟨i, (mem_erase.mp hi).1⟩, mem_univ _, he⟩
    · intro i _
      rfl
  let Φ : (I → ℝ) → ℝ≥0∞ := fun d => ∏ i, φ (eOf i) (d i)
  have hΦ : Measurable Φ := Finset.measurable_prod univ fun i _ =>
    (hφ _).comp (measurable_pi_apply i)
  have hb := lintegral_endpoint_sectors root par (fun i => T.dist i root)
    (fun i hi => (hpar i hi).2) u H hH Φ hΦ
  have heq (x : V → ℂ) : (∏ e ∈ T.edgeFinset,
      φ e (Peeling.dipoleDistOn (ofPosVec x u) e)) =
      Φ (fun i => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) := by
    rw [← hre]
    rfl
  simp_rw [heq]
  refine hb.trans_eq ?_
  rw [lintegral_root_coordinates root H hH
    (fun z : I → ℂ => ∏ i, φ (eOf i) ‖z i‖)
    (Finset.measurable_prod univ fun i _ => (hφ _).comp (by fun_prop))]
  have hp : (∫⁻ z : I → ℂ, ∏ i, φ (eOf i) ‖z i‖) =
      ∏ i : I, ∫⁻ z : ℂ, φ (eOf i) ‖z‖ := by
    rw [volume_pi]
    exact lintegral_pi_prod (fun _ => (volume : Measure ℂ))
      (fun i z => φ (eOf i) ‖z‖) (fun i => (hφ _).comp (by fun_prop))
  change 4 ^ Fintype.card I * ((∫⁻ t, H t) * ∫⁻ z : I → ℂ, ∏ i, φ (eOf i) ‖z i‖) = _
  rw [hp, ← hre, prod_mul_distrib, prod_const, card_univ]
  ring

end MultipoleBKT.AbsoluteLower.RoutePosition

end
