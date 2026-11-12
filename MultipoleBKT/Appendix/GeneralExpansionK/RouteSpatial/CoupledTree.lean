/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.UncutFamily

/-!
# Endpoint sectors for a coupled profile on the whole original tree

See Step 3 of
the proof of Lemma A.7. The edge profile can contain
both a single global odd tail and the distinguished exterior even edge.
The root and all edge coordinates are separated after the endpoint sectors.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- Endpoint sectors for an arbitrary measurable coupled profile of all tree
edge distances. This permits joint odd integration with a retained long even mark. -/
theorem lintegral_coupled_tree_le {W : Type*} [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) (hT : T.IsTree) (root : W) (u : W → ℂ)
    (H : ℂ → ℝ≥0∞) (hH : Measurable H)
    (Φ : (T.edgeFinset → ℝ) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ x : W → ℂ, H (x root) * Φ (fun e => dipoleDistOn (ofPosVec x u) e)) ≤
      (4 : ℝ≥0∞) ^ (Fintype.card W - 1) *
        ((∫⁻ t, H t) * ∫⁻ z : T.edgeFinset → ℂ, Φ (fun e => ‖z e‖)) := by
  obtain ⟨par,hpar,hinj,himg⟩ := exists_parent_of_isTree hT root
  let I := {i : W // i ≠ root}
  let f (i : I) : T.edgeFinset := ⟨s(i.val,par i.val),mem_edgeFinset.2 (hpar i.val i.property).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      exact Subtype.ext (hinj (mem_erase.2 ⟨i.property,mem_univ _⟩)
        (mem_erase.2 ⟨j.property,mem_univ _⟩) (congrArg Subtype.val he))
    · intro e
      have he : e.val ∈ (univ.erase root).image (fun i => s(i,par i)) := by rw [himg]; exact e.property
      obtain ⟨i,hi,he⟩ := mem_image.1 he
      exact ⟨⟨i,(mem_erase.1 hi).1⟩,Subtype.ext he⟩
  let e := Equiv.ofBijective f hf
  let Ψ (d : I → ℝ) := Φ (fun j => d (e.symm j))
  have hΨ : Measurable Ψ := hΦ.comp (by fun_prop)
  have hs := lintegral_endpoint_sectors root par (fun i => T.dist i root)
    (fun i hi => (hpar i hi).2) u H hH Ψ hΨ
  have hre (x : W → ℂ) : Ψ (fun i => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) =
      Φ (fun j => dipoleDistOn (ofPosVec x u) j) := by
    unfold Ψ
    congr 1
    funext j
    have hj : (f (e.symm j)).val = j.val := congrArg Subtype.val (e.apply_symm_apply j)
    rw [← hj]
    rfl
  change (∫⁻ x : W → ℂ, H (x root) * Ψ
    (fun i : I => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i)))) ≤ _ at hs
  simp_rw [hre] at hs
  have hnorm : Measurable (fun z : T.edgeFinset → ℂ => Φ (fun j => ‖z j‖)) := hΦ.comp (by fun_prop)
  have hp := (volume_measurePreserving_piCongrLeft (fun _ : T.edgeFinset => ℂ) e).lintegral_comp hnorm
  have hcomp (z : I → ℂ) : Φ (fun j => ‖(MeasurableEquiv.piCongrLeft (fun _ : T.edgeFinset => ℂ) e z) j‖) =
      Ψ (fun i => ‖z i‖) := by
    simp [Ψ,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  simp_rw [hcomp] at hp
  have hI : Fintype.card I = Fintype.card W - 1 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_subtype_eq]
  have hr := lintegral_root_coordinates root H hH
    (fun z : I → ℂ => Ψ (fun i => ‖z i‖)) (hΨ.comp (show Measurable (fun z : I → ℂ => fun i : I => ‖z i‖) by fun_prop))
  rw [hr,hI,hp] at hs
  exact hs

end MultipoleBKT.ExpansionK.RouteSpatial

end
