/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.Decomposition
public import MultipoleBKT.Matching.RouteGeneric.ConfigurationRelabel
public import Mathlib.Logic.Equiv.Fintype

/-!
# Simultaneous relabeling in the starting upper bound

The paper: (5.60) and (5.61). The relabeling preserves volume and energy. The hierarchical relabeling transports
matching and bad labels off the distance exceptional set. The induced graph
isomorphism transports the good multipoles as well.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT.UpperBound.RouteExchange

open Hierarchical Multipole SetPartition TheoremTwo PropFiveFortyFive

variable {N p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- Simultaneous permutation of both charge species. -/
noncomputable def relabel (e : Equiv.Perm (Fin N)) :
    (Fin N → ℂ × ℂ) ≃ᵐ (Fin N → ℂ × ℂ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ × ℂ) e.symm

theorem relabel_apply (e : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) :
    relabel e c = c ∘ e := by
  funext i
  simp [relabel, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem measurePreserving_relabel (e : Equiv.Perm (Fin N)) :
    MeasurePreserving (relabel e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℂ × ℂ) e.symm

theorem energy_relabel (χ : ℂ → ℝ) (lam : ℝ) (e : Equiv.Perm (Fin N))
    (c : Fin N → ℂ × ℂ) : energy χ lam (relabel e c) = energy χ lam c := by
  simp only [energy, relabel_apply, Function.comp_apply]
  congr 2
  conv_lhs =>
    rw [← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs =>
    rw [← Equiv.sum_comp e.symm]
    simp only [Equiv.apply_symm_apply]

theorem relabel_mem_box (e : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) :
    relabel e c ∈ (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ↔
      c ∈ (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) := by
  simp only [Set.mem_univ_pi, relabel_apply, Function.comp_apply]
  exact ⟨fun h i => by simpa using h (e.symm i), fun h i => h (e i)⟩

/-- The permutation on natural labels fixes every label outside `[N]`. -/
noncomputable def natPerm (e : Equiv.Perm (Fin N)) : Equiv.Perm ℕ :=
  e.viaFintypeEmbedding Fin.valEmbedding

theorem natPerm_apply (e : Equiv.Perm (Fin N)) (i : Fin N) : natPerm e i = e i :=
  Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _

/-- Transport a family of blocks by the permutation of its labels. -/
noncomputable def mapBlocks (e : Equiv.Perm (Fin N)) (π : Finset (Finset ℕ)) :
    Finset (Finset ℕ) := π.image (fun S => S.map (natPerm e).toEmbedding)

theorem mapBlocks_injective (e : Equiv.Perm (Fin N)) : Function.Injective (mapBlocks e) :=
  Finset.image_injective (Finset.map_injective _)

theorem blockCount_mapBlocks (e : Equiv.Perm (Fin N)) (π : Finset (Finset ℕ)) (p : ℕ) :
    blockCount p (mapBlocks e π) = blockCount p π := by
  classical
  funext i
  simp only [blockCount, mapBlocks, Finset.filter_image, Finset.card_map]
  exact Finset.card_image_of_injective _ (Finset.map_injective _)

private theorem matching_relabel {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (e : Equiv.Perm (Fin N)) :
    stableMatching (relabel e c) = e.symm * stableMatching c * e := by
  have he : RouteGeneric.relabelCharges e e c = relabel e c := by
    ext i <;> simp [RouteGeneric.relabelCharges, relabel_apply]
  rw [← he]
  exact RouteGeneric.stableMatching_permutation hc e e

theorem matching_relabel_iff {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (e : Equiv.Perm (Fin N)) :
    stableMatching (relabel e c) = Equiv.refl _ ↔ stableMatching c = Equiv.refl _ := by
  rw [matching_relabel hc]
  change e⁻¹ * stableMatching c * e = 1 ↔ stableMatching c = 1
  constructor
  · intro h
    have := congrArg (fun s => e * s * e⁻¹) h
    simpa [mul_assoc] using this
  · intro h
    simp [h]

private noncomputable def graphIso {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (e : Equiv.Perm (Fin N)) :
    multipoleGraph M lam (relabel e c) ≃g multipoleGraph M lam c := by
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro i j
  simp only [multipoleGraph, SimpleGraph.fromRel_adj]
  rw [matching_relabel hc]
  simp only [relabel_apply, Function.comp_apply, Equiv.Perm.mul_apply, Equiv.apply_symm_apply,
    e.injective.ne_iff]

/-- The good blocks commute with the same permutation as the bad labels. -/
theorem goodBlocks_relabel {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (e : Equiv.Perm (Fin N)) :
    mapBlocks e (goodBlocks p₀ β lam M ε₀ (relabel e c)) = goodBlocks p₀ β lam M ε₀ c := by
  classical
  let g := graphIso (M := M) (lam := lam) hc e
  have hr : Function.Injective fun i => ‖(matched c i).1 - (matched c i).2‖ := by
    intro i j hij
    exact congrArg Prod.fst (hc (show
      (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
        (i, stableMatching c i) =
      (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
        (j, stableMatching c j) from hij))
  have hm : matched (relabel e c) = matched c ∘ e := by
    funext i
    unfold matched
    rw [matching_relabel hc]
    simp only [relabel_apply, Function.comp_apply, Equiv.Perm.mul_apply,
      Equiv.apply_symm_apply]
  have hgood : goodPoints p₀ β lam M ε₀ (matched c) =
      (goodPoints p₀ β lam M ε₀ (matched (relabel e c))).map e.toEmbedding := by
    rw [hm]
    exact BadPointTypes.Permutation.goodPoints_permutation e p₀ β lam M ε₀ (matched c) hr
  have hcomp : ∀ C, (componentLabels M lam (relabel e c) C).map (natPerm e).toEmbedding =
      componentLabels M lam c (g.connectedComponentEquiv C) := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ i =>
      ext n
      simp only [Finset.mem_map, mem_componentLabels]
      constructor
      · rintro ⟨k, ⟨j, hj, rfl⟩, rfl⟩
        refine ⟨e j, ?_, natPerm_apply e j |>.symm⟩
        exact congrArg g.connectedComponentEquiv hj
      · rintro ⟨j, hj, rfl⟩
        refine ⟨(e.symm j : ℕ), ⟨e.symm j, ?_, rfl⟩, ?_⟩
        · apply g.connectedComponentEquiv.injective
          simp only [SimpleGraph.Iso.connectedComponentEquiv_apply,
            SimpleGraph.ConnectedComponent.map_mk] at hj
          change (multipoleGraph M lam c).connectedComponentMk j =
            (multipoleGraph M lam c).connectedComponentMk (e i) at hj
          change (multipoleGraph M lam c).connectedComponentMk (e (e.symm j)) =
            (multipoleGraph M lam c).connectedComponentMk (e i)
          simpa only [Equiv.apply_symm_apply] using hj
        · simp only [Equiv.coe_toEmbedding, natPerm_apply, Equiv.apply_symm_apply]
  have hsupp : ∀ C, C.supp ⊆ ↑(goodPoints p₀ β lam M ε₀ (matched (relabel e c))) ↔
      (g.connectedComponentEquiv C).supp ⊆ ↑(goodPoints p₀ β lam M ε₀ (matched c)) := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ i =>
      simp only [Set.subset_def, Finset.mem_coe, SimpleGraph.ConnectedComponent.mem_supp_iff]
      constructor
      · intro h j hj
        rw [hgood]
        refine Finset.mem_map.2 ⟨e.symm j, h _ ?_, e.apply_symm_apply j⟩
        apply g.connectedComponentEquiv.injective
        simp only [SimpleGraph.Iso.connectedComponentEquiv_apply,
          SimpleGraph.ConnectedComponent.map_mk] at hj
        change (multipoleGraph M lam c).connectedComponentMk j =
          (multipoleGraph M lam c).connectedComponentMk (e i) at hj
        change (multipoleGraph M lam c).connectedComponentMk (e (e.symm j)) =
          (multipoleGraph M lam c).connectedComponentMk (e i)
        simpa only [Equiv.apply_symm_apply] using hj
      · intro h j hj
        have hj' := h (e j) (congrArg g.connectedComponentEquiv hj)
        rw [hgood] at hj'
        exact (Finset.mem_map' e.toEmbedding).1 hj'
  ext S
  simp only [mapBlocks, goodBlocks, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨g.connectedComponentEquiv C, (hsupp C).1 hC, (hcomp C).symm⟩
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨D, rfl⟩ := g.connectedComponentEquiv.surjective C
    exact ⟨_, ⟨D, (hsupp D).2 hC, rfl⟩, hcomp D⟩

end MultipoleBKT.UpperBound.RouteExchange

end
