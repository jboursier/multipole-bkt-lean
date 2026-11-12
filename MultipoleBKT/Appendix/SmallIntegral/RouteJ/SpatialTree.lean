/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EdgeProfiles

/-!
# The logarithmic spatial integral for a retained mixed tree

See Lemma A.4. Orient the retained tree, reindex
its odd family jointly, expand the endpoint sectors, and integrate the root
and independent edge coordinates.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset SimpleGraph Limits Peeling TwoComponentCoulomb
open scoped Classical ENNReal

/-- The mixed spatial profile on the original edge sets. -/
noncomputable def treeProfile {V : Type*} [Fintype V] [Nonempty V]
    (M lam : ℝ) (A E F : Finset (Sym2 V)) (c : V → ℂ × ℂ) : ℝ≥0∞ :=
  jointOdd (minRad lam c) (maxRad lam c) (fun e : A => (dipoleDistOn c e : ℂ)) *
    ((∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam c e)) *
      ∏ e ∈ F, ENNReal.ofReal (edgeProfile false M lam c e))

/-- The full spatial tree estimate, retaining the odd maximum tail.
The hypotheses state the three edge families of the same spanning tree.
See the proof of Lemma A.4. -/
theorem lintegral_treeProfile {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V],
      Fintype.card V = k + 1 → ∀ (T : SimpleGraph V), T.IsTree →
      ∀ (A E F : Finset (Sym2 V)), A ∪ (E ∪ F) = T.edgeFinset →
      Disjoint A (E ∪ F) → Disjoint E F →
      ∀ (root : V) (u : V → ℂ) (lam : ℝ), 0 < lam → ∀ N : ℕ,
      (∫⁻ x : V → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (x root) *
        treeProfile M lam A E F (ofPosVec x u)) ≤
          ENNReal.ofReal (C * N * (1 + Real.log (maxRho lam u / minRho lam u)) ^ k) := by
  obtain ⟨C, hC, hb⟩ := lintegral_endpoint_mixed_profiles hM k
  refine ⟨C, hC, fun V _ _ _ hV T hT A E F hpart hA hEF root u lam hlam N => ?_⟩
  obtain ⟨par, hpar, hinj, himg⟩ := exists_parent_of_isTree hT root
  let I := {i : V // i ≠ root}
  let eOf (i : I) : Sym2 V := s(i.val, par i.val)
  have heT (i : I) : eOf i ∈ T.edgeFinset := mem_edgeFinset.mpr (hpar i.val i.property).1
  let f : I → T.edgeFinset := fun i => ⟨eOf i, heT i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      exact hinj (mem_erase.mpr ⟨i.property, mem_univ _⟩)
        (mem_erase.mpr ⟨j.property, mem_univ _⟩) (congrArg Subtype.val hij)
    · intro e
      have he : e.val ∈ (univ.erase root).image (fun i => s(i, par i)) := by
        simpa only [himg] using e.property
      obtain ⟨i, hi, he⟩ := mem_image.mp he
      exact ⟨⟨i, (mem_erase.mp hi).1⟩, Subtype.ext he⟩
  let eqv := Equiv.ofBijective f hf
  let c₀ := ofPosVec (fun _ : V => (0 : ℂ)) u
  let s : Sym2 V → ℝ := edgeMin id (fun i => rho lam (u i))
  let t : Sym2 V → ℝ := radMax (fun i => rho lam (u i))
  let ev : Sym2 V → Bool := fun e => if e ∈ E then true else false
  let odd : I → Prop := fun i => eOf i ∈ A
  have hsub : A ⊆ T.edgeFinset := by rw [← hpart]; exact subset_union_left
  have hsdiff : T.edgeFinset \ A = E ∪ F := by
    rw [← hpart, union_sdiff_cancel_left hA]
  have hrad (x : V → ℂ) (e : Sym2 V) (b : Bool) :
      edgeProfile b M lam (ofPosVec x u) e =
        spatialProfile b M (s e) (t e) (dipoleDistOn (ofPosVec x u) e) / s e ^ 2 := by
    induction e using Sym2.ind with
    | h i j =>
      simp only [edgeProfile_mk, rhoD_mk, ofPosVec_apply, dipoleDistOn_mk,
        s, t, edgeMin_mk, id_eq, radMax_mk]
  let Φ := mixedDistanceProfile odd (fun i => ev (eOf i.val))
    (fun i => s (eOf i.val)) (fun i => t (eOf i.val)) M (minRho lam u) (maxRho lam u)
  have heq (x : V → ℂ) : treeProfile M lam A E F (ofPosVec x u) =
      Φ (fun i => dipoleDist (ofPosVec x u i) (ofPosVec x u (par i))) := by
    have hre := mixedDistanceProfile_reindex T.edgeFinset A hsub eqv ev s t
      (dipoleDistOn (ofPosVec x u)) M (minRho lam u) (maxRho lam u)
    change _ = mixedDistanceProfile (fun i => (eqv i).val ∈ A)
      (fun i => ev (eqv i.val)) (fun i => s (eqv i.val)) (fun i => t (eqv i.val))
      M (minRho lam u) (maxRho lam u) (fun i => dipoleDistOn (ofPosVec x u) (eqv i))
    rw [hre, hsdiff, prod_union hEF]
    unfold treeProfile
    rw [minRad_ofPosVec_eq, maxRad_ofPosVec_eq]
    congr 2
    · apply prod_congr rfl
      intro e he
      rw [hrad, show ev e = true by exact ite_eq_left he]
    · apply prod_congr rfl
      intro e he
      rw [hrad, show ev e = false by exact ite_eq_right (fun h => Finset.disjoint_left.mp hEF h he)]
  simp_rw [heq]
  apply hb V root par (fun i => T.dist i root) (fun i hi => (hpar i hi).2)
    (by
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_subtype_eq, hV]
      omega) u odd
  · exact minRho_pos hlam u
  · obtain ⟨i⟩ := ‹Nonempty V›
    exact (minRho_le_rho lam u i).trans (rho_le_maxRho lam u i)
  · intro i
    induction eOf i.val using Sym2.ind with
    | h a b =>
      dsimp only [s, t]
      simp only [edgeMin_mk, id_eq, radMax_mk]
      exact ⟨le_min (minRho_le_rho lam u a) (minRho_le_rho lam u b), min_le_max,
        max_le (rho_le_maxRho lam u a) (rho_le_maxRho lam u b)⟩

end MultipoleBKT.SmallIntegral.RouteJ

end
