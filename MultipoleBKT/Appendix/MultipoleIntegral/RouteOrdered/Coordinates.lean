/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.TreeIntegral
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The measure-preserving tree coordinate map

See (A.9) and (A.10). Fix the dipole vectors and an endpoint realization on each
edge. The position map keeps the root and replaces every other position by
its difference from its parent, plus the selected endpoint offset.
The Jacobian is one: remove the vertices in decreasing tree rank, composing
translations of one coordinate at a time.
-/

@[expose] public section

namespace MultipoleBKT.MultipoleIntegral

open MeasureTheory Finset Function
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem lintegral_coordinate_shear (a b : ι) (hab : b ≠ a) (v : ℂ)
    {F : (ι → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (Function.update x a (x a - x b + v)) = ∫⁻ x, F x := by
  have hm : Measurable (fun x : ι → ℂ => Function.update x a (x a - x b + v)) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne hi]
      fun_prop
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => (0 : ℂ)),
    lintegral_eq_lmarginal_univ (fun _ => (0 : ℂ))]
  rw [← insert_erase (mem_univ a)]
  rw [lmarginal_insert' (fun x => F (Function.update x a (x a - x b + v))) (hF.comp hm) (notMem_erase a univ),
    lmarginal_insert' _ hF (notMem_erase a univ)]
  congr 1
  funext x
  simp only [Function.update_self, Function.update_of_ne hab, Function.update_idem]
  calc
    _ = ∫⁻ t : ℂ, F (Function.update x a (t + (-x b + v))) := by
      apply lintegral_congr
      intro t
      congr 2
      abel
    _ = _ := lintegral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun t => F (Function.update x a t)) (-x b + v)

/-- A translation of coordinate `a` depending on a different coordinate has
Jacobian one. -/
private theorem measurePreserving_coordinate_shear (a b : ι) (hab : b ≠ a) (v : ℂ) :
    MeasurePreserving (fun x : ι → ℂ => Function.update x a (x a - x b + v)) := by
  have hm : Measurable (fun x : ι → ℂ => Function.update x a (x a - x b + v)) := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i = a
    · subst i
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne hi]
      fun_prop
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, ← lintegral_indicator_one (hm hs),
    ← lintegral_indicator_one hs]
  have heq := lintegral_coordinate_shear a b hab v (F := s.indicator (1 : (ι → ℂ) → ℝ≥0∞)) (measurable_const.indicator hs)
  refine (lintegral_congr fun x => ?_).trans heq
  by_cases hx : Function.update x a (x a - x b + v) ∈ s <;> simp [hx]

/-- The root coordinate and selected endpoint differences along the tree.
The root occupies its original slot, so the codomain has exactly `|ι|`
complex coordinates. -/
def treeCoordinates (root : ι) (par : ι → ι) (offset : ι → ℂ) (x : ι → ℂ) : ι → ℂ :=
  fun i => if i = root then x i else x i - x (par i) + offset i

/-- The change of variables (A.10) preserves Lebesgue measure for every
fixed family of dipole vectors and endpoint realizations. -/
theorem measurePreserving_treeCoordinates {root : ι} {par : ι → ι}
    (hpar : IsParentMap root par) (offset : ι → ℂ) :
    MeasurePreserving (treeCoordinates root par offset) := by
  obtain ⟨rank, hrank⟩ := hpar
  let C (s : Finset ι) (x : ι → ℂ) : ι → ℂ :=
    fun i => if i ∈ s then x i - x (par i) + offset i else x i
  have key : ∀ s : Finset ι, s ⊆ univ.erase root → MeasurePreserving (C s) := by
    intro s
    induction s using Finset.induction_on_min_value rank with
    | empty =>
      intro _
      change MeasurePreserving (id : (ι → ℂ) → (ι → ℂ))
      exact MeasurePreserving.id _
    | insert a s ha hmin ih =>
      intro hsub
      have har : a ≠ root := (mem_erase.mp (hsub (mem_insert_self a s))).1
      have hpa_s : par a ∉ s := by
        intro hp
        have := hmin _ hp
        have := hrank a har
        omega
      have hpa_a : par a ≠ a := by
        intro heq
        have := hrank a har
        rw [heq] at this
        exact lt_irrefl _ this
      have ih' := ih (fun i hi => hsub (mem_insert_of_mem hi))
      have heq : C (insert a s) =
          (fun x => Function.update x a (x a - x (par a) + offset a)) ∘ C s := by
        funext x i
        by_cases hi : i = a
        · subst i
          simp [C, ha, hpa_s]
        · simp [C, hi]
      rw [heq]
      exact (measurePreserving_coordinate_shear a (par a) hpa_a (offset a)).comp ih'
  have heq : treeCoordinates root par offset = C (univ.erase root) := by
    funext x i
    by_cases hi : i = root <;> simp [treeCoordinates, C, hi]
  rw [heq]
  exact key _ subset_rfl

/-- Integration in the endpoint tree coordinates, without a separability
assumption on the function being integrated. -/
theorem lintegral_treeCoordinates {root : ι} {par : ι → ι}
    (hpar : IsParentMap root par) (offset : ι → ℂ)
    {F : (ι → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F (treeCoordinates root par offset x) = ∫⁻ z, F z :=
  (measurePreserving_treeCoordinates hpar offset).lintegral_comp hF

omit [Fintype ι] in
/-- The tree coordinate map is injective. Equal root and edge coordinates
recover equal positions by induction on distance from the root. -/
theorem treeCoordinates_injective {root : ι} {par : ι → ι}
    (hpar : IsParentMap root par) (offset : ι → ℂ) :
    Function.Injective (treeCoordinates root par offset) := by
  obtain ⟨rank, hrank⟩ := hpar
  intro x y hxy
  have key : ∀ n : ℕ, ∀ i : ι, rank i = n → x i = y i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have heq := congrFun hxy i
      by_cases hir : i = root
      · simpa only [treeCoordinates, hir, ↓reduceIte] using heq
      · have hp : x (par i) = y (par i) := ih (rank (par i)) (hi ▸ hrank i hir) (par i) rfl
        simpa only [treeCoordinates, hir, ↓reduceIte, hp, add_left_inj, sub_left_inj] using heq
  funext i
  exact key (rank i) i rfl

/-- The affine change of tree coordinates is a bijection, in addition to
preserving volume. No selection of endpoint realizations enters its inverse. -/
theorem treeCoordinates_bijective {root : ι} {par : ι → ι}
    (hpar : IsParentMap root par) (offset : ι → ℂ) :
    Function.Bijective (treeCoordinates root par offset) := by
  let L : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    { toFun := treeCoordinates root par (fun _ => 0)
      map_add' := by
        intro x y
        funext i
        by_cases hi : i = root
        · simp [treeCoordinates, hi]
        · simp [treeCoordinates, hi]
          ring
      map_smul' := by
        intro a x
        funext i
        by_cases hi : i = root <;> simp [treeCoordinates, hi, mul_sub] }
  have hL : Function.Injective L := treeCoordinates_injective hpar (fun _ => 0)
  have hsurj := LinearMap.surjective_of_injective hL
  refine ⟨treeCoordinates_injective hpar offset, fun z => ?_⟩
  obtain ⟨x, hx⟩ := hsurj (fun i => if i = root then z i else z i - offset i)
  refine ⟨x, ?_⟩
  funext i
  have heq := congrFun hx i
  change treeCoordinates root par (fun _ => 0) x i = _ at heq
  by_cases hi : i = root
  · simpa only [treeCoordinates, hi, ↓reduceIte] using heq
  · simp only [treeCoordinates, hi, ↓reduceIte, add_zero] at heq ⊢
    rw [heq, sub_add_cancel]

/-- Integrating a product in the tree coordinates. This is the spatial
integration in (A.11) after the endpoint realization has been fixed. -/
theorem lintegral_treeCoordinates_prod {root : ι} {par : ι → ι}
    (hpar : IsParentMap root par) (offset : ι → ℂ)
    (h : ℂ → ℝ≥0∞) (hh : Measurable h)
    (f : ι → ℂ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → ℂ, h (x root) *
      ∏ i ∈ univ.erase root, f i (x i - x (par i) + offset i) =
        (∫⁻ t, h t) * ∏ i ∈ univ.erase root, ∫⁻ t, f i t := by
  let F (z : ι → ℂ) := h (z root) * ∏ i ∈ univ.erase root, f i (z i)
  have hF : Measurable F := (hh.comp (measurable_pi_apply root)).mul
    (Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i))
  have hcoord : ∀ x, F (treeCoordinates root par offset x) =
      h (x root) * ∏ i ∈ univ.erase root, f i (x i - x (par i) + offset i) := by
    intro x
    simp only [F, treeCoordinates, ↓reduceIte]
    congr 1
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_right (mem_erase.mp hi).1]
  simp_rw [← hcoord]
  rw [lintegral_treeCoordinates hpar offset hF]
  let g (i : ι) := if i = root then h else f i
  have hg : ∀ i, Measurable (g i) := by
    intro i
    dsimp only [g]
    split_ifs
    · exact hh
    · exact hf i
  have hsplit : ∀ z : ι → ℂ, F z = ∏ i, g i (z i) := by
    intro z
    rw [← Finset.mul_prod_erase _ _ (mem_univ root)]
    simp only [g, ↓reduceIte, F]
    congr 1
    apply prod_congr rfl
    intro i hi
    rw [ite_eq_right (mem_erase.mp hi).1]
  simp_rw [hsplit]
  rw [lintegral_pi_prod_eq g hg, ← Finset.mul_prod_erase _ _ (mem_univ root)]
  simp only [g, ↓reduceIte]
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [ite_eq_right (mem_erase.mp hi).1]

end MultipoleBKT.MultipoleIntegral

end
