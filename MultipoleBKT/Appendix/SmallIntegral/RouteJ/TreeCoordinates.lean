/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.TreeIntegral

/-!
# The tree change of variables with a shared tail

See (A.24) and the
change of variables following it. At fixed dipole vectors,
each selected endpoint difference is the difference of two positions plus
a fixed shift. These coordinates preserve volume for arbitrary measurable
integrands, including a tail depending on the maximum of several edges.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Function
open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem lintegral_shear (i j : V) (hij : j ≠ i) (shift : ℂ)
    (F : (V → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : V → ℂ, F (update x i (x i - x j + shift))) = ∫⁻ x, F x := by
  have hm : Measurable fun x : V → ℂ => F (update x i (x i - x j + shift)) := by fun_prop
  rw [volume_pi]
  apply lintegral_eq_of_lmarginal_eq (μ := fun _ : V => (volume : Measure ℂ)) {i} hm hF
  funext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [update_self, update_of_ne hij, update_idem]
  have heq : (fun t : ℂ => F (update x i (t - x j + shift))) =
      (fun t : ℂ => F (update x i t)) ∘ (fun t => t + (-x j + shift)) := by
    funext t
    congr 2
    ring
  rw [heq]
  convert! (@lintegral_add_right_eq_self ℂ Complex.measurableSpace volume
    inferInstance inferInstance inferInstance (fun t : ℂ => F (update x i t)) (-x j + shift)) using 1


/-- Tree edge coordinates, indexed by the child, with the root position retained.
The shifts select any of the four endpoint differences at fixed dipole vectors. -/
noncomputable def treeCoordinates (root : V) (par : V → V) (shift : V → ℂ)
    (x : V → ℂ) (i : V) : ℂ :=
  if i = root then x i else x i - x (par i) + shift i

/-- The tree-coordinate change of variables has Jacobian one for arbitrary
measurable integrands. In particular the maximum tail need not factor over edges.
See the proof of Lemma A.4. -/
theorem lintegral_treeCoordinates (root : V) (par : V → V) (depth : V → ℕ)
    (hdepth : ∀ i, i ≠ root → depth (par i) < depth i) (shift : V → ℂ)
    (F : (V → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x : V → ℂ, F (treeCoordinates root par shift x)) = ∫⁻ z, F z := by
  let coords (s : Finset V) (x : V → ℂ) : V → ℂ :=
    fun i => if i ∈ s then x i - x (par i) + shift i else x i
  have main : ∀ s : Finset V, s ⊆ univ.erase root →
      ∀ F : (V → ℂ) → ℝ≥0∞, Measurable F → (∫⁻ x, F (coords s x)) = ∫⁻ z, F z := by
    intro s
    induction s using Finset.induction_on_min_value depth with
    | empty => intro _ F _; simp [coords]
    | insert a s ha hmin ih =>
      intro hsub F hF
      have har : a ≠ root := (mem_erase.mp (hsub (mem_insert_self a s))).1
      have hpa : par a ≠ a := by
        intro h
        have hd := hdepth a har
        rw [h] at hd
        exact lt_irrefl _ hd
      have hpas : par a ∉ s := by
        intro hp
        have := hmin _ hp
        have := hdepth a har
        omega
      let shear (x : V → ℂ) := update x a (x a - x (par a) + shift a)
      have hs : Measurable shear := by fun_prop
      have heq (x : V → ℂ) : coords (insert a s) x = shear (coords s x) := by
        funext i
        by_cases hi : i = a
        · subst i
          simp only [coords, mem_insert_self, ite_true, shear, update_self,
            ite_eq_right ha, ite_eq_right hpas]
        · simp only [coords, mem_insert, hi, false_or, shear, update_of_ne hi]
      simp_rw [heq]
      exact (ih (fun i hi => hsub (mem_insert_of_mem hi)) (F ∘ shear) (hF.comp hs)).trans
        (lintegral_shear a (par a) hpa (shift a) F hF)
  have heq : coords (univ.erase root) = treeCoordinates root par shift := by
    funext x i
    simp only [coords, treeCoordinates, mem_erase, mem_univ, and_true]
    split_ifs <;> simp_all
  rw [← heq]
  exact main _ subset_rfl F hF

end MultipoleBKT.SmallIntegral.RouteJ

end
