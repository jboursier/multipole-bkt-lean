/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Tail
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Finite averages of ear deletions

See the proof of (A.30). An ordinary ear contributes the average of its two endpoint
choices. Lists retain both choices even when they give the same value.
-/

@[expose] public section

namespace MultipoleBKT.Limits

/-- The uniform average over a finite list of deletion choices. -/
noncomputable def deletionAverage {α : Type*} (L : List α) (f : α → ℝ) : ℝ :=
  (L.map f).sum / L.length

/-- Independent deletion choices multiply their averages. -/
theorem deletionAverage_product {α β γ : Type*} (L : List α) (J : List β)
    (g : α → β → γ) (f : γ → ℝ) (k : α → ℝ) (l : β → ℝ)
    (h : ∀ x ∈ L, ∀ j ∈ J, f (g x j) = k x * l j) :
    deletionAverage (L.flatMap fun x => J.map (g x)) f =
      deletionAverage L k * deletionAverage J l := by
  have hs : ((L.flatMap fun x => J.map (g x)).map f).sum =
      (L.map k).sum * (J.map l).sum := by
    induction L with
    | nil => simp
    | cons x L ih =>
      have hinner : ((J.map (g x)).map f).sum = k x * (J.map l).sum := by
        rw [List.map_map]
        have heq : J.map (f ∘ g x) = J.map (fun j => k x * l j) := by
          apply List.map_congr_left
          intro j hj
          exact h x (by simp) j hj
        rw [heq, List.sum_map_mul_left]
      rw [List.flatMap_cons, List.map_append, List.sum_append, hinner,
        ih (fun y hy => h y (by simp [hy])), List.map_cons, List.sum_cons]
      ring
  have hn : (L.flatMap fun x => J.map (g x)).length = L.length * J.length := by
    clear h hs
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      ring
  unfold deletionAverage
  rw [hs, hn, Nat.cast_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The finite average preserves pointwise inequalities. -/
theorem deletionAverage_mono {α : Type*} (L : List α) (f g : α → ℝ)
    (h : ∀ x ∈ L, f x ≤ g x) : deletionAverage L f ≤ deletionAverage L g :=
  div_le_div_of_nonneg_right (List.sum_le_sum h) (Nat.cast_nonneg _)

/-- A common factor can be kept outside the finite average. -/
theorem deletionAverage_mul {α : Type*} (L : List α) (c : ℝ) (f : α → ℝ) :
    deletionAverage L (fun x => c * f x) = c * deletionAverage L f := by
  unfold deletionAverage
  rw [List.sum_map_mul_left]
  ring

/-- A common upper bound for all members bounds their nonempty average. -/
theorem deletionAverage_le {α : Type*} (L : List α) (hL : L ≠ [])
    (f : α → ℝ) (b : ℝ) (hb : ∀ x ∈ L, f x ≤ b) : deletionAverage L f ≤ b := by
  have hn : (0 : ℝ) < L.length := Nat.cast_pos.2 (List.length_pos_iff_ne_nil.2 hL)
  apply (div_le_iff₀ hn).2
  have hsum := List.sum_le_length_nsmul (L.map f) b (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact hb x hx)
  simpa only [List.length_map, nsmul_eq_mul, mul_comm] using hsum

/-- A nonempty finite average is at most one of its terms. -/
theorem deletionAverage_le_member {α : Type*} (L : List α) (hL : L ≠ []) (f : α → ℝ) :
    ∃ x ∈ L, deletionAverage L f ≤ f x := by
  classical
  obtain ⟨x, hx, hm⟩ := Finset.exists_max_image L.toFinset f (by simpa using hL)
  refine ⟨x, List.mem_toFinset.1 hx, ?_⟩
  exact deletionAverage_le L hL f (f x) fun y hy => hm y (List.mem_toFinset.2 hy)

end MultipoleBKT.Limits

end
