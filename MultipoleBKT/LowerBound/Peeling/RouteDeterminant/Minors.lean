/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.RouteDeterminant.Trace
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Principal Gram minors in the forest determinant

The determinant expansion used at (4.71) in
the proof of Lemma 4.49. We need only the sum of Gram minors,
rather than an evaluation of the weight of each forest.
-/

@[expose] public section

namespace MultipoleBKT.Peeling.RouteDeterminant

open Matrix Finset

/-- Expanding the identity rows gives the sum of principal minors. -/
private theorem det_one_add_eq_sum_principal_minors {E R : Type*} [Fintype E] [DecidableEq E]
    [CommRing R] (A : Matrix E E R) :
    (1 + A).det = ∑ s : Finset E, (A.submatrix (fun i : s => i.val) (fun i : s => i.val)).det := by
  rw [add_comm]
  let D := (detRowAlternating : (E → R) [⋀^E]→ₗ[R] R)
  change D ((fun i => A i) + (fun i => (1 : Matrix E E R) i)) = _
  rw [D.map_add_univ]
  apply sum_congr rfl
  intro s _
  exact det_piecewise_one_eq_submatrix_det A s

/-- The Gram form of the determinant expansion: each subset of incidence columns
contributes its Gram determinant. Equation (4.71) in the proof of Lemma 4.49. -/
theorem det_one_add_gram {V E R : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [CommRing R] (B : Matrix V E R) :
    (1 + B * Bᵀ).det = ∑ s : Finset E,
      ((B.submatrix id (fun i : s => i.val))ᵀ * B.submatrix id (fun i : s => i.val)).det := by
  rw [det_one_add_mul_comm, det_one_add_eq_sum_principal_minors]
  apply sum_congr rfl
  intro s _
  congr 1

/-- The ordered-minor form of Cauchy–Binet. Every unordered minor occurs
`|E|!` times, and repeated rows have zero determinant. This form avoids choosing
enumerations of the minors. Equation (4.71) in the proof of Lemma 4.49. -/
theorem factorial_mul_det_gram_eq_sum_sq {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (B : Matrix V E ℝ) :
    (Nat.factorial (Fintype.card E) : ℝ) * (Bᵀ * B).det =
      ∑ f : E → V, (B.submatrix f id).det ^ 2 := by
  let minor (f : E → V) := (B.submatrix f id).det
  have expand : (Bᵀ * B).det = ∑ f : E → V, (∏ i, B (f i) i) * minor f := by
    calc
      (Bᵀ * B).det =
          ∑ f : E → V, ∑ σ : Equiv.Perm E,
            ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f i) (σ i) * B (f i) i := by
        simp only [det_apply', mul_apply, transpose_apply, prod_univ_sum, mul_sum,
          Fintype.piFinset_univ]
        rw [sum_comm]
      _ = ∑ f : E → V, (∏ i, B (f i) i) * minor f := by
        apply sum_congr rfl
        intro f _
        have hd : ∑ σ : Equiv.Perm E,
            ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f i) (σ i) = minor f := by
          simpa only [minor, det_apply', transpose_apply, submatrix_apply, id_eq]
            using (det_transpose (B.submatrix f id))
        simp only [prod_mul_distrib, ← mul_assoc]
        rw [← sum_mul, hd, mul_comm]
  have permute (σ : Equiv.Perm E) :
      ∑ f : E → V, (((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∏ i, B (f (σ i)) i) * minor f = (Bᵀ * B).det := by
    let e : (E → V) ≃ (E → V) :=
      ⟨fun f i => f (σ i), fun f i => f (σ.symm i),
        fun f => by funext i; simp, fun f => by funext i; simp⟩
    rw [expand]
    apply Fintype.sum_equiv e
    intro f
    have hd : minor (e f) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * minor f := by
      exact det_permute σ (B.submatrix f id)
    change _ = (∏ i, B (f (σ i)) i) * minor (e f)
    rw [hd]
    ring
  calc
    (Nat.factorial (Fintype.card E) : ℝ) * (Bᵀ * B).det =
        ∑ σ : Equiv.Perm E, (Bᵀ * B).det := by simp [Fintype.card_perm]
    _ = ∑ σ : Equiv.Perm E, ∑ f : E → V,
        (((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, B (f (σ i)) i) * minor f := by
      apply sum_congr rfl
      intro σ _
      exact (permute σ).symm
    _ = ∑ f : E → V, minor f ^ 2 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro f _
      rw [← sum_mul]
      have hd : ∑ σ : Equiv.Perm E, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i, B (f (σ i)) i = minor f := (det_apply' (B.submatrix f id)).symm
      rw [hd]
      ring

/-- Cauchy–Binet makes every Gram minor nonnegative. -/
theorem gram_det_nonneg {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (B : Matrix V E ℝ) : 0 ≤ (Bᵀ * B).det := by
  have h := factorial_mul_det_gram_eq_sum_sq B
  have hf : (0 : ℝ) < Nat.factorial (Fintype.card E) := by positivity
  have hs : 0 ≤ ∑ f : E → V, (B.submatrix f id).det ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

end MultipoleBKT.Peeling.RouteDeterminant
