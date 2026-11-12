/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Weighted determinant bound for the forest count

The spectral arithmetic-geometric mean step in the proof of (4.71) in the proof of Lemma 4.49. The diagonal change of variables
is `D⁻¹ᐟ² (I + L) D⁻¹ᐟ²`.
-/

@[expose] public section

namespace MultipoleBKT.Peeling.RouteDeterminant

open Matrix Finset
open scoped ComplexOrder

/-- Arithmetic-geometric mean applied to the nonnegative eigenvalues of a real
positive semidefinite matrix, equation (4.71) in the proof of Lemma 4.49. -/
theorem det_le_trace_pow {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.PosSemidef) :
    A.det ≤ (A.trace / Fintype.card V) ^ Fintype.card V := by
  have hn : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have ham := Real.geom_mean_le_arith_mean univ (fun _ : V => (1 : ℝ))
    hA.isHermitian.eigenvalues (by simp) (by simpa using hn)
    (fun i _ => hA.eigenvalues_nonneg i)
  simp only [Real.rpow_one, sum_const, card_univ, nsmul_eq_mul, mul_one, one_mul] at ham
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg (prod_nonneg fun i _ =>
    hA.eigenvalues_nonneg i) _) ham (Fintype.card V)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (prod_nonneg fun i _ =>
    hA.eigenvalues_nonneg i), inv_mul_cancel₀ hn.ne', Real.rpow_one] at hp
  simpa only [hA.isHermitian.det_eq_prod_eigenvalues,
    hA.isHermitian.trace_eq_sum_eigenvalues, RCLike.ofReal_real_eq_id, id_eq] using hp

/-- Weighted determinant/trace inequality. The weights are the diagonal entries of
`D`, and the proof applies spectral AM–GM after conjugating by `D⁻¹ᐟ²`.
Equation (4.71) in the proof of Lemma 4.49. -/
theorem det_le_prod_mul_weighted_trace_pow {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] {A : Matrix V V ℝ} (hA : A.PosSemidef) (w : V → ℝ)
    (hw : ∀ i, 0 < w i) :
    A.det ≤ (∏ i, w i) * ((∑ i, A i i / w i) / Fintype.card V) ^ Fintype.card V := by
  let S : Matrix V V ℝ := diagonal fun i => (Real.sqrt (w i))⁻¹
  have hS : Sᴴ = S := by
    simp only [S, diagonal_conjTranspose, star_trivial]
  have hB : (S * A * S).PosSemidef := by
    simpa only [hS] using hA.conjTranspose_mul_mul_same S
  have ht : (S * A * S).trace = ∑ i, A i i / w i := by
    apply sum_congr rfl
    intro i _
    change (S * A * S) i i = A i i / w i
    simp only [S, diagonal_mul, mul_diagonal]
    calc (Real.sqrt (w i))⁻¹ * A i i * (Real.sqrt (w i))⁻¹ =
          A i i * ((Real.sqrt (w i))⁻¹) ^ 2 := by ring
      _ = A i i / w i := by rw [inv_pow, Real.sq_sqrt (hw i).le, div_eq_mul_inv]
  have hd : (∏ i, w i) * (S * A * S).det = A.det := by
    rw [det_mul, det_mul, det_diagonal, ← mul_assoc]
    have hs : (∏ i, w i) * (∏ i, (Real.sqrt (w i))⁻¹) ^ 2 = 1 := by
      rw [← prod_pow, ← prod_mul_distrib]
      apply prod_eq_one
      intro i _
      rw [inv_pow, Real.sq_sqrt (hw i).le, mul_inv_cancel₀ (hw i).ne']
    calc (∏ i, w i) * ((∏ i, (Real.sqrt (w i))⁻¹) * A.det) *
          (∏ i, (Real.sqrt (w i))⁻¹) =
        ((∏ i, w i) * (∏ i, (Real.sqrt (w i))⁻¹) ^ 2) * A.det := by ring
      _ = A.det := by rw [hs, one_mul]
  calc A.det = (∏ i, w i) * (S * A * S).det := hd.symm
    _ ≤ (∏ i, w i) * ((S * A * S).trace / Fintype.card V) ^ Fintype.card V :=
      mul_le_mul_of_nonneg_left (det_le_trace_pow hB) (prod_nonneg fun i _ => (hw i).le)
    _ = _ := by rw [ht]

/-- The weighted trace in the paper is exactly the weighted degree sum.
Equation (4.71) in the proof of Lemma 4.49. -/
theorem weighted_trace_laplacian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) :
    (diagonal (fun i => (w i)⁻¹) * (1 + G.lapMatrix ℝ)).trace =
      ∑ i, (1 + (G.degree i : ℝ)) / w i := by
  apply sum_congr rfl
  intro i _
  simp [diagonal_mul, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix, div_eq_mul_inv, mul_comm]

/-- The weighted determinant estimate specialized to `I + L_G`.
Equation (4.71) in the proof of Lemma 4.49. -/
theorem det_one_add_laplacian_le {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (hw : ∀ i, 0 < w i) :
    (1 + G.lapMatrix ℝ).det ≤ (∏ i, w i) *
      ((∑ i, (1 + (G.degree i : ℝ)) / w i) / Fintype.card V) ^ Fintype.card V := by
  have h := det_le_prod_mul_weighted_trace_pow
    (Matrix.PosSemidef.one.add (G.posSemidef_lapMatrix ℝ)) w hw
  simpa [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix] using h

end MultipoleBKT.Peeling.RouteDeterminant
