/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ZPointwise
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.EvenEdge

/-!
# The quadratic marked even-bond error

See case E,
(A.61). The interaction error retains its screening-radius
bound and its large-distance bound. Their minimum gives the maximum in the
squared denominator. The hyperbolic estimate contributes the second pair
of endpoint radii before the marked edge is integrated.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits MultipoleIntegralZ UpperBound BoundedUpper TwoComponentCoulomb

/-- Internal scalar form of the marked even-bond calculation. -/
theorem internal_marked_cosh_error {a b β C D p Q τ d : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hτ : 0 < τ) (hd : 0 < d) (hQ : d ^ 2 ≤ Q)
    (ha : |a| + |b| ≤ C * (p / Q)) (ha1 : p / Q ≤ 1)
    (herr : |a - b| ≤ D * (p / τ ^ 2)) :
    |Real.cosh (β * a) - Real.cosh (β * b)| ≤
      (β ^ 2 * C * max C D * Real.exp (β * C)) * p ^ 2 / (max τ d ^ 2 * Q) := by
  have hQ0 : 0 < Q := (pow_pos hd 2).trans_le hQ
  have hmax0 : 0 < max τ d := hτ.trans_le (le_max_left _ _)
  have hK0 : 0 ≤ max C D := hC.trans (le_max_left _ _)
  have hdiff : |a - b| ≤ max C D * (p / max τ d ^ 2) := by
    by_cases htd : τ ≤ d
    · rw [max_eq_right htd]
      calc |a - b| ≤ |a| + |b| := abs_sub a b
           _ ≤ C * (p / Q) := ha
           _ ≤ max C D * (p / d ^ 2) := mul_le_mul (le_max_left _ _)
             (div_le_div_of_nonneg_left hp (pow_pos hd 2) hQ) (div_nonneg hp hQ0.le) hK0
    · rw [max_eq_left (le_of_not_ge htd)]
      exact herr.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (div_nonneg hp (sq_nonneg _)))
  have hab : |a| + |b| ≤ C := ha.trans (mul_le_of_le_one_right hC ha1)
  have hsum : |β * a| + |β * b| ≤ β * C * (p / Q) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, ← mul_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left ha hβ
  have hsum1 : |β * a| + |β * b| ≤ β * C := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, ← mul_add]
    exact mul_le_mul_of_nonneg_left hab hβ
  have hdelta : |β * a - β * b| ≤ β * max C D * (p / max τ d ^ 2) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hβ, mul_assoc]
    exact mul_le_mul_of_nonneg_left hdiff hβ
  calc |Real.cosh (β * a) - Real.cosh (β * b)| ≤
        (|β * a| + |β * b|) * |β * a - β * b| * Real.exp (|β * a| + |β * b|) :=
          abs_cosh_sub_cosh_le _ _
       _ ≤ (β * C * (p / Q)) * (β * max C D * (p / max τ d ^ 2)) * Real.exp (β * C) := by
          gcongr
       _ = _ := by field_simp

/-- Internal extraction of the root screening-radius factor. The marked kernel
still contains both endpoint squares and is the kernel integrated in (A.62). -/
theorem internal_marked_even_root {K s t τ d τ₀ : ℝ} (hK : 0 ≤ K)
    (hτ₀ : 0 < τ₀) (hτ : τ₀ ≤ τ) (hd : 0 ≤ d) :
    K * s ^ 2 * t ^ 2 / (max τ d ^ 2 * (d * max d (max s t))) ≤
      K / τ₀ ^ 2 * markedEvenKernel s t d := by
  have hden : 0 ≤ d * max d (max s t) := mul_nonneg hd (hd.trans (le_max_left _ _))
  have hh : τ₀ ^ 2 ≤ max τ d ^ 2 :=
    pow_le_pow_left₀ hτ₀.le (hτ.trans (le_max_left _ _)) 2
  unfold markedEvenKernel
  calc _ = (K * s ^ 2 * t ^ 2 / max τ d ^ 2) / (d * max d (max s t)) := by ring
       _ ≤ (K * s ^ 2 * t ^ 2 / τ₀ ^ 2) / (d * max d (max s t)) :=
         div_le_div_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) (pow_pos hτ₀ 2) hh) hden
       _ = _ := by ring

/-- Enlarging each radius in the marked even kernel preserves its upper bound. -/
theorem markedEvenKernel_mono {s t S T d : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsS : s ≤ S) (htT : t ≤ T) (hd : 0 < d) :
    markedEvenKernel s t d ≤ markedEvenKernel S T d := by
  have hp : s * t ≤ S * T := mul_le_mul hsS htT ht (hs.trans hsS)
  have ha := div_mul_max_le hs ht hsS htT hd
  have heq : ∀ a b : ℝ, markedEvenKernel a b d = a * b * (a * b / (d * max d (max a b))) := by
    intro a b
    unfold markedEvenKernel
    ring
  rw [heq, heq]
  exact mul_le_mul hp ha (div_nonneg (mul_nonneg hs ht) (mul_nonneg hd.le (hd.le.trans (le_max_left _ _))))
    (mul_nonneg (hs.trans hsS) (ht.trans htT))

end MultipoleBKT.ExpansionK.RouteCases

end
