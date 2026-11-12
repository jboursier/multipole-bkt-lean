/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Energy.ScreenedError
public import MultipoleBKT.Gibbs.Activities
public import MultipoleBKT.Matching.Pair
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The odd and even parts of the Mayer bond (Definitions 4.28–4.29, Remarks 4.30–4.31)

Section 4.9. Two dipoles `d = (x_i, y_i)` and
`e = (x_j, y_j)` with `i < j` are passed in label order (as for `𝒜_ij`), and a
"collection of weights" `w = (w_ij)_{i<j}` is a pair weight `w : ℂ × ℂ → ℂ × ℂ → ℝ`. The paper
instantiates the weights at

* `w = ṽ` (`MultipoleBKT.upperBoundInteraction`, Definition 3.11) in Remarks 4.30–4.31,
  Corollary 4.34 and the proof of Proposition 4.23 for `𝖪^-_{ε₀}` (proof of Proposition 4.23);
* `w = v` (`MultipoleBKT.dipoleInteraction`) for `𝖪^0_{ε₀}` and `𝖪^0_∞ = 𝖪^mult` (proof of Proposition 4.23);
* `w = v^Z` in Section 5 and a general `w` in Appendix A (proof of Lemma A.7).

Definitions:

* `mayerBondOf β w d e = e^{-β w_ij} 𝟙_{𝒜_ij} - 1`, the Mayer bond `f^w_ij` (Definition 4.14);
* `oddBond β w d e = a^w_ij = -∑_{k odd} β^k/k! w_ij^k 𝟙_{𝒜_ij}` and
  `evenBond β w d e = b^w_ij = ∑_{k even, k ≠ 0} β^k/k! w_ij^k 𝟙_{𝒜_ij} - 𝟙_{𝒜_ij^c}`
  (Definition 4.28), in the closed forms `-sinh(β w) 𝟙_𝒜` and
  `(cosh(β w) - 1) 𝟙_𝒜 - 𝟙_{𝒜^c}`; the series forms are `oddBond_eq_tsum`, `evenBond_eq_tsum`;
* `oddBondUnlinked`, `evenBondUnlinked`: `a^w_ij 𝟙_{𝓑_ij^c}` and `b^w_ij 𝟙_{𝓑_ij^c}`;
  `evenBondMult`: `b^w_ij 𝟙_{𝓑_ij^c} - 𝟙_{𝓑_ij}`;
* `absOddWeight`, `absEvenWeight`: the majorants `a^abs_ij` and `b^abs_ij` (Definition 4.29, eqs. (4.57), (4.58)), with `R` standing for the truncation scale `R̄_{β,λ}`.

Results:

* `mayerBondOf_eq_add`: `f^w = a^w + b^w`; `mayerBondOf_unlinked_eq_add`: the same on `𝓑^c`;
* `unlinkedPairWeight_sub_one_eq`: the bond `e^{-β v} 𝟙_{𝓑^c} - 1` of `𝖪^mult` is
  `a^v 𝟙_{𝓑^c} + (b^v 𝟙_{𝓑^c} - 𝟙_𝓑)` (`M ≥ 1`);
* **Remark 4.31**: `v_ij` and `ṽ_ij` are odd under the reversal `x ↔ y` of
  either dipole (`dipoleInteraction_swap_left`, `upperBoundInteraction_swap_left`, …); for every
  weight with this property, `a^w 𝟙_{𝓑^c}` is odd and `b^w 𝟙_{𝓑^c}` is even in each dipole
  (`oddBondUnlinked_swap_left`, …, `evenBondUnlinked_swap_right`, `evenBondMult_swap_left`, …),
  `𝓑_ij` is invariant (`multipoleLinked_swap_left`, …), and `𝒜_ij`, `e^{-β w} 𝟙_𝒜` and `f^w` are
  invariant under the reversal of both dipoles (`isStableDipolePair_swap_swap`,
  `stableExp_swap_swap`, `mayerBondOf_swap_swap`);
* **Remark 4.30**: `|a^ṽ_ij 𝟙_{𝓑_ij^c}| ≤ C a^abs_ij`,
  `|b^ṽ_ij 𝟙_{𝓑_ij^c}| ≤ C b^abs_ij` and `|b^ṽ_ij 𝟙_{𝓑_ij^c}| + 𝟙_{𝓑_ij} ≤ C b^abs_ij` when
  `max(r_i, r_j) ≤ ε₀ R̄` (`remark_4_30`), with the elementary bounds `abs_sinh_le`,
  `abs_cosh_sub_one_le` that the paper leaves implicit.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace MultipoleBKT

namespace Parity

variable {χ : ℂ → ℝ}

/-! ### Definitions 4.14, 4.28 and 4.29 -/

section Definitions

open scoped Classical

/-- The Mayer bond `f^w_ij = e^{-β w_ij} 𝟙_{𝒜_ij} - 1` (Definition 4.14) of the dipoles `d = (x_i, y_i)`, `e = (x_j, y_j)`, `i < j`, for the pair weight
`w`. -/
noncomputable def mayerBondOf (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (d e : ℂ × ℂ) : ℝ :=
  (if IsStableDipolePair d e then Real.exp (-β * w d e) else 0) - 1

/-- The odd part `a^w_ij = -∑_{k odd} β^k/k! w_ij^k 𝟙_{𝒜_ij} = -sinh(β w_ij) 𝟙_{𝒜_ij}` of the
Mayer bond (Definition 4.28); the series form is
`MultipoleBKT.Parity.oddBond_eq_tsum`. -/
noncomputable def oddBond (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (d e : ℂ × ℂ) : ℝ :=
  if IsStableDipolePair d e then -Real.sinh (β * w d e) else 0

/-- The even part `b^w_ij = ∑_{k even, k ≠ 0} β^k/k! w_ij^k 𝟙_{𝒜_ij} - 𝟙_{𝒜_ij^c}
= (cosh(β w_ij) - 1) 𝟙_{𝒜_ij} - 𝟙_{𝒜_ij^c}` of the Mayer bond (Definition 4.28); the series form is `MultipoleBKT.Parity.evenBond_eq_tsum`. -/
noncomputable def evenBond (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (d e : ℂ × ℂ) : ℝ :=
  if IsStableDipolePair d e then Real.cosh (β * w d e) - 1 else -1

/-- `a^w_ij 𝟙_{𝓑_ij^c}`: the odd part of the Mayer bond on the event that the dipoles are not
linked by the multipole relation (`𝓑_ij`, eq. (2.14), Definition 2.3). -/
noncomputable def oddBondUnlinked (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (d e : ℂ × ℂ) :
    ℝ :=
  if MultipoleLinked M lam d e then 0 else oddBond β w d e

/-- `b^w_ij 𝟙_{𝓑_ij^c}`: the even part of the Mayer bond on the event `𝓑_ij^c`. -/
noncomputable def evenBondUnlinked (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (d e : ℂ × ℂ) :
    ℝ :=
  if MultipoleLinked M lam d e then 0 else evenBond β w d e

/-- `b^w_ij 𝟙_{𝓑_ij^c} - 𝟙_{𝓑_ij}`: the even part of the bond `e^{-β w_ij} 𝟙_{𝓑_ij^c} - 1` of the
multipole activity (Definition 2.13), whose odd part is `a^w_ij 𝟙_{𝓑_ij^c}`
(`MultipoleBKT.Parity.unlinkedPairWeight_sub_one_eq`). -/
noncomputable def evenBondMult (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  evenBondUnlinked β w M lam d e - if MultipoleLinked M lam d e then 1 else 0

/-- The majorant `a^abs_ij = r_i r_j / (d_ij max(r_i, r_j, d_ij)) 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R̄}`
(Definition 4.29, eq. (4.57), Definition 4.29), with `r_i = |x_i - y_i|`,
`d_ij = dist({x_i, y_i}, {x_j, y_j})` (`MultipoleBKT.dipoleDist`) and `R` standing for the
truncation scale `R̄_{β,λ}` (`MultipoleBKT.truncationScale`). -/
noncomputable def absOddWeight (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) : ℝ :=
  ‖d.1 - d.2‖ * ‖e.1 - e.2‖ /
      (dipoleDist d e * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) *
    (if MultipoleLinked M lam d e then 0 else 1) * (if dipoleDist d e ≤ 17 * ε₀ * R then 1 else 0)

/-- The majorant `b^abs_ij = (a^abs_ij)² + 𝟙_{𝓑_ij}` (Definition 4.29, eq. (4.58)). -/
noncomputable def absEvenWeight (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) : ℝ :=
  absOddWeight M lam ε₀ R d e ^ 2 + if MultipoleLinked M lam d e then 1 else 0

end Definitions

/-! ### The decomposition `f = a + b` and the series forms -/

section Decomposition

variable (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (d e : ℂ × ℂ)

/-- `f^w_ij = a^w_ij + b^w_ij` (Section 4.9). -/
theorem mayerBondOf_eq_add : mayerBondOf β w d e = oddBond β w d e + evenBond β w d e := by
  unfold mayerBondOf oddBond evenBond
  split_ifs
  · rw [neg_mul, ← Real.cosh_sub_sinh]
    ring
  · ring

/-- The odd series `∑_{n} β^{2n+1}/(2n+1)! t^{2n+1} = sinh(β t)`. -/
theorem hasSum_odd_series (t : ℝ) :
    HasSum (fun n : ℕ => β ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) * t ^ (2 * n + 1))
      (Real.sinh (β * t)) := by
  convert Real.hasSum_sinh (β * t) using 1
  funext n
  rw [mul_pow]
  ring

/-- The even series without its constant term,
`∑_{n} β^{2n+2}/(2n+2)! t^{2n+2} = cosh(β t) - 1`. -/
theorem hasSum_even_series (t : ℝ) :
    HasSum (fun n : ℕ => β ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ) * t ^ (2 * n + 2))
      (Real.cosh (β * t) - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cosh (β * t))
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at h
  convert h using 1
  funext n
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, mul_pow]
  ring

open scoped Classical in
/-- The series form of `a^w_ij` (Definition 4.28):
`a^w_ij = -∑_{k odd} β^k/k! w_ij^k 𝟙_{𝒜_ij}`, with `k = 2n + 1`. -/
theorem oddBond_eq_tsum :
    oddBond β w d e = -(∑' n : ℕ, β ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) *
      w d e ^ (2 * n + 1)) * (if IsStableDipolePair d e then 1 else 0) := by
  rw [(hasSum_odd_series β (w d e)).tsum_eq]
  unfold oddBond
  split_ifs <;> simp

open scoped Classical in
/-- The series form of `b^w_ij` (Definition 4.28):
`b^w_ij = ∑_{k even, k ≠ 0} β^k/k! w_ij^k 𝟙_{𝒜_ij} - 𝟙_{𝒜_ij^c}`, with `k = 2n + 2`. -/
theorem evenBond_eq_tsum :
    evenBond β w d e = (∑' n : ℕ, β ^ (2 * n + 2) / ((2 * n + 2).factorial : ℝ) *
      w d e ^ (2 * n + 2)) * (if IsStableDipolePair d e then 1 else 0) -
        (if IsStableDipolePair d e then 0 else 1) := by
  rw [(hasSum_even_series β (w d e)).tsum_eq]
  unfold evenBond
  split_ifs <;> simp

end Decomposition

/-! ### Reversal of a dipole (Remark 4.31) -/

section Swap

variable (d e : ℂ × ℂ)

/-- The multipole relation does not see the orientation of the first dipole. -/
theorem multipoleLinked_swap_left (M lam : ℝ) :
    MultipoleLinked M lam d.swap e ↔ MultipoleLinked M lam d e := by
  unfold MultipoleLinked
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [min_comm (min ‖d.2 - e.1‖ ‖d.2 - e.2‖), norm_sub_rev d.2 d.1]

/-- The multipole relation does not see the orientation of the second dipole. -/
theorem multipoleLinked_swap_right (M lam : ℝ) :
    MultipoleLinked M lam d e.swap ↔ MultipoleLinked M lam d e := by
  unfold MultipoleLinked
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [min_comm ‖d.1 - e.2‖, min_comm ‖d.2 - e.2‖, norm_sub_rev e.2 e.1]

/-- `𝒜_ij` is invariant under the simultaneous reversal of both dipoles. -/
theorem isStableDipolePair_swap_swap :
    IsStableDipolePair d.swap e.swap ↔ IsStableDipolePair d e := by
  rw [isStableDipolePair_iff, isStableDipolePair_iff]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev d.2 d.1, norm_sub_rev e.2 e.1, norm_sub_rev d.2 e.1, norm_sub_rev e.2 d.1]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr ⟨h1, h3, h2⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr ⟨h1, h3, h2⟩

/-- `v_ij` is odd in the first dipole (Section 4.9): reversing `x_i ↔ y_i` changes its sign. -/
theorem dipoleInteraction_swap_left (hχ : IsMollifier χ) (lam : ℝ) :
    dipoleInteraction χ lam d.swap e = -dipoleInteraction χ lam d e := by
  unfold dipoleInteraction
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← smearedKernel_neg hχ lam (d.2 - e.1), ← smearedKernel_neg hχ lam (e.1 - d.1), neg_sub,
    neg_sub]
  ring

/-- `v_ij` is odd in the second dipole. -/
theorem dipoleInteraction_swap_right (hχ : IsMollifier χ) (lam : ℝ) :
    dipoleInteraction χ lam d e.swap = -dipoleInteraction χ lam d e := by
  unfold dipoleInteraction
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← smearedKernel_neg hχ lam (d.2 - e.1), ← smearedKernel_neg hχ lam (e.2 - d.2), neg_sub,
    neg_sub]
  ring

/-- The barycentre does not depend on the orientation of the dipole. -/
theorem dipoleMidpoint_swap : dipoleMidpoint d.swap = dipoleMidpoint d := by
  unfold dipoleMidpoint
  rw [Prod.fst_swap, Prod.snd_swap, add_comm]

/-- Reversing the dipole changes the sign of its screened field `∇u` (Remark 4.31: the
quantity `∇u_i` of (3.16) is changed into `-∇u_i`). -/
theorem screenedField_swap (χ : ℂ → ℝ) (lam τ : ℝ) (z : ℂ) :
    screenedField χ lam τ d.swap z = -screenedField χ lam τ d z := by
  unfold screenedField dipoleField screenedCorrectionField
  rw [dipoleMidpoint_swap, Prod.fst_swap, Prod.snd_swap]
  ring

/-- `ṽ_ij` (eq. (3.18)) is odd in the first dipole (Remark 4.31). -/
theorem screenedInteraction_swap_left (χ : ℂ → ℝ) (lam τ : ℝ) :
    screenedInteraction χ lam τ d.swap e = -screenedInteraction χ lam τ d e := by
  unfold screenedInteraction
  rw [dipoleMidpoint_swap, ← mul_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun (measurableSet_ball.inter measurableSet_ball) fun z _ => ?_
  rw [screenedField_swap, inner_neg_left]

/-- `ṽ_ij` (eq. (3.18)) is odd in the second dipole (Remark 4.31). -/
theorem screenedInteraction_swap_right (χ : ℂ → ℝ) (lam τ : ℝ) :
    screenedInteraction χ lam τ d e.swap = -screenedInteraction χ lam τ d e := by
  unfold screenedInteraction
  rw [dipoleMidpoint_swap, ← mul_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun (measurableSet_ball.inter measurableSet_ball) fun z _ => ?_
  rw [screenedField_swap, inner_neg_right]

/-- The interaction `ṽ_ij` of the lower-bound model (Definition 3.11) is odd in the first
dipole. -/
theorem upperBoundInteraction_swap_left (χ : ℂ → ℝ) (lam ε₀ R : ℝ) :
    upperBoundInteraction χ lam ε₀ R d.swap e = -upperBoundInteraction χ lam ε₀ R d e :=
  screenedInteraction_swap_left d e χ lam _

/-- The interaction `ṽ_ij` of the lower-bound model (Definition 3.11) is odd in the second
dipole. -/
theorem upperBoundInteraction_swap_right (χ : ℂ → ℝ) (lam ε₀ R : ℝ) :
    upperBoundInteraction χ lam ε₀ R d e.swap = -upperBoundInteraction χ lam ε₀ R d e :=
  screenedInteraction_swap_right d e χ lam _

end Swap

/-! ### Parity of `a^w 𝟙_{𝓑^c}` and `b^w 𝟙_{𝓑^c}` (Remark 4.31) -/

section ParityOfBonds

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {d e : ℂ × ℂ}

/-- On `𝓑_ij^c` (with `M ≥ 1`, so that `𝓑_ij^c ⊆ 𝒜_ij`), `a^w_ij = -sinh(β w_ij)`. -/
theorem oddBondUnlinked_of_not_linked (hM : 1 ≤ M) (h : ¬ MultipoleLinked M lam d e) :
    oddBondUnlinked β w M lam d e = -Real.sinh (β * w d e) := by
  unfold oddBondUnlinked oddBond
  rw [ite_eq_right h, ite_eq_left (remark_4_6 hM h)]

/-- On `𝓑_ij^c` (with `M ≥ 1`), `b^w_ij = cosh(β w_ij) - 1`. -/
theorem evenBondUnlinked_of_not_linked (hM : 1 ≤ M) (h : ¬ MultipoleLinked M lam d e) :
    evenBondUnlinked β w M lam d e = Real.cosh (β * w d e) - 1 := by
  unfold evenBondUnlinked evenBond
  rw [ite_eq_right h, ite_eq_left (remark_4_6 hM h)]

theorem oddBondUnlinked_of_linked (h : MultipoleLinked M lam d e) :
    oddBondUnlinked β w M lam d e = 0 := by
  unfold oddBondUnlinked
  rw [ite_eq_left h]

theorem evenBondUnlinked_of_linked (h : MultipoleLinked M lam d e) :
    evenBondUnlinked β w M lam d e = 0 := by
  unfold evenBondUnlinked
  rw [ite_eq_left h]

/-- A weight odd in each dipole is invariant under the reversal of both. -/
theorem weight_swap_swap (hw₁ : ∀ d e, w d.swap e = -w d e) (hw₂ : ∀ d e, w d e.swap = -w d e)
    (d e : ℂ × ℂ) : w d.swap e.swap = w d e := by
  rw [hw₁, hw₂, neg_neg]

/-- The intra-block weight `e^{-β w_ij} 𝟙_{𝒜_ij}` is invariant under the simultaneous reversal of
both dipoles, for a weight odd in each dipole (`w = v`, `ṽ`; proof of Corollary 4.34). -/
theorem stableExp_swap_swap (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (d e : ℂ × ℂ) :
    (if IsStableDipolePair d.swap e.swap then Real.exp (-β * w d.swap e.swap) else 0) =
      if IsStableDipolePair d e then Real.exp (-β * w d e) else 0 := by
  rw [weight_swap_swap hw₁ hw₂]
  exact if_congr (isStableDipolePair_swap_swap d e) rfl rfl

/-- The Mayer bond `f^w_ij` is invariant under the simultaneous reversal of both dipoles, for a
weight odd in each dipole. -/
theorem mayerBondOf_swap_swap (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (d e : ℂ × ℂ) :
    mayerBondOf β w d.swap e.swap = mayerBondOf β w d e := by
  unfold mayerBondOf
  rw [stableExp_swap_swap hw₁ hw₂]

/-- **Remark 4.31** for `a`: if the weight is odd in the first dipole, so is `a^w 𝟙_{𝓑^c}`. -/
theorem oddBondUnlinked_swap_left (hM : 1 ≤ M) (hw : ∀ d e, w d.swap e = -w d e) (d e : ℂ × ℂ) :
    oddBondUnlinked β w M lam d.swap e = -oddBondUnlinked β w M lam d e := by
  by_cases h : MultipoleLinked M lam d e
  · rw [oddBondUnlinked_of_linked h,
      oddBondUnlinked_of_linked ((multipoleLinked_swap_left d e M lam).2 h), neg_zero]
  · rw [oddBondUnlinked_of_not_linked hM h,
      oddBondUnlinked_of_not_linked hM (mt (multipoleLinked_swap_left d e M lam).1 h), hw,
      mul_neg, Real.sinh_neg]

/-- **Remark 4.31** for `a`: if the weight is odd in the second dipole, so is `a^w 𝟙_{𝓑^c}`. -/
theorem oddBondUnlinked_swap_right (hM : 1 ≤ M) (hw : ∀ d e, w d e.swap = -w d e)
    (d e : ℂ × ℂ) : oddBondUnlinked β w M lam d e.swap = -oddBondUnlinked β w M lam d e := by
  by_cases h : MultipoleLinked M lam d e
  · rw [oddBondUnlinked_of_linked h,
      oddBondUnlinked_of_linked ((multipoleLinked_swap_right d e M lam).2 h), neg_zero]
  · rw [oddBondUnlinked_of_not_linked hM h,
      oddBondUnlinked_of_not_linked hM (mt (multipoleLinked_swap_right d e M lam).1 h), hw,
      mul_neg, Real.sinh_neg]

/-- **Remark 4.31** for `b`: if the weight is odd in the first dipole, `b^w 𝟙_{𝓑^c}` is even in
it. -/
theorem evenBondUnlinked_swap_left (hM : 1 ≤ M) (hw : ∀ d e, w d.swap e = -w d e)
    (d e : ℂ × ℂ) : evenBondUnlinked β w M lam d.swap e = evenBondUnlinked β w M lam d e := by
  by_cases h : MultipoleLinked M lam d e
  · rw [evenBondUnlinked_of_linked h,
      evenBondUnlinked_of_linked ((multipoleLinked_swap_left d e M lam).2 h)]
  · rw [evenBondUnlinked_of_not_linked hM h,
      evenBondUnlinked_of_not_linked hM (mt (multipoleLinked_swap_left d e M lam).1 h), hw,
      mul_neg, Real.cosh_neg]

/-- **Remark 4.31** for `b`: if the weight is odd in the second dipole, `b^w 𝟙_{𝓑^c}` is even in
it. -/
theorem evenBondUnlinked_swap_right (hM : 1 ≤ M) (hw : ∀ d e, w d e.swap = -w d e)
    (d e : ℂ × ℂ) : evenBondUnlinked β w M lam d e.swap = evenBondUnlinked β w M lam d e := by
  by_cases h : MultipoleLinked M lam d e
  · rw [evenBondUnlinked_of_linked h,
      evenBondUnlinked_of_linked ((multipoleLinked_swap_right d e M lam).2 h)]
  · rw [evenBondUnlinked_of_not_linked hM h,
      evenBondUnlinked_of_not_linked hM (mt (multipoleLinked_swap_right d e M lam).1 h), hw,
      mul_neg, Real.cosh_neg]

/-- On `𝓑^c`, `f^w = a^w + b^w` reads `f^w 𝟙_{𝓑^c} = a^w 𝟙_{𝓑^c} + b^w 𝟙_{𝓑^c}`. -/
theorem mayerBondOf_unlinked_eq_add (d e : ℂ × ℂ) :
    (if MultipoleLinked M lam d e then 0 else mayerBondOf β w d e) =
      oddBondUnlinked β w M lam d e + evenBondUnlinked β w M lam d e := by
  unfold oddBondUnlinked evenBondUnlinked
  split_ifs
  · ring
  · exact mayerBondOf_eq_add β w d e

/-- **Remark 4.31** for `b^w 𝟙_{𝓑^c} - 𝟙_𝓑`: even in the first dipole. -/
theorem evenBondMult_swap_left (hM : 1 ≤ M) (hw : ∀ d e, w d.swap e = -w d e) (d e : ℂ × ℂ) :
    evenBondMult β w M lam d.swap e = evenBondMult β w M lam d e := by
  unfold evenBondMult
  rw [evenBondUnlinked_swap_left hM hw]
  congr 1
  exact if_congr (multipoleLinked_swap_left d e M lam) rfl rfl

/-- **Remark 4.31** for `b^w 𝟙_{𝓑^c} - 𝟙_𝓑`: even in the second dipole. -/
theorem evenBondMult_swap_right (hM : 1 ≤ M) (hw : ∀ d e, w d e.swap = -w d e) (d e : ℂ × ℂ) :
    evenBondMult β w M lam d e.swap = evenBondMult β w M lam d e := by
  unfold evenBondMult
  rw [evenBondUnlinked_swap_right hM hw]
  congr 1
  exact if_congr (multipoleLinked_swap_right d e M lam) rfl rfl

/-- The bond `e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1` of the multipole activity `𝖪^mult` (Definition 2.13)
splits as `a^v_ij 𝟙_{𝓑_ij^c} + (b^v_ij 𝟙_{𝓑_ij^c} - 𝟙_{𝓑_ij})`, the first term odd and the
second even in each dipole (`M ≥ 1`). -/
theorem unlinkedPairWeight_sub_one_eq (hM : 1 ≤ M) (χ : ℂ → ℝ) (d e : ℂ × ℂ) :
    unlinkedPairWeight χ β lam M d e - 1 =
      oddBondUnlinked β (dipoleInteraction χ lam) M lam d e +
        evenBondMult β (dipoleInteraction χ lam) M lam d e := by
  unfold unlinkedPairWeight evenBondMult
  by_cases h : MultipoleLinked M lam d e
  · rw [ite_eq_left h, oddBondUnlinked_of_linked h, evenBondUnlinked_of_linked h, ite_eq_left h]
    ring
  · rw [ite_eq_right h, oddBondUnlinked_of_not_linked hM h, evenBondUnlinked_of_not_linked hM h,
      ite_eq_right h, neg_mul, ← Real.cosh_sub_sinh]
    ring

/-- Recovering the odd part of a bond from the bond and its reversal:
`a(d, e) = (f(d, e) - f(d^swap, e)) / 2` when `f = a + b` with `a` odd and `b` even in `d`. -/
theorem odd_eq_half_sub {a b : ℂ × ℂ → ℂ × ℂ → ℝ} (ha : ∀ d e, a d.swap e = -a d e)
    (hb : ∀ d e, b d.swap e = b d e) (d e : ℂ × ℂ) :
    a d e = ((a d e + b d e) - (a d.swap e + b d.swap e)) / 2 := by
  rw [ha, hb]
  ring

/-- Recovering the even part of a bond from the bond and its reversal:
`b(d, e) = (f(d, e) + f(d^swap, e)) / 2` when `f = a + b` with `a` odd and `b` even in `d`. -/
theorem even_eq_half_add {a b : ℂ × ℂ → ℂ × ℂ → ℝ} (ha : ∀ d e, a d.swap e = -a d e)
    (hb : ∀ d e, b d.swap e = b d e) (d e : ℂ × ℂ) :
    b d e = ((a d e + b d e) + (a d.swap e + b d.swap e)) / 2 := by
  rw [ha, hb]
  ring

end ParityOfBonds

/-! ### Remark 4.30 -/

section Remark430

open scoped Classical

/-- `|e^x - 1| ≤ |x| e^{|x|}`. -/
theorem abs_exp_sub_one_le_mul_exp (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h2 : (1 - x) * Real.exp x ≤ 1 := by
      have h := Real.add_one_le_exp (-x)
      have hpos := Real.exp_pos x
      calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
            mul_le_mul_of_nonneg_right (by linarith) hpos.le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [abs_of_nonneg h1, abs_of_nonneg hx]
    linarith
  · have h1 : Real.exp x - 1 ≤ 0 := by linarith [Real.exp_lt_one_iff.2 hx]
    have h2 : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h4 : 0 ≤ -x := by linarith
    have h3 : 1 ≤ Real.exp (-x) := Real.one_le_exp h4
    rw [abs_of_nonpos h1, abs_of_neg hx]
    calc -(Real.exp x - 1) ≤ -x := by linarith
      _ = -x * 1 := (mul_one _).symm
      _ ≤ -x * Real.exp (-x) := mul_le_mul_of_nonneg_left h3 h4

/-- `|sinh t| ≤ |t| e^{|t|}`. -/
theorem abs_sinh_le (t : ℝ) : |Real.sinh t| ≤ |t| * Real.exp |t| := by
  have h1 := abs_exp_sub_one_le_mul_exp t
  have h2 := abs_exp_sub_one_le_mul_exp (-t)
  rw [abs_neg] at h2
  rw [Real.sinh_eq, show (Real.exp t - Real.exp (-t)) / 2 =
    ((Real.exp t - 1) - (Real.exp (-t) - 1)) / 2 by ring, abs_div, abs_two]
  have h3 := abs_sub (Real.exp t - 1) (Real.exp (-t) - 1)
  rw [div_le_iff₀ two_pos]
  linarith

/-- `|cosh t - 1| ≤ t² e^{|t|}`. -/
theorem abs_cosh_sub_one_le (t : ℝ) : |Real.cosh t - 1| ≤ t ^ 2 * Real.exp |t| := by
  have hc : Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
    have h := Real.cosh_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring, Real.cosh_sq] at h
    rw [h]
    ring
  have hs := abs_sinh_le (t / 2)
  have hexp : Real.exp |t / 2| ^ 2 = Real.exp |t| := by
    rw [← Real.exp_nat_mul, abs_div, abs_two]
    congr 1
    push_cast
    ring
  rw [hc, abs_mul, abs_two, abs_pow]
  calc 2 * |Real.sinh (t / 2)| ^ 2 ≤ 2 * (|t / 2| * Real.exp |t / 2|) ^ 2 := by
        gcongr
    _ = t ^ 2 / 2 * Real.exp |t| := by
        rw [mul_pow, hexp, abs_div, abs_two, div_pow, sq_abs]
        ring
    _ ≤ t ^ 2 * Real.exp |t| := by
        have : 0 ≤ t ^ 2 * Real.exp |t| := by positivity
        linarith

theorem absOddWeight_nonneg (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) : 0 ≤ absOddWeight M lam ε₀ R d e := by
  unfold absOddWeight
  have hD : 0 ≤ dipoleDist d e := by
    unfold dipoleDist
    positivity
  refine mul_nonneg (mul_nonneg ?_ (by split_ifs <;> norm_num)) (by split_ifs <;> norm_num)
  positivity

theorem absEvenWeight_nonneg (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) :
    0 ≤ absEvenWeight M lam ε₀ R d e := by
  unfold absEvenWeight
  have : (0 : ℝ) ≤ if MultipoleLinked M lam d e then 1 else 0 := by split_ifs <;> norm_num
  positivity

/-- The bound of Lemma 3.10 on `ṽ_ij` in terms of `a^abs_ij`, on `𝓑_ij^c`, with the bound
`a^abs_ij ≤ 1`. -/
theorem abs_upperBoundInteraction_le_absOddWeight {C₀ : ℝ} (hC₀ : 0 < C₀)
    (h310 : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e →
        |screenedInteraction χ lam τ d e| ≤
          (if dipoleDist d e ≤ 17 / 8 * τ then C₀ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
            (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖))
          else 0))
    {lam ε₀ R M : ℝ} (hlam : 0 < lam) (hlamR : lam ≤ ε₀ * R) (hM : 1 ≤ M) {d e : ℂ × ℂ}
    (hr : max ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ ε₀ * R) (h : ¬ MultipoleLinked M lam d e) :
    |upperBoundInteraction χ lam ε₀ R d e| ≤ C₀ * absOddWeight M lam ε₀ R d e ∧
      absOddWeight M lam ε₀ R d e ≤ 1 := by
  set r₁ := ‖d.1 - d.2‖ with hr₁
  set r₂ := ‖e.1 - e.2‖ with hr₂
  set D := dipoleDist d e with hDdef
  have hDlt : M * min (max r₁ lam) (max r₂ lam) < D := not_le.1 h
  have hmin0 : lam ≤ min (max r₁ lam) (max r₂ lam) := le_min (le_max_right _ _) (le_max_right _ _)
  have hMmin : min (max r₁ lam) (max r₂ lam) ≤ M * min (max r₁ lam) (max r₂ lam) :=
    le_mul_of_one_le_left (hlam.le.trans hmin0) hM
  have hDpos : 0 < D := lt_of_lt_of_le hlam (hmin0.trans hMmin) |>.trans hDlt
  have hminD : min r₁ r₂ ≤ D :=
    ((min_le_min (le_max_left _ _) (le_max_left _ _)).trans hMmin).trans hDlt.le
  have hd8 : 8 * max ‖d.2 - d.1‖ lam ≤ 8 * ε₀ * R := by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le ((le_max_left _ _).trans hr) hlamR) (by norm_num)
  have he8 : 8 * max ‖e.2 - e.1‖ lam ≤ 8 * ε₀ * R := by
    rw [norm_sub_rev, mul_assoc]
    exact mul_le_mul_of_nonneg_left (max_le ((le_max_right _ _).trans hr) hlamR) (by norm_num)
  have hv := h310 lam (8 * ε₀ * R) hlam d e hd8 he8 hminD
  have h17 : 17 / 8 * (8 * ε₀ * R) = 17 * ε₀ * R := by ring
  rw [h17] at hv
  set m := max D (max r₁ r₂) with hm
  have hmpos : 0 < m := lt_of_lt_of_le hDpos (le_max_left _ _)
  have hrr : r₁ * r₂ ≤ D * m := by
    rw [← min_mul_max]
    exact mul_le_mul hminD (le_max_right _ _) (by positivity) hDpos.le
  have hA1 : r₁ * r₂ / (D * m) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hrr
  have hW : absOddWeight M lam ε₀ R d e =
      r₁ * r₂ / (D * m) * (if D ≤ 17 * ε₀ * R then 1 else 0) := by
    unfold absOddWeight
    rw [ite_eq_right h, mul_one]
  refine ⟨?_, ?_⟩
  · rw [hW]
    have hupper : upperBoundInteraction χ lam ε₀ R d e =
        screenedInteraction χ lam (8 * ε₀ * R) d e := rfl
    rw [hupper]
    by_cases hnear : D ≤ 17 * ε₀ * R
    · rw [ite_eq_left hnear] at hv ⊢
      refine hv.trans ?_
      rw [mul_one, mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₀.le
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hmpos.le)
    · rw [ite_eq_right hnear] at hv ⊢
      rw [mul_zero, mul_zero]
      exact hv
  · rw [hW]
    split_ifs
    · rw [mul_one]
      exact hA1
    · rw [mul_zero]
      exact zero_le_one

/-- **Remark 4.30**: there is `C ≥ 1` (depending on `β` and on
the mollifier `χ`) such that, if `max(r_i, r_j) ≤ ε₀ R̄`,
`|a^ṽ_ij 𝟙_{𝓑_ij^c}| ≤ C a^abs_ij` (eq. (4.59)), `|b^ṽ_ij 𝟙_{𝓑_ij^c}| ≤ C b^abs_ij`, and
`|b^ṽ_ij| 𝟙_{𝓑_ij^c} + 𝟙_{𝓑_ij} ≤ C b^abs_ij` (the form used in the proof of Proposition 4.23). Here `ṽ` is
`upperBoundInteraction χ λ ε₀ R` with `R` in the role of `R̄_{β,λ}`.

The hypotheses `λ ≤ ε₀ R` and `M ≥ 1` are implicit in the paper: Lemma 3.10 is applied with
`τ₀ = 8 ε₀ R̄`, which needs `τ₀ ≥ 8 max(r_i, λ)`, and `𝓑_ij^c ⊆ 𝒜_ij` needs `M ≥ 1` (the paper
has `M > 20`). -/
theorem remark_4_30 (hχ : IsMollifier χ) (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ lam ε₀ R M : ℝ, 0 < lam → lam ≤ ε₀ * R → 1 ≤ M → ∀ d e : ℂ × ℂ,
      max ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ ε₀ * R →
      |oddBondUnlinked β (upperBoundInteraction χ lam ε₀ R) M lam d e| ≤
          C * absOddWeight M lam ε₀ R d e ∧
        |evenBondUnlinked β (upperBoundInteraction χ lam ε₀ R) M lam d e| ≤
          C * absEvenWeight M lam ε₀ R d e ∧
        |evenBondUnlinked β (upperBoundInteraction χ lam ε₀ R) M lam d e| +
            (if MultipoleLinked M lam d e then 1 else 0) ≤
          C * absEvenWeight M lam ε₀ R d e := by
  obtain ⟨C₀, hC₀, h310⟩ := lemma_3_10 hχ
  have h310' : ∀ lam τ : ℝ, 0 < lam → ∀ d e : ℂ × ℂ,
      8 * max ‖d.2 - d.1‖ lam ≤ τ → 8 * max ‖e.2 - e.1‖ lam ≤ τ →
      min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ dipoleDist d e →
        |screenedInteraction χ lam τ d e| ≤
          (if dipoleDist d e ≤ 17 / 8 * τ then C₀ * (‖d.1 - d.2‖ * ‖e.1 - e.2‖) /
            (max (dipoleDist d e) lam * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖))
          else 0) :=
    fun lam τ hlam d e hd he hmin => ((h310 lam τ hlam d e hd he).2 hmin).1
  set K := |β| * C₀ with hK
  set C := 1 + K * Real.exp K + K ^ 2 * Real.exp K with hC
  have hK0 : 0 ≤ K := by positivity
  have hC1 : 1 ≤ C := by
    have : 0 ≤ K * Real.exp K + K ^ 2 * Real.exp K := by positivity
    linarith
  refine ⟨C, hC1, fun lam ε₀ R M hlam hlamR hM d e hr => ?_⟩
  have hA := absOddWeight_nonneg M lam ε₀ R d e
  have hB := absEvenWeight_nonneg M lam ε₀ R d e
  by_cases h : MultipoleLinked M lam d e
  · rw [oddBondUnlinked_of_linked h, evenBondUnlinked_of_linked h, abs_zero, ite_eq_left h,
      zero_add]
    have hB1 : 1 ≤ absEvenWeight M lam ε₀ R d e := by
      unfold absEvenWeight
      rw [ite_eq_left h]
      nlinarith [sq_nonneg (absOddWeight M lam ε₀ R d e)]
    refine ⟨by positivity, by positivity, ?_⟩
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ C * absEvenWeight M lam ε₀ R d e := mul_le_mul hC1 hB1 zero_le_one (by linarith)
  · obtain ⟨hv, hA1⟩ := abs_upperBoundInteraction_le_absOddWeight hC₀ h310' hlam hlamR hM hr h
    set A := absOddWeight M lam ε₀ R d e with hAdef
    set t := β * upperBoundInteraction χ lam ε₀ R d e with ht
    have hEven : absEvenWeight M lam ε₀ R d e = A ^ 2 := by
      unfold absEvenWeight
      rw [ite_eq_right h, add_zero]
    have htA : |t| ≤ K * A := by
      rw [ht, abs_mul, hK, mul_assoc]
      exact mul_le_mul_of_nonneg_left hv (abs_nonneg β)
    have htK : |t| ≤ K := htA.trans (by nlinarith)
    have hexp : Real.exp |t| ≤ Real.exp K := Real.exp_le_exp.2 htK
    have hexp0 : 0 ≤ Real.exp K := (Real.exp_pos K).le
    rw [oddBondUnlinked_of_not_linked hM h, evenBondUnlinked_of_not_linked hM h, ite_eq_right h,
      add_zero, hEven, abs_neg]
    have hodd : |Real.sinh t| ≤ C * A := by
      calc |Real.sinh t| ≤ |t| * Real.exp |t| := abs_sinh_le t
        _ ≤ (K * A) * Real.exp K := mul_le_mul htA hexp (Real.exp_pos _).le (by positivity)
        _ = (K * Real.exp K) * A := by ring
        _ ≤ C * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          have : 0 ≤ K ^ 2 * Real.exp K := by positivity
          linarith
    have heven : |Real.cosh t - 1| ≤ C * A ^ 2 := by
      calc |Real.cosh t - 1| ≤ t ^ 2 * Real.exp |t| := abs_cosh_sub_one_le t
        _ ≤ (K * A) ^ 2 * Real.exp K := by
            refine mul_le_mul ?_ hexp (Real.exp_pos _).le (by positivity)
            rw [← sq_abs t]
            exact pow_le_pow_left₀ (abs_nonneg t) htA 2
        _ = (K ^ 2 * Real.exp K) * A ^ 2 := by ring
        _ ≤ C * A ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg A)
          have : 0 ≤ K * Real.exp K := by positivity
          linarith
    exact ⟨hodd, heven, heven⟩

end Remark430

end Parity

end MultipoleBKT

end
