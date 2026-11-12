/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Potential.LowerError
public import MultipoleBKT.UpperBound.BadPoints.GoodBad
public import MultipoleBKT.Matching.Pair

/-!
# Bounds on the odd and even weights with frozen bad points (Remark 5.22)

The paper: Definition 5.21 and
Remark 5.22 (Remark 5.22, eqs. (5.72), (5.73)). Notation as in
`MultipoleBKT.UpperBound.BadPoints.Radii`: `d : Fin N → ℂ × ℂ` is a dipole configuration (on the
event `I_bad = V_bad` the bad set is that of `d`, as in Lemmas 5.9–5.11), `v^Z = interactionZ`,
`τ^{±,Z} = radiusPlusZ, radiusMinusZ`, `d_{i,bad} = badDist`, `R̄ = truncationScale p₀ β λ`,
`r_i = |x_i - y_i|`, `d_ij = dipoleDist (d i) (d j)`, `𝓑_ij = MultipoleLinked M λ (d i) (d j)`,
`𝒜_ij = IsStableDipolePair (d i) (d j)`.

**The weights, written out.** The weights of Definitions 4.28–4.29 are formalized in
`MultipoleBKT.LowerBound.Parity.MayerBond` (`Parity.oddBondUnlinked`, `Parity.evenBondUnlinked`,
`Parity.absOddWeight`, `Parity.absEvenWeight`). The statements below write them out; each
expression is the body of the corresponding `Parity` definition, with the weight `w` taking the
value `v^Z_ij` at the pair `(d i, d j)` (the configuration is fixed). The identifications are `rfl`
and the restatement with the `Parity` names is `MultipoleBKT.UpperBound.Quadratic.bornesabZ_parity`
(`MultipoleBKT.UpperBound.Quadratic.ParityForms`):

* `a^{v^Z}_ij 𝟙_{𝓑_ij^c} = if 𝓑_ij then 0 else if 𝒜_ij then -sinh(β v^Z_ij) else 0`
  (`Parity.oddBondUnlinked β (fun _ _ => v^Z_ij) M λ (d i) (d j)`);
* `b^{v^Z}_ij 𝟙_{𝓑_ij^c} = if 𝓑_ij then 0 else if 𝒜_ij then cosh(β v^Z_ij) - 1 else -1`
  (`Parity.evenBondUnlinked`);
* `a^abs_ij = r_i r_j / (d_ij max(d_ij, max(r_i, r_j))) 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R̄}`
  (`Parity.absOddWeight M λ ε₀ R̄`), `b^abs_ij = (a^abs_ij)² + 𝟙_{𝓑_ij}` (`Parity.absEvenWeight`).

The weights `a^{v^Z}_{i∞} = -∑_{k odd} β^k/k! (∑_{j ∈ V_bad} v^Z_ij)^k` and
`b^{v^Z}_{i∞} = ∑_{k even, k ≠ 0} β^k/k! (∑_{j ∈ V_bad} v^Z_ij)^k` of Definition 5.21 are
`-sinh(β S_i)` and `cosh(β S_i) - 1`, `S_i = ∑_{j ∈ I_bad} v^Z_ij` (the series are those of
`Parity.hasSum_odd_series`, `Parity.hasSum_even_series`); they are written in these closed forms.

Main results:

* (5.72): **eq. (5.72)**: for good `i`,
  `|a^{v^Z}_{i∞}| ≤ C r_i / d_{i,bad}` and `|b^{v^Z}_{i∞}| ≤ C r_i² / d_{i,bad}²`, from Lemma 5.11
  and (5.9) (`r_i ≤ d_{i,bad}`); `C` depends on `β`, `q(β)` and `χ`.
* (5.73): **eq. (5.73)**: for good `i, j`,
  `|a^{v^Z}_ij 𝟙_{𝓑_ij^c}| ≤ C a^abs_ij` and `|b^{v^Z}_ij 𝟙_{𝓑_ij^c}| ≤ C b^abs_ij`, and also
  `|b^{v^Z}_ij 𝟙_{𝓑_ij^c}| + 𝟙_{𝓑_ij} ≤ C b^abs_ij` (the form used for the bond
  `e^{-β v^Z} 𝟙_{𝓑^c} - 1`); `C` depends on `β` and `χ` only. The proof is the paper's:
  on `𝓑_ij^c`, `d_ij > M max(min(r_i, r_j), λ) ≥ min(r_i, r_j)`, so Lemma 3.9 (3) applies to
  `v^Z_ij = v'_ij` with the radii `τ^{±,Z}` (equal for good points, Remark 5.10, with
  `r_i ≤ 2(τ_i^{+,Z} + τ_i^{-,Z})`), and its support `d_ij ≤ τ_i^Z + τ_j^Z ≤ 2 ε₀ R̄` gives the
  indicator `𝟙_{d_ij ≤ 17 ε₀ R̄}` of `a^abs`.
* `abs_interactionZ_le_absOdd`: the intermediate bound `|v^Z_ij| ≤ C a^abs_ij` on `𝓑_ij^c`.

The standing hypotheses are those of §5: `0 < λ ≤ ε₀ R̄` (Section 5.2) and `M ≥ 3^{p(β)}` (the paper
has `M > max(20, 3^{p(β)})`).
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open TheoremTwo

variable {χ : ℂ → ℝ}

/-! ### Elementary bounds on the odd and even parts -/

section Elementary

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

/-- If `|t| ≤ C₀ a` with `0 ≤ a ≤ 1`, then `|sinh(β t)| ≤ C a` and `|cosh(β t) - 1| ≤ C a²` with
`C = 1 + K e^K + K² e^K`, `K = |β| C₀`. -/
theorem abs_sinh_cosh_le {β C₀ a t : ℝ} (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : |t| ≤ C₀ * a) :
    |Real.sinh (β * t)| ≤
        (1 + |β| * C₀ * Real.exp (|β| * C₀) + (|β| * C₀) ^ 2 * Real.exp (|β| * C₀)) * a ∧
      |Real.cosh (β * t) - 1| ≤
        (1 + |β| * C₀ * Real.exp (|β| * C₀) + (|β| * C₀) ^ 2 * Real.exp (|β| * C₀)) * a ^ 2 := by
  set K := |β| * C₀ with hK
  have hK0 : 0 ≤ K := by positivity
  have hE0 : 0 ≤ Real.exp K := (Real.exp_pos K).le
  have htK : |β * t| ≤ K * a := by
    rw [abs_mul, hK, mul_assoc]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg β)
  have htK' : |β * t| ≤ K := htK.trans (by nlinarith)
  have hexp : Real.exp |β * t| ≤ Real.exp K := Real.exp_le_exp.2 htK'
  have h1 : 0 ≤ K * Real.exp K := by positivity
  have h2 : 0 ≤ K ^ 2 * Real.exp K := by positivity
  refine ⟨?_, ?_⟩
  · calc |Real.sinh (β * t)| ≤ |β * t| * Real.exp |β * t| := abs_sinh_le _
      _ ≤ (K * a) * Real.exp K := mul_le_mul htK hexp (Real.exp_pos _).le (by positivity)
      _ = (K * Real.exp K) * a := by ring
      _ ≤ (1 + K * Real.exp K + K ^ 2 * Real.exp K) * a :=
          mul_le_mul_of_nonneg_right (by linarith) ha
  · have hsq : (β * t) ^ 2 ≤ (K * a) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) htK 2
    calc |Real.cosh (β * t) - 1| ≤ (β * t) ^ 2 * Real.exp |β * t| := abs_cosh_sub_one_le _
      _ ≤ (K * a) ^ 2 * Real.exp K := mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
      _ = (K ^ 2 * Real.exp K) * a ^ 2 := by ring
      _ ≤ (1 + K * Real.exp K + K ^ 2 * Real.exp K) * a ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Elementary

/-! ### Eq. (5.73) -/

section BornesabZ

open scoped Classical

/-- On `𝓑_ij^c` with `M ≥ 1`: `d_ij > λ` and `d_ij ≥ min(r_i, r_j)`. -/
theorem lt_dipoleDist_of_not_linked {M lam : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M) {a b : ℂ × ℂ}
    (h : ¬ MultipoleLinked M lam a b) :
    lam < dipoleDist a b ∧ min ‖a.1 - a.2‖ ‖b.1 - b.2‖ ≤ dipoleDist a b := by
  have h' : M * min (max ‖a.1 - a.2‖ lam) (max ‖b.1 - b.2‖ lam) < dipoleDist a b := by
    rw [MultipoleLinked, not_le] at h
    exact h
  have hmin0 : lam ≤ min (max ‖a.1 - a.2‖ lam) (max ‖b.1 - b.2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  have hMmin : min (max ‖a.1 - a.2‖ lam) (max ‖b.1 - b.2‖ lam) ≤
      M * min (max ‖a.1 - a.2‖ lam) (max ‖b.1 - b.2‖ lam) :=
    le_mul_of_one_le_left (hlam.le.trans hmin0) hM
  refine ⟨by linarith, ?_⟩
  exact ((min_le_min (le_max_left _ _) (le_max_left _ _)).trans hMmin).trans h'.le

/-- `a^abs_ij` (Definition 4.29, eq. (4.57)) written out, as in `Parity.absOddWeight`. -/
theorem absOdd_nonneg (M lam ε₀ R : ℝ) (a b : ℂ × ℂ) :
    0 ≤ ‖a.1 - a.2‖ * ‖b.1 - b.2‖ /
        (dipoleDist a b * max (dipoleDist a b) (max ‖a.1 - a.2‖ ‖b.1 - b.2‖)) *
      (if MultipoleLinked M lam a b then 0 else 1) *
        (if dipoleDist a b ≤ 17 * ε₀ * R then 1 else 0) := by
  have hD : 0 ≤ dipoleDist a b := dipoleDist_nonneg a b
  refine mul_nonneg (mul_nonneg ?_ (by split_ifs <;> norm_num)) (by split_ifs <;> norm_num)
  positivity

/-- **Eq. (5.73) for the weight** (Lemma 3.9 (3)): there is `C₀ > 0` depending only
on `χ` such that, for good `i, j` on `𝓑_ij^c`, `|v^Z_ij| ≤ C₀ a^abs_ij`, and `a^abs_ij ≤ 1`. -/
theorem abs_interactionZ_le_absOdd (hχ : IsMollifier χ) : ∃ C₀ > 0,
    ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ i ∈ goodPoints p₀ β lam M ε₀ d, ∀ j ∈ goodPoints p₀ β lam M ε₀ d,
        ¬ MultipoleLinked M lam (d i) (d j) →
        |interactionZ χ p₀ β lam M ε₀ d i j| ≤
            C₀ * (‖(d i).1 - (d i).2‖ * ‖(d j).1 - (d j).2‖ /
                (dipoleDist (d i) (d j) * max (dipoleDist (d i) (d j))
                  (max ‖(d i).1 - (d i).2‖ ‖(d j).1 - (d j).2‖)) *
              (if MultipoleLinked M lam (d i) (d j) then 0 else 1) *
              (if dipoleDist (d i) (d j) ≤ 17 * ε₀ * truncationScale p₀ β lam then 1 else 0)) ∧
          ‖(d i).1 - (d i).2‖ * ‖(d j).1 - (d j).2‖ /
                (dipoleDist (d i) (d j) * max (dipoleDist (d i) (d j))
                  (max ‖(d i).1 - (d i).2‖ ‖(d j).1 - (d j).2‖)) *
              (if MultipoleLinked M lam (d i) (d j) then 0 else 1) *
              (if dipoleDist (d i) (d j) ≤ 17 * ε₀ * truncationScale p₀ β lam then 1 else 0) ≤
            1 := by
  obtain ⟨C₀, hC₀, h39⟩ := lemma_3_9_3 hχ
  refine ⟨C₀, hC₀, fun p₀ β lam M ε₀ d hlam hlamh hM i hi j hj h => ?_⟩
  set R := truncationScale p₀ β lam
  set τp := radiusPlusZ p₀ β lam M ε₀ d
  set τm := radiusMinusZ p₀ β lam M ε₀ d
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  obtain ⟨hDlam, hminD⟩ := lt_dipoleDist_of_not_linked hlam hM1 h
  obtain ⟨hτi, -, hri⟩ := remark_5_10_good hlam hlamh hM hi
  obtain ⟨hτj, -, hrj⟩ := remark_5_10_good hlam hlamh hM hj
  have hv := ((h39 lam τp τm d i j hlam (lam_le_radiusPlusZ i) hτi (lam_le_radiusPlusZ j)
    hτj).2 hri hrj hminD).1
  rw [← interactionZ_eq_ballGrowthInteraction] at hv
  set D := dipoleDist (d i) (d j) with hDdef
  set ri := ‖(d i).1 - (d i).2‖
  set rj := ‖(d j).1 - (d j).2‖
  set Y := max D (max ri rj) with hYdef
  have hD0 : 0 < D := hlam.trans hDlam
  have hY : 0 < Y := hD0.trans_le (le_max_left _ _)
  have hXD : max D lam = D := max_eq_left hDlam.le
  rw [hXD] at hv
  have hrr : ri * rj ≤ D * Y := by
    rw [← min_mul_max]
    exact mul_le_mul hminD (le_max_right _ _) (by positivity) hD0.le
  rw [ite_eq_right h, mul_one]
  have hcut : τp i + τp j ≤ 17 * ε₀ * R := by
    have h1 := radiusPlusZ_le (p₀ := p₀) (β := β) (M := M) (d := d) hlamh i
    have h2 := radiusPlusZ_le (p₀ := p₀) (β := β) (M := M) (d := d) hlamh j
    have hR : 0 ≤ ε₀ * R := hlam.le.trans hlamh
    simp only [clusterCutoff] at h1 h2
    linarith
  refine ⟨?_, ?_⟩
  · by_cases hnear : D ≤ τp i + τp j
    · rw [ite_eq_left hnear] at hv
      rw [ite_eq_left (hnear.trans hcut), mul_one, mul_div_assoc]
      exact hv.trans (le_of_eq (by ring))
    · rw [ite_eq_right hnear] at hv
      refine hv.trans ?_
      have : 0 ≤ ri * rj / (D * Y) * (if D ≤ 17 * ε₀ * R then (1 : ℝ) else 0) := by
        refine mul_nonneg (by positivity) ?_
        split_ifs <;> norm_num
      exact mul_nonneg hC₀.le this
  · have hA1 : ri * rj / (D * Y) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact hrr
    split_ifs
    · rw [mul_one]
      exact hA1
    · rw [mul_zero]
      exact zero_le_one

/-- **Eq. (5.73)** (Remark 5.22): there is `C ≥ 1`
depending only on `β` and `χ` such that, for `0 < λ ≤ ε₀ R̄`, `M ≥ 3^{p(β)}` and good `i, j`,
`|a^{v^Z}_ij 𝟙_{𝓑_ij^c}| ≤ C a^abs_ij`, `|b^{v^Z}_ij 𝟙_{𝓑_ij^c}| ≤ C b^abs_ij`, and
`|b^{v^Z}_ij 𝟙_{𝓑_ij^c}| + 𝟙_{𝓑_ij} ≤ C b^abs_ij`. The weights are written out as explained in the
module docstring (they are the bodies of `Parity.oddBondUnlinked`, `Parity.evenBondUnlinked`,
`Parity.absOddWeight`, `Parity.absEvenWeight`). -/
theorem bornesabZ (hχ : IsMollifier χ) (β : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {N : ℕ} (p₀ : ℕ) (lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ i ∈ goodPoints p₀ β lam M ε₀ d, ∀ j ∈ goodPoints p₀ β lam M ε₀ d,
        |if MultipoleLinked M lam (d i) (d j) then 0 else
            if IsStableDipolePair (d i) (d j) then
              -Real.sinh (β * interactionZ χ p₀ β lam M ε₀ d i j) else 0| ≤
            C * (‖(d i).1 - (d i).2‖ * ‖(d j).1 - (d j).2‖ /
                (dipoleDist (d i) (d j) * max (dipoleDist (d i) (d j))
                  (max ‖(d i).1 - (d i).2‖ ‖(d j).1 - (d j).2‖)) *
              (if MultipoleLinked M lam (d i) (d j) then 0 else 1) *
              (if dipoleDist (d i) (d j) ≤ 17 * ε₀ * truncationScale p₀ β lam then 1 else 0)) ∧
          |if MultipoleLinked M lam (d i) (d j) then 0 else
            if IsStableDipolePair (d i) (d j) then
              Real.cosh (β * interactionZ χ p₀ β lam M ε₀ d i j) - 1 else -1| ≤
            C * ((‖(d i).1 - (d i).2‖ * ‖(d j).1 - (d j).2‖ /
                (dipoleDist (d i) (d j) * max (dipoleDist (d i) (d j))
                  (max ‖(d i).1 - (d i).2‖ ‖(d j).1 - (d j).2‖)) *
              (if MultipoleLinked M lam (d i) (d j) then 0 else 1) *
              (if dipoleDist (d i) (d j) ≤ 17 * ε₀ * truncationScale p₀ β lam then 1 else 0)) ^ 2 +
              (if MultipoleLinked M lam (d i) (d j) then 1 else 0)) ∧
          |if MultipoleLinked M lam (d i) (d j) then 0 else
            if IsStableDipolePair (d i) (d j) then
              Real.cosh (β * interactionZ χ p₀ β lam M ε₀ d i j) - 1 else -1| +
              (if MultipoleLinked M lam (d i) (d j) then 1 else 0) ≤
            C * ((‖(d i).1 - (d i).2‖ * ‖(d j).1 - (d j).2‖ /
                (dipoleDist (d i) (d j) * max (dipoleDist (d i) (d j))
                  (max ‖(d i).1 - (d i).2‖ ‖(d j).1 - (d j).2‖)) *
              (if MultipoleLinked M lam (d i) (d j) then 0 else 1) *
              (if dipoleDist (d i) (d j) ≤ 17 * ε₀ * truncationScale p₀ β lam then 1 else 0)) ^ 2 +
              (if MultipoleLinked M lam (d i) (d j) then 1 else 0)) := by
  obtain ⟨C₀, hC₀, hv⟩ := abs_interactionZ_le_absOdd hχ
  set C := 1 + |β| * C₀ * Real.exp (|β| * C₀) + (|β| * C₀) ^ 2 * Real.exp (|β| * C₀) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |β| * C₀ * Real.exp (|β| * C₀) + (|β| * C₀) ^ 2 * Real.exp (|β| * C₀) := by
      positivity
    linarith
  refine ⟨C, hC1, fun p₀ lam M ε₀ d hlam hlamh hM i hi j hj => ?_⟩
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  have hA := absOdd_nonneg M lam ε₀ (truncationScale p₀ β lam) (d i) (d j)
  by_cases h : MultipoleLinked M lam (d i) (d j)
  · simp only [ite_eq_left h, abs_zero, mul_zero, zero_mul, zero_add, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one]
    exact ⟨by positivity, by positivity, by linarith⟩
  · obtain ⟨hvij, hA1⟩ := hv p₀ β lam M ε₀ d hlam hlamh hM i hi j hj h
    have hst := remark_4_6 hM1 h
    obtain ⟨h1, h2⟩ := abs_sinh_cosh_le (β := β) hC₀.le hA hA1 hvij
    simp only [ite_eq_right h, ite_eq_left hst, abs_neg, add_zero] at h1 h2 ⊢
    exact ⟨h1, h2, h2⟩

end BornesabZ

/-! ### Eq. (5.72) -/

section Bornesabinfty

/-- **Eq. (5.72)** (Remark 5.22): there is `C > 0`
depending only on `χ`, `p₀` and `β` (through `q(β)`) such that, for `0 < λ ≤ ε₀ R̄`,
`M ≥ 3^{p(β)}` and good `i`, with `S_i = ∑_{j ∈ I_bad} v^Z_ij`,
`|a^{v^Z}_{i∞}| = |sinh(β S_i)| ≤ C r_i / d_{i,bad}` and
`|b^{v^Z}_{i∞}| = |cosh(β S_i) - 1| ≤ C r_i² / d_{i,bad}²`. -/
theorem bornesabinfty (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} (lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∀ i ∈ goodPoints p₀ β lam M ε₀ d,
        |Real.sinh (β * ∑ j ∈ badPoints p₀ β lam M ε₀ d, interactionZ χ p₀ β lam M ε₀ d i j)| ≤
            C * (‖(d i).1 - (d i).2‖ / badDist p₀ β lam M ε₀ d i) ∧
          |Real.cosh (β * ∑ j ∈ badPoints p₀ β lam M ε₀ d, interactionZ χ p₀ β lam M ε₀ d i j) -
              1| ≤
            C * (‖(d i).1 - (d i).2‖ / badDist p₀ β lam M ε₀ d i) ^ 2 := by
  obtain ⟨C₁, hC₁, h511⟩ := lemma_5_11 hχ p₀ β
  set C := 1 + |β| * C₁ * Real.exp (|β| * C₁) + (|β| * C₁) ^ 2 * Real.exp (|β| * C₁) with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |β| * C₁ * Real.exp (|β| * C₁) + (|β| * C₁) ^ 2 * Real.exp (|β| * C₁) := by
      positivity
    linarith
  refine ⟨C, by linarith, fun lam M ε₀ d hlam hlamh hM i hi => ?_⟩
  set D := badDist p₀ β lam M ε₀ d i
  set S := ∑ j ∈ badPoints p₀ β lam M ε₀ d, interactionZ χ p₀ β lam M ε₀ d i j
  have hrD := norm_le_badDist hlam hlamh hM hi
  have hD : 0 < D := hlam.trans_le (lam_le_badDist hlam hlamh hM hi)
  have ha0 : 0 ≤ ‖(d i).1 - (d i).2‖ / D := div_nonneg (norm_nonneg _) hD.le
  have ha1 : ‖(d i).1 - (d i).2‖ / D ≤ 1 := by rwa [div_le_one hD]
  have hS : |S| ≤ C₁ * (‖(d i).1 - (d i).2‖ / D) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [← mul_div_assoc]
    exact h511 lam M ε₀ d hlam hlamh hM i hi
  exact abs_sinh_cosh_le hC₁.le ha0 ha1 hS

end Bornesabinfty

end Quadratic

end UpperBound

end MultipoleBKT

end
