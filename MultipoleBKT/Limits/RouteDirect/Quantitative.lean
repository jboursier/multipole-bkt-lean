/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.ParityMajorant
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RadialRelabel
public import MultipoleBKT.Limits.RouteDirect.RadialFactorization

/-!
# Two radial routes for the uniform dipole power

See Lemma A.5 of the paper. The ordered logarithmic radial integral is evaluated in
the three β regimes. The limiting-integrand path instead uses the small-power
factorization of Lemma 4.26.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph
open SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

variable {I : Type*} [Fintype I] [LinearOrder I] [Nonempty I]
variable {χ : ℂ → ℝ} {β M : ℝ}

/-- In the subcritical size range, the radial normalization has the power
`λ^((4-β)k-2)`, after integrating all logarithmic moments. -/
theorem radial_power_eq {lam : ℝ} (hlam : 0 < lam) {k : ℕ}
    (hk : 1 ≤ k) (hsize : (k : ℕ∞) ≤ pStar β) :
    lam ^ ((2 - β) * k) * Appendix.gammaBeta 0 β lam k = lam ^ ((4 - β) * k - 2) := by
  have hneg := (Appendix.transitionBeta_lt_iff hk β).mp ((Appendix.le_pStar_iff hk).mp hsize)
  rw [Appendix.gammaBeta_of_neg hk hneg]
  have hz : 2 * ((k : ℤ) - 1) = ((2 * (k - 1) : ℕ) : ℤ) := by omega
  rw [hz, zpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add hlam]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hk]
  push_cast
  ring

private theorem exists_lintegral_mixedTreeSum_le_of_radial
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (hI : 2 ≤ Fintype.card I)
    (Cr : ℝ) (hCr : 0 < Cr)
    (hrad : ∀ lam : ℝ, 0 < lam →
      (∫⁻ u : I → ℂ, ENNReal.ofReal (logRadialWeight β lam (Fintype.card I - 1) u)) ≤
        ENNReal.ofReal (Cr * lam ^ ((4 - β) * Fintype.card I - 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * mixedTreeSum χ β lam M c) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  let k := Fintype.card I
  obtain ⟨Cs, hCs, hs⟩ := lintegral_limitingTreeTerm_le (I := I) (β := β) (M := M)
    hχ (by linarith) hM (k - 1)
  let C := ((mixedTrees I).card : ℝ) * (Cs * Cr)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C + 1, by linarith, fun lam hlam root => ?_⟩
  have hterm (t : SimpleGraph I × Finset (Sym2 I) × Finset (Sym2 I) × Finset (Sym2 I))
      (ht : t ∈ mixedTrees I) :
      (∫⁻ c, anchor root c * limitingTreeTerm χ β lam M t.2.1 t.2.2.1 t.2.2.2 c) ≤
        ENNReal.ofReal (Cs * Cr * lam ^ ((4 - β) * k - 2)) := by
    obtain ⟨hT, hpart, hA, hB⟩ := (mem_filter.mp ht).2
    exact ((hs lam hlam t.1 hT (by dsimp only [k]; omega) t.2.1 t.2.2.1 t.2.2.2
      hpart hA hB root).trans (mul_le_mul_right (hrad lam hlam) _)).trans_eq (by
        rw [← ENNReal.ofReal_mul hCs.le]
        congr 1
        ring)
  unfold mixedTreeSum
  simp_rw [Finset.mul_sum]
  have hm (t : SimpleGraph I × Finset (Sym2 I) × Finset (Sym2 I) × Finset (Sym2 I)) :
      Measurable (fun c => anchor root c * limitingTreeTerm χ β lam M t.2.1 t.2.2.1 t.2.2.2 c) :=
    (measurable_anchor root).mul (measurable_limitingTreeTerm hχ hlam t.2.1 t.2.2.1 t.2.2.2)
  rw [lintegral_finsetSum _ fun t _ => hm t]
  calc
    _ ≤ ∑ _t ∈ mixedTrees I, ENNReal.ofReal (Cs * Cr * lam ^ ((4 - β) * k - 2)) :=
      sum_le_sum hterm
    _ = ENNReal.ofReal (C * lam ^ ((4 - β) * k - 2)) := by
      rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      dsimp only [C]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- Uniform quantitative integration of the finite retained-tree sum. The
constant is chosen before λ. The ordered calculation distinguishes β below,
at, and above four through the logarithmic moment bounds. -/
theorem exists_lintegral_mixedTreeSum_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (hI : 2 ≤ Fintype.card I)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * mixedTreeSum χ β lam M c) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  let k := Fintype.card I
  have hkn : k - 2 + 2 = k := Nat.sub_add_cancel hI
  have hkr : ((k - 2 : ℕ) : ℝ) + 2 = (k : ℝ) := by exact_mod_cast hkn
  have hsize : (((k - 2) + 2 : ℕ) : ℕ∞) ≤ pStar β := by rw [hkn]; exact hk
  obtain ⟨Cr, hCr, hr⟩ := logRadialWeightInfinity_bound_any hβ (k - 2) (k - 1) hsize
  refine exists_lintegral_mixedTreeSum_le_of_radial hχ hβ hM hI Cr hCr (fun lam hlam => ?_)
  have hrad : (∫⁻ u : I → ℂ, ENNReal.ofReal (logRadialWeight β lam (k - 1) u)) ≤
      ENNReal.ofReal (Cr * lam ^ ((4 - β) * k - 2)) := by
    have h := hr I (Nat.sub_add_cancel hI).symm 0 lam hlam
    rw [hkn, hkr, radial_power_eq hlam (by omega : 1 ≤ k) hk] at h
    exact h
  exact hrad

/-- Quantitative integration for the limiting integrands, using logarithmic
absorption followed by a product of one-dimensional radial integrals.
See Lemma 4.26 of the paper. -/
theorem exists_lintegral_mixedTreeSum_factorized_le (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) (hI : 2 ≤ Fintype.card I)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ root : I,
      (∫⁻ c, anchor root c * mixedTreeSum χ β lam M c) ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * Fintype.card I - 2)) := by
  obtain ⟨Cr, hCr, hr⟩ := exists_lintegral_logRadialWeight_factorized_le hk (Fintype.card I - 1)
  exact exists_lintegral_mixedTreeSum_le_of_radial hχ hβ hM hI Cr hCr hr

end MultipoleBKT.Limits.RouteDirect

end
