/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Anchor
public import MultipoleBKT.Appendix.SmallIntegral.IntDipole

/-!
# The full singleton-averaged dipole integrand

See (4.48) and
(4.49), and Lemma 4.26.
The singleton average is taken on the entire integrand. Its near/far
expansion is an average of the merged-part averages, by the subgroup identity.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Set Finset SimpleGraph Filter Topology SmallIntegral
open scoped Classical ENNReal

variable {ι : Type*} [Fintype ι] [LinearOrder ι]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- The full specified `Sym_{{i}}` integrand of (4.48), before fixing an origin. -/
noncomputable def singletonBox (χ : ℂ → ℝ) (β lam : ℝ) (E : SimpleGraph ι) :
    (ι → ℂ × ℂ) → ℝ := reversalAverage id (dipBox χ β lam E)

/-- The complete singleton average is the original average of the merged-part
averages. No term-dependent average replaces the specified integrand. -/
theorem singletonBox_eq_sum (M : ℝ) (E : SimpleGraph ι) (c : ι → ℂ × ℂ) :
    singletonBox χ β lam E c =
      ∑ E' ∈ E.edgeFinset.powerset, reversalAverage id (dipSym χ β lam M E E') c := by
  have hs (E' : Finset (Sym2 ι)) :
      reversalAverage id (dipSym χ β lam M E E') c =
        reversalAverage id (dipTerm χ β lam M E E') c :=
    reversalAverage_subgroup id (blkOf E E') _ c
  simp_rw [hs]
  unfold singletonBox reversalAverage
  simp_rw [dipBox_eq_sum (M := M)]
  rw [Finset.sum_comm, Finset.sum_div]

/-- Measurability of the unsymmetrized dipole integrand. -/
theorem measurable_dipBox (hχ : IsMollifier χ) (hlam : 0 < lam) (E : SimpleGraph ι) :
    Measurable (dipBox χ β lam E) := by
  have heq : dipBox χ β lam E = fun c =>
      ∑ E' ∈ E.edgeFinset.powerset, dipTerm χ β lam 1 E E' c :=
    funext (dipBox_eq_sum (M := 1) E)
  rw [heq]
  exact Finset.measurable_sum _ fun E' _ => measurable_dipTerm hχ hlam β 1 E E'

/-- Measurability of the full specified average. -/
theorem measurable_singletonBox (hχ : IsMollifier χ) (hlam : 0 < lam) (E : SimpleGraph ι) :
    Measurable (singletonBox χ β lam E) :=
  measurable_reversalAverage id (measurable_dipBox hχ hlam E)

/-- Translation invariance of the full specified average. -/
theorem singletonBox_translate (E : SimpleGraph ι) (a : ℂ) (c : ι → ℂ × ℂ) :
    singletonBox χ β lam E (translate a c) = singletonBox χ β lam E c := by
  unfold singletonBox reversalAverage
  simp_rw [flipCfg_translate, dipBox_eq_sum (M := 1), dipTerm_translate]

/-- Integrability of the full specified `G'`, in unit-area rooted coordinates.
The subgroup identity is essential here: all singleton reversals remain present. -/
theorem integrable_anchor_singletonBox (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) [Nonempty ι] (hk : (Fintype.card ι : ℕ∞) ≤ pStar β)
    (E : SimpleGraph ι) (hE : E.Connected) (root : ι) :
    Integrable fun c => anchorR root c * singletonBox χ β lam E c := by
  have hint : ∀ E' ∈ E.edgeFinset.powerset,
      Integrable fun c => anchorR root c * reversalAverage id (dipSym χ β lam 30 E E') c := by
    intro E' hE'
    exact integrable_anchor_reversalAverage id root (measurable_dipSym hχ hlam β 30 E E')
      (fun a c => dipSym_translate E E' a c)
      (integrable_anchor_dipSym hχ hβ hlam (by norm_num) hk E hE hE' root)
  have h := integrable_finsetSum _ hint
  convert h using 1
  ext c
  rw [singletonBox_eq_sum (M := 30), Finset.mul_sum]

/-- The full original average leaves each finite-box numerator unchanged. -/
theorem integral_boxConfig_singletonBox (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (E : SimpleGraph ι) (N : ℕ) :
    ∫ c in boxConfig ι N, singletonBox χ β lam E c =
      ∫ c in boxConfig ι N, dipBox χ β lam E c := by
  obtain ⟨B, hB⟩ := exists_abs_dipTerm_le (M := 30) hχ hβ hlam E
  have hb (c : ι → ℂ × ℂ) : |dipBox χ β lam E c| ≤ ∑ _E' ∈ E.edgeFinset.powerset, B := by
    rw [dipBox_eq_sum (M := 30)]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun E' hE' => hB E' hE' c)
  exact integral_boxConfig_avg_flip id (measurable_dipBox hχ hlam E) hb N

/-- Direct translation averaging for each connected dipole graph.
This is the individual numerator limit in (4.49). -/
theorem tendsto_dipoleIntegral_div (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) {V : Finset ℕ} (root : V)
    (hk : (V.card : ℕ∞) ≤ pStar β) (E : SimpleGraph V) (hE : E.Connected) :
    Tendsto (fun N : ℕ => (1 / (N : ℝ)) * dipoleIntegral χ N β lam V E) atTop
      (𝓝 (∫ c, anchorR root c * singletonBox χ β lam E c)) := by
  have : Nonempty V := ⟨root⟩
  have h := tendsto_boxAverage root (measurable_singletonBox hχ hlam E)
    (singletonBox_translate E)
    (integrable_anchor_singletonBox hχ hβ hlam (by simpa only [Fintype.card_coe] using hk) E hE root)
  refine h.congr fun N => ?_
  rw [integral_boxConfig_singletonBox hχ (by linarith) hlam]
  rfl

/-- The coefficient displayed in (4.49), with the translation
coordinate integrated against a unit-area square. -/
noncomputable def dipoleCoefficient (χ : ℂ → ℝ) (β lam : ℝ) (V : Finset ℕ) (root : V) : ℝ :=
  (∑ E ∈ (univ : Finset (SimpleGraph V)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty),
    ∫ c, anchorR root c * singletonBox χ β lam E c) /
      (∫ z : ℂ, Real.exp (β * smearedKernel χ lam z)) ^ V.card

/-- The dipole activity converges directly to its displayed integral coefficient.
See (4.53). -/
theorem tendsto_dipoleActivity_integral (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) {V : Finset ℕ} (root : V) (hk : (V.card : ℕ∞) ≤ pStar β) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (V.card - 1) * dipoleActivity χ N β lam V) atTop
      (𝓝 (dipoleCoefficient χ β lam V root)) := by
  have hV1 : 1 ≤ V.card := Finset.card_pos.mpr ⟨root, root.property⟩
  have hc := limNormalization_pos hχ hβ hlam
  have hnorm := ((tendsto_dipoleNormalization hχ hβ hlam).inv₀ hc.ne').pow V.card
  have hnum := tendsto_finsetSum
    ((univ : Finset (SimpleGraph V)).filter (fun E => E.Connected ∧ E.edgeSet.Nonempty))
    (fun E hE => tendsto_dipoleIntegral_div hχ hβ hlam root hk E (mem_filter.mp hE).2.1)
  have h := hnorm.mul hnum
  rw [inv_pow, ← div_eq_inv_mul, ← integral_exp_smearedKernel hχ hlam β] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  rw [dipoleActivity_eq_sum_dipoleIntegral hχ hlam hN, Finset.mul_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro E _
  rw [mul_inv, mul_pow]
  have hp : (N : ℝ) ^ (V.card - 1) * ((N : ℝ)⁻¹) ^ V.card = (N : ℝ)⁻¹ := by
    rw [inv_pow, ← Nat.sub_add_cancel hV1, pow_succ, Nat.add_sub_cancel]
    field_simp
  calc
    _ = ((N : ℝ) ^ (V.card - 1) * ((N : ℝ)⁻¹) ^ V.card) *
        ((dipoleNormalization χ N β lam)⁻¹ ^ V.card * dipoleIntegral χ N β lam V E) := by rw [hp]; ring
    _ = _ := by ring

end MultipoleBKT.Limits.RouteDirect

end
