/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Series
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Convex.Topology

/-!
# Smoothness of the cluster part of the rate function

The cluster part `h = rateCluster p kmult` of the rate function is a power series in `γ`. Under the coefficient bound
(2.48) and for `λ` small, the termwise first and second derivatives are dominated by the same
summable majorant as the series itself (`MultipoleBKT.abs_rateSeriesTerm_one_mul_pow_le`), on
the open box `rateDomain p = (-2, 2)^p ⊇ [0,1]^p`. Hence `h` is `C²` there and

  `|h(γ)| + ‖Dh(γ)‖ + ‖D²h(γ)‖ ≤ C' λ²`

(`MultipoleBKT.rateCluster_smooth`), which is eq. (5.152) of the proof of Theorem 2. Norms on `Fin p → ℝ` are sup norms; derivatives are Fréchet derivatives.
-/

@[expose] public section

namespace MultipoleBKT

open Finset Real Filter Topology ContinuousLinearMap

variable {p : ℕ}

section Monomial

/-- `γ^{m - eᵢ}`-type monomial: `∏_j γ_j^{m'_j}` with `m' = update m i k` equals
`γ_i^k ∏_{j ≠ i} γ_j^{m_j}`. -/
theorem piPow_update (m : Fin p → ℕ) (i : Fin p) (k : ℕ) (γ : Fin p → ℝ) :
    piPow (Function.update m i k) γ = γ i ^ k * ∏ j ∈ univ.erase i, γ j ^ m j := by
  rw [piPow, ← mul_prod_erase univ _ (mem_univ i), Function.update_self]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

theorem sum_update_le (m : Fin p → ℕ) (i : Fin p) :
    ∑ j, Function.update m i (m i - 1) j ≤ ∑ j, m j := by
  refine sum_le_sum fun j _ => ?_
  by_cases h : j = i
  · subst h
    rw [Function.update_self]
    exact Nat.sub_le _ _
  · rw [Function.update_of_ne h]

/-- The coordinate projection `γ ↦ γᵢ` as a continuous linear map. -/
abbrev coordCLM (i : Fin p) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin p => ℝ) i

theorem norm_coordCLM_le (i : Fin p) : ‖coordCLM i‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v => by
    rw [one_mul]
    exact norm_le_pi_norm v i

/-- The derivative of the monomial `γ^m`: `∑ᵢ mᵢ γ^{m - eᵢ} dγᵢ`. -/
noncomputable def piPowDeriv (m : Fin p → ℕ) (γ : Fin p → ℝ) : (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((m i : ℝ) * piPow (Function.update m i (m i - 1)) γ) • coordCLM i

/-- The second derivative of the monomial `γ^m`. -/
noncomputable def piPowDeriv2 (m : Fin p → ℕ) (γ : Fin p → ℝ) :
    (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑ i, ((m i : ℝ) • piPowDeriv (Function.update m i (m i - 1)) γ).smulRight (coordCLM i)

theorem hasFDerivAt_piPow (m : Fin p → ℕ) (γ : Fin p → ℝ) :
    HasFDerivAt (piPow m) (piPowDeriv m γ) γ := by
  have h := HasFDerivAt.finsetProd (u := univ) (g := fun i (γ : Fin p → ℝ) => γ i ^ m i)
    (x := γ) fun i _ => (hasFDerivAt_apply (𝕜 := ℝ) i γ).pow (m i)
  refine h.congr_fderiv ?_
  rw [piPowDeriv]
  refine sum_congr rfl fun i _ => ?_
  rw [smul_smul, piPow_update, nsmul_eq_mul]
  congr 1
  ring

theorem hasFDerivAt_piPowDeriv (m : Fin p → ℕ) (γ : Fin p → ℝ) :
    HasFDerivAt (piPowDeriv m) (piPowDeriv2 m γ) γ := by
  have h := HasFDerivAt.sum (u := univ)
    (A := fun i (y : Fin p → ℝ) => ((m i : ℝ) * piPow (Function.update m i (m i - 1)) y) •
      coordCLM i) (x := γ) fun i _ =>
    ((hasFDerivAt_piPow (Function.update m i (m i - 1)) γ).const_mul (m i : ℝ)).smul_const
      (coordCLM i)
  have heq : (∑ i ∈ univ, fun y : Fin p → ℝ =>
      ((m i : ℝ) * piPow (Function.update m i (m i - 1)) y) • coordCLM i) = piPowDeriv m := by
    funext y
    rw [piPowDeriv, Finset.sum_apply]
  rw [heq] at h
  exact h

theorem contDiff_piPow (m : Fin p → ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (piPow m) :=
  contDiff_prod fun i _ => (contDiff_apply ℝ ℝ i).pow (m i)

theorem fderiv_piPow (m : Fin p → ℕ) : fderiv ℝ (piPow m) = piPowDeriv m :=
  funext fun γ => (hasFDerivAt_piPow m γ).fderiv

theorem fderiv_piPowDeriv (m : Fin p → ℕ) : fderiv ℝ (piPowDeriv m) = piPowDeriv2 m :=
  funext fun γ => (hasFDerivAt_piPowDeriv m γ).fderiv

theorem continuous_piPowDeriv2 (m : Fin p → ℕ) : Continuous (piPowDeriv2 m) := by
  have h2 : ContDiff ℝ 2 (piPow m) := contDiff_piPow m
  have h1 : ContDiff ℝ 1 (fderiv ℝ (piPow m)) := h2.fderiv_right (by norm_num)
  rw [fderiv_piPow] at h1
  rw [← fderiv_piPowDeriv]
  exact h1.continuous_fderiv one_ne_zero

theorem norm_piPowDeriv_le (m : Fin p → ℕ) {γ : Fin p → ℝ} {R : ℝ} (hR : 1 ≤ R)
    (hγ : ∀ i, |γ i| ≤ R) : ‖piPowDeriv m γ‖ ≤ (∑ i, m i : ℕ) * R ^ (∑ i, m i) := by
  rw [piPowDeriv]
  refine (norm_sum_le _ _).trans ?_
  push_cast
  rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  have h1 := abs_piPow_le (Function.update m i (m i - 1)) hγ
  have h2 : R ^ (∑ j, Function.update m i (m i - 1) j) ≤ R ^ (∑ j, m j) :=
    pow_le_pow_right₀ hR (sum_update_le m i)
  have h3 := norm_coordCLM_le i
  calc (m i : ℝ) * |piPow (Function.update m i (m i - 1)) γ| * ‖coordCLM i‖
      ≤ (m i : ℝ) * R ^ (∑ j, m j) * 1 := by
        gcongr
        exact h1.trans h2
    _ = (m i : ℝ) * R ^ (∑ j, m j) := mul_one _

theorem norm_piPowDeriv2_le (m : Fin p → ℕ) {γ : Fin p → ℝ} {R : ℝ} (hR : 1 ≤ R)
    (hγ : ∀ i, |γ i| ≤ R) :
    ‖piPowDeriv2 m γ‖ ≤ ((∑ i, m i : ℕ) : ℝ) ^ 2 * R ^ (∑ i, m i) := by
  rw [piPowDeriv2]
  refine (norm_sum_le (E := (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) →L[ℝ] ℝ) _ _).trans ?_
  have hM : ((∑ i, m i : ℕ) : ℝ) ^ 2 * R ^ (∑ i, m i) =
      ∑ i, (m i : ℝ) * (((∑ i, m i : ℕ) : ℝ) * R ^ (∑ i, m i)) := by
    rw [← sum_mul]
    push_cast
    ring
  rw [hM]
  refine sum_le_sum fun i _ => ?_
  rw [norm_smulRight_apply, norm_smul, Real.norm_eq_abs, Nat.abs_cast]
  have h1 := norm_piPowDeriv_le (Function.update m i (m i - 1)) hR hγ
  have h2 : (((∑ j, Function.update m i (m i - 1) j : ℕ) : ℝ)) ≤ ((∑ j, m j : ℕ) : ℝ) := by
    exact_mod_cast sum_update_le m i
  have h3 : R ^ (∑ j, Function.update m i (m i - 1) j) ≤ R ^ (∑ j, m j) :=
    pow_le_pow_right₀ hR (sum_update_le m i)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  calc (m i : ℝ) * ‖piPowDeriv (Function.update m i (m i - 1)) γ‖ * ‖coordCLM i‖
      ≤ (m i : ℝ) * (((∑ j, m j : ℕ) : ℝ) * R ^ (∑ j, m j)) * 1 := by
        gcongr
        · exact h1.trans (mul_le_mul h2 h3 (by positivity) (by positivity))
        · exact norm_coordCLM_le i
    _ = _ := mul_one _

end Monomial

section Domain

/-- The open box `(-2, 2)^p`, a convex open neighbourhood of `[0,1]^p` on which the cluster
series and its first two derivatives converge. -/
def rateDomain (p : ℕ) : Set (Fin p → ℝ) :=
  Set.univ.pi fun _ => Set.Ioo (-2 : ℝ) 2

theorem isOpen_rateDomain : IsOpen (rateDomain p) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem convex_rateDomain : Convex ℝ (rateDomain p) :=
  convex_pi fun _ _ => convex_Ioo _ _

theorem mem_rateDomain {γ : Fin p → ℝ} : γ ∈ rateDomain p ↔ ∀ i, γ i ∈ Set.Ioo (-2 : ℝ) 2 := by
  simp [rateDomain]

theorem abs_le_two_of_mem_rateDomain {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p) (i : Fin p) :
    |γ i| ≤ 2 := by
  have := mem_rateDomain.mp hγ i
  rw [abs_le]
  exact ⟨this.1.le, this.2.le⟩

theorem zero_mem_rateDomain : (0 : Fin p → ℝ) ∈ rateDomain p :=
  mem_rateDomain.mpr fun _ => by norm_num

theorem mem_rateDomain_of_mem_Icc {γ : Fin p → ℝ} (hγ : ∀ i, γ i ∈ Set.Icc (0 : ℝ) 1) :
    γ ∈ rateDomain p :=
  mem_rateDomain.mpr fun i => ⟨by linarith [(hγ i).1], by linarith [(hγ i).2]⟩

end Domain

/-- The cluster part `h(γ) = ∑_{n ≥ 1} ∑_{m ∈ ℕ^p} rateSeriesTerm p kmult γ n m` of the rate
function. -/
noncomputable def rateCluster (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) : ℝ :=
  ∑' n : ℕ+, ∑' m : Fin p → ℕ, rateSeriesTerm p kmult γ n m

/-- `ℐ = ∑ᵢ γᵢ (log i! - 1 + log γᵢ - log 𝗆(i)) + 1 + h`. -/
theorem rateFunction_eq (p : ℕ) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) :
    rateFunction p msf kmult γ =
      ∑ i, γ i * (Real.log ((i : ℕ) + 1).factorial - 1 + Real.log (γ i) -
        Real.log (msf ((i : ℕ) + 1))) + 1 + rateCluster p kmult γ :=
  rfl

section Series

variable {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

/-- The joint sum `F(γ) = ∑_{(n,m)} c(n,m) γ^m`. -/
private noncomputable def clusterF (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) : ℝ :=
  ∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesTerm p kmult 1 nm.1 nm.2 * piPow nm.2 γ

/-- Its termwise derivative. -/
private noncomputable def clusterF' (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) :
    (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesTerm p kmult 1 nm.1 nm.2 • piPowDeriv nm.2 γ

/-- Its termwise second derivative. -/
private noncomputable def clusterF'' (p : ℕ) (kmult : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) :
    (Fin p → ℝ) →L[ℝ] (Fin p → ℝ) →L[ℝ] ℝ :=
  ∑' nm : ℕ+ × (Fin p → ℕ), rateSeriesTerm p kmult 1 nm.1 nm.2 • piPowDeriv2 nm.2 γ

private theorem norm_term_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p)
    (nm : ℕ+ × (Fin p → ℕ)) :
    ‖rateSeriesTerm p kmult 1 nm.1 nm.2 * piPow nm.2 γ‖ ≤ rateSeriesMajorant p C lam nm := by
  rw [← rateSeriesTerm_eq_mul_piPow, Real.norm_eq_abs]
  exact abs_rateSeriesTerm_le_majorant hk hlam hsmall (abs_le_two_of_mem_rateDomain hγ) nm

private theorem norm_term'_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p)
    (nm : ℕ+ × (Fin p → ℕ)) :
    ‖rateSeriesTerm p kmult 1 nm.1 nm.2 • piPowDeriv nm.2 γ‖ ≤ rateSeriesMajorant p C lam nm := by
  rw [norm_smul, Real.norm_eq_abs]
  have h := abs_rateSeriesTerm_one_mul_pow_le hk hlam hsmall nm (by norm_num : (0 : ℝ) ≤ 2)
    le_rfl (by norm_num : 1 ≤ 2)
  rw [pow_one] at h
  refine (mul_le_mul_of_nonneg_left (norm_piPowDeriv_le nm.2 (by norm_num)
    (abs_le_two_of_mem_rateDomain hγ)) (abs_nonneg _)).trans ?_
  rw [← mul_assoc]
  exact h

private theorem norm_term''_le (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p)
    (nm : ℕ+ × (Fin p → ℕ)) :
    ‖rateSeriesTerm p kmult 1 nm.1 nm.2 • piPowDeriv2 nm.2 γ‖ ≤ rateSeriesMajorant p C lam nm := by
  refine (opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs]
  have h := abs_rateSeriesTerm_one_mul_pow_le hk hlam hsmall nm (by norm_num : (0 : ℝ) ≤ 2)
    le_rfl (le_refl 2)
  refine (mul_le_mul_of_nonneg_left (norm_piPowDeriv2_le nm.2 (by norm_num)
    (abs_le_two_of_mem_rateDomain hγ)) (abs_nonneg _)).trans ?_
  rw [← mul_assoc]
  exact h

private theorem hasFDerivAt_clusterF (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p) :
    HasFDerivAt (clusterF p kmult) (clusterF' p kmult γ) γ := by
  refine hasFDerivAt_tsum_of_isPreconnected (summable_rateSeriesMajorant p C lam)
    isOpen_rateDomain convex_rateDomain.isPreconnected
    (fun nm y _ => (hasFDerivAt_piPow nm.2 y).const_mul _)
    (fun nm y hy => norm_term'_le hk hlam hsmall hy nm) zero_mem_rateDomain ?_ hγ
  exact (summable_rateSeriesMajorant p C lam).of_norm_bounded
    fun nm => norm_term_le hk hlam hsmall zero_mem_rateDomain nm

private theorem hasFDerivAt_clusterF' (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p) :
    HasFDerivAt (clusterF' p kmult) (clusterF'' p kmult γ) γ := by
  refine hasFDerivAt_tsum_of_isPreconnected (summable_rateSeriesMajorant p C lam)
    isOpen_rateDomain convex_rateDomain.isPreconnected
    (fun nm y _ => (hasFDerivAt_piPowDeriv nm.2 y).const_smul _)
    (fun nm y hy => norm_term''_le hk hlam hsmall hy nm) zero_mem_rateDomain ?_ hγ
  exact (summable_rateSeriesMajorant p C lam).of_norm_bounded
    fun nm => norm_term'_le hk hlam hsmall zero_mem_rateDomain nm

/-- `continuousOn_tsum` for `(Fin p → ℝ) →L[ℝ] G`-valued series with `G` abstract (stating it
directly for `G = (Fin p → ℝ) →L[ℝ] ℝ` makes instance unification expensive). -/
private theorem continuousOn_clm_tsum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {ι : Type*} {f : ι → (Fin p → ℝ) → (Fin p → ℝ) →L[ℝ] G} {u : ι → ℝ}
    {s : Set (Fin p → ℝ)} (hf : ∀ i, ContinuousOn (f i) s) (hu : Summable u)
    (h : ∀ i x, x ∈ s → ‖f i x‖ ≤ u i) :
    ContinuousOn (fun x => ∑' i, f i x) s :=
  continuousOn_tsum hf hu h

private theorem continuousOn_clusterF'' (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) :
    ContinuousOn (clusterF'' p kmult) (rateDomain p) := by
  have hc : ∀ nm : ℕ+ × (Fin p → ℕ), ContinuousOn
      (fun γ => rateSeriesTerm p kmult 1 nm.1 nm.2 • piPowDeriv2 nm.2 γ) (rateDomain p) :=
    fun nm => ((continuous_piPowDeriv2 nm.2).fun_const_smul _).continuousOn
  have hb : ∀ (nm : ℕ+ × (Fin p → ℕ)) γ, γ ∈ rateDomain p →
      ‖rateSeriesTerm p kmult 1 nm.1 nm.2 • piPowDeriv2 nm.2 γ‖ ≤
        rateSeriesMajorant p C lam nm := fun nm _ hy => norm_term''_le hk hlam hsmall hy nm
  exact continuousOn_clm_tsum hc (summable_rateSeriesMajorant p C lam) hb

private theorem rateCluster_eq_clusterF (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) {γ : Fin p → ℝ} (hγ : γ ∈ rateDomain p) :
    rateCluster p kmult γ = clusterF p kmult γ := by
  rw [rateCluster, (rateCluster_eq_tsum_and_le hk hlam hsmall
    (abs_le_two_of_mem_rateDomain hγ)).1, clusterF]
  exact tsum_congr fun nm => rateSeriesTerm_eq_mul_piPow p kmult γ nm.1 nm.2

private theorem bound_of_majorant {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ+ × (Fin p → ℕ) → E} (hf : ∀ nm, ‖f nm‖ ≤ rateSeriesMajorant p C lam nm) :
    ‖∑' nm, f nm‖ ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 := by
  rw [← (hasSum_rateSeriesMajorant p C lam).tsum_eq]
  exact tsum_of_norm_bounded (summable_rateSeriesMajorant p C lam).hasSum hf

/-- `bound_of_majorant` for `(Fin p → ℝ) →L[ℝ] G`-valued families with `G` abstract. -/
private theorem bound_of_majorant_clm {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {f : ℕ+ × (Fin p → ℕ) → (Fin p → ℝ) →L[ℝ] G}
    (hf : ∀ nm, ‖f nm‖ ≤ rateSeriesMajorant p C lam nm) :
    ‖∑' nm, f nm‖ ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 :=
  bound_of_majorant hf

/-- The analytic package for the cluster part at a fixed small `λ`: on `rateDomain p`, `h` is
`C²`, its derivatives are the termwise ones, and `h`, `Dh`, `D²h` are bounded by
`16 K² 2^p λ²` each. -/
theorem rateCluster_smooth_of_small (hk : KmultBound p kmult C lam) (hlam : 0 ≤ lam)
    (hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4) :
    ContDiffOn ℝ 2 (rateCluster p kmult) (rateDomain p) ∧
      ∀ γ ∈ rateDomain p,
        HasFDerivAt (rateCluster p kmult) (fderiv ℝ (rateCluster p kmult) γ) γ ∧
        HasFDerivAt (fderiv ℝ (rateCluster p kmult))
          (fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ) γ ∧
        |rateCluster p kmult γ| ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ∧
        ‖fderiv ℝ (rateCluster p kmult) γ‖ ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ‖ ≤
          16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 := by
  set U := rateDomain p
  have hEq : ∀ γ ∈ U, rateCluster p kmult γ = clusterF p kmult γ := fun γ hγ =>
    rateCluster_eq_clusterF hk hlam hsmall hγ
  have hEv : ∀ γ ∈ U, rateCluster p kmult =ᶠ[𝓝 γ] clusterF p kmult := fun γ hγ =>
    Filter.eventually_of_mem (isOpen_rateDomain.mem_nhds hγ) hEq
  have hD1 : ∀ γ ∈ U, HasFDerivAt (rateCluster p kmult) (clusterF' p kmult γ) γ := fun γ hγ =>
    (hasFDerivAt_clusterF hk hlam hsmall hγ).congr_of_eventuallyEq (hEv γ hγ)
  have hfd : ∀ γ ∈ U, fderiv ℝ (rateCluster p kmult) γ = clusterF' p kmult γ := fun γ hγ =>
    (hD1 γ hγ).fderiv
  have hEv' : ∀ γ ∈ U, fderiv ℝ (rateCluster p kmult) =ᶠ[𝓝 γ] clusterF' p kmult := fun γ hγ =>
    Filter.eventually_of_mem (isOpen_rateDomain.mem_nhds hγ) hfd
  have hD2 : ∀ γ ∈ U, HasFDerivAt (fderiv ℝ (rateCluster p kmult)) (clusterF'' p kmult γ) γ :=
    fun γ hγ => (hasFDerivAt_clusterF' hk hlam hsmall hγ).congr_of_eventuallyEq (hEv' γ hγ)
  have hfd2 : ∀ γ ∈ U, fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ = clusterF'' p kmult γ :=
    fun γ hγ => (hD2 γ hγ).fderiv
  refine ⟨?_, fun γ hγ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · have h1 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h1, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_rateDomain]
    refine ⟨fun γ hγ => (hD1 γ hγ).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_rateDomain]
    refine ⟨fun γ hγ => (hD2 γ hγ).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact (continuousOn_clusterF'' hk hlam hsmall).congr fun γ hγ => hfd2 γ hγ
  · rw [hfd γ hγ]
    exact hD1 γ hγ
  · rw [hfd2 γ hγ]
    exact hD2 γ hγ
  · rw [hEq γ hγ, ← Real.norm_eq_abs]
    exact bound_of_majorant fun nm => norm_term_le hk hlam hsmall hγ nm
  · rw [hfd γ hγ]
    exact bound_of_majorant fun nm => norm_term'_le hk hlam hsmall hγ nm
  · rw [hfd2 γ hγ]
    exact bound_of_majorant_clm (G := (Fin p → ℝ) →L[ℝ] ℝ)
      fun nm => norm_term''_le hk hlam hsmall hγ nm

/-- **Derivative bounds** (equation (5.152)). For every `C`
and `p` there are `λ₀ > 0` and `C' > 0` such that for `0 < λ < λ₀` and coefficients `kmult`
satisfying (2.48) with constant `C`, the cluster part `h` of the rate function is `C²` on the
open neighbourhood `rateDomain p = (-2, 2)^p` of `[0,1]^p`, with
`|h(γ)| + ‖Dh(γ)‖ + ‖D²h(γ)‖ ≤ C' λ²` there. -/
theorem rateCluster_smooth (p : ℕ) (C : ℝ) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ C' : ℝ, 0 < C' ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ kmult : (ℕ →₀ ℕ) → ℝ, KmultBound p kmult C lam →
        ContDiffOn ℝ 2 (rateCluster p kmult) (rateDomain p) ∧
        ∀ γ ∈ rateDomain p,
          HasFDerivAt (rateCluster p kmult) (fderiv ℝ (rateCluster p kmult) γ) γ ∧
          HasFDerivAt (fderiv ℝ (rateCluster p kmult))
            (fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ) γ ∧
          |rateCluster p kmult γ| + ‖fderiv ℝ (rateCluster p kmult) γ‖ +
            ‖fderiv ℝ (fderiv ℝ (rateCluster p kmult)) γ‖ ≤ C' * lam ^ 2 := by
  refine ⟨rateSeriesLam₀ p C, rateSeriesLam₀_pos p C,
    3 * (16 * rateSeriesConst p C ^ 2 * 2 ^ p) + 1, by positivity, ?_⟩
  intro lam hlam hlam₀ kmult hk
  have hsmall := rateSeriesConst_mul_sq_le p C hlam.le hlam₀
  obtain ⟨hcd, hall⟩ := rateCluster_smooth_of_small hk hlam.le hsmall
  refine ⟨hcd, fun γ hγ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hall γ hγ
  refine ⟨h1, h2, ?_⟩
  nlinarith [sq_nonneg lam]

end Series

end MultipoleBKT

end
