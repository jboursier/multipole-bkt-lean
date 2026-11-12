/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.MultipoleDiff
public import MultipoleBKT.LowerBound.BoundedLower.DipoleActivity

/-!
# Proposition 4.24, eq. (4.43), from Lemma A.8

Proposition 4.24,
eq. (4.43) (Proposition 4.24); proof of Proposition 4.24: for `1 < |S| = k ≤ p*(β)`,

`|𝖪^dip_{β,λ,ε₀}(S) - 𝖪^dip_{β,λ}(S)| ≤ C N^{1-k} R̄^{-2}`.

* `truncatedDipoleActivity`: `𝖪^dip_{β,λ,ε₀}(V)` (Definition 4.20,
  eq. (4.37), Section 4.7);
* `dipoleIntegralCut`: `I_{dip,ε₀}(V; E)` (eq. (A.28), Section A.3) for `ε₀ < ∞`;
  `I_{dip,∞}(V; E)` is `SmallIntegral.dipoleIntegral`;
* `LemmaI3Statement`: the statement of Lemma A.8 (its proof is omitted
  in the paper), as a hypothesis;
* `eq_Kdip_diff_of_lemma_I3` (internal, conditional on Lemma A.8): (4.43).

**Proof** (proof of Proposition 4.24: "combining (4.13) and the integral estimate of Lemma A.8").
`𝖪^dip_{β,λ,ε₀}(V) = (N C_{β,λ,ε₀})^{-k} ∑_E I_{dip,ε₀}(V; E)` and
`𝖪^dip_{β,λ}(V) = (N C_{β,λ})^{-k} ∑_E I_{dip,∞}(V; E)`; Lemma A.8 bounds the difference of the
sums, (4.13) the change of normalization, and (4.41)
(`BoundedLower.dipoleActivity_bound`) the size of `𝖪^dip_{β,λ}(V)`, exactly as for (4.42)
(`abs_normalized_sub_le`).
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open TwoComponentCoulomb (box)
open Hierarchical Limits

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam ε₀ : ℝ}

open scoped Classical in
/-- **The truncated dipole activity** `𝖪^dip_{β,λ,ε₀}(V)` (Definition 4.20, eq. (4.37), Section 4.7): the sum over
`E ∈ 𝒢_c(V)` (connected edge sets on `V` with at least one edge) of
`𝔼_{μ_{β,λ,ε₀}^{⊗|V|}} ∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝒜_ij} - 1)`, with `μ_{β,λ,ε₀}` the truncated
dipole measure (eq. (4.9)). It is the frozen `dipoleActivity` with `μ_{β,λ}` replaced by
`μ_{β,λ,ε₀}`. -/
noncomputable def truncatedDipoleActivity (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ)
    (V : Finset ℕ) : ℝ :=
  ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty),
    ∫ c : V → ℂ × ℂ,
      ∏ i : V, ∏ j : V,
        if i < j ∧ E.Adj i j then
          (if IsStableDipolePair (c i) (c j) then
              Real.exp (-β * dipoleInteraction χ lam (c i) (c j)) else 0) - 1
        else 1
      ∂Measure.pi fun _ : V => cutoffDipoleMeasure χ N p₀ β lam ε₀

open scoped Classical in
/-- **The truncated dipole integral** `I_{dip,ε₀}(V; E)` (eq. (A.28), Section A.3):
`∫_{(Λ²)^{|V|}} ∏_{ij ∈ E} f_ij^v ∏_{i ∈ V} e^{β g_λ(x_i - y_i)} 𝟙_{r_i ≤ ε₀ R̄} dx_i dy_i`, with
`f_ij^v = e^{-β v_ij} 𝟙_{𝒜_ij} - 1` evaluated with `i < j`. -/
noncomputable def dipoleIntegralCut (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset ℕ)
    (E : SimpleGraph V) : ℝ :=
  ∫ c in boxConfig V N, dipoleActivityIntegrand χ β lam E c *
    ∏ i, cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam) (c i)

open scoped Classical in
/-- **Lemma A.8** ( the proof is omitted in the paper), as a
statement: for `β > 2`, `k ≤ p*(β)` and `ε₀ ∈ (0, 1)` there is `C > 0` such that
`|∑_{E ∈ 𝒢_c(V)} (I_{dip,ε₀}(V; E) - I_{dip,∞}(V; E))| ≤ C N λ^{(2-β)|V|} R̄^{-2}` for `|V| = k`.
The paper gives no restriction on `λ` or `N`; this statement asks it only for `λ` small and `N`
large (so it is implied by the paper's form) and for `V ⊆ [N]`. `C` may depend on `χ, β, k, p₀`
and `ε₀`. -/
def LemmaI3Statement (χ : ℂ → ℝ) (β : ℝ) (p₀ k : ℕ) : Prop :=
  ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
        |∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
            (fun E => E.Connected ∧ E.edgeSet.Nonempty),
          (dipoleIntegralCut χ N p₀ β lam ε₀ V E - SmallIntegral.dipoleIntegral χ N β lam V E)| ≤
        C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))

open scoped Classical in
/-- `𝖪^dip_{β,λ,ε₀}(V) = (N C_{β,λ,ε₀})^{-|V|} ∑_{E ∈ 𝒢_c(V)} I_{dip,ε₀}(V; E)`, for `λ > 0`,
`ε₀ > 0`, `N ≥ 1`. -/
theorem truncatedDipoleActivity_eq_sum (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (V : Finset ℕ) :
    truncatedDipoleActivity χ N p₀ β lam ε₀ V =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ V.card *
        ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
            (fun E => E.Connected ∧ E.edgeSet.Nonempty),
          dipoleIntegralCut χ N p₀ β lam ε₀ V E := by
  rw [Finset.mul_sum]
  refine sum_congr rfl fun E _ => ?_
  have h := integral_pi_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
    (dipoleActivityIntegrand χ β lam E)
  rw [Fintype.card_coe] at h
  exact h

open scoped Classical in
/-- **Proposition 4.24, eq. (4.43)**, conditional on Lemma A.8 (internal helper;
Proposition 4.24; proof of Proposition 4.24): for `β > 2`, `2 ≤ k ≤ p*(β)` and `p₀`,
if Lemma A.8 holds for `k`, then for `ε₀ ∈ (0, 1)` there are `C > 0` and `λ₀ ∈ (0, 1]` such
that for `λ ∈ (0, λ₀)` there is `N₀` with
`|𝖪^dip_{β,λ,ε₀}(V) - 𝖪^dip_{β,λ}(V)| ≤ C N^{1-k} R̄^{-2}` for `N ≥ N₀`, `V ⊆ [N]`, `|V| = k`. -/
theorem eq_Kdip_diff_of_lemma_I3 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (p₀ : ℕ) (hI3 : LemmaI3Statement χ β p₀ k) :
    ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
          |truncatedDipoleActivity χ N p₀ β lam ε₀ V - dipoleActivity χ N β lam V| ≤
            C / (N : ℝ) ^ (k - 1) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  intro ε₀ hε₀ hε₁
  have hk1 : 1 ≤ k := by omega
  obtain ⟨CI, hCI, l₁, hl₁, hI⟩ := hI3 ε₀ hε₀ hε₁
  obtain ⟨Cd, hCd, l₂, hl₂, hl₂1, hdip⟩ := BoundedLower.dipoleActivity_bound χ hχ β hβ k hk hkp
  obtain ⟨Cn, hCn, l₃, hl₃, hl₃1, hnorm⟩ := normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨CI * (2 / Z) ^ k + k * 2 ^ (k - 1) * Cn * Cd, by positivity, min (min l₁ l₂) l₃,
    lt_min (lt_min hl₁ hl₂) hl₃, (min_le_right _ _).trans hl₃1, fun lam hlam hlt => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hI lam hlam (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨N₂, hN₂⟩ := hdip lam hlam (hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨N₃, hN₃⟩ := hnorm lam hlam (hlt.trans_le (min_le_right _ _))
  refine ⟨max (max N₁ N₂) N₃, fun N hN V hV hVk => ?_⟩
  obtain ⟨hN1, -, hCe, -, hC, hCZ, hδ⟩ :=
    hN₃ N (le_trans (le_max_right _ _) hN)
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans hl₃1)).le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  set R := truncationScale p₀ β lam
  set Ce := cutoffDipoleNormalization χ N p₀ β lam ε₀
  set C := dipoleNormalization χ N β lam
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  have hCe0 : 0 < Ce := lt_of_lt_of_le (by positivity) hCe
  have hratio : C / Ce ≤ 2 := by
    rw [div_le_iff₀ hCe0]
    nlinarith
  have hCe' : Z / 2 * lam ^ (2 - β) ≤ Ce := by linarith
  rw [truncatedDipoleActivity_eq_sum hχ hlam hε₀ hN1 V,
    SmallIntegral.dipoleActivity_eq_sum_dipoleIntegral hχ hlam hN1 V, ← Finset.mul_sum, hVk]
  -- Lemma A.8
  have hJ := hN₁ N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) V hV hVk
  rw [Finset.sum_sub_distrib, rpow_mul_natCast_eq hlam k] at hJ
  have hJ' : |∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
        (fun E => E.Connected ∧ E.edgeSet.Nonempty), dipoleIntegralCut χ N p₀ β lam ε₀ V E -
      ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
        (fun E => E.Connected ∧ E.edgeSet.Nonempty), SmallIntegral.dipoleIntegral χ N β lam V E| ≤
      CI * N * (lam ^ (2 - β)) ^ k * R ^ (-2 : ℝ) := hJ.trans_eq (by ring)
  -- (4.41)
  have hQ : |((N : ℝ) * C)⁻¹ ^ k * ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
        (fun E => E.Connected ∧ E.edgeSet.Nonempty), SmallIntegral.dipoleIntegral χ N β lam V E| ≤
      Cd / (N : ℝ) ^ (k - 1) := by
    have h := hN₂ N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN) V hV hVk
    rw [SmallIntegral.dipoleActivity_eq_sum_dipoleIntegral hχ hlam hN1 V, ← Finset.mul_sum,
      hVk] at h
    refine h.trans ?_
    have hΛ : lam ^ (2 * (k - 1)) ≤ 1 := pow_le_one₀ hlam.le hlam1
    have hNk : 0 < (N : ℝ) ^ (k - 1) := by positivity
    rw [div_le_div_iff_of_pos_right hNk]
    calc Cd * lam ^ (2 * (k - 1)) ≤ Cd * 1 := by gcongr
      _ = Cd := mul_one _
  have h := abs_normalized_sub_le hk1 hNpos hZ hℓ hCe' hC0 hratio hδ hJ' hQ
  refine h.trans (le_of_eq ?_)
  ring

end ExpansionErrors

end MultipoleBKT

end
