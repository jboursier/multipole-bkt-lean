/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.RouteNormalization.AtLambda
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Gate
public import MultipoleBKT.UpperBound.UpperBoundLDP.GoodAt
public import MultipoleBKT.UpperBound.UpperBoundLDP.RetainedHat
public import MultipoleBKT.UpperBound.UpperBoundLDP.BadBound
public import MultipoleBKT.UpperBound.SimplifiedUpper.Assembly
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Transfer
public import MultipoleBKT.LowerBound.LowerBoundLDP.Assembly
public import MultipoleBKT.Main.PropFiveFortyFive.Final
public import MultipoleBKT.Frozen.Proposition423

/-!
# Proposition 5.43

**Proposition 5.43** (the large deviations upper bound), as the internal theorem
`MultipoleBKT.UpperBoundLDP.proposition_5_43_upper`. It has no hypotheses beyond the binders
`χ, hχ, p₀, hp₀, β, hβ`, and its conclusion is the type of the frozen statement
`MultipoleBKT.proposition_5_43` after these binders.

The damping constant of the external normalization is `L = β L₀` with `L₀` of eq. (5.50)
(`MultipoleBKT.UpperBound.exists_energyLowerBound`), as in Lemma 5.16. The constants are chosen in
the order of the frozen statement:

* `M₀`: the thresholds of Proposition 5.20 (`prop_5_20_of_simplified`, with Lemma 5.37 and the
  transfer of Lemma 4.59 / Proposition 4.27 proved), of Proposition 5.19 and (4.45) for the sizes
  `k ≤ p` (`MultipoleBKT.UpperBoundLDP.prop_5_19_uniform`, `K_diff0_uniform`), of (4.38)–(4.40)
  (Proposition 4.23), `21` and `3^{p(β)}`;
* at `M`: the constants that do not depend on `ε₀`: `C_coef` of (2.47)–(2.48), `C` of
  Proposition 5.19, `C_z` of (4.38) for `𝖬^0_{ε₀}`; with them `K_V` and
  `t' = t + β L₀ + β C_bb + K_V + 1`;
* `ε₁ = min(ε₁(5.38 at t'), ε₁(5.20))`;
* at `ε₀`: `C = C₃₈ + K_δ + K_norm + 1` and `λ₀` (`bound_at_eps_upper`), from the constants of
  Propositions 5.19, 5.20, 5.38 at `ε₀`, of `|𝖬^0_{ε₀} - 𝖬^0_∞|`, (4.45), the retained hatted
  activities, the cluster-sum estimate, the polymer gas, and the logarithmic normalization
  expansion (`RouteNormalization.log_normalization_expansion`: coefficient `K_norm`, and `λ₀` below
  its threshold);
* `N₀(λ)`: `MultipoleBKT.UpperBoundLDP.bound_at_lambda_upper_of_log_normalization` with
  `MultipoleBKT.UpperBoundLDP.good_eventually`.

The absolute summability of the rate series on `⋃_{x ∈ [0,1]} Δ_{p,x}` is
`MultipoleBKT.rateSeries_summable_and_bound` (`|γᵢ| ≤ 1` on `Δ_{p,x}`).
-/

@[expose] public section

open MeasureTheory Finset Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical PropFiveFortyFive UpperBound SetPartition

open scoped Classical in
/-- **Proposition 5.43 at fixed `M` and `ε₀`** (internal; see the module docstring). The
hypotheses are the constants chosen before `ε₀` (eq. (5.50), eq. (5.112), (2.47)–(2.48), the constant
of Proposition 5.19, (4.38) for `𝖬^0_{ε₀}` and `𝖬^0_∞`) and the estimates at `ε₀` (Propositions
5.19, 5.20, 5.38 and (4.45)). -/
theorem bound_at_eps_upper {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ}
    (hβ : 2 < β) {M ε₀ t : ℝ} (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hε₀ : 0 < ε₀)
    (hε₀1 : ε₀ < 1) (ht : 1 ≤ t) {msf : ℝ → ℕ → ℝ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}
    (hS : TheoremTwo.MsfLimits χ β M msf) (hX : TheoremTwo.KmultLimits χ β M kmult)
    {L₀ Cbb Cc lc CM Cz Cl' ll t' : ℝ} (hb1 : EnergyLowerBound χ L₀)
    (hbb : ∀ {N : ℕ} (V : Finset (Fin N)) (lam M ε₀ : ℝ), 0 < lam →
      ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z')) ≤
        ENNReal.ofReal (Real.exp (β * Cbb * V.card)) *
          badPartitionFunction p₀ β lam M ε₀ N V.card)
    (hCc : 0 < Cc) (hlc : 0 < lc)
    (hcoef : ∀ lam : ℝ, 0 < lam → lam < lc →
      MsfBound (pBeta p₀ β) (msf lam) Cc lam ∧ KmultBound (pBeta p₀ β) (kmult lam) Cc lam)
    (hCM : 0 < CM)
    (h19 : ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
        Prop519At χ p₀ β M ε₀ (β * L₀) CM s Cε lam N)
    (hCz : 1 ≤ Cz)
    (hz : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, 2 ≤ S.card → S.card ≤ pBeta p₀ β →
        lam ^ (2 * (S.card - 1)) / (Cz * (N : ℝ) ^ (S.card - 1)) ≤
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S})
    (hCl' : 0 < Cl') (hll : 0 < ll)
    (hlow' : ∀ lam : ℝ, 0 < lam → lam < ll → ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ,
      S ⊆ Finset.range N → 1 ≤ S.card → S.card ≤ pBeta p₀ β →
        lam ^ (2 * (S.card - 1)) / (Cl' * (N : ℝ) ^ (S.card - 1)) ≤
          multipolePartitionFunction χ N β lam M S)
    (ht' : t' = t + β * L₀ + β * Cbb + (max Cc 1 * CM * pBeta p₀ β +
      4 * Real.exp 2 * (CM * Cz ^ pBeta p₀ β) * Real.exp (pBeta p₀ β)) + 1)
    (h38 : ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N →
        (N.choose m : ℝ≥0∞) * badPartitionFunction p₀ β lam M ε₀ N m *
            ENNReal.ofReal (Real.exp (t' * m)) ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ m * Real.exp (C * N * errorRate p₀ β lam)))
    (h20 : ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
        ∀ π : Finset (Finset ℕ), IsSubpartition π →
          (∀ S ∈ π, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
          (∀ S ∈ π, S.card ≤ pBeta p₀ β) → AbsoluteUpper.ProfileBound p₀ β lam ε₀ N π →
          AbsoluteUpper.AbsoluteUpperBounds (hatActivity χ N p₀ β lam M ε₀ (β * L₀) V Z) π
            (pBeta p₀ β) (C * N * errorRate p₀ β lam))
    (hK0 : ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
          1 < X.card → (X.biUnion id).card = s →
          |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
            C * truncationScale p₀ β lam ^ (-2 : ℝ) /
              ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (s - 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex (pBeta p₀ β) x,
          Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
            ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin (pBeta p₀ β) → ℕ,
          ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
          (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
            (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
          ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
              {c | ∀ i : Fin (pBeta p₀ β),
                goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
            ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
                fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
              ENNReal.ofReal (Real.exp (-β * energy χ lam c))
            ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                - N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                + C * N * errorRate p₀ β lam)) := by
  have hp1 : 1 ≤ pBeta p₀ β := TheoremTwo.one_le_pBeta' hp₀ hβ
  have hpS : ((pBeta p₀ β : ℕ) : ℕ∞) ≤ pStar β := TheoremTwo.pBeta_le_pStar hp₀ hβ
  have hM1 : 1 ≤ M := by linarith
  have hA : 0 ≤ ε₀ ^ (-alphaExponent β) := Real.rpow_nonneg hε₀.le _
  have hCm : 1 ≤ max Cc 1 := le_max_right _ _
  have hClow : 1 ≤ max Cl' 1 := le_max_right _ _
  obtain ⟨Cε, hCε, l19, hl19, h19l⟩ := h19
  obtain ⟨lz, hlz, hzl⟩ := hz
  obtain ⟨C₃₈, hC₃₈, l38, hl38, h38l⟩ := h38
  obtain ⟨C20, hC20, l20, hl20, h20l⟩ := h20
  obtain ⟨CK0, hCK0, lK0, hlK0, hK0l⟩ := hK0
  obtain ⟨C0, hC0, lM0, hlM0, hM0l⟩ := zero_M_diff_uniform (χ := χ) hχ hβ hp₀ (M := M)
    (by linarith) hε₀ hε₀1
  obtain ⟨Cs, hCs, lret, hlret, hretl⟩ := hat_retained_bound hχ hp₀ hβ (β * L₀) hM hMp hε₀ hε₀1
  obtain ⟨lr, hlr, -, C'', -, hrate⟩ := TheoremTwo.exists_rateSetup hp1 hCc
  obtain ⟨lrs, hlrs, Crs, -, hrs⟩ := rateSeries_summable_and_bound (pBeta p₀ β) Cc
  obtain ⟨Ct₂, hCt₂, hlogpoly⟩ :=
    exists_log_polymerSum_subpartition (2 * Cc) (by positivity) (pBeta p₀ β)
  have hC₀ : 0 ≤ Cs + 2 * Cc := by positivity
  obtain ⟨Ct, hCt, hlogDall⟩ := exists_log_disjointSum_le (Cs + 2 * Cc) hC₀ (pBeta p₀ β)
  have hE : 0 ≤ Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (Cs + 2 * Cc)))) := by positivity
  -- The logarithmic expansion in the paper, (5.150).
  obtain ⟨Knorm, hKnorm, hnorm⟩ :=
    RouteNormalization.log_normalization_expansion hχ hβ ε₀ hε₀ hε₀1
  obtain ⟨lnorm, hlnorm, hnorml⟩ := hnorm p₀ hp₀
  refine ⟨C₃₈ + (max Cc 1 * (Cε + C0 + 1) * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) +
      4 * Real.exp 2 * (Cε * Cz ^ pBeta p₀ β + CK0 * max Cl' 1 ^ pBeta p₀ β) *
        Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) + C20 + 1) + Knorm + 1,
    by positivity,
    min lnorm (min (min (min lc lr) (min lrs ll)) (min (min (min l19 lz) (min l38 l20))
      (min (min lK0 lM0) (min (min lret (1 / 2)) (min (1 / (2 * Ct + 2))
        (min (1 / (2 * (Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (Cs + 2 * Cc))))) + 2))
          (1 / (2 * Ct₂ + 2)))))))), ?_, ?_, fun lam hlam hlaml => ?_⟩
  · apply lt_min hlnorm
    simp only [lt_min_iff]
    exact ⟨⟨⟨hlc, hlr⟩, hlrs, hll⟩, ⟨⟨hl19, hlz⟩, hl38, hl20⟩, ⟨hlK0, hlM0⟩,
      ⟨hlret, by norm_num⟩, by positivity, by positivity, by positivity⟩
  · refine (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_left _ _).trans
        ((min_le_right _ _).trans (by norm_num))))))
  obtain ⟨hlnorm', hlaml⟩ := lt_min_iff.mp hlaml
  simp only [lt_min_iff] at hlaml
  obtain ⟨⟨⟨hlc', hlr'⟩, hlrs', hll'⟩, ⟨⟨hl19', hlz'⟩, hl38', hl20'⟩, ⟨hlK0', hlM0'⟩,
    ⟨hlret', hlh'⟩, hlt₁, hlt₂, hlt₃⟩ := hlaml
  have hlam1 : lam < 1 := hlh'.trans (by norm_num)
  obtain ⟨hMB, hKB⟩ := hcoef lam hlam hlc'
  have hset := (hrate lam hlam hlr' (msf lam) (kmult lam) hMB hKB).1
  refine ⟨fun x _ γ hγ => (hrs lam hlam hlrs' (kmult lam) hKB γ fun i => ?_).1, ?_⟩
  · have h := hγ.1 i
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  -- the lower bound on `𝗆(k)`
  have hmsf : ∀ k, 1 ≤ k → k ≤ pBeta p₀ β → lam ^ (2 * (k - 1)) / max Cc 1 ≤ msf lam k := by
    intro k hk1 hkp
    rcases Nat.lt_or_ge k 2 with h | h
    · rw [show k = 1 by omega, hMB.1, Nat.sub_self, mul_zero, pow_zero]
      exact div_le_one_of_le₀ hCm (by linarith)
    · calc lam ^ (2 * (k - 1)) / max Cc 1 ≤ lam ^ (2 * (k - 1)) / Cc :=
            div_le_div_of_nonneg_left (by positivity) hCc (le_max_left _ _)
        _ = Cc⁻¹ * lam ^ (2 * (k - 1)) := by rw [div_eq_inv_mul]
        _ ≤ msf lam k := (hMB.2 k h hkp).1
  -- the limits (2.45)–(2.46) at `λ`
  have hSl : ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ pBeta p₀ β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S)
        atTop (𝓝 (msf lam S.card)) := fun S hS1 hSp =>
    hS lam hlam hlam1 S hS1 ((Nat.cast_le.2 hSp).trans hpS)
  have hKinv : ∀ N, 1 ≤ N → IsProfileInvariant (multipoleActivity χ N β lam M) :=
    fun N hN X X' hX hX' hprof => Limits.multipoleActivity_eq_of_blockProfile_eq hχ hlam hN hX hX'
      hprof
  have hKlim : ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card ≤ pBeta p₀ β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * multipoleActivity χ N β lam M X) atTop
        (𝓝 (kmult lam (blockProfile X))) := by
    intro X hX' h2 hV
    have hS' : ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β := by
      rw [TheoremTwo.sum_card_eq_card_biUnion hX']
      exact (Nat.cast_le.2 hV).trans hpS
    refine (hX lam hlam hlam1 X hX' hS').congr fun N => ?_
    rw [TheoremTwo.zpow_card_sub_one (by omega)]
  have hact := eventually_abs_multipoleActivity_le hχ hpS hlam hCc hKB (hX lam hlam hlam1)
  -- the polymer gas and the cluster sums
  have hδ : 0 < errorRate p₀ β lam := TheoremTwo.errorRate_pos hβ hlam
  have hpoly := hlogpoly (kmult lam) Cc lam (fun N => multipoleActivity χ N β lam M) hlam
    hlam1.le (LowerBoundLDP.mul_sq_le_half hCt₂.le hlam hlam1.le hlt₃.le) hKB hset.hsmall hKinv
    hKlim hact (errorRate p₀ β lam) hδ
  have hCtl : Ct * lam ^ 2 ≤ 1 / 2 := LowerBoundLDP.mul_sq_le_half hCt.le hlam hlam1.le hlt₁.le
  have hsmallD : Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (Cs + 2 * Cc)) * lam ^ 2)) ≤
      1 / 2 := by
    have h := LowerBoundLDP.mul_sq_le_half hE hlam hlam1.le hlt₂.le
    calc Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (Cs + 2 * Cc)) * lam ^ 2))
        = Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (Cs + 2 * Cc)))) * lam ^ 2 := by ring
      _ ≤ 1 / 2 := h
  -- the estimates for `N` large
  have ev : ∀ {P : ℕ → Prop}, (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P N) → ∀ᶠ N : ℕ in atTop, P N :=
    fun h => eventually_atTop.2 h
  have hgood := good_eventually (L := β * L₀) hχ hβ hlam hlam1.le hε₀ hε₀1.le hM1 hCε.le hCM.le
    hC0.le hCm hCK0.le hCz hClow hCs hCc.le hSl hmsf (ev (h19l lam hlam hl19'))
    (ev (hM0l lam hlam hlM0')) (ev (hK0l lam hlam hlK0'))
    (ev (hzl lam hlam hlz'))
    (by
      filter_upwards [hlow' lam hlam hll', eventually_ge_atTop 1] with N hN hN1 S hS h1 hp
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
      refine le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (hN S hS h1 hp))
    (ev (hretl lam hlam hlret')) hact (ev (h20l lam hlam hl20')) hpoly
    (fun N π K₁ K₂ B hπ hπN hK1 hb₁ hb₂ habs hbad => by
      convert hlogDall N π K₁ K₂ lam B hπ hπN hlam hlam1.le hCtl hsmallD hK1 hb₁ hb₂
        (by convert habs) (by convert hbad))
  exact bound_at_lambda_upper_of_log_normalization (K := Knorm)
    (R := truncationScale p₀ β lam ^ (-2 : ℝ))
    (C := C₃₈ + (max Cc 1 * (Cε + C0 + 1) * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) +
      4 * Real.exp 2 * (Cε * Cz ^ pBeta p₀ β + CK0 * max Cl' 1 ^ pBeta p₀ β) *
        Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) + C20 + 1) + Knorm + 1)
    hχ hβ hlam (by linarith) hε₀ (by linarith) hb1 (fun V => hbb V lam M ε₀ hlam)
    (h38l lam hlam hl38') ht' rfl hKnorm.le
    (LowerBoundLDP.rpow_neg_two_truncationScale_le_errorRate hβ hlam hlam1.le)
    ((hnorml lam hlam hlnorm').mono fun N hN => (abs_le.mp hN).2) hgood

open scoped Classical in
/-- **Proposition 5.43** (the large deviations upper bound), internal form (see the module docstring). The conclusion is the
statement of the frozen statement `MultipoleBKT.proposition_5_43` after its binders
`χ, hχ, p₀, hp₀, β, hβ`. -/
theorem proposition_5_43_upper {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    {β : ℝ} (hβ : 2 < β) :
    let p := pBeta p₀ β
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    ∀ msf : ℝ → ℕ → ℝ, ∀ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) →
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X)))) →
      ∀ t : ℝ, 1 ≤ t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex p x, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N →
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                  {c | ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
                ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
                    fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c))
                ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                    + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                    - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                    + C * N * errorRate p₀ β lam)) := by
  intro p
  have hpS : ((pBeta p₀ β : ℕ) : ℕ∞) ≤ pStar β := TheoremTwo.pBeta_le_pStar hp₀ hβ
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨L₀, hL₀, hb1⟩ := exists_energyLowerBound hχ
  obtain ⟨Cbb, hCbb, hbb⟩ := lintegral_badWeightZ_le hχ p₀ hβ0
  obtain ⟨M20, -, h20M⟩ := AbsoluteUpper.prop_5_20_of_simplified χ hχ p₀ hp₀ β hβ (β * L₀)
    (SimplifiedUpper.simplifiedBoundUpper_holds hχ hp₀ hβ (β * L₀))
    (AbsoluteLower.absoluteConvergenceTransfer hχ hp₀ hβ)
  obtain ⟨M19, -, h19M⟩ := prop_5_19_uniform hχ hβ hp₀ (β * L₀)
  obtain ⟨MK0, -, hK0M⟩ := K_diff0_uniform (χ := χ) hχ hβ hp₀
  obtain ⟨P1, P2, -⟩ := MultipoleBKT.proposition_4_23 χ hχ β hβ
  -- the thresholds of (4.38)–(4.40) for the finitely many sizes `k ≤ p`
  have E1 : ∀ᶠ M in atTop, ∀ k ∈ Finset.Icc 2 (pBeta p₀ β), TheoremTwo.MsfGateAt χ β M k :=
    (Filter.eventually_all_finset _).mpr fun k hk => by
      obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hk
      obtain ⟨M₀, -, hM₀⟩ := P1 k hk2 (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)
      exact eventually_atTop.mpr ⟨M₀, hM₀⟩
  have E2 : ∀ᶠ M in atTop, ∀ k ∈ Finset.range (pBeta p₀ β + 1),
      TheoremTwo.KmultGateAt χ β M k :=
    (Filter.eventually_all_finset _).mpr fun k hk => by
      have hkp : k ≤ pBeta p₀ β := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      obtain ⟨M₀, -, hM₀⟩ := P2 k (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)
      exact eventually_atTop.mpr ⟨M₀, hM₀⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (E1.and (E2.and ((eventually_ge_atTop M20).and
    ((eventually_ge_atTop M19).and ((eventually_ge_atTop MK0).and ((eventually_ge_atTop 21).and
      (eventually_ge_atTop ((3 : ℝ) ^ pBeta p₀ β))))))))
  refine ⟨max M₀ 21, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    fun M hM msf kmult hS hX t ht => ?_⟩
  obtain ⟨hG1, hG2, hM20, hM19, hMK0, hM21, hMp⟩ := hM₀ M ((le_max_left _ _).trans hM)
  have hM20' : 20 < M := by linarith
  -- the constants at `M`, not depending on `ε₀`
  obtain ⟨Cc, hCc, lc, hlc, -, hcoef⟩ := TheoremTwo.coefficient_bounds_uniform hχ hβ hpS hG1
    (fun k hk => hG2 k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))) hS hX
  obtain ⟨CM, hCM, h19ε⟩ := h19M M hM19 hMp
  obtain ⟨Cz, hCz, hzε⟩ := zero_lower_uniform hχ hβ hp₀ hM20'
  obtain ⟨Cl', hCl', ll, hll, -, hlow'⟩ := TheoremTwo.msf_lower_uniform (M := M) hχ hG1
  have hKV : 0 ≤ max Cc 1 * CM * pBeta p₀ β +
      4 * Real.exp 2 * (CM * Cz ^ pBeta p₀ β) * Real.exp (pBeta p₀ β) := by
    have : 0 ≤ Cz := by linarith
    positivity
  have ht'1 : 1 ≤ t + β * L₀ + β * Cbb + (max Cc 1 * CM * pBeta p₀ β +
      4 * Real.exp 2 * (CM * Cz ^ pBeta p₀ β) * Real.exp (pBeta p₀ β)) + 1 := by
    have h1 : 0 ≤ β * L₀ := mul_nonneg hβ0 hL₀.le
    have h2 : 0 ≤ β * Cbb := mul_nonneg hβ0 hCbb.le
    linarith
  -- `ε₁`: Propositions 5.38 (at `t'`) and 5.20
  obtain ⟨ε38, hε38, hε38', h38ε⟩ := bad_points_bound hχ hp₀ hβ (M := M) (by linarith) _ ht'1
  obtain ⟨ε20, hε20, -, h20ε⟩ := h20M M hM20
  refine ⟨min ε38 ε20, lt_min hε38 hε20, (min_le_left _ _).trans hε38',
    fun ε₀ hε₀ hε₀lt => ?_⟩
  have hε₀38 : ε₀ < ε38 := hε₀lt.trans_le (min_le_left _ _)
  have hε₀1 : ε₀ < 1 := hε₀38.trans_le hε38'
  obtain ⟨C20, hC20, l20, hl20, -, h20l⟩ := h20ε ε₀ hε₀ (hε₀lt.trans_le (min_le_right _ _))
  exact bound_at_eps_upper hχ hp₀ hβ hM20' hMp hε₀ hε₀1 ht hS hX hb1 hbb hCc hlc hcoef hCM
    (h19ε ε₀ hε₀ hε₀1) hCz (hzε ε₀ hε₀ hε₀1) hCl' hll hlow' rfl (h38ε ε₀ hε₀ hε₀38)
    ⟨C20, hC20, l20, hl20, fun lam hlam hlt => by
      obtain ⟨N₀, hN₀⟩ := h20l lam hlam hlt
      exact ⟨N₀, fun N hN V Z hVZ π hπ hπV hπp hprof =>
        (hN₀ N hN V Z hVZ π hπ hπV hπp hprof).2.1⟩⟩
    (hK0M M hMK0 ε₀ hε₀ hε₀1)

end UpperBoundLDP

end MultipoleBKT

end
