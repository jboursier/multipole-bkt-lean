/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.AtLambda
public import MultipoleBKT.LowerBound.LowerBoundLDP.Singleton
public import MultipoleBKT.LowerBound.ExpansionErrors.KDiff
public import MultipoleBKT.Frozen.Proposition423

/-!
# Proposition 4.62 from Proposition 4.27 and Lemma A.7

**Proposition 4.62** (large deviations lower bound),
as the internal conditional theorem `MultipoleBKT.LowerBoundLDP.proposition_4_62_of_inputs`. Its only hypotheses are the
statements of the two inputs (`MultipoleBKT.LowerBoundLDP.Inputs`): Proposition 4.27 in the
paper's form (`Prop427Statement`) and the two estimates of Lemma A.7 (`LemmaA8Inputs`), for one
damping constant `L ≥ β/64` of (3.53). Both are proved
(`MultipoleBKT.AbsoluteLower.prop427Statement_holds`,
`MultipoleBKT.ExpansionK.lemmaA8Inputs_holds`) and are supplied to this theorem by the provider of
the frozen statement (`MultipoleBKT.LowerBound.Proposition462`). Its conclusion is the type of
the frozen statement `MultipoleBKT.proposition_4_62` after the binders `χ, hχ, p₀, hp₀, β, hβ`.

The constants are chosen in the order of the frozen statement:

* `M₀`: the thresholds of Proposition 4.27, of Lemma A.7, of (4.38)–(4.40) (Proposition 4.23) for the sizes `k ≤ p`, of (4.44) (Proposition 4.24) for `2 ≤ k ≤ p`, and `21`;
* `ε₁ = min(ε₁(4.27), 1)`;
* `C = a₁ + a₂ + a₃ + C₂₇ + 1` and `λ₀` (`bound_at_eps`), from the uniform constants of
  (2.47)–(2.48), (4.38), the singleton display after (4.142), (4.42) for sizes at least
  two, (4.44), (4.11), Proposition 4.27 at `ε₀`, Lemma 4.53, and
  the smallness of `R̄^{-2}` against `λ^{2(p-1)}`;
* `N₀(λ)`: `MultipoleBKT.LowerBoundLDP.bound_at_lambda`.

The absolute summability of the rate series on `Δ_{p,0}` is
`MultipoleBKT.rateSeries_summable_and_bound`.
-/

@[expose] public section

open MeasureTheory Finset Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace LowerBoundLDP

open Hierarchical PropFiveFortyFive

/-! ### Elementary smallness conditions -/

/-- `c λ² ≤ 1/2` for `0 < λ ≤ min(1, 1/(2c + 2))`. -/
theorem mul_sq_le_half {c lam : ℝ} (hc : 0 ≤ c) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (h : lam ≤ 1 / (2 * c + 2)) : c * lam ^ 2 ≤ 1 / 2 := by
  have h1 : lam ^ 2 ≤ lam := by nlinarith
  have h2 : c * lam ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hc]

/-- `a R ≤ x/2` when `R ≤ η x` and `η ≤ 1/(2(a + 1))`. -/
theorem mul_le_half_of_le_mul {a R x η : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hη0 : 0 ≤ η)
    (hRη : R ≤ η * x) (hη : η ≤ 1 / (2 * (a + 1))) : a * R ≤ x / 2 := by
  have h1 : a * R ≤ a * (η * x) := mul_le_mul_of_nonneg_left hRη ha
  have h2 : a * η ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hη
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hx]

/-- `b R ≤ Z/2` when `R ≤ η x`, `0 ≤ x ≤ 1` and `η ≤ Z/(2(b + 1))`. -/
theorem mul_le_half_of_le_mul' {b R x η Z : ℝ} (hb : 0 ≤ b) (hx1 : x ≤ 1)
    (hη0 : 0 ≤ η) (hRη : R ≤ η * x) (hη : η ≤ Z / (2 * (b + 1))) :
    b * R ≤ Z / 2 := by
  have h1 : b * R ≤ b * η := by
    refine mul_le_mul_of_nonneg_left (hRη.trans ?_) hb
    exact mul_le_of_le_one_right hη0 hx1
  have h2 : b * η ≤ Z / 2 := by
    rw [le_div_iff₀ (by positivity)] at hη
    nlinarith
  linarith

/-! ### Proposition 4.62 at fixed `M` and `ε₀` -/

open scoped Classical in
/-- **Proposition 4.62 at fixed `M` and `ε₀`** (internal): from (4.38)–(4.40) (`hG1`, `hG2`),
(4.44) for `2 ≤ k ≤ p` (`hKd`), Proposition 4.27 at `ε₀` (`h27`) and the limits (2.45)–(2.46),
there are `C > 0` and `λ₀ ∈ (0, 1]` such that for `λ ∈ (0, λ₀)` the rate series converges
absolutely on `Δ_{p,0}` and (4.141) holds for `N ≥ N₀(λ)`, uniformly in the profile.
The singleton error uses `singleton_damping_bound`, with its coefficient quantified before
`M`. Proposition 4.24 is used only for block sizes at least two, as in
the display after (4.142) in Step 1 of the proof of Proposition 4.62. -/
theorem bound_at_eps {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ}
    (hβ : 2 < β) {L M ε₀ : ℝ} (hL : β / 64 ≤ L) (hM : 20 < M) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    {msf : ℝ → ℕ → ℝ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}
    (hS : TheoremTwo.MsfLimits χ β M msf) (hX : TheoremTwo.KmultLimits χ β M kmult)
    (hG1 : ∀ k ∈ Finset.Icc 2 (pBeta p₀ β), TheoremTwo.MsfGateAt χ β M k)
    (hG2 : ∀ k, k ≤ pBeta p₀ β → TheoremTwo.KmultGateAt χ β M k)
    (hKd : ∀ k ∈ Finset.Icc 2 (pBeta p₀ β), ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)))
    (h27 : ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ π ∈ boundedBlockPartitions N (pBeta p₀ β),
          (∀ k : ℕ, 2 ≤ k → k ≤ pBeta p₀ β →
            ((π.filter fun S => S.card = k).card : ℝ) ≤
              ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1))) →
          (∑ X ∈ π.powerset.filter (fun X => pBeta p₀ β < (X.biUnion id).card),
              |minusActivity χ N p₀ β lam M ε₀ L X| ≤ C * N * errorRate p₀ β lam) ∧
          (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
            ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
                (fun X => (connectionGraph X).Connected),
              |(∏ i, minusActivity χ N p₀ β lam M ε₀ L (X i)) *
                (ursell (connectionGraph X) : ℝ)|) ∧
          ∑' n : ℕ, 1 / (n.factorial : ℝ) *
            ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
                (fun X => (connectionGraph X).Connected ∧
                  ∃ i, pBeta p₀ β < ((X i).biUnion id).card),
              |(∏ i, minusActivity χ N p₀ β lam M ε₀ L (X i)) *
                (ursell (connectionGraph X) : ℝ)| ≤ C * N * errorRate p₀ β lam) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        (∀ γ ∈ simplex (pBeta p₀ β) 0, Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
          ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin (pBeta p₀ β) → ℕ,
          ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i = N →
          (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
            (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
          ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
              + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
              - N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
              - C * N * errorRate p₀ β lam))
            ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                {c | (∀ i : Fin (pBeta p₀ β), multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
                  ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
                    ε₀ * truncationScale p₀ β lam},
              ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  have hp1 : 1 ≤ pBeta p₀ β := TheoremTwo.one_le_pBeta' hp₀ hβ
  have hpS : ((pBeta p₀ β : ℕ) : ℕ∞) ≤ pStar β := TheoremTwo.pBeta_le_pStar hp₀ hβ
  have hM1 : 1 ≤ M := by linarith
  have hZ : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  -- The singleton coefficient is chosen without the separation parameter `M`.
  obtain ⟨CS, hCS, lS, hlS, -, hsingleton⟩ := singleton_damping_bound hχ hβ p₀ hε₀
    (show 0 ≤ L by linarith only [hL, hβ])
  -- the coefficient bounds (2.47)–(2.48) and the rate function
  obtain ⟨Cc, hCc, lc, hlc, -, hcoef⟩ :=
    TheoremTwo.coefficient_bounds_uniform hχ hβ hpS hG1 hG2 hS hX
  obtain ⟨lr, hlr, -, C'', -, hrate⟩ := TheoremTwo.exists_rateSetup hp1 hCc
  obtain ⟨lrs, hlrs, Crs, -, hrs⟩ := rateSeries_summable_and_bound (pBeta p₀ β) Cc
  obtain ⟨Ct₂, hCt₂, hlogpoly⟩ := exists_log_polymerSum (2 * Cc) (by positivity) (pBeta p₀ β)
  -- (4.38)
  obtain ⟨Cl', hCl', ll, hll, -, hlow'⟩ := TheoremTwo.msf_lower_uniform (M := M) hχ hG1
  set Clow := max Cl' 1 with hClow_def
  have hClow : 1 ≤ Clow := le_max_right _ _
  -- Direct singleton damping and (4.42) for sizes at least two, uniformly in the size
  obtain ⟨CM, hCM, lM, hlM, hMd⟩ := ExpansionErrors.exists_uniform
    (fun s C lam N => 0 < lam → ∀ S : Finset ℕ, S.card = s →
      |minusPartitionFunction χ N p₀ β lam M ε₀ L {S} - multipolePartitionFunction χ N β lam M S| ≤
        C / (N : ℝ) ^ (s - 1) * truncationScale p₀ β lam ^ (-2 : ℝ))
    (fun s C C' lam N hCC' h hlam S hS => (h hlam S hS).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hCC' (by positivity))
      (Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _)))
    (pBeta p₀ β) fun s hs1 hsp => by
      rcases Nat.eq_or_lt_of_le hs1 with hs | hs
      · subst s
        refine ⟨CS, hCS, lS, hlS, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := hsingleton lam hlam hlt
        refine ⟨max N₀ 1, fun N hN _ S hS => ?_⟩
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
        have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
        obtain ⟨h0, hd⟩ := hN₀ N ((le_max_left _ _).trans hN) M i
        rw [multipolePartitionFunction_singleton hχ hlam β M hN1 i,
          abs_sub_comm, abs_of_nonneg h0]
        simpa only [Nat.sub_self, pow_zero, div_one] using hd
      · obtain ⟨C, hC, l, hl, -, h⟩ := ExpansionErrors.eq_M_diff (M := M) hχ hβ (by omega)
          (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hsp) (by linarith) L p₀ ε₀ hε₀ hε₀1
        refine ⟨C, hC, l, hl, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
        exact ⟨N₀, fun N hN _ S hS => hN₀ N hN S hS⟩
  -- (4.44), uniformly in the size
  obtain ⟨CK, hCK, lK, hlK, hKdU⟩ := ExpansionErrors.exists_uniform
    (fun s C lam N => 0 < lam → ∀ X : Finset (Finset ℕ), IsSubpartition X →
      X.biUnion id ⊆ Finset.range N → 1 < X.card → (X.biUnion id).card = s →
        |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
          C * truncationScale p₀ β lam ^ (-2 : ℝ) /
            ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (s - 1)))
    (fun s C C' lam N hCC' h hlam X hX hXN h1 hs => (h hlam X hX hXN h1 hs).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC'
        (Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _))
        (mul_nonneg (prod_nonneg fun S _ => multipolePartitionFunction_nonneg χ N β lam M S)
          (by positivity))))
    (pBeta p₀ β) fun s hs1 hsp => by
      rcases Nat.lt_or_ge s 2 with hs2 | hs2
      · refine ⟨1, one_pos, 1, one_pos, fun lam _ _ => ⟨0, fun N _ _ X hX _ h1 hs => ?_⟩⟩
        have := PropFiveFortyFive.card_le_card_biUnion hX
        omega
      · obtain ⟨C, hC, l, hl, -, h⟩ := hKd s (Finset.mem_Icc.mpr ⟨hs2, hsp⟩) ε₀ hε₀ hε₀1
        refine ⟨C, hC, l, hl, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
        exact ⟨N₀, fun N hN _ X hX hXN h1 hs => hN₀ N hN X hX hXN h1 hs⟩
  -- (4.11)
  obtain ⟨CZ, hCZ, hnorm⟩ := lem411_devtCbeta_eventually hχ hβ
  -- Proposition 4.27 at `ε₀`
  obtain ⟨C₂₇, hC₂₇, l27, hl27, h27l⟩ := h27
  -- Lemma 4.53 for the cluster sum
  have hC₀ : 0 ≤ 2 * Cc + CK * Clow ^ pBeta p₀ β := by positivity
  obtain ⟨Ct₁, hCt₁, hlogD⟩ := exists_log_disjointSum_ge _ hC₀ (pBeta p₀ β)
  -- the smallness of `R̄^{-2}`
  have hη : 0 < min (1 / (2 * (CM * Clow + 1)))
      (min 1 (dipoleConstant χ β / (2 * (CZ * (ε₀ ^ 2)⁻¹ + 1)))) := by
    refine lt_min (by positivity) (lt_min one_pos (by positivity))
  obtain ⟨lη, hlη, -, hRη⟩ := exists_rpow_neg_two_truncationScale_le hp₀ hβ hη
  have hE : 0 ≤ Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (2 * Cc + CK * Clow ^ pBeta p₀ β)))) :=
    by positivity
  refine ⟨2 * (CZ * (ε₀ ^ 2)⁻¹) / dipoleConstant χ β +
      2 * CM * Clow * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) +
      4 * Real.exp 2 * (CK * Clow ^ pBeta p₀ β) *
        Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) + C₂₇ + 1, ?_,
    min (min (min lc lr) (min lrs ll)) (min (min lM lK) (min (min l27 lη)
      (min (min (ε₀ / 2) (1 / 2)) (min (1 / (2 * Ct₁ + 2)) (min (1 / (2 * Ct₂ + 2))
        (1 / (2 * (Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β *
          (2 * (2 * Cc + CK * Clow ^ pBeta p₀ β))))) + 2))))))), ?_, ?_, fun lam hlam hlaml => ?_⟩
  · have hA : 0 ≤ ε₀ ^ (-alphaExponent β) := Real.rpow_nonneg hε₀.le _
    positivity
  · simp only [lt_min_iff]
    refine ⟨⟨⟨hlc, hlr⟩, hlrs, hll⟩, ⟨hlM, hlK⟩, ⟨hl27, hlη⟩, ⟨by linarith, by norm_num⟩,
      by positivity, by positivity, by positivity⟩
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num)))))
  simp only [lt_min_iff] at hlaml
  obtain ⟨⟨⟨hlc', hlr'⟩, hlrs', hll'⟩, ⟨hlM', hlK'⟩, ⟨hl27', hlη'⟩, ⟨hlε', hlh'⟩, hlt₁, hlt₂,
    hlt₃⟩ := hlaml
  have hlam1 : lam < 1 := hlh'.trans (by norm_num)
  obtain ⟨hMB, hKB⟩ := hcoef lam hlam hlc'
  have hset := (hrate lam hlam hlr' (msf lam) (kmult lam) hMB hKB).1
  refine ⟨fun γ hγ => (hrs lam hlam hlrs' (kmult lam) hKB γ fun i => ?_).1, ?_⟩
  · have h := hγ.1 i
    rw [abs_le]
    constructor <;> linarith [h.1, h.2]
  -- the polymer gas
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
  have hCt₂l : Ct₂ * lam ^ 2 ≤ 1 / 2 := mul_sq_le_half hCt₂.le hlam hlam1.le hlt₂.le
  have hΞ := hlogpoly (kmult lam) Cc lam (fun N => multipoleActivity χ N β lam M) hlam hlam1.le
    hCt₂l hKB hset.hsmall hKinv hKlim hact
  -- (4.38) with `C' = max C 1`
  have hlowC : ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Finset.range N → 1 ≤ S.card →
      S.card ≤ pBeta p₀ β →
        lam ^ (2 * (S.card - 1)) / (Clow * (N : ℝ) ^ (S.card - 1)) ≤
          multipolePartitionFunction χ N β lam M S := by
    filter_upwards [hlow' lam hlam hll', eventually_ge_atTop 1] with N hN hN1 S hS h1 hp
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    refine le_trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) (hN S hS h1 hp)
  -- the smallness conditions
  have hR := hRη lam hlam hlη'
  have hx0 : 0 ≤ (lam ^ 2) ^ (pBeta p₀ β - 1) := by positivity
  have hx1 : (lam ^ 2) ^ (pBeta p₀ β - 1) ≤ 1 := pow_le_one₀ (by positivity)
    (pow_le_one₀ hlam.le hlam1.le)
  have hR1 : CM * Clow * truncationScale p₀ β lam ^ (-2 : ℝ) ≤ (lam ^ 2) ^ (pBeta p₀ β - 1) / 2 :=
    mul_le_half_of_le_mul (by positivity) hx0 hη.le hR (min_le_left _ _)
  have hR2 : truncationScale p₀ β lam ^ (-2 : ℝ) ≤ (lam ^ 2) ^ (pBeta p₀ β - 1) :=
    hR.trans (mul_le_of_le_one_left hx0 ((min_le_right _ _).trans (min_le_left _ _)))
  have hR3 : CZ * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ ≤ dipoleConstant χ β / 2 := by
    rw [inv_sq_mul_truncationScale hlam, ← mul_assoc]
    exact mul_le_half_of_le_mul' (by positivity) hx1 hη.le hR
      ((min_le_right _ _).trans (min_le_right _ _))
  have hsmallD : Real.exp 2 * (pBeta p₀ β *
      (pBeta p₀ β * (2 * (2 * Cc + CK * Clow ^ pBeta p₀ β)) * lam ^ 2)) ≤ 1 / 2 := by
    have h := mul_sq_le_half hE hlam hlam1.le hlt₃.le
    calc Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (2 * Cc + CK * Clow ^ pBeta p₀ β)) *
          lam ^ 2))
        = Real.exp 2 * (pBeta p₀ β * (pBeta p₀ β * (2 * (2 * Cc + CK * Clow ^ pBeta p₀ β)))) *
            lam ^ 2 := by ring
      _ ≤ 1 / 2 := h
  exact bound_at_lambda hχ hp₀ hβ hL hM1 hε₀ hlam hlam1 hlε'.le (hS lam hlam hlam1)
    (hX lam hlam hlam1) hset hΞ hCM.le
    (by
      obtain ⟨N₀, hN₀⟩ := hMd lam hlam hlM'
      exact ⟨N₀, fun N hN s hs1 hsp S hS => hN₀ N hN s hs1 hsp hlam S hS⟩)
    hCK.le
    (by
      obtain ⟨N₀, hN₀⟩ := hKdU lam hlam hlK'
      exact ⟨N₀, fun N hN s hs1 hsp X hX' hXN h1 hs => hN₀ N hN s hs1 hsp hlam X hX' hXN h1 hs⟩)
    hClow hlowC hCZ.le (hnorm p₀ ε₀ lam hε₀ hε₀1 hlam hlam1) (h27l lam hlam hl27') hlogD
    (mul_sq_le_half hCt₁.le hlam hlam1.le hlt₁.le) hsmallD hR1 hR2 hR3 rfl

/-! ### Proposition 4.62 -/

open scoped Classical in
/-- **Proposition 4.62** (Proposition 4.62, large deviations lower bound, Corollary 4.61;
proof of Corollary 4.61), conditional on the statements of Proposition 4.27 (`Prop427Statement`) and
Lemma A.7 (`LemmaA8Inputs`) for a damping constant `L ≥ β/64` of (3.53) (internal helper; see
the module docstring). The conclusion is the statement of the frozen statement
`MultipoleBKT.proposition_4_62` after its binders `χ, hχ, p₀, hp₀, β, hβ`. -/
theorem proposition_4_62_of_inputs {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    {β : ℝ} (hβ : 2 < β) (L : ℝ) (hL : β / 64 ≤ L) (h427 : Prop427Statement χ p₀ β L)
    (hA8 : LemmaA8Inputs χ p₀ β L) :
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
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            (∀ γ ∈ simplex p 0, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i = N →
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                  + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
                  - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                  - C * N * errorRate p₀ β lam))
                ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                    {c | (∀ i : Fin p, multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
                      ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
                        ε₀ * truncationScale p₀ β lam},
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  intro p
  obtain ⟨M₂₇, h27M⟩ := h427
  obtain ⟨MA8, hA8M⟩ := hA8
  obtain ⟨P1, P2, -⟩ := MultipoleBKT.proposition_4_23 χ hχ β hβ
  -- the thresholds of (4.38)–(4.40) and (4.44) for the finitely many sizes `k ≤ p`
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
  have E3 : ∀ᶠ M in atTop, ∀ k ∈ Finset.Icc 2 (pBeta p₀ β),
      ExpansionErrors.LemmaA8MinusStatement χ β M L p₀ k →
      ExpansionErrors.LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) :=
    (Filter.eventually_all_finset _).mpr fun k hk => by
      obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hk
      obtain ⟨M₀, -, hM₀⟩ := ExpansionErrors.eq_K_diff_of_lemma_A8 hχ hβ hk2
        (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp) L p₀
      exact eventually_atTop.mpr ⟨M₀, hM₀⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (E1.and (E2.and (E3.and ((eventually_ge_atTop M₂₇).and
    ((eventually_ge_atTop MA8).and (eventually_ge_atTop 21))))))
  refine ⟨max M₀ 21, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    fun M hM msf kmult hS hX => ?_⟩
  obtain ⟨hG1, hG2, hE3, hM27, hMA8, hM21⟩ := hM₀ M ((le_max_left _ _).trans hM)
  obtain ⟨ε₁, hε₁, hε₁'⟩ := h27M M hM27
  refine ⟨min ε₁ 1, lt_min hε₁ one_pos, min_le_right _ _, fun ε₀ hε₀ hε₀lt => ?_⟩
  have hε₀1 : ε₀ < 1 := hε₀lt.trans_le (min_le_right _ _)
  exact bound_at_eps hχ hp₀ hβ hL (by linarith) hε₀ hε₀1 hS hX hG1
    (fun k hk => hG2 k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    (fun k hk => hE3 k hk (hA8M M hMA8 k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2).1
      (hA8M M hMA8 k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2).2)
    (hε₁' ε₀ hε₀ (hε₀lt.trans_le (min_le_left _ _)))

end LowerBoundLDP

end MultipoleBKT

end
