/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.Core
public import MultipoleBKT.LowerBound.LowerBoundLDP.Estimates
public import MultipoleBKT.LowerBound.LowerBoundLDP.Scales
public import MultipoleBKT.Main.PropFiveFortyFive.Final

/-!
# Proposition 4.62 at a fixed small `λ`

The proof of Proposition 4.62 at fixed `M`, `ε₀` and `λ`: from
the bounds of Propositions 4.23, 4.24 and 4.27, the limits (2.45)–(2.46) of Lemma 4.26 and the smallness of `λ`, all taken as hypotheses with their
constants, there is `N₀` (uniform in the profile) such that for `N ≥ N₀` and every
profile `n` with `n_1 + 2n_2 + ⋯ + p n_p = N` satisfying (4.22),

  `e^{N log N + log N! + (2-β) N log λ + N log 𝒵_β - N ℐ(γ) - C N δ} ≤ ∫_𝒜 e^{-βF_λ}`

with `C = a₁ + a₂ + a₃ + C₂₇ + 1` (`bound_at_lambda`): `a₁` from (4.11), `a₂` from (4.143),
`a₃` from the replacement of `𝖪^-_{ε₀}` by `𝖪^mult` (`D ≤ C N R̄^{-2}`), `C₂₇` from (4.55) and `1`
for the `o(N)` errors of Stirling's formula and of the hypertree limit in Step 3 of the proof of Proposition 4.62, absorbed in
`N δ_{β,λ}` for `N` large at fixed `λ` (Section 4.20). The rest of the proof only chooses the
constants (`MultipoleBKT.LowerBoundLDP.proposition_4_62_of_inputs`).
-/

@[expose] public section

open MeasureTheory Finset Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace LowerBoundLDP

open Hierarchical PropFiveFortyFive

/-- The assumption (4.22) on a profile, in the frozen form (`n i = n_{i+1}`), gives the form
(4.22) on the block counts of a partition of that profile. -/
theorem blockCount_le_of_profile {N p : ℕ} {n : Fin p → ℕ} {π : Finset (Finset ℕ)}
    (hbc : blockCount p π = n) {A lam : ℝ}
    (h420 : ∀ i : Fin p, 1 ≤ (i : ℕ) → (n i : ℝ) ≤ A * lam ^ (2 * (i : ℕ)) * N) :
    ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ((π.filter fun S => S.card = k).card : ℝ) ≤ A * N * lam ^ (2 * (k - 1)) := by
  intro k hk2 hkp
  have h := h420 ⟨k - 1, by omega⟩ (by simp only; omega)
  have hb : n ⟨k - 1, by omega⟩ = (π.filter fun S => S.card = k).card := by
    rw [← hbc]
    unfold blockCount
    simp only
    congr 2
    ext S
    constructor <;> intro hS <;> omega
  rw [hb] at h
  simp only at h
  linarith [show A * lam ^ (2 * (k - 1)) * N = A * N * lam ^ (2 * (k - 1)) by ring]

open scoped Classical in
/-- **Proposition 4.62 at a fixed `λ`** (internal; see the module docstring). The hypotheses are,
in order: the parameters; the limits (2.45)–(2.46) at `λ`; the coefficient bounds (2.47)–(2.48)
(`TheoremTwo.RateSetup`); the logarithm of the polymer gas (`hΞ`, from the hypertree limit);
the direct singleton damping estimate (4.142), combined in `hMdiff` with
(4.42) of Proposition 4.24 for sizes `2, …, p`, (4.44), (4.38) of
Proposition 4.23; (4.11) of Lemma 4.12; Proposition 4.27 at `λ`; the cluster-sum estimate
`DisjointSumLogBound`; and the smallness of `λ` and of `R̄^{-2}`. -/
theorem bound_at_lambda {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ}
    (hβ : 2 < β) {L M ε₀ lam : ℝ} (hL : β / 64 ≤ L) (hM : 1 ≤ M) (hε₀ : 0 < ε₀)
    (hlam : 0 < lam) (hlam1 : lam < 1) (hlamε : lam ≤ ε₀ / 2)
    {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {Ccoef CM CK Clow CZ C₂₇ Ct₁ C : ℝ}
    (hS : ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ =>
          (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
        (𝓝 (msf S.card)))
    (hX : ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ =>
          (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
        (𝓝 (kmult (blockProfile X))))
    (hset : TheoremTwo.RateSetup (pBeta p₀ β) msf kmult Ccoef lam)
    (hΞ : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π ∈ boundedBlockPartitions N (pBeta p₀ β),
      0 < polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π ∧
        |Real.log (polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π) +
          N * rateCluster (pBeta p₀ β) kmult (profileVec (pBeta p₀ β) N π)| ≤ ε * N)
    (hCM : 0 ≤ CM)
    (hMdiff : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
      ∀ S : Finset ℕ, S.card = s →
        |minusPartitionFunction χ N p₀ β lam M ε₀ L {S} -
            multipolePartitionFunction χ N β lam M S| ≤
          CM / (N : ℝ) ^ (s - 1) * truncationScale p₀ β lam ^ (-2 : ℝ))
    (hCK : 0 ≤ CK)
    (hKdiff : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
        1 < X.card → (X.biUnion id).card = s →
        |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
          CK * truncationScale p₀ β lam ^ (-2 : ℝ) /
            ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (s - 1)))
    (hClow : 1 ≤ Clow)
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Finset.range N → 1 ≤ S.card →
      S.card ≤ pBeta p₀ β →
        lam ^ (2 * (S.card - 1)) / (Clow * (N : ℝ) ^ (S.card - 1)) ≤
          multipolePartitionFunction χ N β lam M S)
    (hCZ : 0 ≤ CZ)
    (hnorm : ∀ᶠ N : ℕ in atTop, |cutoffDipoleNormalization χ N p₀ β lam ε₀ -
        lam ^ (2 - β) * dipoleConstant χ β| ≤
      lam ^ (2 - β) * (CZ * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹))
    (h27 : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ π ∈ boundedBlockPartitions N (pBeta p₀ β),
      (∀ k : ℕ, 2 ≤ k → k ≤ pBeta p₀ β →
        ((π.filter fun S => S.card = k).card : ℝ) ≤
          ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1))) →
      (∑ X ∈ π.powerset.filter (fun X => pBeta p₀ β < (X.biUnion id).card),
          |minusActivity χ N p₀ β lam M ε₀ L X| ≤ C₂₇ * N * errorRate p₀ β lam) ∧
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
            (ursell (connectionGraph X) : ℝ)| ≤ C₂₇ * N * errorRate p₀ β lam)
    (hlogD : DisjointSumLogBound (pBeta p₀ β) (2 * Ccoef + CK * Clow ^ pBeta p₀ β) Ct₁)
    (hCt₁ : Ct₁ * lam ^ 2 ≤ 1 / 2)
    (hsmallD : Real.exp 2 * (pBeta p₀ β *
      (pBeta p₀ β * (2 * (2 * Ccoef + CK * Clow ^ pBeta p₀ β)) * lam ^ 2)) ≤ 1 / 2)
    (hR1 : CM * Clow * truncationScale p₀ β lam ^ (-2 : ℝ) ≤ (lam ^ 2) ^ (pBeta p₀ β - 1) / 2)
    (hR2 : truncationScale p₀ β lam ^ (-2 : ℝ) ≤ (lam ^ 2) ^ (pBeta p₀ β - 1))
    (hR3 : CZ * ((ε₀ * truncationScale p₀ β lam) ^ 2)⁻¹ ≤ dipoleConstant χ β / 2)
    (hC : C = 2 * (CZ * (ε₀ ^ 2)⁻¹) / dipoleConstant χ β +
      2 * CM * Clow * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) +
      4 * Real.exp 2 * (CK * Clow ^ pBeta p₀ β) *
        Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) + C₂₇ + 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin (pBeta p₀ β) → ℕ,
      ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i = N →
      (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
        (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
      ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
          + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
          - N * rateFunction (pBeta p₀ β) msf kmult (fun i => (n i : ℝ) / N)
          - C * N * errorRate p₀ β lam))
        ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
            {c | (∀ i : Fin (pBeta p₀ β), multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
              ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
                ε₀ * truncationScale p₀ β lam},
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  have hp1 : 1 ≤ pBeta p₀ β := TheoremTwo.one_le_pBeta' hp₀ hβ
  have hpS : ((pBeta p₀ β : ℕ) : ℕ∞) ≤ pStar β := TheoremTwo.pBeta_le_pStar hp₀ hβ
  have hR0 : 0 ≤ truncationScale p₀ β lam ^ (-2 : ℝ) :=
    Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _
  have hδ : 0 < errorRate p₀ β lam := TheoremTwo.errorRate_pos hβ hlam
  have hRδ := rpow_neg_two_truncationScale_le_errorRate (p₀ := p₀) hβ hlam hlam1.le
  have hA : 0 ≤ ε₀ ^ (-alphaExponent β) := Real.rpow_nonneg hε₀.le _
  have hZ : 0 < dipoleConstant χ β := dipoleConstant_pos hχ hβ
  have hlamR : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have := BoundedLowerEps.two_mul_le_cutoff hβ hlam hlam1.le hε₀ hlamε p₀
    linarith
  -- the activity bound on `𝖪^mult` and the profile asymptotics
  have hact := eventually_abs_multipoleActivity_le hχ hpS hlam hset.hC hset.hk hX
  have hmsf : ∀ k ∈ Icc 1 (pBeta p₀ β), 0 < msf k := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := mem_Icc.1 hk
    rcases Nat.lt_or_ge k 2 with h | h
    · rw [show k = 1 by omega, hset.hmsf.1]
      exact one_pos
    · have h1 := (hset.hmsf.2 k h hkp).1
      have hpos : 0 < Ccoef⁻¹ * lam ^ (2 * (k - 1)) := by
        have := hset.hC
        positivity
      linarith
  have hMf : ∀ k ∈ Icc 1 (pBeta p₀ β), Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) *
      multipolePartitionFunction χ N β lam M (Finset.range k)) atTop (𝓝 (msf k)) := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := mem_Icc.1 hk
    have h := hS (Finset.range k) (by rw [card_range]; exact hk1)
      (by rw [card_range]; exact (Nat.cast_le.2 hkp).trans hpS)
    rw [card_range] at h
    exact h
  have hcount := eventually_abs_log_count_mul_le (p := pBeta p₀ β) (kmult := kmult)
    (Mf := fun N k => multipolePartitionFunction χ N β lam M (Finset.range k)) hmsf hMf
    (Ξ := fun N π => polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π) hΞ
    (errorRate p₀ β lam) hδ
  obtain ⟨N₁, hN₁⟩ := hMdiff
  obtain ⟨N₂, hN₂⟩ := hKdiff
  obtain ⟨N₃, hN₃⟩ := h27
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp
    (hact.and (hcount.and (hlow.and (hnorm.and (eventually_ge_atTop 1)))))
  refine ⟨max (max N₁ N₂) (max N₃ N₄), fun N hN n hn h420 => ?_⟩
  have hN₁N : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂N : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN₃N : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN₄N : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hactN, hcountN, hlowN, hnormN, hN1⟩ := hN₄ N hN₄N
  -- a partition of the profile
  obtain ⟨π, hπ⟩ := profilePartitions_nonempty hn
  obtain ⟨hπb, hbc⟩ := mem_profilePartitions_iff.mp hπ
  obtain ⟨hπP, -, -, hπ1⟩ := facts_of_mem_boundedBlockPartitions hN1 hπb
  have hπN : π.biUnion id = Finset.range N := biUnion_of_mem_boundedBlockPartitions hπb
  have hn' := blockCount_le_of_profile hbc h420
  -- the normalization (4.11)
  obtain ⟨hCpos, hlogC⟩ := log_ge_of_abs_sub_le hlam hZ (by positivity) hR3 hnormN
  rw [inv_sq_mul_truncationScale hlam] at hlogC
  have e : 2 * (CZ * ((ε₀ ^ 2)⁻¹ * truncationScale p₀ β lam ^ (-2 : ℝ))) / dipoleConstant χ β =
      2 * (CZ * (ε₀ ^ 2)⁻¹) / dipoleConstant χ β * truncationScale p₀ β lam ^ (-2 : ℝ) := by ring
  rw [e] at hlogC
  -- the block partition functions (4.143)
  obtain ⟨hMpos, hMzpos, hlogM⟩ := log_minusPartitionFunction_ge hχ hN1 hπb hlam hlam1.le
    (lt_of_lt_of_le one_pos hClow) hCM hR0 hA hn' (hN₁ N hN₁N) hlowN hR1
  -- the cluster sum (4.145)
  have hXsub : ∀ X ⊆ π, IsSubpartition X ∧ X.biUnion id ⊆ Finset.range N := fun X hX =>
    ⟨SetPartition.isSubpartition_mono hπP hX, hπN ▸ biUnion_subset_biUnion_of_subset_left _ hX⟩
  have hdiffX : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |minusActivity χ N p₀ β lam M ε₀ L X - multipoleActivity χ N β lam M X| ≤
        CK * Clow ^ pBeta p₀ β * truncationScale p₀ β lam ^ (-2 : ℝ) *
          (N * ∏ S ∈ X, blockWeight lam N S) := by
    intro X hX hr
    obtain ⟨hXP, hXN⟩ := hXsub X hX
    have hX1 : 1 ≤ X.card := by have := hr.1; omega
    have hs1 : 1 ≤ (X.biUnion id).card := hX1.trans (PropFiveFortyFive.card_le_card_biUnion hXP)
    have hd := hN₂ N hN₂N _ hs1 hr.2 X hXP hXN (by have := hr.1; omega) rfl
    rw [zeroActivityInf_eq_multipoleActivity hχ hlam β hN1 hM hXP] at hd
    refine abs_sub_le_of_kdiff hXP hX1 (card_le_of_retained hπP hX hr) hlam hN1 hCK hR0 hClow hd
      fun S hS => ?_
    have hSπ : S ∈ π := hX hS
    exact hlowN S (hπN ▸ subset_biUnion_of_mem id hSπ) (hπ1 S hSπ).1 (hπ1 S hSπ).2
  have hb₂ : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |multipoleActivity χ N β lam M X| ≤ (2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1) :=
    fun X hX hr => hactN X (hXsub X hX).1 hr.1 hr.2
  have hC₀ : 0 ≤ CK * Clow ^ pBeta p₀ β := by positivity
  have hb₁ : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |minusActivity χ N p₀ β lam M ε₀ L X| ≤
        (2 * Ccoef + CK * Clow ^ pBeta p₀ β) * (lam ^ 2 / N) ^ (X.card - 1) :=
    fun X hX hr => abs_le_of_abs_sub_le (hXsub X hX).1 hr hlam hlam1.le hN1 hC₀ hR2 (hb₂ X hX hr)
      (hdiffX X hX hr)
  have hb₂' : ∀ X ⊆ π, Retained (pBeta p₀ β) X →
      |multipoleActivity χ N β lam M X| ≤
        (2 * Ccoef + CK * Clow ^ pBeta p₀ β) * (lam ^ 2 / N) ^ (X.card - 1) := by
    intro X hX hr
    refine (hb₂ X hX hr).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hK1 : ∀ X ⊆ π, X.card ≤ 1 → minusActivity χ N p₀ β lam M ε₀ L X = 0 :=
    fun X _ h => modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ h
  obtain ⟨-, habs, hbad⟩ := hN₃ N hN₃N π hπb hn'
  obtain ⟨hΞpos, hPpos, hlogΞ'⟩ := hlogD N π (minusActivity χ N p₀ β lam M ε₀ L)
    (multipoleActivity χ N β lam M) lam (C₂₇ * N * errorRate p₀ β lam) hπb hN1 hlam hlam1.le
    hCt₁ hsmallD hK1 hb₁ hb₂' (by convert habs) (by convert hbad)
  have hD := sum_retained_diff_le hN1 hπb hlam hA hC₀ hR0 hn' hdiffX
  have hlogΞ : Real.log (polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π) -
      (4 * Real.exp 2 * (CK * Clow ^ pBeta p₀ β) *
        Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β)))) *
        truncationScale p₀ β lam ^ (-2 : ℝ) * N - C₂₇ * N * errorRate p₀ β lam ≤
      Real.log (disjointSum (minusActivity χ N p₀ β lam M ε₀ L) π) := by
    have h4 : 0 ≤ 4 * Real.exp 2 := by positivity
    have := mul_le_mul_of_nonneg_left hD h4
    linarith
  -- the profile asymptotics
  obtain ⟨-, hcountπ⟩ := hcountN π hπb
  rw [hbc] at hcountπ
  have hγ : profileVec (pBeta p₀ β) N π = fun i => (n i : ℝ) / N := by
    funext i
    simp only [profileVec, hbc]
  rw [hγ] at hcountπ
  -- the bookkeeping
  rw [hC]
  exact lower_bound_of_estimates hχ hN1 hlam (by linarith) hε₀ hlamR hL hM hπ hCpos hlogC hMpos
    hMzpos hlogM hΞpos hPpos hlogΞ hcountπ hRδ (by positivity) (by positivity) (by positivity)

end LowerBoundLDP

end MultipoleBKT

end
