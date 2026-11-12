/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Sum
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Integral
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.GroupSum
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Absorption

/-!
# Fixed-group integration and summation over groups

Lemma 4.58, its Appendix proof,
proof of Lemma 4.58, and (4.124) through (4.125) in the proof of Lemma 4.59.

`integration_summation_fixed_groups` proves the written tree-summed
inequality while keeping the groups fixed. Its right-hand side contains
`|Coarse|^|Coarse| ∏ₗ |Xₗ|^|Xₗ|`. The position estimate supplies the spatial integral.
Weighted Cayley and arithmetic-geometric mean sum both tree families,
and their radial powers are allocated as `4C₀/M`.

Both radial regimes use the symmetric exponent `2 - 2/k`. The
high-β calculation includes the exponent margin and critical
logarithm absorption of (A.69). The retained explicit cutoff interface
also covers larger `λ` by the symmetric bound before the harmless
critical logarithm is inserted.

`lemma_4_59` follows by the separate written group enumeration, using
binomial and multinomial coefficients, Stirling bounds and stars and bars.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
open UpperBound.AbsoluteUpper (jLargeIntegrand jLarge simplifiedMajorant)
open TheoremTwo (errorRate_of_lt_four' errorRate_of_four_le tsum_transition_nonneg)
open scoped ENNReal

variable {lam ε₀ β : ℝ} {p₀ : ℕ}

/-! ### The scales -/

/-- `((ε₀ R̄)^{4-β-2/k})^k ≤ ε₀^{(4-β)k-2} λ^{(2-β)k} δ` for `β ∈ (2,4)`. -/
theorem cutoff_rpow_le_lt_four (hβ : 2 < β) (hβ4 : β < 4) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    {k : ℕ} (hk : 0 < k) :
    ((ε₀ * truncationScale p₀ β lam) ^ (4 - β - 2 / (k : ℝ))) ^ k ≤
      ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam := by
  have hR := Appendix.truncationScale_of_lt (p₀ := p₀) hβ4 hlam
  have hRpos : 0 < truncationScale p₀ β lam := Appendix.truncationScale_pos hlam
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h4 : 0 < 4 - β := by linarith
  have hα : 2 * alphaExponent β = 4 - β := by
    unfold alphaExponent
    rw [ite_eq_left hβ4]
    ring
  rw [← Real.rpow_mul_natCast (by positivity), Real.mul_rpow hε₀.le hRpos.le, hα]
  have hexp : (4 - β - 2 / (k : ℝ)) * k = (4 - β) * k - 2 := by field_simp
  rw [hexp, hR, ← Real.rpow_mul hlam.le]
  have hsplit : -(β - 2) / (4 - β) * ((4 - β) * k - 2) = (2 - β) * k + 2 * (β - 2) / (4 - β) := by
    field_simp
    ring
  rw [hsplit, Real.rpow_add hlam, errorRate_of_lt_four' hβ hβ4 hlam, ← mul_assoc]
  have hT := tsum_transition_nonneg β lam
  have h1 : 0 ≤ ε₀ ^ ((4 - β) * (k : ℝ) - 2) * lam ^ ((2 - β) * (k : ℝ)) *
      lam ^ (2 * (β - 2) / (4 - β)) := by positivity
  nlinarith

/-- `λ^{(4-β)k-2} (ε₀ R̄/λ)^{a k} ≤ ε₀^{k-2} λ^{(2-β)k} δ` for `β ≥ 4`, `(2p₀+1) a ≤ 1/2`,
`k ≥ 2p₀ + 1`, `λ ≤ ε₀² ≤ 1`. -/
theorem cutoff_rpow_le_ge_four (hβ4 : 4 ≤ β) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1)
    (hlε : lam ≤ ε₀ ^ 2) {a : ℝ} (ha : 0 ≤ a) (ha2 : (2 * p₀ + 1) * a ≤ 1 / 2) {k : ℕ}
    (hk : 2 * p₀ + 1 ≤ k) (hk2 : 2 ≤ k) :
    lam ^ ((4 - β) * k - 2) * ((ε₀ * truncationScale p₀ β lam) / lam) ^ (a * k) ≤
      ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam := by
  have hlam1 : lam ≤ 1 := hlε.trans (pow_le_one₀ hε₀.le hε₀1)
  have hα : 2 * alphaExponent β = 1 := by
    unfold alphaExponent
    rw [ite_eq_right (not_lt.2 hβ4)]
    norm_num
  have hRr : truncationScale p₀ β lam = lam ^ (-(2 * (p₀ : ℝ))) := by
    rw [Appendix.truncationScale_of_ge hβ4, ← Real.rpow_intCast]
    push_cast
    ring_nf
  rw [hα, errorRate_of_four_le hβ4, hRr]
  have hkR : (2 * (p₀ : ℝ) + 1) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  -- `ε₀ R̄/λ ≤ λ^{-(2p₀+1)}`
  have hq : ε₀ * lam ^ (-(2 * (p₀ : ℝ))) / lam ≤ lam ^ (-(2 * (p₀ : ℝ) + 1)) := by
    rw [div_le_iff₀ hlam, show -(2 * (p₀ : ℝ) + 1) = -(2 * (p₀ : ℝ)) - 1 by ring,
      Real.rpow_sub hlam, Real.rpow_one, div_mul_cancel₀ _ hlam.ne']
    exact mul_le_of_le_one_left (by positivity) hε₀1
  have hq' : (ε₀ * lam ^ (-(2 * (p₀ : ℝ))) / lam) ^ (a * k) ≤
      lam ^ (-(2 * (p₀ : ℝ) + 1) * (a * k)) := by
    rw [Real.rpow_mul hlam.le]
    exact Real.rpow_le_rpow (by positivity) hq (by positivity)
  -- the exponent of `λ`
  set E : ℝ := 2 * k - 2 - (2 * p₀ + 1) * a * k with hE
  have hE1 : 2 * p₀ + ((k : ℝ) - 2) / 2 ≤ E := by
    have : (2 * (p₀ : ℝ) + 1) * a * k ≤ k / 2 := by nlinarith
    simp only [hE]
    linarith
  have hsplit : lam ^ ((4 - β) * k - 2) * lam ^ (-(2 * (p₀ : ℝ) + 1) * (a * k)) =
      lam ^ ((2 - β) * k) * lam ^ E := by
    rw [← Real.rpow_add hlam, ← Real.rpow_add hlam]
    congr 1
    simp only [hE]
    ring
  have hE2 : lam ^ E ≤ lam ^ (2 * p₀) * ε₀ ^ (1 * (k : ℝ) - 2) := by
    calc lam ^ E ≤ lam ^ (2 * (p₀ : ℝ) + ((k : ℝ) - 2) / 2) :=
          Real.rpow_le_rpow_of_exponent_ge hlam hlam1 hE1
      _ = lam ^ (2 * p₀) * lam ^ (((k : ℝ) - 2) / 2) := by
          rw [Real.rpow_add hlam]
          norm_cast
      _ ≤ lam ^ (2 * p₀) * (ε₀ ^ 2) ^ (((k : ℝ) - 2) / 2) := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
          gcongr
      _ = lam ^ (2 * p₀) * ε₀ ^ (1 * (k : ℝ) - 2) := by
          rw [← Real.rpow_two, ← Real.rpow_mul hε₀.le]
          congr 2
          ring
  calc lam ^ ((4 - β) * k - 2) * (ε₀ * lam ^ (-(2 * (p₀ : ℝ))) / lam) ^ (a * k)
      ≤ lam ^ ((4 - β) * k - 2) * lam ^ (-(2 * (p₀ : ℝ) + 1) * (a * k)) :=
        mul_le_mul_of_nonneg_left hq' (by positivity)
    _ = lam ^ ((2 - β) * k) * lam ^ E := hsplit
    _ ≤ lam ^ ((2 - β) * k) * (lam ^ (2 * p₀) * ε₀ ^ (1 * (k : ℝ) - 2)) :=
        mul_le_mul_of_nonneg_left hE2 (by positivity)
    _ = _ := by ring

/-- The high-β scale calculation including the critical logarithm.
(A.69) and the calculation
immediately following it, proof of Lemma 4.58. -/
theorem cutoff_rpow_log_le_ge_four (hp₀ : 1 ≤ p₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.exp (-1) ∧ ∀ {β lam ε₀ a : ℝ}, 4 ≤ β →
      0 < lam → lam ≤ δ → 0 < ε₀ → ε₀ ≤ 1 → lam ^ (1 / 12 : ℝ) ≤ ε₀ →
      0 ≤ a → (2 * p₀ + 1) * a ≤ 1 / 2 → ∀ {k : ℕ}, 2 * p₀ < k →
        lam ^ ((4 - β) * k - 2) * ((ε₀ * truncationScale p₀ β lam) / lam) ^ (a * k) *
          (if β = 4 then |Real.log lam| else 1) ≤
        ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam := by
  obtain ⟨δ, hδ, hδ1, hgain⟩ := RouteFixedGroups.high_beta_power_log_absorption p₀ hp₀
  refine ⟨min δ (Real.exp (-1)), lt_min hδ (Real.exp_pos _), min_le_right _ _, ?_⟩
  intro β lam ε₀ a hβ hlam hlδ heps heps1 hlε ha ha2 k hk
  have hδ' : lam ≤ δ := hlδ.trans (min_le_left _ _)
  have hlam1 : lam ≤ 1 := hδ'.trans hδ1
  have hα : 2 * alphaExponent β = 1 := by
    unfold alphaExponent
    rw [ite_eq_right (not_lt.mpr hβ)]
    norm_num
  have hRr : truncationScale p₀ β lam = lam ^ (-(2 * (p₀ : ℝ))) := by
    rw [Appendix.truncationScale_of_ge hβ, ← Real.rpow_intCast]
    push_cast
    ring_nf
  have hq : ε₀ * lam ^ (-(2 * (p₀ : ℝ))) / lam ≤ lam ^ (-(2 * (p₀ : ℝ) + 1)) := by
    rw [div_le_iff₀ hlam, show -(2 * (p₀ : ℝ) + 1) = -(2 * (p₀ : ℝ)) - 1 by ring,
      Real.rpow_sub hlam, Real.rpow_one, div_mul_cancel₀ _ hlam.ne']
    exact mul_le_of_le_one_left (by positivity) heps1
  have hq' : (ε₀ * lam ^ (-(2 * (p₀ : ℝ))) / lam) ^ (a * k) ≤
      lam ^ (-(2 * (p₀ : ℝ) + 1) * (a * k)) := by
    rw [Real.rpow_mul hlam.le]
    exact Real.rpow_le_rpow (by positivity) hq (by positivity)
  let L := if β = 4 then |Real.log lam| else 1
  have hL : 0 ≤ L := by dsimp only [L]; split_ifs <;> positivity
  have hs := hgain hβ hlam hδ' heps heps1 hlε ha2 hk
  rw [hα, TheoremTwo.errorRate_of_four_le hβ, hRr]
  calc
    _ ≤ (lam ^ ((4 - β) * k - 2) * lam ^ (-(2 * (p₀ : ℝ) + 1) * (a * k))) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' (by positivity)) hL
    _ = lam ^ ((2 - β) * k) *
        (lam ^ (2 * k - 2 - (2 * p₀ + 1) * a * k) * L) := by
      rw [← Real.rpow_add hlam,
        show (4 - β) * k - 2 + -(2 * (p₀ : ℝ) + 1) * (a * k) =
          (2 - β) * k + (2 * k - 2 - (2 * p₀ + 1) * a * k) by ring,
        Real.rpow_add hlam, mul_assoc]
    _ ≤ lam ^ ((2 - β) * k) * (lam ^ (2 * p₀) * ε₀ ^ ((k : ℝ) - 2)) :=
      mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hlam.le _)
    _ = _ := by simp only [one_mul]; ring

/-! ### Lemma 4.59 -/

variable {χ : ℂ → ℝ}

open scoped Classical in
/-- The series of the right-hand side of Lemma 4.57 (the second factor of
`MultipoleBKT.UpperBound.AbsoluteUpper.simplifiedMajorant`). -/
noncomputable def treeSeries (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ C₀ : ℝ)
    (X : Finset (Finset ℕ)) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n.factorial : ℝ≥0∞))⁻¹ *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
        ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb

theorem simplifiedMajorant_eq (N : ℕ) (lam M C₀ C : ℝ) (X : Finset (Finset ℕ)) :
    simplifiedMajorant χ N p₀ β lam M ε₀ C₀ C X =
      ENNReal.ofReal (Real.exp (C * (X.biUnion id).card)) /
        ENNReal.ofReal (((N : ℝ) * lam ^ (2 - β)) ^ (X.biUnion id).card *
          Hierarchical.zeroPartitionFunction χ N p₀ β lam M ε₀ X) *
        treeSeries χ N p₀ β lam M ε₀ C₀ X := rfl

/-- The size above which Lemma 4.59 applies: `⌊4/(4-β)⌋` for `β < 4`, `2p₀` for `β ≥ 4`. -/
noncomputable def largeThreshold (p₀ : ℕ) (β : ℝ) : ℕ :=
  if β < 4 then ⌊4 / (4 - β)⌋₊ else 2 * p₀

/-- The size cutoff `q₀` in the convergence proof, with the boundary size
handled by the bounded estimate.
(4.120). -/
noncomputable def qZero (p₀ : ℕ) (β : ℝ) : ℕ :=
  if β < 4 then ⌊4 / (4 - β)⌋₊ + 1 else 2 * p₀

/-- Above the written `q₀`, the size hypothesis of Lemma 4.59 holds.
(4.120) and Step 2 of
Lemma 4.59, (4.120). -/
theorem largeThreshold_le_qZero (p₀ : ℕ) (β : ℝ) :
    largeThreshold p₀ β ≤ qZero p₀ β := by
  unfold largeThreshold qZero
  split_ifs <;> omega

/-- The exponent `a'` of the logarithmic weights in the proof of Lemma 4.59. -/
noncomputable def logExponent (p₀ : ℕ) (β : ℝ) : ℝ :=
  if β < 4 then (4 - β) / 16 else 1 / (8 * (2 * p₀ + 1))

theorem logExponent_pos (β : ℝ) : 0 < logExponent p₀ β := by
  unfold logExponent
  split_ifs with h
  · linarith
  · positivity

/-- The literal fixed-group form of Lemma 4.58.
(4.115), Lemma 4.58.
The explicit cutoff assumptions suffice uniformly in the groups and their number. -/
theorem integration_summation_fixed_groups (hχ : IsMollifier χ) (hβ : 2 < β)
    (hp₀ : 1 ≤ p₀) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∃ B : ℝ, 1 ≤ B ∧
      ∀ ε₀ lam : ℝ, 0 < ε₀ → ε₀ ≤ 1 → 0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam →
        (4 ≤ β → lam ≤ ε₀ ^ 2) → ∀ (N : ℕ) (X : Finset (Finset ℕ)), IsSubpartition X →
        (∀ S ∈ X, S.card ≤ pBeta p₀ β) → largeThreshold p₀ β < (X.biUnion id).card →
        ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
        (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
        (∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) ≤
          ENNReal.ofReal ((N : ℝ) * B ^ (X.biUnion id).card *
            RouteFixedGroups.groupCardinality X Xs *
              (ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) *
                lam ^ ((2 - β) * (X.biUnion id).card) * errorRate p₀ β lam)) := by
  let d := logExponent p₀ β
  have hd : 0 < d := logExponent_pos β
  refine ⟨max 21 (4 * C₀ / d), lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun M hM => ?_⟩
  have hM21 : (21 : ℝ) ≤ M := (le_max_left _ _).trans hM
  have hMpos : 0 < M := by linarith
  let a := 4 * C₀ / M
  have ha : 0 < a := div_pos (by positivity) hMpos
  have had : a ≤ d := by
    have h := (le_max_right _ _).trans hM
    rw [div_le_iff₀ hd] at h
    exact (div_le_iff₀ hMpos).mpr (by linarith)
  let K := RouteFixedGroups.fixedGroupConstant (pBeta p₀ β) M (C₀ / M)
  have hK : 0 ≤ K := by unfold K RouteFixedGroups.fixedGroupConstant; positivity
  have hinput {ε₀ lam : ℝ} (hlam : 0 < lam) (hlh : lam ≤ ε₀ * truncationScale p₀ β lam)
      {N : ℕ} {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (hk : 0 < (X.biUnion id).card)
      (hXp : ∀ S ∈ X, S.card ≤ pBeta p₀ β) {n : ℕ}
      (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
      (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :
      (∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
        ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (K ^ (X.biUnion id).card * RouteFixedGroups.groupCardinality X Xs) *
          ∫⁻ u : X.biUnion id → ℂ, (∏ i, ENNReal.ofReal
            (dipoleWeight χ β lam (ε₀ * truncationScale p₀ β lam) a (u i))) *
              ENNReal.ofReal (radiusFactor lam u) := by
    by_cases hne : ∀ l, (Xs l).Nonempty
    · have hXne : X.Nonempty := by
        obtain ⟨i, hi⟩ := card_pos.mp hk
        obtain ⟨S, hS, _⟩ := mem_biUnion.mp hi
        exact ⟨S, hS⟩
      exact (RouteFixedGroups.fixed_groups_tree_sum_le_radial hχ hlam (by linarith) hC₀
        (hlam.le.trans hlh) hX hXne hXp N Xs hXs hdisj hne).trans
          (mul_le_mul' le_rfl (RouteFixedGroups.source_radial_le hlam (hlam.le.trans hlh) ha.le))
    · have hz : (∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) = 0 := by
        apply sum_eq_zero
        intro Ta hTa
        exact (hne (fun l => nonempty_of_mem_relTreePairs (isSubpartition_of_subset hX (hXs l))
          (Fintype.mem_piFinset.mp hTa l))).elim
      rw [hz]
      exact bot_le
  by_cases hβ4 : β < 4
  · obtain ⟨Cr, hCr, hrad⟩ := lintegral_large_lt_four hχ hβ hβ4
    have hdv : d = (4 - β) / 16 := by simp only [d, logExponent, ite_eq_left hβ4]
    refine ⟨max 1 (K * max Cr 1), le_max_left _ _,
      fun ε₀ lam hε₀ hε₀1 hlam hlh _ N X hX hXp hk n Xs hXs hdisj => ?_⟩
    let k := (X.biUnion id).card
    have hthr : ⌊4 / (4 - β)⌋₊ < k := by simpa only [largeThreshold, ite_eq_left hβ4] using hk
    have hk0 : 0 < k := by omega
    have : Nonempty (X.biUnion id) := by obtain ⟨i, hi⟩ := card_pos.mp hk0; exact ⟨⟨i, hi⟩⟩
    have hkR : 4 / (4 - β) < (k : ℝ) := by
      have h1 := Nat.lt_floor_add_one (4 / (4 - β))
      have h2 : ((⌊4 / (4 - β)⌋₊ : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hthr
      linarith
    have h4 : 0 < 4 - β := by linarith
    have hk0R : (0 : ℝ) < k := by exact_mod_cast hk0
    have h2k : 2 / (k : ℝ) < (4 - β) / 2 := by
      rw [div_lt_div_iff₀ hk0R (by norm_num)]
      rw [div_lt_iff₀ h4] at hkR
      linarith
    have hcond : (4 - β) / 4 ≤ 4 - β - 2 / (Fintype.card (X.biUnion id) : ℝ) - a := by
      rw [Fintype.card_coe]
      rw [hdv] at had
      linarith
    have hrad' := hrad lam (ε₀ * truncationScale p₀ β lam) a hlam hlh ha
      (by rw [hdv] at had; linarith) hcond
    rw [Fintype.card_coe] at hrad'
    have hG := RouteFixedGroups.groupCardinality_nonneg X Xs
    have hcut : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlh
    refine (hinput hlam hlh hX hk0 hXp Xs hXs hdisj).trans ((mul_le_mul' le_rfl hrad').trans ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hs := cutoff_rpow_le_lt_four (p₀ := p₀) hβ hβ4 hlam hε₀ hk0
    have hG := RouteFixedGroups.groupCardinality_nonneg X Xs
    calc
      _ = (N : ℝ) * (K * Cr) ^ k * RouteFixedGroups.groupCardinality X Xs *
          ((ε₀ * truncationScale p₀ β lam) ^ (4 - β - 2 / (k : ℝ))) ^ k := by rw [mul_pow, mul_pow]; ring
      _ ≤ (N : ℝ) * max 1 (K * max Cr 1) ^ k * RouteFixedGroups.groupCardinality X Xs *
          (ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam) := by
        apply mul_le_mul
        · gcongr
          exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hK).trans (le_max_right _ _)
        · exact hs
        · positivity
        · positivity
      _ = _ := rfl
  · have hβ4' : 4 ≤ β := not_lt.mp hβ4
    obtain ⟨Cr, hCr, hrad⟩ := lintegral_large_ge_four hχ hβ4'
    have hdv : d = 1 / (8 * (2 * p₀ + 1)) := by simp only [d, logExponent, ite_eq_right hβ4]
    have hpR : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
    have ha2 : (2 * (p₀ : ℝ) + 1) * a ≤ 1 / 2 := by
      have he : (2 * (p₀ : ℝ) + 1) * d = 1 / 8 := by rw [hdv]; field_simp
      nlinarith
    have ha1 : a ≤ 1 := by nlinarith
    let D := Cr * (2 + 1 / a)
    have hD : 0 ≤ D := by positivity
    refine ⟨max 1 (K * max D 1), le_max_left _ _,
      fun ε₀ lam hε₀ hε₀1 hlam hlh hlε N X hX hXp hk n Xs hXs hdisj => ?_⟩
    let k := (X.biUnion id).card
    have hthr : 2 * p₀ < k := by simpa only [largeThreshold, ite_eq_right hβ4] using hk
    have hk0 : 0 < k := by omega
    have : Nonempty (X.biUnion id) := by obtain ⟨i, hi⟩ := card_pos.mp hk0; exact ⟨⟨i, hi⟩⟩
    have hrad' := hrad lam (ε₀ * truncationScale p₀ β lam) a hlam hlh ha ha1 (ι := X.biUnion id)
    rw [Fintype.card_coe] at hrad'
    have hG := RouteFixedGroups.groupCardinality_nonneg X Xs
    have hcut : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlh
    refine (hinput hlam hlh hX hk0 hXp Xs hXs hdisj).trans ((mul_le_mul' le_rfl hrad').trans ?_)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨δ, hδ, hδexp, hlogs⟩ := cutoff_rpow_log_le_ge_four (p₀ := p₀) hp₀
    have hs : lam ^ ((4 - β) * k - 2) *
        (ε₀ * truncationScale p₀ β lam / lam) ^ (a * k) ≤
        ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam := by
      by_cases hsmall : lam ≤ δ ∧ lam ^ (1 / 12 : ℝ) ≤ ε₀
      · have hL : 1 ≤ (if β = 4 then |Real.log lam| else 1) := by
          split_ifs
          · have hlog : Real.log lam ≤ -1 := by
              have h := Real.log_le_log hlam (hsmall.1.trans hδexp)
              rwa [Real.log_exp] at h
            rw [abs_of_nonpos (by linarith)]
            linarith
          · exact le_rfl
        exact (le_mul_of_one_le_right (by positivity) hL).trans
          (hlogs hβ4' hlam hsmall.1 hε₀ hε₀1 hsmall.2 ha.le ha2 hthr)
      · exact cutoff_rpow_le_ge_four (p₀ := p₀) (k := k) hβ4' hlam hε₀ hε₀1 (hlε hβ4')
          ha.le ha2 (by omega) (by omega)
    have hG := RouteFixedGroups.groupCardinality_nonneg X Xs
    calc
      _ = (N : ℝ) * (K * D) ^ k * RouteFixedGroups.groupCardinality X Xs *
          (lam ^ ((4 - β) * k - 2) * (ε₀ * truncationScale p₀ β lam / lam) ^ (a * k)) := by
        rw [mul_pow K D]
        ring
      _ ≤ (N : ℝ) * max 1 (K * max D 1) ^ k * RouteFixedGroups.groupCardinality X Xs *
          (ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam) := by
        apply mul_le_mul
        · gcongr
          exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hK).trans (le_max_right _ _)
        · exact hs
        · positivity
        · positivity
      _ = _ := rfl

/-- **Lemma 4.58**, summed over the groups. -/
theorem lemma_4_59 (hχ : IsMollifier χ) (hβ : 2 < β) (hp₀ : 1 ≤ p₀) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∃ B : ℝ, 1 ≤ B ∧
      ∀ ε₀ lam : ℝ, 0 < ε₀ → ε₀ ≤ 1 → 0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam →
        (4 ≤ β → lam ≤ ε₀ ^ 2) → ∀ (N : ℕ) (X : Finset (Finset ℕ)), IsSubpartition X →
        (∀ S ∈ X, S.card ≤ pBeta p₀ β) → largeThreshold p₀ β < (X.biUnion id).card →
        treeSeries χ N p₀ β lam M ε₀ C₀ X ≤ ENNReal.ofReal ((N : ℝ) * B ^ (X.biUnion id).card *
          (X.card.factorial : ℝ) * (ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) *
            lam ^ ((2 - β) * (X.biUnion id).card) * errorRate p₀ β lam)) := by
  obtain ⟨M₀, hM₀, hfixed⟩ := integration_summation_fixed_groups hχ hβ hp₀ hC₀
  refine ⟨M₀, hM₀, fun M hM => ?_⟩
  obtain ⟨B, hB, hbound⟩ := hfixed M hM
  let D : ℝ := 4 * Real.exp 6
  have hD : 1 ≤ D := by
    have he : 1 ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
    dsimp only [D]
    linarith
  refine ⟨B * D, one_le_mul_of_one_le_of_one_le hB hD,
    fun ε₀ lam hε₀ hε₀1 hlam hlh hlε N X hX hXp hk => ?_⟩
  let k := (X.biUnion id).card
  let E := ε₀ ^ (2 * alphaExponent β * k - 2) * lam ^ ((2 - β) * k) * errorRate p₀ β lam
  have hE : 0 ≤ E := mul_nonneg (mul_nonneg (Real.rpow_nonneg hε₀.le _)
    (Real.rpow_nonneg hlam.le _)) (TheoremTwo.errorRate_pos hβ hlam).le
  let A := (N : ℝ) * B ^ k * E
  have hA : 0 ≤ A := mul_nonneg (by positivity) hE
  have hs := RouteFixedGroups.summed_integrals_le_of_fixed hX hA
    (χ := χ) (N := N) (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (C₀ := C₀)
    (fun Xs hXs hd => (hbound ε₀ lam hε₀ hε₀1 hlam hlh hlε N X hX hXp hk Xs hXs hd).trans_eq
      (by congr 1; dsimp only [A]; ring))
  refine hs.trans (ENNReal.ofReal_le_ofReal ?_)
  have hXk : X.card ≤ k := card_le_card_biUnion hX.2 hX.1
  have hp : D ^ X.card ≤ D ^ k := pow_le_pow_right₀ hD hXk
  calc
    _ = (N : ℝ) * B ^ k * D ^ X.card * (X.card.factorial : ℝ) * E := by dsimp only [A, D]; ring
    _ ≤ (N : ℝ) * B ^ k * D ^ k * (X.card.factorial : ℝ) * E := by gcongr
    _ = _ := by rw [mul_pow B D]; ring

end AbsoluteLower

end MultipoleBKT

end
