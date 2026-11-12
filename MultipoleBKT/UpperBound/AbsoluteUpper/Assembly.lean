/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.Uniform

/-!
# Proposition 5.20 from its inputs

The paper: Proposition 5.20 and
its proof.

`prop_5_20_of_inputs` (internal, conditional): from Lemma 5.37 (`SimplifiedBoundUpper`), eq.
(5.67) of Proposition 5.18 (`KPlusBoundInput`), eq. (5.101)
(`ExternalPositivityInput`) and the transfer of Lemma 4.59 and Proposition 4.27 to an abstract
activity (`AbsoluteConvergenceTransfer`): for `p₀ ≥ 1`, `β > 2` and `L ∈ ℝ`, there is `M₀ > 20`
such that for `M ≥ M₀` there is `ε₁ ∈ (0, 1]` such that for `ε₀ ∈ (0, ε₁)` there are `C > 0` and
`λ₀ ∈ (0, 1]` such that for `λ ∈ (0, λ₀)` and `N` large, for every frozen configuration `(V, Z)`
and every subpartition `π` of the good labels with blocks of size at most `p(β)` satisfying
(5.56), with `δ = δ_{β,λ}`:

* (5.70), the absolute convergence of the full connected series and (5.71) (whose series
  converges) for `𝖪^{+,Z}_{ε₀}` and for `𝖪̂^{+,Z}_{ε₀}`, with the bound `C N δ` independent of `Z`
  (`AbsoluteUpperBounds`);
* `W(Z) = exp(S(Z)) > 0`, `S(Z)` the full connected series of the `𝖪̂^{+,Z}_{ε₀}`
  (used by Proposition 5.38 and
  Proposition 5.43).

The proof is the paper's: the transfer is applied to `𝖪^{+,Z}` (Lemma 5.37 and (5.67)) and to
`𝖪̂^{+,Z}` (`|𝖪̂^{+,Z}| ≤ |𝖪^{+,Z}|` by (5.101), the hypothesis `𝖬^{+,Z}(S) > 0` of
which comes from (5.65)); for clusters with `|V_X| ≤ p(β)`, (5.67) and (4.38)
for `𝖬^0_{ε₀}` give `|𝖪(X)| ≤ C_{ε₀} (λ²/N)^{|X|-1}`, so that Lemma 4.53 and
(5.71) give the absolute convergence of the full series; Lemma 4.7 gives `W = exp(S) > 0`.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

open Hierarchical

/-- The good labels lie in `{0, …, N-1}`. -/
theorem subset_range_of_subset_good {N : ℕ} {V : Finset (Fin N)} {S : Finset ℕ}
    (hS : S ⊆ (Finset.univ \ V).map Fin.valEmbedding) : S ⊆ Finset.range N := by
  intro i hi
  obtain ⟨j, -, rfl⟩ := mem_map.1 (hS hi)
  exact mem_range.2 j.isLt

/-- A subpartition of `{0, …, N-1}` has at most `N` blocks. -/
theorem card_le_of_subset_range {N : ℕ} {π : Finset (Finset ℕ)} (hπ : IsSubpartition π)
    (h : ∀ S ∈ π, S ⊆ Finset.range N) : π.card ≤ N :=
  (card_le_card_biUnion_of_isSubpartition hπ).trans
    ((card_le_card (biUnion_subset.2 fun S hS => h S hS)).trans (card_range N).le)

/-- **The step from the bounds on the activity to the conclusions** for one activity `K`: the
outputs (4.55), (4.56) of the transfer, and the small-cluster majorant feeding Lemma 4.53. -/
theorem absoluteUpperBounds_of {π : Finset (Finset ℕ)} {N : ℕ} {K : Finset (Finset ℕ) → ℝ}
    {p : ℕ} {B Ct Cs lam : ℝ}
    (hfull : ∀ (π : Finset (Finset ℕ)) (N : ℕ) (K : Finset (Finset ℕ) → ℝ) (lam : ℝ),
      IsSubpartition π → π.card ≤ N → (∀ X ⊆ π, X.card ≤ 1 → K X = 0) →
      (∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
        |K X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1)) →
      0 < lam → lam ≤ 1 → Ct * lam ^ 2 ≤ 1 / 2 →
      Summable (bigClusterTerm K π p) → Summable (connectedTerm K π))
    (hπ : IsSubpartition π) (hπN : π.card ≤ N) (hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0)
    (hsmall : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1))
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hCt : Ct * lam ^ 2 ≤ 1 / 2)
    (htr : (∑ X ∈ π.powerset.filter (fun X => p < (X.biUnion id).card), |K X| ≤ B) ∧
      Summable (bigClusterTerm K π p) ∧ ∑' n, bigClusterTerm K π p n ≤ B) :
    AbsoluteUpperBounds K π p B :=
  ⟨htr.1, hfull π N K lam hπ hπN hK1 hsmall hlam hlam1 hCt htr.2.1, htr.2.1, htr.2.2⟩

/-- **Proposition 5.20**, internal form, from its inputs
(see the module docstring). -/
theorem prop_5_20_of_inputs (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀) (β : ℝ)
    (hβ : 2 < β) (L : ℝ) (hsimp : SimplifiedBoundUpper χ p₀ β L)
    (hKplus : KPlusBoundInput χ p₀ β L) (hext : ExternalPositivityInput χ p₀ β L)
    (htr : AbsoluteConvergenceTransfer χ p₀ β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
            IsFrozenConfig p₀ β lam M ε₀ V Z →
            ∀ π : Finset (Finset ℕ), IsSubpartition π →
              (∀ S ∈ π, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
              (∀ S ∈ π, S.card ≤ pBeta p₀ β) → ProfileBound p₀ β lam ε₀ N π →
              AbsoluteUpperBounds (plusActivity χ N p₀ β lam M ε₀ L V Z) π (pBeta p₀ β)
                  (C * N * errorRate p₀ β lam) ∧
                AbsoluteUpperBounds (hatActivity χ N p₀ β lam M ε₀ L V Z) π (pBeta p₀ β)
                  (C * N * errorRate p₀ β lam) ∧
                0 < clusterSeriesW χ N p₀ β lam M ε₀ L V Z π ∧
                clusterSeriesW χ N p₀ β lam M ε₀ L V Z π =
                  Real.exp (connectedSeries (hatActivity χ N p₀ β lam M ε₀ L V Z) π) := by
  set p := pBeta p₀ β with hp
  obtain ⟨C₀, hC₀, hsimpM⟩ := hsimp
  obtain ⟨M₁, hM₁, htrM⟩ := htr C₀ hC₀
  refine ⟨max M₁ (max 21 ((3 : ℝ) ^ p)), hM₁.trans_le (le_max_left _ _), fun M hM => ?_⟩
  have hM21 : (21 : ℝ) ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hM20 : (20 : ℝ) < M := by linarith
  have hM3p : (3 : ℝ) ^ p ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hMM₁ : M₁ ≤ M := (le_max_left _ _).trans hM
  obtain ⟨C, hC, hsimpε⟩ := hsimpM M hM20 hM3p
  obtain ⟨ε₁, hε₁, hε₁1, q, htrε⟩ := htrM M hMM₁ C hC
  refine ⟨ε₁, hε₁, hε₁1, fun ε₀ hε₀ hε₀₁ => ?_⟩
  have hε₀1 : ε₀ < 1 := hε₀₁.trans_le hε₁1
  -- the bounded-cluster estimates for the sizes `k ≤ max q p`
  obtain ⟨CK, hCK, Cm, hCm, lamU, hlamU, hU⟩ :=
    uniform_bounded_estimates hχ hp₀ hβ L hKplus hM20 hM3p hε₀ hε₀1 (max q p)
  set Cb : ℝ := ∑ k ∈ range (max q p + 1), CK k with hCb
  have hCb0 : 0 ≤ Cb := sum_nonneg fun k _ => hCK k
  have hCKb : ∀ k, k ≤ max q p → CK k ≤ Cb := fun k hk =>
    single_le_sum (f := CK) (fun k _ => hCK k) (mem_range.2 (Nat.lt_succ_of_le hk))
  obtain ⟨C', hC', lamT, hlamT, hlamT1, htrL⟩ := htrε ε₀ hε₀ hε₀₁ Cb hCb0
  -- the small-cluster majorant and Lemma 4.53
  set Cs : ℝ := Cb * Cm ^ p with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  obtain ⟨Ct, hCt, hfull⟩ := summable_connectedTerm_of_small hCs0 p
  obtain ⟨lamS, hlamS, hsimpL⟩ := hsimpε ε₀ hε₀ hε₀1
  refine ⟨C', hC', min (min lamT lamS) (min lamU (min (ε₀ / 2) (1 / (2 * Ct + 1)))),
    lt_min (lt_min hlamT hlamS) (lt_min hlamU (lt_min (by linarith) (by positivity))),
    (min_le_left _ _).trans ((min_le_left _ _).trans hlamT1), fun lam hlam hlt => ?_⟩
  have hltT : lam < lamT := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hltS : lam < lamS := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hltU : lam < lamU := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hltε : lam < ε₀ / 2 :=
    hlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hltC : lam < 1 / (2 * Ct + 1) :=
    hlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlam1 : lam ≤ 1 := (hltT.trans_le hlamT1).le
  have hCtl : Ct * lam ^ 2 ≤ 1 / 2 := by
    have h1 : lam ^ 2 ≤ lam := by nlinarith
    have h2 : Ct * lam ≤ 1 / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hltC
      nlinarith
    calc Ct * lam ^ 2 ≤ Ct * lam := mul_le_mul_of_nonneg_left h1 hCt.le
      _ ≤ 1 / 2 := h2
  have hlamR : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
    nlinarith
  obtain ⟨NT, hNT⟩ := htrL lam hlam hltT
  obtain ⟨NS, hNS⟩ := hsimpL lam hlam hltS
  obtain ⟨NU, hNU⟩ := hU lam hlam hltU
  refine ⟨max (max NT NS) (max NU 1), fun N hN V Z hVZ π hπ hπg hπp hprof => ?_⟩
  have hNT' : NT ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNS' : NS ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNU' : NU ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  obtain ⟨hKb, hM0b, hMpos⟩ := hNU N hNU'
  have hπr : ∀ S ∈ π, S ⊆ Finset.range N := fun S hS => subset_range_of_subset_good (hπg S hS)
  have hπN : π.card ≤ N := card_le_of_subset_range hπ hπr
  have hXsub : ∀ X ⊆ π, IsSubpartition X := fun X hX => isSubpartition_of_subset hπ hX
  set K := plusActivity χ N p₀ β lam M ε₀ L V Z with hK
  set Kh := hatActivity χ N p₀ β lam M ε₀ L V Z with hKh
  -- `𝖪̂ ≤ 𝖪` on the subfamilies of `π`
  have hg : ∀ S ∈ π, 1 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S := by
    intro S hS
    have hSne := hπ.1 S hS
    exact hext lam M ε₀ V Z hlam hε₀ hN1 hlamR hM3p (by linarith) hVZ.1.symm.subset S hSne
      (hMpos V Z hVZ.1 S hSne.card_pos (hπp S hS))
  have hhat : ∀ X ⊆ π, |Kh X| ≤ |K X| := fun X hX =>
    abs_hatActivity_le fun S hS => hg S (hX hS)
  -- the hypotheses of the transfer for `𝖪^{+,Z}`
  have hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0 := fun X _ h =>
    plusActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h
  have hKh1 : ∀ X ⊆ π, X.card ≤ 1 → Kh X = 0 := fun X _ h =>
    hatActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h
  have hKs : ∀ X ⊆ π, 2 ≤ X.card →
      ENNReal.ofReal |K X| ≤ simplifiedMajorant χ N p₀ β lam M ε₀ C₀ C X := fun X hX _ =>
    hNS N hNS' V Z hVZ X (hXsub X hX) (fun S hS => hπg S (hX hS)) fun S hS => hπp S (hX hS)
  have hKbd : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ q →
      |K X| ≤ Cb * Appendix.gammaBeta p₀ β lam (X.biUnion id).card /
        (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ ((X.biUnion id).card - 1)) := by
    intro X hX h2 hq
    have hk1 : 1 ≤ (X.biUnion id).card :=
      (by omega : 1 ≤ X.card).trans (card_le_card_biUnion_of_isSubpartition (hXsub X hX))
    have hkQ : (X.biUnion id).card ≤ max q p := hq.trans (le_max_left _ _)
    refine (hKb _ hk1 hkQ V Z hVZ X (hXsub X hX) (card_pos.1 (by omega))
      (fun S hS => hπg S (hX hS)) (fun S hS => hπp S (hX hS)) rfl).trans ?_
    have hg0 := SmallIntegral.gammaBeta_nonneg hlam p₀ β (X.biUnion id).card
    have hz := zeroPartitionFunction_nonneg χ N p₀ β lam M ε₀ X
    gcongr
    exact hCKb _ hkQ
  -- the small-cluster majorant
  have hKsm : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1) := by
    intro X hX h2 hkp
    have hXs := hXsub X hX
    have hk1 : 1 ≤ (X.biUnion id).card :=
      (by omega : 1 ≤ X.card).trans (card_le_card_biUnion_of_isSubpartition hXs)
    have hkQ : (X.biUnion id).card ≤ max q p := hkp.trans (le_max_right _ _)
    have hb := hKb _ hk1 hkQ V Z hVZ X hXs (card_pos.1 (by omega))
      (fun S hS => hπg S (hX hS)) (fun S hS => hπp S (hX hS)) rfl
    rw [gammaBeta_of_le_pStar hk1 (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp)] at hb
    have hm : ∀ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
      intro S hS
      have hS1 := (hXs.1 S hS).card_pos
      by_cases hS2 : 2 ≤ S.card
      · exact hM0b S hS2 (hπp S (hX hS))
      · have hc : S.card = 1 := by omega
        rw [zeroPartitionFunction_singleton hχ hlam hε₀ hN1 hc, hc]
        simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
        exact div_le_one_of_le₀ hCm (by linarith)
    have hprod : zeroPartitionFunction χ N p₀ β lam M ε₀ X =
        ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
      rw [zeroPartitionFunction]
      exact prod_congr rfl fun S _ => (prod_singleton _ S).symm
    rw [hprod] at hb
    refine (abs_le_of_gamma_bound hXs (by omega) hNpos hlam (by linarith) (hCK _) hm hb).trans ?_
    have hXp : X.card ≤ p := (card_le_card_biUnion_of_isSubpartition hXs).trans hkp
    have hpow : Cm ^ X.card ≤ Cm ^ p := pow_le_pow_right₀ hCm hXp
    have hb0 : 0 ≤ (lam ^ 2 / N) ^ (X.card - 1) := by positivity
    calc CK (X.biUnion id).card * Cm ^ X.card * (lam ^ 2 / N) ^ (X.card - 1)
        ≤ Cb * Cm ^ p * (lam ^ 2 / N) ^ (X.card - 1) := by
          gcongr
          · exact hCKb _ hkQ
      _ = Cs * (lam ^ 2 / N) ^ (X.card - 1) := rfl
  -- the transfer, for `𝖪` and `𝖪̂`
  have hTK := hNT N hNT' π hπ hπr hπp hprof K hK1 hKs hKbd
  have hTKh := hNT N hNT' π hπ hπr hπp hprof Kh hKh1
    (fun X hX h2 => (ENNReal.ofReal_le_ofReal (hhat X hX)).trans (hKs X hX h2))
    (fun X hX h2 hq => (hhat X hX).trans (hKbd X hX h2 hq))
  have hAK := absoluteUpperBounds_of hfull hπ hπN hK1 hKsm hlam hlam1 hCtl hTK
  have hAKh := absoluteUpperBounds_of hfull hπ hπN hKh1
    (fun X hX h2 hkp => (hhat X hX).trans (hKsm X hX h2 hkp)) hlam hlam1 hCtl hTKh
  refine ⟨hAK, hAKh, ?_⟩
  have hW := disjointSeries_eq_exp (π := π) (K := Kh)
    (hatActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z (by simp)) hAKh.2.1
  exact hW

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
