/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.GoodBound
public import MultipoleBKT.UpperBound.UpperBoundLDP.Uniform
public import MultipoleBKT.Limits.MultipoleLimit

/-!
# Proposition 5.43, Steps 1–2 for `N` large

The paper: proof of Proposition 5.43, at fixed `M, ε₀, λ`: the bound
`𝖬̂^{+,Z}(π) W(Z) ≤ exp(∑ₖ n_k log 𝗆(k) - (N' - m) log N - N h(n/N) + K_δ N δ + K_V |V_bad|)`
of `MultipoleBKT.UpperBoundLDP.good_bound` holds for all `N` large, uniformly in the profile `n`
with (5.56), the frozen configuration and the partition (`good_eventually`), from the estimates of
Propositions 5.18–5.20 and 4.23–4.24 for `N` large (in the uniform forms of
`MultipoleBKT.UpperBoundLDP.Uniform`) and the limits (2.45) at `λ`. The limit (2.45) is used for
the finitely many sizes `k ≤ p(β)`, with `𝖬(S) = 𝖬([k])` for `|S| = k`
(`MultipoleBKT.Limits.multipolePartitionFunction_congr_card`).
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical PropFiveFortyFive UpperBound SetPartition LowerBoundLDP

/-- **The limit (2.45) uniformly in `S`**: for `R > 0`, for `N` large,
`|N^{|S|-1} 𝖬(S) - 𝗆(|S|)| ≤ R` for every `S` with `1 ≤ |S| ≤ p`. -/
theorem eventually_abs_msf_sub_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M : ℝ} (hlam : 0 < lam)
    {p : ℕ} {msf : ℕ → ℝ}
    (hS : ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S)
        atTop (𝓝 (msf S.card)))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ p →
      |(N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S - msf S.card| ≤ R := by
  have hk : ∀ k ∈ Finset.Icc 1 p, ∀ᶠ N : ℕ in atTop,
      |(N : ℝ) ^ (k - 1) * multipolePartitionFunction χ N β lam M (Finset.range k) - msf k| ≤
        R := by
    intro k hk
    obtain ⟨hk1, hkp⟩ := mem_Icc.1 hk
    have h := hS (Finset.range k) (by rw [card_range]; exact hk1) (by rw [card_range]; exact hkp)
    rw [card_range] at h
    have h' := (Metric.tendsto_nhds.1 h) R hR
    filter_upwards [h'] with N hN
    rw [Real.dist_eq] at hN
    exact hN.le
  filter_upwards [(eventually_all_finset _).2 hk, eventually_ge_atTop 1] with N hN hN1 S hS1 hSp
  have h := hN S.card (mem_Icc.2 ⟨hS1, hSp⟩)
  rwa [Limits.multipolePartitionFunction_congr_card hχ hlam hN1 (card_range S.card).symm]

open scoped Classical in
/-- **Steps 1–2 for `N` large** (see the module docstring). -/
theorem good_eventually {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} {β lam M ε₀ L : ℝ}
    (hβ : 2 < β) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1) (hM : 1 ≤ M)
    {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ}
    {Cε CM C0 Cm CK0 Cz Clow Cs Ccoef C20 : ℝ}
    (hCε : 0 ≤ Cε) (hCM : 0 ≤ CM) (hC0 : 0 ≤ C0) (hCm : 1 ≤ Cm) (hCK0 : 0 ≤ CK0)
    (hCz : 1 ≤ Cz) (hClow : 1 ≤ Clow) (hCs : 0 ≤ Cs) (hCcoef : 0 ≤ Ccoef)
    (hS : ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ pBeta p₀ β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S)
        atTop (𝓝 (msf S.card)))
    (hmsf : ∀ k, 1 ≤ k → k ≤ pBeta p₀ β → lam ^ (2 * (k - 1)) / Cm ≤ msf k)
    (h19 : ∀ᶠ N : ℕ in atTop, ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
      Prop519At χ p₀ β M ε₀ L CM s Cε lam N)
    (hM0 : ∀ᶠ N : ℕ in atTop, ∀ s, 1 ≤ s → s ≤ pBeta p₀ β → ∀ S : Finset ℕ, S.card = s →
      |zeroPartitionFunction χ N p₀ β lam M ε₀ {S} - multipolePartitionFunction χ N β lam M S| ≤
        C0 / (N : ℝ) ^ (s - 1) * truncationScale p₀ β lam ^ (-2 : ℝ))
    (hK0 : ∀ᶠ N : ℕ in atTop, ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
        1 < X.card → (X.biUnion id).card = s →
        |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
          CK0 * truncationScale p₀ β lam ^ (-2 : ℝ) /
            ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (s - 1)))
    (hlow0 : ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, 2 ≤ S.card → S.card ≤ pBeta p₀ β →
      lam ^ (2 * (S.card - 1)) / (Cz * (N : ℝ) ^ (S.card - 1)) ≤
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S})
    (hlow : ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Finset.range N → 1 ≤ S.card →
      S.card ≤ pBeta p₀ β →
      lam ^ (2 * (S.card - 1)) / (Clow * (N : ℝ) ^ (S.card - 1)) ≤
        multipolePartitionFunction χ N β lam M S)
    (hret : ∀ᶠ N : ℕ in atTop, ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ BoundedUpper.goodLabels V →
        2 ≤ X.card → (X.biUnion id).card ≤ pBeta p₀ β →
        |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1))
    (hretm : ∀ᶠ N : ℕ in atTop, ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card ≤ pBeta p₀ β →
      |multipoleActivity χ N β lam M X| ≤ (2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1))
    (h20 : ∀ᶠ N : ℕ in atTop, ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
      ∀ π : Finset (Finset ℕ), IsSubpartition π →
        (∀ S ∈ π, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
        (∀ S ∈ π, S.card ≤ pBeta p₀ β) → AbsoluteUpper.ProfileBound p₀ β lam ε₀ N π →
        AbsoluteUpper.AbsoluteUpperBounds (hatActivity χ N p₀ β lam M ε₀ L V Z) π (pBeta p₀ β)
          (C20 * N * errorRate p₀ β lam))
    (hpoly : ∀ᶠ N : ℕ in atTop, ∀ π : Finset (Finset ℕ), IsSubpartition π →
      (∀ S ∈ π, S.card ≤ pBeta p₀ β) → π.card ≤ N →
      0 < polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π ∧
        |Real.log (polymerSum (pBeta p₀ β) (multipoleActivity χ N β lam M) π) +
          N * rateCluster (pBeta p₀ β) kmult (profileVec (pBeta p₀ β) N π)| ≤
          errorRate p₀ β lam * N)
    (hlogD : ∀ (N : ℕ) (π : Finset (Finset ℕ)) (K₁ K₂ : Finset (Finset ℕ) → ℝ) (B : ℝ),
      IsSubpartition π → π.card ≤ N →
      (∀ X ⊆ π, X.card ≤ 1 → K₁ X = 0) →
      (∀ X ⊆ π, Retained (pBeta p₀ β) X →
        |K₁ X| ≤ (Cs + 2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1)) →
      (∀ X ⊆ π, Retained (pBeta p₀ β) X →
        |K₂ X| ≤ (Cs + 2 * Ccoef) * (lam ^ 2 / N) ^ (X.card - 1)) →
      (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
          |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)|) →
      (∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected ∧
              ∃ i, pBeta p₀ β < ((X i).biUnion id).card),
          |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)| ≤ B) →
      0 < LowerBoundLDP.disjointSum K₁ π ∧ 0 < polymerSum (pBeta p₀ β) K₂ π ∧
        Real.log (LowerBoundLDP.disjointSum K₁ π) ≤ Real.log (polymerSum (pBeta p₀ β) K₂ π) +
          4 * Real.exp 2 *
            (∑ Y ∈ π.powerset, if Retained (pBeta p₀ β) Y then |K₁ Y - K₂ Y| else 0) + B) :
    ∀ᶠ N : ℕ in atTop, ∀ n : Fin (pBeta p₀ β) → ℕ,
      ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
      (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
        (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
      ∀ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
          (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
        ∀ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
            (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
          ∀ Z : Fin N → ℂ × ℂ, AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
            hatPartitionFunctions χ N p₀ β lam M ε₀ L V Z π *
                clusterSeriesW χ N p₀ β lam M ε₀ L V Z π ≤
              Real.exp (∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
                ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) *
                  Real.log N -
                N * rateCluster (pBeta p₀ β) kmult (fun i => (n i : ℝ) / N) +
                (Cm * (Cε + C0 + 1) * (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) +
                  4 * Real.exp 2 * (Cε * Cz ^ pBeta p₀ β + CK0 * Clow ^ pBeta p₀ β) *
                    Real.exp (pBeta p₀ β * (1 + ε₀ ^ (-alphaExponent β))) + C20 + 1) *
                  N * errorRate p₀ β lam +
                (Cm * CM * pBeta p₀ β + 4 * Real.exp 2 * (CM * Cz ^ pBeta p₀ β) *
                  Real.exp (pBeta p₀ β)) *
                  (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ)) := by
  have hRpos : 0 < truncationScale p₀ β lam ^ (-2 : ℝ) :=
    Real.rpow_pos_of_pos (Appendix.truncationScale_pos hlam) _
  have hRδ := rpow_neg_two_truncationScale_le_errorRate (p₀ := p₀) hβ hlam hlam1
  filter_upwards [h19, hM0, hK0, hlow0, hlow, hret, hretm, h20, hpoly,
    eventually_abs_msf_sub_le hχ hlam hS hRpos, eventually_ge_atTop 1]
    with N h19N hM0N hK0N hlow0N hlowN hretN hretmN h20N hpolyN hlimN hN1
  intro n _ h556
  refine good_bound hχ hN1 hlam hε₀ hε₀1 hM hRpos.le hRδ hCε hCM hC0 hCm hCM hCK0 hCz hClow hCs
    hCcoef h556 ?_ (fun S hS1 hSp => hM0N S.card hS1 hSp S rfl) hlimN hmsf ?_ ?_ hlow0N hlowN
    hretN hretmN h20N hpolyN (hlogD N)
  · intro V Z hVZ S hS hS1 hSp
    exact (h19N S.card hS1 hSp hN1 hlam V Z hVZ).1 S hS rfl
  · intro V Z hVZ X hX hXg hX2 hXp
    have hk1 : 1 ≤ (X.biUnion id).card :=
      (by omega : 1 ≤ X.card).trans (PropFiveFortyFive.card_le_card_biUnion hX)
    exact (h19N _ hk1 hXp hN1 hlam V Z hVZ).2 X hX hXg rfl
  · intro X hX hXN hX2 hXp
    have hk1 : 1 ≤ (X.biUnion id).card :=
      (by omega : 1 ≤ X.card).trans (PropFiveFortyFive.card_le_card_biUnion hX)
    exact hK0N _ hk1 hXp X hX hXN (by omega) rfl

end UpperBoundLDP

end MultipoleBKT

end
