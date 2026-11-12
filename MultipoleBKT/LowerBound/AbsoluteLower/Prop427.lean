/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Transfer
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Minus
public import MultipoleBKT.LowerBound.LowerBoundLDP.Inputs

/-!
# Proposition 4.27: absolute convergence of the cluster expansion series

The proof of Proposition 4.27. For `β > 2`, a mollifier `χ`, `p₀ ≥ 1` and `L ∈ ℝ`: for `M` large, `ε₀` small,
`λ` small and `N` large, for every partition `π` of `[N]` into blocks of size at most `p(β)`
satisfying (4.22) (`#_k π ≤ ε₀^{-α(β)} N λ^{2(k-1)}`, `2 ≤ k ≤ p(β)`), the activity `𝖪^-_{ε₀}`
satisfies (4.55), the full connected series is absolutely convergent, and (4.56) holds, with the
bound `C N δ_{β,λ}` (`prop427Statement_holds`, the statement
`MultipoleBKT.LowerBoundLDP.Prop427Statement` used by the proof of Proposition 4.62).

**Proof.** `MultipoleBKT.AbsoluteLower.absolute_core` (Lemma 4.59 and the
Kotecký–Preiss argument for an abstract activity) applied to `𝖪^-_{ε₀}`, with the large-cluster
bound `MultipoleBKT.AbsoluteLower.minus_large_bound` (Lemmas 4.54–4.57 and 4.59) and, for the
bounded clusters `|V_X| ≤ q`, eq. (4.40) of Proposition 4.23
(`MultipoleBKT.BoundedLowerEps.minusActivity_bound`), for the finitely many sizes
`k ≤ q` at once. Here `q = max q₀ p(β)`, with the written `q₀` from
(4.120). The boundary size `k = q₀` uses the
bounded estimate as in (4.128) in the proof of Lemma 4.59.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Hierarchical
open UpperBound.AbsoluteUpper (bigClusterTerm connectedTerm exists_lam_N_forall_le)

open scoped Classical in
/-- **Proposition 4.27** in the form
`MultipoleBKT.LowerBoundLDP.Prop427Statement` (for every `L`, in particular `L = β/64`). -/
theorem prop427Statement_holds {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    {β : ℝ} (hβ : 2 < β) (L : ℝ) : LowerBoundLDP.Prop427Statement χ p₀ β L := by
  obtain ⟨M₀, hM₀, hlarge⟩ := minus_large_bound (χ := χ) hχ hβ hp₀ L
  refine ⟨M₀, fun M hM => ?_⟩
  have hM20 : 20 < M := hM₀.trans_le hM
  have hM1 : 1 ≤ M := by linarith
  obtain ⟨B, hB1, hB⟩ := hlarge M hM
  set p := pBeta p₀ β with hp
  set q := max (qZero p₀ β) p with hq
  obtain ⟨ε₁, hε₁, hε₁1, hcore⟩ := absolute_core hχ hp₀ hβ hM20 hB1 (q := q) (le_max_right _ _)
  refine ⟨ε₁, hε₁, fun ε₀ hε₀ hε₀₁ => ?_⟩
  have hε₀1 : ε₀ < 1 := hε₀₁.trans_le hε₁1
  -- the bounded clusters: (4.40) for the sizes `k ≤ q`
  have hK : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Finset (Finset ℕ), IsSubpartition X → 1 < X.card →
        (X.biUnion id).card = k →
        |minusActivity χ N p₀ β lam M ε₀ L X| ≤
          C * Appendix.gammaBeta p₀ β lam k /
            (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1)) := fun k => by
    obtain ⟨C, hC, lam₀, hlam₀, h⟩ := BoundedLowerEps.minusActivity_bound hχ hβ k hM1 L hε₀ hε₀1
    exact ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => h p₀ lam hlam hlt⟩
  choose CK hCK lamK hlamK hKb using hK
  set Cb : ℝ := ∑ k ∈ range (q + 1), CK k with hCb
  have hCb0 : 0 ≤ Cb := sum_nonneg fun k _ => (hCK k).le
  have hCKb : ∀ k ≤ q, CK k ≤ Cb := fun k hk =>
    single_le_sum (f := CK) (fun k _ => (hCK k).le) (mem_range.2 (Nat.lt_succ_of_le hk))
  obtain ⟨lamU, hlamU, hU⟩ := exists_lam_N_forall_le (P := fun k lam N =>
    ∀ X : Finset (Finset ℕ), IsSubpartition X → 1 < X.card → (X.biUnion id).card = k →
      |minusActivity χ N p₀ β lam M ε₀ L X| ≤
        CK k * Appendix.gammaBeta p₀ β lam k /
          (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1))) q
    fun k _ => ⟨lamK k, hlamK k, fun lam hlam hlt => hKb k lam hlam hlt⟩
  obtain ⟨C', hC', lamc, hlamc, -, hcore'⟩ := hcore ε₀ hε₀ hε₀₁ Cb hCb0
  obtain ⟨lamB, hlamB, hBl⟩ := hB ε₀ hε₀ hε₀1
  refine ⟨C', hC', min lamc (min lamB lamU), lt_min hlamc (lt_min hlamB hlamU),
    fun lam hlam hlt => ?_⟩
  have hltc : lam < lamc := hlt.trans_le (min_le_left _ _)
  have hltB : lam < lamB := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hltU : lam < lamU := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N₀, hN₀⟩ := hcore' lam hlam hltc
  obtain ⟨N₁, hN₁⟩ := hBl lam hlam hltB
  obtain ⟨N₂, hN₂⟩ := hU lam hlam hltU
  refine ⟨max N₀ (max N₁ N₂), fun N hN π hπ hprof => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN2 : N₂ ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  unfold boundedBlockPartitions at hπ
  obtain ⟨-, hπs, hπV, hπp⟩ := mem_filter.1 hπ
  have hπN : ∀ S ∈ π, S ⊆ Finset.range N := fun S hS => by
    rw [← hπV]
    exact subset_biUnion_of_mem id hS
  have hsub : ∀ X ⊆ π, IsSubpartition X := fun X hX =>
    SmallIntegral.isSubpartition_of_subset hπs hX
  obtain ⟨h1, h2, -, h4⟩ := hN₀ N hN0 π hπs hπN hπp
    (fun k hk2 hkp => by
      have := hprof k hk2 hkp
      rwa [mul_right_comm] at this)
    (minusActivity χ N p₀ β lam M ε₀ L)
    (fun X _ hX1 => modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ hX1)
    (fun X hX h2 hqk => by
      -- Lemma 4.59, Step 2, proof of Lemma 4.59: only sizes above `q₀` use Lemma 4.59.
      have hq₀k : qZero p₀ β < (X.biUnion id).card :=
        lt_of_le_of_lt (le_max_left _ _) hqk
      exact hN₁ N hN1 X (hsub X hX) (fun S hS => hπp S (hX hS))
        ((largeThreshold_le_qZero p₀ β).trans_lt hq₀k))
    (fun X hX h2 hkq => by
      refine (hN₂ N hN2 _ hkq X (hsub X hX) (by omega) rfl).trans ?_
      have hγ := SmallIntegral.gammaBeta_nonneg hlam p₀ β (X.biUnion id).card
      have hZ0 := UpperBound.AbsoluteUpper.zeroPartitionFunction_nonneg χ N p₀ β lam M ε₀ X
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hCKb _ hkq) hγ)
        (by positivity))
  exact ⟨h1, h2, h4⟩

end AbsoluteLower

end MultipoleBKT

end
