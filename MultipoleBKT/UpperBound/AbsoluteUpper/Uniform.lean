/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.FullSeries
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Gate
public import MultipoleBKT.Main.TheoremTwo.Parameters

/-!
# The bounded-cluster estimates, uniformly over the cluster sizes `k ≤ Q`

For the proof of Proposition 5.20, the estimates on bounded clusters are needed for the finitely many sizes up to a
fixed `Q`, for one `λ₀` and one `N₀(λ)`:

* eq. (5.67) for `|V_X| = k ≤ Q` (input `KPlusBoundInput`);
* eq. (4.38) for `𝖬^0_{ε₀}(S)`, `2 ≤ |S| ≤ p(β)` (`MultipoleBKT.BoundedLowerEps.zeroPartitionFunction_two_sided`, with a constant independent of
  `ε₀`);
* `𝖬^{+,Z}_{ε₀}(S) > 0` for `1 ≤ |S| ≤ p(β)`, from eq. (5.65) (`MultipoleBKT.plusPartitionFunction_two_sided`), the hypothesis under which
  eq. (5.101) applies.

`uniform_bounded_estimates` packages them.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

open Hierarchical

/-- Two statements holding for `λ` small and then `N` large hold together. -/
theorem exists_lam_N_and {P Q : ℝ → ℕ → Prop}
    (hP : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P lam N)
    (hQ : ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Q lam N) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P lam N ∧ Q lam N := by
  obtain ⟨l₁, hl₁, h₁⟩ := hP
  obtain ⟨l₂, hl₂, h₂⟩ := hQ
  refine ⟨min l₁ l₂, lt_min hl₁ hl₂, fun lam hlam hlt => ?_⟩
  obtain ⟨N₁, hN₁⟩ := h₁ lam hlam (hlt.trans_le (min_le_left _ _))
  obtain ⟨N₂, hN₂⟩ := h₂ lam hlam (hlt.trans_le (min_le_right _ _))
  exact ⟨max N₁ N₂, fun N hN => ⟨hN₁ N ((le_max_left _ _).trans hN),
    hN₂ N ((le_max_right _ _).trans hN)⟩⟩

/-- A statement that holds trivially for `λ` small and `N` large. -/
theorem exists_lam_N_of_forall {P : ℝ → ℕ → Prop} (h : ∀ lam N, P lam N) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P lam N :=
  ⟨1, one_pos, fun lam _ _ => ⟨0, fun N _ => h lam N⟩⟩

/-- **The bounded-cluster estimates for the sizes `k ≤ Q`**, with one `λ₀` and one `N₀(λ)`: for
`M > max(20, 3^{p(β)})` and `ε₀ ∈ (0, 1)`, under eq. (5.67) (`KPlusBoundInput`), there are
constants `C_k ≥ 0` (`k ≤ Q`) and `C_m ≥ 1` such that for `λ` small and `N` large:
eq. (5.67) holds with `C_k` for `1 ≤ |V_X| = k ≤ Q`; `𝖬^0_{ε₀}(S) ≥ λ^{2(|S|-1)} /
(C_m N^{|S|-1})` for `2 ≤ |S| ≤ p(β)`; and `𝖬^{+,Z}_{ε₀}(S) > 0` for `1 ≤ |S| ≤ p(β)` and every
`(V, Z)` with `I_bad^V(Z) = V`. -/
theorem uniform_bounded_estimates {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    {β : ℝ} (hβ : 2 < β) (L : ℝ) (hKplus : KPlusBoundInput χ p₀ β L) {M : ℝ} (hM : 20 < M)
    (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) (Q : ℕ) :
    ∃ CK : ℕ → ℝ, (∀ k, 0 ≤ CK k) ∧ ∃ Cm : ℝ, 1 ≤ Cm ∧
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∀ k, 1 ≤ k → k ≤ Q → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
            IsFrozenConfig p₀ β lam M ε₀ V Z →
            ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty →
              (∀ S ∈ X, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
              (∀ S ∈ X, S.card ≤ pBeta p₀ β) → (X.biUnion id).card = k →
              |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
                CK k * Appendix.gammaBeta p₀ β lam k /
                  (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1))) ∧
          (∀ S : Finset ℕ, 2 ≤ S.card → S.card ≤ pBeta p₀ β →
            lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤
              zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) ∧
          (∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
            ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ pBeta p₀ β →
              0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) := by
  set p := pBeta p₀ β
  have hM9 : (9 : ℝ) ≤ M := by linarith
  -- the constants
  choose! CK hCK hKrest using hKplus M hM hMp ε₀ hε₀ hε₁
  have hZ0 : ∀ k : ℕ, 2 ≤ k → k ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ (p₀' : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
                zeroPartitionFunction χ N p₀' β lam M ε₀ {S} ∧
              zeroPartitionFunction χ N p₀' β lam M ε₀ {S} ≤
                C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := fun k hk hkp =>
    BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ hk
      (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp) hM
  choose! Cz hCz hZrest using hZ0
  set Cm : ℝ := 1 + ∑ k ∈ range (p + 1), max (Cz k) 0 with hCm
  have hCm1 : 1 ≤ Cm := le_add_of_nonneg_right (sum_nonneg fun _ _ => le_max_right _ _)
  have hCzm : ∀ k, k ≤ p → Cz k ≤ Cm := fun k hk => by
    have : max (Cz k) 0 ≤ ∑ k ∈ range (p + 1), max (Cz k) 0 :=
      single_le_sum (f := fun k => max (Cz k) 0) (fun _ _ => le_max_right _ _)
        (mem_range.2 (Nat.lt_succ_of_le hk))
    linarith [le_max_left (Cz k) 0]
  refine ⟨fun k => max (CK k) 0, fun k => le_max_right _ _, Cm, hCm1, ?_⟩
  -- the statements for each size
  have hk : ∀ k ≤ max Q p, ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (1 ≤ k → k ≤ Q → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
            IsFrozenConfig p₀ β lam M ε₀ V Z →
            ∀ X : Finset (Finset ℕ), IsSubpartition X → X.Nonempty →
              (∀ S ∈ X, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
              (∀ S ∈ X, S.card ≤ p) → (X.biUnion id).card = k →
              |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
                max (CK k) 0 * Appendix.gammaBeta p₀ β lam k /
                  (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ (k - 1))) ∧
        ((2 ≤ k → k ≤ p → ∀ S : Finset ℕ, S.card = k →
            lam ^ (2 * (k - 1)) / (Cm * (N : ℝ) ^ (k - 1)) ≤
              zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) ∧
          (1 ≤ k → k ≤ p → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
            badPointsOn p₀ β lam M ε₀ V Z = V → ∀ S : Finset ℕ, S.card = k →
              0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S)) := by
    intro k _
    refine exists_lam_N_and ?_ (exists_lam_N_and ?_ ?_)
    · -- (5.67)
      by_cases hk1 : 1 ≤ k
      · obtain ⟨lam₀, hlam₀, h⟩ := hKrest k hk1
        refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
        refine ⟨N₀, fun N hN _ _ V Z hVZ X hX hXne hXg hXp hXk => ?_⟩
        refine (hN₀ N hN V Z hVZ X hX hXne hXg hXp hXk).trans ?_
        have hg := SmallIntegral.gammaBeta_nonneg hlam p₀ β k
        have hz := zeroPartitionFunction_nonneg χ N p₀ β lam M ε₀ X
        gcongr
        exact le_max_left _ _
      · exact exists_lam_N_of_forall fun _ _ h => absurd h hk1
    · -- (4.38) for `𝖬^0_{ε₀}`
      by_cases hkk : 2 ≤ k ∧ k ≤ p
      · obtain ⟨lam₀, hlam₀, -, h⟩ := hZrest k hkk.1 hkk.2 ε₀ hε₀ hε₁
        refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h p₀ lam hlam hlt
        refine ⟨N₀, fun N hN _ _ S hS => ?_⟩
        refine le_trans ?_ (hN₀ N hN S hS).1
        have hNk : (0 : ℝ) ≤ (N : ℝ) ^ (k - 1) := by positivity
        rcases hNk.eq_or_lt with h0 | h0
        · rw [← h0, mul_zero, div_zero, mul_zero, div_zero]
        · refine div_le_div_of_nonneg_left (by positivity)
            (mul_pos (hCz k hkk.1 hkk.2) h0) ?_
          exact mul_le_mul_of_nonneg_right (hCzm k hkk.2) h0.le
      · exact exists_lam_N_of_forall fun _ _ h2 hkp => absurd ⟨h2, hkp⟩ hkk
    · -- `𝖬^{+,Z}_{ε₀}(S) > 0`
      by_cases hkk : 1 ≤ k ∧ k ≤ p
      · obtain ⟨Cp, hCp, h⟩ := plusPartitionFunction_two_sided (χ := χ) hχ hβ hkk.1
          (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkk.2) hM9 L
        obtain ⟨lam₀, hlam₀, h'⟩ := h ε₀ hε₀ hε₁
        refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h' p₀ lam hlam hlt
        refine ⟨max N₀ 1, fun N hN _ _ V Z hVZ S hS => ?_⟩
        have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
        have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
        refine lt_of_lt_of_le ?_ (hN₀ N ((le_max_left _ _).trans hN) hMp V Z hVZ S hS).1
        positivity
      · exact exists_lam_N_of_forall fun _ _ h1 hkp => absurd ⟨h1, hkp⟩ hkk
  obtain ⟨lam₀, hlam₀, hall⟩ := exists_lam_N_forall_le (max Q p) hk
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hall lam hlam hlt
  refine ⟨N₀, fun N hN => ⟨?_, ?_, ?_⟩⟩
  · intro k hk1 hkQ
    exact (hN₀ N hN k (hkQ.trans (le_max_left _ _))).1 hk1 hkQ
  · intro S h2 hSp
    exact (hN₀ N hN S.card (hSp.trans (le_max_right _ _))).2.1 h2 hSp S rfl
  · intro V Z hVZ S h1 hSp
    exact (hN₀ N hN S.card (hSp.trans (le_max_right _ _))).2.2 h1 hSp V Z hVZ S rfl

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
