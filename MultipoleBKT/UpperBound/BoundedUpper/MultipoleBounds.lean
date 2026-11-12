/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.External
public import MultipoleBKT.UpperBound.BoundedUpper.Inputs
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Gate
public import MultipoleBKT.LowerBound.Hierarchical.Instances

/-!
# Eqs. (5.65), (5.66) of Proposition 5.18, their hatted versions, and the block comparison

The paper: Proposition 5.18, eqs.
(5.65)–(5.66), and its proof.

* `plusPartitionFunction_bounds`: (5.65)–(5.66) for `𝖬^{+,Z}_{ε₀}` (`MultipoleBKT.plusPartitionFunction_two_sided`, Lemma A.3 for `(v^Z, τ^Z)`) and for
  `𝖬̂^{+,Z}_{ε₀} = 𝖬^{+,Z}_{ε₀} g^Z_{ε₀}` with eq. (5.101), for `1 ≤ |S| ≤ p*(β)`, `p₀`, `ε₀ ∈ (0, 1)`, `M` fixed;
* `zeroPartitionFunction_singleton`: `𝖬^0_{ε₀}({a}) = 1`;
* `block_comparison`: the comparison of ("by (5.65), (4.39) and the
  singleton bounds, for `S' ∈ X` and `s = |S'|`, `𝖬^{+,Z}_{ε₀}(S') ≥ c N^{1-s} λ^{2(s-1)}`"), in the
  form `0 < 𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)` for all `1 ≤ |S| ≤ k` with `|S| ≤ p*(β)`, uniformly
  (with the input (4.38)/(4.39) for `𝖬^0_{ε₀}`, `MXZeroBounds`).
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Multipole

variable {χ : ℂ → ℝ} {β M ε₀ : ℝ}

/-- `λ ≤ ε₀ R̄_{β,λ}` for `0 < λ ≤ min(1, ε₀)`. -/
theorem lam_le_cutoff (hβ : 2 < β) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hε₀ : 0 < ε₀)
    (hlamε : lam ≤ ε₀) (p₀ : ℕ) : lam ≤ ε₀ * truncationScale p₀ β lam := by
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have : ε₀ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le hR1
  linarith

/-- **(5.65)–(5.66) for `𝖬^{+,Z}_{ε₀}` and `𝖬̂^{+,Z}_{ε₀}`** (Proposition 5.18, the bounds on the
multipole functions and the following sentence): for `1 ≤ |S| ≤ p*(β)`, from Lemma A.3 for
`(v^Z, τ^Z)`, with eq. (5.101) for `𝖬̂^{+,Z} = 𝖬^{+,Z} g^Z`. The
threshold `λ₀` also ensures `λ ≤ min(1, ε₀)`. -/
theorem plusPartitionFunction_bounds (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) (L : ℝ)
    (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) (hM9 : 9 ≤ M) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k : ℕ}
    (hk : 1 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ min 1 ε₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        badPointsOn p₀ β lam M ε₀ V Z = V → ∀ S : Finset ℕ, S.card = k →
          (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) ∧
          (lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
              hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≤
              C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) := by
  have hβ0 : 0 ≤ β := by linarith
  have hM3 : 3 ≤ M := by linarith
  obtain ⟨C, hC, h⟩ := MultipoleBKT.plusPartitionFunction_two_sided (χ := χ) hχ hβ hk hkp hM9 L
  obtain ⟨lam₁, hlam₁, h1⟩ := h ε₀ hε₀ hε₁
  obtain ⟨Cg, hCg, hg⟩ := externalNormalization_le hχ p₀ β hβ0
  set G := Real.exp (β * (Cg * k))
  have hG : 1 ≤ G := Real.one_le_exp (by positivity)
  refine ⟨C * G, by positivity, min lam₁ (min 1 ε₀), lt_min hlam₁ (lt_min one_pos hε₀),
    min_le_right _ _, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h1 p₀ lam hlam (hlt.trans_le (min_le_left _ _))
  refine ⟨max N₀ 1, fun N hN V Z hVZ S hSk => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlamε : lam ≤ ε₀ := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hlamh := lam_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
  have hVZ' : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hVZ.symm.subset
  obtain ⟨hlo, hup⟩ := hN₀ N (le_trans (le_max_left _ _) hN) hM V Z hVZ S hSk
  have hNk : 0 < (N : ℝ) ^ (k - 1) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  have hΛ : 0 < lam ^ (2 * (k - 1)) := pow_pos hlam _
  have hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
    lt_of_lt_of_le (by positivity) hlo
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  have hg1 := one_le_externalNormalization hχ hlam hε₀ hN1 hlamh hM hM3 hVZ' hSne hpos
  have hg2 := hg lam M ε₀ L V Z hlam hε₀ hN1 hlamh hM hM3 hVZ' S hpos
  rw [hSk] at hg2
  have hlo' : lam ^ (2 * (k - 1)) / (C * G * (N : ℝ) ^ (k - 1)) ≤
      lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) := by
    refine div_le_div_of_nonneg_left hΛ.le (by positivity) ?_
    have : C * (N : ℝ) ^ (k - 1) ≤ C * (N : ℝ) ^ (k - 1) * G :=
      le_mul_of_one_le_right (by positivity) hG
    linarith
  have hup' : C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) ≤
      C * G * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
    refine div_le_div_of_nonneg_right ?_ hNk.le
    have : C * lam ^ (2 * (k - 1)) ≤ C * lam ^ (2 * (k - 1)) * G :=
      le_mul_of_one_le_right (by positivity) hG
    linarith
  refine ⟨⟨hlo'.trans hlo, hup.trans hup'⟩, ⟨?_, ?_⟩⟩
  · refine (hlo'.trans hlo).trans ?_
    unfold hatPartitionFunction
    exact le_mul_of_one_le_right hpos.le hg1
  · unfold hatPartitionFunction
    calc plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
          externalNormalization χ N p₀ β lam M ε₀ L V Z S
        ≤ (C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) * G :=
          mul_le_mul hup hg2 (by linarith) (by positivity)
      _ = C * G * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by ring

/-- `𝖬^0_{ε₀}({a}) = 1`: a single dipole is a multipole, with no pair weight. -/
theorem zeroPartitionFunction_singleton (hχ : IsMollifier χ) {N p₀ : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (a : ℕ) :
    zeroPartitionFunction χ N p₀ β lam M ε₀ {{a}} = 1 := by
  classical
  have h := modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN
  have := h.isProbabilityMeasure
  unfold zeroPartitionFunction
  rw [Finset.prod_singleton, h.modelPartitionFunction_eq_integral_labelField]
  have hone : ∀ c : ℕ → ℂ × ℂ, blockWeightOf β (dipoleInteraction χ lam) (fun _ => (1 : ℝ)) M lam
      {a} c = 1 := by
    intro c
    have hconn : ConnOn {a} (linkedPairs M lam c {a}) := by
      refine ⟨Finset.singleton_nonempty a, fun i hi j hj => ?_⟩
      rw [Finset.mem_singleton] at hi hj
      rw [hi, hj]
    unfold blockWeightOf
    rw [ite_eq_left hconn, pairsOn_singleton, Finset.prod_empty, Finset.prod_const_one]
    ring
  simp_rw [hone]
  rw [integral_const, smul_eq_mul, mul_one, probReal_univ]

/-- **The block comparison** (proof of Proposition 5.18): for every `k` there are
`C ≥ 1` and `λ₀ ∈ (0, min(1, ε₀)]` such that for `λ ∈ (0, λ₀)` and `N` large, every frozen
configuration and every `S` with `1 ≤ |S| ≤ k`, `|S| ≤ p*(β)`:
`0 < 𝖬^{+,Z}_{ε₀}(S)`, `0 < 𝖬^0_{ε₀}(S)` and `𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)`. -/
theorem block_comparison (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) (L : ℝ) (hε₀ : 0 < ε₀)
    (hε₁ : ε₀ < 1) (hM9 : 9 ≤ M) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hMX : MXZeroBounds χ p₀ β M ε₀) (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ min 1 ε₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        badPointsOn p₀ β lam M ε₀ V Z = V → ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ k →
          (S.card : ℕ∞) ≤ pStar β →
          0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
            0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
              C * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
  induction k with
  | zero =>
    refine ⟨1, le_rfl, min 1 ε₀, lt_min one_pos hε₀, le_rfl, fun lam _ _ => ⟨1, le_rfl,
      fun N _ V Z _ S h1 h0 _ => absurd (h1.trans h0) (by norm_num)⟩⟩
  | succ k ih =>
    obtain ⟨C', hC', lam', hlam', hlam'1, h'⟩ := ih
    by_cases hkp : ((k + 1 : ℕ) : ℕ∞) ≤ pStar β
    swap
    · refine ⟨C', hC', lam', hlam', hlam'1, fun lam hlam hlt => ?_⟩
      obtain ⟨N₀, hN₀1, hN₀⟩ := h' lam hlam hlt
      refine ⟨N₀, hN₀1, fun N hN V Z hVZ S h1 hS hSp => ?_⟩
      rcases Nat.lt_or_ge S.card (k + 1) with hlt' | hge
      · exact hN₀ N hN V Z hVZ S h1 (by omega) hSp
      · exact absurd (hS.antisymm hge ▸ hSp) hkp
    obtain ⟨C₁, hC₁, lam₁, hlam₁, hlam₁1, h1⟩ :=
      plusPartitionFunction_bounds (χ := χ) hχ hβ p₀ L hε₀ hε₁ hM9 hM (Nat.succ_pos k) hkp
    -- the bounds on `𝖬^0_{ε₀}` for the size `k + 1`
    have hzero : ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ lam₂ : ℝ, 0 < lam₂ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₂ →
        ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → ∀ S : Finset ℕ, S.card = k + 1 →
          lam ^ (2 * k) / (C₂ * (N : ℝ) ^ k) ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤ C₂ * lam ^ (2 * k) / (N : ℝ) ^ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        refine ⟨1, le_rfl, 1, one_pos, fun lam hlam _ => ⟨1, fun N hN S hS => ?_⟩⟩
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hS
        rw [zeroPartitionFunction_singleton hχ hlam hε₀ hN]
        norm_num
      · obtain ⟨C₂, hC₂, lam₂, hlam₂, h2⟩ := hMX (k + 1) (by omega) hkp
        refine ⟨max C₂ 1, le_max_right _ _, lam₂, hlam₂, fun lam hlam hlt => ?_⟩
        obtain ⟨N₂, hN₂⟩ := h2 lam hlam hlt
        refine ⟨max N₂ 1, fun N hN S hS => ?_⟩
        have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
        have hNk : 0 < (N : ℝ) ^ k := pow_pos (by linarith) k
        have hΛ : 0 ≤ lam ^ (2 * k) := pow_nonneg hlam.le _
        obtain ⟨hlo, hup⟩ := hN₂ N (le_trans (le_max_left _ _) hN) S hS
        simp only [Nat.add_sub_cancel] at hlo hup
        refine ⟨le_trans (div_le_div_of_nonneg_left hΛ (by positivity)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hNk.le)) hlo, hup.trans ?_⟩
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hΛ) hNk.le
    obtain ⟨C₂, hC₂, lam₂, hlam₂, h2⟩ := hzero
    refine ⟨max C' (C₁ * C₂), le_max_of_le_left hC', min lam' (min lam₁ lam₂),
      lt_min hlam' (lt_min hlam₁ hlam₂), (min_le_left _ _).trans hlam'1, fun lam hlam hlt => ?_⟩
    obtain ⟨N', hN'1, hN'⟩ := h' lam hlam (hlt.trans_le (min_le_left _ _))
    obtain ⟨N₁, hN₁⟩ := h1 lam hlam (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    obtain ⟨N₂, hN₂⟩ := h2 lam hlam (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    refine ⟨max N' (max N₁ N₂), le_trans hN'1 (le_max_left _ _), fun N hN V Z hVZ S h1S hS hSp => ?_⟩
    rcases Nat.lt_or_ge S.card (k + 1) with hlt' | hge
    · obtain ⟨a, b, c⟩ := hN' N (le_trans (le_max_left _ _) hN) V Z hVZ S h1S (by omega) hSp
      refine ⟨a, b, c.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) a.le)⟩
    · have hSk : S.card = k + 1 := le_antisymm hS hge
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hN'1 (le_trans (le_max_left _ _) hN)
      have hNk : 0 < (N : ℝ) ^ k := pow_pos (by linarith) k
      have hΛ : 0 < lam ^ (2 * k) := pow_pos hlam _
      obtain ⟨⟨hlo, -⟩, -⟩ := hN₁ N (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hN)
        V Z hVZ S hSk
      obtain ⟨hzlo, hzup⟩ := hN₂ N (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hN) S hSk
      have hC₁0 : 0 < C₁ := hC₁
      have hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
        lt_of_lt_of_le (by positivity) hlo
      refine ⟨hpos, lt_of_lt_of_le (by positivity) hzlo, ?_⟩
      calc zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤ C₂ * lam ^ (2 * k) / (N : ℝ) ^ k := hzup
        _ = (C₁ * C₂) * (lam ^ (2 * k) / (C₁ * (N : ℝ) ^ k)) := by
          field_simp
        _ ≤ (C₁ * C₂) * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
        _ ≤ max C' (C₁ * C₂) * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpos.le

end BoundedUpper

end UpperBound

end MultipoleBKT

end
