/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Inputs
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.RateFunction.Uniform
public import MultipoleBKT.Gibbs.Activities

/-!
# Theorem 2 from the gates: item (1), the coefficient bounds

Item (1) of Theorem 2:
the limits (2.45), (2.46) exist (this is the input `LimitingActivitiesExist`), and inserting the
bounds of Proposition 4.23 in the normalized activities gives (2.47) and
(2.48):

* `C⁻¹ λ^{2(k-1)} ≤ 𝗆(k) ≤ C λ^{2(k-1)}` for `2 ≤ k ≤ p` (`MultipoleBKT.TheoremTwo.msf_bound`),
 from (4.38)–(4.39) for `S = {0, …, k-1}`;
* `|𝗄^mult((#_k X)_k)| ≤ C λ^{2(|X|-1)}` for subpartitions `X` with `|V_X| ≤ p`
 (`kmult_bound`), from (4.40) and the lower bound (4.38) on each block (`𝖬(S) = 1` for
  singletons); for `|X| ≤ 1`, `𝖪^mult(X) = 0` and the limit is `0`.

`𝗆(1) = 1` since `𝖬({i}) = 1` (`msf_one`). Finally the per-index constants are made uniform
(`coefficient_bounds_uniform`), as needed by the analysis of the rate function.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremTwo

/-! ### The gate (4.38)–(4.40) at a fixed `M` -/

/-- (4.38)–(4.39) of Proposition 4.23 for one size `k`, at a fixed `M`. -/
def MsfGateAt (χ : ℂ → ℝ) (β M : ℝ) (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
        lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ multipolePartitionFunction χ N β lam M S ∧
        multipolePartitionFunction χ N β lam M S ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)

/-- (4.40) of Proposition 4.23 for one size `k = |V_X|`, at a fixed `M`. -/
def KmultGateAt (χ : ℂ → ℝ) (β M : ℝ) (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
        1 < X.card → (X.biUnion id).card = k →
        |multipoleActivity χ N β lam M X| ≤
          C * lam ^ (2 * (k - 1)) /
            ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1))

/-- The limits (2.45) of Theorem 2 item (1), at a fixed `M`. -/
def MsfLimits (χ : ℂ → ℝ) (β M : ℝ) (msf : ℝ → ℕ → ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → lam < 1 →
    ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ =>
          (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
        (𝓝 (msf lam S.card))

/-- The limits (2.46) of Theorem 2 item (1), at a fixed `M`. -/
def KmultLimits (χ : ℂ → ℝ) (β M : ℝ) (kmult : ℝ → (ℕ →₀ ℕ) → ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam → lam < 1 →
    ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
      Tendsto (fun N : ℕ =>
          (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
        (𝓝 (kmult lam (blockProfile X)))

variable {χ : ℂ → ℝ} {β M : ℝ} {msf : ℝ → ℕ → ℝ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}

/-! ### `𝗆(1) = 1` -/

theorem msf_one (hχ : IsMollifier χ) (hβ : 2 < β) (hS : MsfLimits χ β M msf) {lam : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) : msf lam 1 = 1 := by
  have h1 : ((({0} : Finset ℕ).card : ℕ) : ℕ∞) ≤ pStar β := by
    rw [Finset.card_singleton]
    exact (Appendix.le_pStar_iff le_rfl).mpr (by unfold transitionBeta; norm_num; linarith)
  have hT := hS lam hlam hlam1 {0} (by simp) h1
  rw [Finset.card_singleton] at hT
  have hev : (fun N : ℕ => (N : ℝ) ^ (1 - 1) * multipolePartitionFunction χ N β lam M {0})
      =ᶠ[atTop] fun _ => 1 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [multipolePartitionFunction_singleton hχ hlam β M hN 0, Nat.sub_self, pow_zero, mul_one]
  exact tendsto_nhds_unique (hT.congr' hev) tendsto_const_nhds

/-! ### (2.47) -/

/-- **(2.47)** for one `k ≥ 2`, from (4.38)–(4.39) and the limit (2.45). -/
theorem msf_bound {k : ℕ} (hk2 : 2 ≤ k) (hkS : (k : ℕ∞) ≤ pStar β) (hG : MsfGateAt χ β M k)
    (hS : MsfLimits χ β M msf) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      C⁻¹ * lam ^ (2 * (k - 1)) ≤ msf lam k ∧ msf lam k ≤ C * lam ^ (2 * (k - 1)) := by
  obtain ⟨C, hC, lam₀, hlam₀, hlam₀1, hb⟩ := hG
  refine ⟨C, hC, lam₀, hlam₀, hlam₀1, fun lam hlam hlaml => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hb lam hlam hlaml
  have hcard : (Finset.range k).card = k := Finset.card_range k
  have hT := hS lam hlam (lt_of_lt_of_le hlaml hlam₀1) (Finset.range k) (by omega)
    (by rw [hcard]; exact hkS)
  rw [hcard] at hT
  have hev : ∀ᶠ N : ℕ in atTop,
      C⁻¹ * lam ^ (2 * (k - 1)) ≤ (N : ℝ) ^ (k - 1) *
          multipolePartitionFunction χ N β lam M (Finset.range k) ∧
        (N : ℝ) ^ (k - 1) * multipolePartitionFunction χ N β lam M (Finset.range k) ≤
          C * lam ^ (2 * (k - 1)) := by
    filter_upwards [eventually_ge_atTop (max N₀ (max k 1))] with N hN
    have hN₀N : N₀ ≤ N := (le_max_left _ _).trans hN
    have hkN : k ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
    have hsub : Finset.range k ⊆ Finset.range N := Finset.range_subset_range.mpr hkN
    obtain ⟨hlo, hhi⟩ := hN₀ N hN₀N (Finset.range k) hsub hcard
    have hNpos : (0 : ℝ) < (N : ℝ) ^ (k - 1) := by
      have : (0 : ℝ) < N := by exact_mod_cast hN1
      positivity
    constructor
    · rw [div_le_iff₀ (by positivity)] at hlo
      rw [inv_mul_le_iff₀ hC]
      linarith [hlo, show (N : ℝ) ^ (k - 1) * multipolePartitionFunction χ N β lam M
        (Finset.range k) * C = multipolePartitionFunction χ N β lam M (Finset.range k) *
          (C * (N : ℝ) ^ (k - 1)) by ring]
    · rw [le_div_iff₀ hNpos] at hhi
      linarith [hhi, show (N : ℝ) ^ (k - 1) * multipolePartitionFunction χ N β lam M
        (Finset.range k) = multipolePartitionFunction χ N β lam M (Finset.range k) *
          (N : ℝ) ^ (k - 1) by ring]
  exact ⟨ge_of_tendsto hT (hev.mono fun _ h => h.1), le_of_tendsto hT (hev.mono fun _ h => h.2)⟩

/-! ### Uniform lower bound on `𝖬(S)` for `1 ≤ |S| ≤ p` -/

/-- From (4.38) for each `2 ≤ k ≤ p` and `𝖬({i}) = 1`: one `C`, `λ₀` for all sizes. -/
theorem msf_lower_uniform (hχ : IsMollifier χ) {p : ℕ}
    (hG : ∀ k ∈ Finset.Icc 2 p, MsfGateAt χ β M k) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Finset.range N → 1 ≤ S.card → S.card ≤ p →
        lam ^ (2 * (S.card - 1)) / (C * (N : ℝ) ^ (S.card - 1)) ≤
          multipolePartitionFunction χ N β lam M S := by
  let Q : ℕ → ℝ → ℝ → Prop := fun k C l => 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam < l →
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ Finset.range N → S.card = k →
      lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ multipolePartitionFunction χ N β lam M S
  have hmono : ∀ k C C' l l', Q k C l → C ≤ C' → 0 < l' → l' ≤ l → Q k C' l' := by
    intro k C C' l l' hQ hCC' _ hll'
    refine ⟨hQ.1.trans_le hCC', fun lam hlam hlaml => ?_⟩
    filter_upwards [hQ.2 lam hlam (lt_of_lt_of_le hlaml hll'), eventually_ge_atTop 1]
      with N hN hN1 S hS hSk
    refine le_trans ?_ (hN S hS hSk)
    have hNpos : (0 : ℝ) < (N : ℝ) ^ (k - 1) := by
      have : (0 : ℝ) < N := by exact_mod_cast hN1
      positivity
    have hl : 0 ≤ lam ^ (2 * (k - 1)) := by positivity
    exact div_le_div_of_nonneg_left hl (mul_pos hQ.1 hNpos)
      (mul_le_mul_of_nonneg_right hCC' hNpos.le)
  have hT : ∀ k ∈ Finset.Icc 2 p, ∃ C : ℝ, 0 < C ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ Q k C l := by
    intro k hk
    obtain ⟨C, hC, l, hl, hl1, hb⟩ := hG k hk
    refine ⟨C, hC, l, hl, hl1, hC, fun lam hlam hlaml => ?_⟩
    obtain ⟨N₀, hN₀⟩ := hb lam hlam hlaml
    filter_upwards [eventually_ge_atTop N₀] with N hN S hS hSk
    exact (hN₀ N hN S hS hSk).1
  obtain ⟨C, hC, l, hl, hl1, hQ⟩ := exists_uniform_constants (Finset.Icc 2 p) Q hmono hT
  refine ⟨max C 1, lt_max_of_lt_right one_pos, l, hl, hl1, fun lam hlam hlaml => ?_⟩
  have hall : ∀ᶠ N : ℕ in atTop, ∀ k ∈ Finset.Icc 2 p, ∀ S : Finset ℕ, S ⊆ Finset.range N →
      S.card = k →
      lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤ multipolePartitionFunction χ N β lam M S :=
    (Filter.eventually_all_finset _).mpr fun k hk => (hQ k hk).2 lam hlam hlaml
  filter_upwards [hall, eventually_ge_atTop 1] with N hN hN1 S hS hS1 hSp
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (S.card - 1) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  have hl : 0 ≤ lam ^ (2 * (S.card - 1)) := by positivity
  rcases Nat.lt_or_ge S.card 2 with h2 | h2
  · have hS1' : S.card = 1 := by omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS1'
    rw [multipolePartitionFunction_singleton hχ hlam β M hN1 i, Finset.card_singleton,
      Nat.sub_self, pow_zero, pow_zero, mul_one]
    rw [div_le_one (lt_max_of_lt_right one_pos)]
    exact le_max_right _ _
  · refine le_trans ?_ (hN S.card (Finset.mem_Icc.mpr ⟨h2, hSp⟩) S hS rfl)
    exact div_le_div_of_nonneg_left hl (mul_pos hC hNpos)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hNpos.le)

/-! ### (2.48) -/

theorem sum_card_eq_card_biUnion {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    ∑ S ∈ X, S.card = (X.biUnion id).card := by
  rw [Finset.card_biUnion]
  · rfl
  · intro S hS T hT hST
    exact hX.2 hS hT hST

theorem sum_card_sub_one {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    ∑ S ∈ X, (S.card - 1) + X.card = (X.biUnion id).card := by
  rw [← sum_card_eq_card_biUnion hX, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S hS => ?_
  have := Finset.card_pos.mpr (hX.1 S hS)
  omega

theorem zpow_card_sub_one {x : ℝ} {X : Finset (Finset ℕ)} (hX : 1 ≤ X.card) :
    x ^ ((X.card : ℤ) - 1) = x ^ (X.card - 1) := by
  rw [show ((X.card : ℤ) - 1) = ((X.card - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hX]; ring,
    zpow_natCast]

theorem zpow_two_mul_card_sub_one {x : ℝ} {X : Finset (Finset ℕ)} (hX : 1 ≤ X.card) :
    x ^ (2 * ((X.card : ℤ) - 1)) = x ^ (2 * (X.card - 1)) := by
  rw [show 2 * ((X.card : ℤ) - 1) = ((2 * (X.card - 1) : ℕ) : ℤ) by
    push_cast [Nat.cast_sub hX]; ring, zpow_natCast]

/-- The product of the lower bounds (4.38) over the blocks of `X`. -/
theorem prod_lower_eq (lam N C : ℝ) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    ∏ S ∈ X, lam ^ (2 * (S.card - 1)) / (C * N ^ (S.card - 1)) =
      lam ^ (2 * ((X.biUnion id).card - X.card)) /
        (C ^ X.card * N ^ ((X.biUnion id).card - X.card)) := by
  have hsum : ∑ S ∈ X, (S.card - 1) = (X.biUnion id).card - X.card := by
    have := sum_card_sub_one hX
    omega
  have h1 : ∏ S ∈ X, lam ^ (2 * (S.card - 1)) = lam ^ (2 * ((X.biUnion id).card - X.card)) := by
    rw [Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, hsum]
  have h2 : ∏ S ∈ X, N ^ (S.card - 1) = N ^ ((X.biUnion id).card - X.card) := by
    rw [Finset.prod_pow_eq_pow_sum, hsum]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, h1, h2]

/-- **(2.48)** for one subpartition `X` with `|V_X| ≤ p`, from (4.38), (4.40), `𝖬({i}) = 1`
and the limit (2.46). -/
theorem kmult_bound (hχ : IsMollifier χ) {p : ℕ} (hpS : (p : ℕ∞) ≤ pStar β)
    (hG1 : ∀ k ∈ Finset.Icc 2 p, MsfGateAt χ β M k) (hG2 : ∀ k, k ≤ p → KmultGateAt χ β M k)
    (hlim : KmultLimits χ β M kmult) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hV : (X.biUnion id).card ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      |kmult lam (blockProfile X)| ≤ C * lam ^ (2 * ((X.card : ℤ) - 1)) := by
  have hXS : ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β := by
    rw [sum_card_eq_card_biUnion hX]
    exact (Nat.cast_le.mpr hV).trans hpS
  rcases Nat.lt_or_ge X.card 2 with hcard | hcard
  · refine ⟨1, one_pos, 1, one_pos, le_rfl, fun lam hlam hlam1 => ?_⟩
    have hT := hlim lam hlam hlam1 X hX hXS
    have h0 : (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) =
        fun _ => 0 := by
      funext N
      rw [multipoleActivity_eq_zero_of_card_le_one χ N β lam M (by omega), mul_zero]
    rw [h0] at hT
    rw [tendsto_nhds_unique hT tendsto_const_nhds, abs_zero, one_mul]
    exact (zpow_pos hlam _).le
  · set k := (X.biUnion id).card
    set m := X.card
    have hkm : m ≤ k := by
      have := sum_card_sub_one hX
      omega
    obtain ⟨C₁, hC₁, l₁, hl₁, hl₁1, hlow⟩ := msf_lower_uniform (M := M) hχ hG1
    obtain ⟨C₂, hC₂, l₂, hl₂, -, hK⟩ := hG2 k hV
    refine ⟨C₂ * C₁ ^ m, by positivity, min l₁ l₂, lt_min hl₁ hl₂, (min_le_left _ _).trans hl₁1,
      fun lam hlam hlaml => ?_⟩
    have hlam1 : lam < 1 := lt_of_lt_of_le hlaml ((min_le_left _ _).trans hl₁1)
    obtain ⟨N₀, hN₀⟩ := hK lam hlam (lt_of_lt_of_le hlaml (min_le_right _ _))
    have hT := (hlim lam hlam hlam1 X hX hXS).abs
    rw [zpow_two_mul_card_sub_one (by omega : 1 ≤ m)]
    obtain ⟨n₀, hn₀⟩ := Finset.exists_nat_subset_range (X.biUnion id)
    have hev : ∀ᶠ N : ℕ in atTop,
        |(N : ℝ) ^ ((m : ℤ) - 1) * multipoleActivity χ N β lam M X| ≤
          C₂ * C₁ ^ m * lam ^ (2 * (m - 1)) := by
      filter_upwards [hlow lam hlam (lt_of_lt_of_le hlaml (min_le_left _ _)),
        eventually_ge_atTop (max N₀ (max n₀ 1))] with N hlowN hN
      have hN₀N : N₀ ≤ N := (le_max_left _ _).trans hN
      have hn₀N : n₀ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
      have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
      have hVN : X.biUnion id ⊆ Finset.range N :=
        hn₀.trans (Finset.range_subset_range.mpr hn₀N)
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      -- the lower bound on the product of the blocks
      set b : ℝ := lam ^ (2 * (k - m)) / (C₁ ^ m * (N : ℝ) ^ (k - m)) with hb_def
      have hbpos : 0 < b := by positivity
      have hab : b ≤ ∏ S ∈ X, multipolePartitionFunction χ N β lam M S := by
        rw [hb_def, ← prod_lower_eq lam N C₁ hX]
        refine Finset.prod_le_prod₀ (fun S _ => by positivity) fun S hS => ?_
        have hSV : S ⊆ X.biUnion id := Finset.subset_biUnion_of_mem id hS
        exact hlowN S (hSV.trans hVN) (Finset.card_pos.mpr (hX.1 S hS))
          ((Finset.card_le_card hSV).trans hV)
      have hKN := hN₀ N hN₀N X hX hVN (by omega) rfl
      have hNk : (0 : ℝ) < (N : ℝ) ^ (k - 1) := by positivity
      have hstep : |multipoleActivity χ N β lam M X| ≤
          C₂ * lam ^ (2 * (k - 1)) / (b * (N : ℝ) ^ (k - 1)) := by
        refine hKN.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_right hab hNk.le))
      have hk1 : k - 1 = (k - m) + (m - 1) := by omega
      have hkey : C₂ * lam ^ (2 * (k - 1)) / (b * (N : ℝ) ^ (k - 1)) =
          C₂ * C₁ ^ m * lam ^ (2 * (m - 1)) / (N : ℝ) ^ (m - 1) := by
        rw [hb_def, hk1, mul_add, pow_add, pow_add]
        field_simp
      rw [zpow_card_sub_one (by omega : 1 ≤ X.card), abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) ^ (m - 1))]
      rw [hkey] at hstep
      calc (N : ℝ) ^ (m - 1) * |multipoleActivity χ N β lam M X|
          ≤ (N : ℝ) ^ (m - 1) * (C₂ * C₁ ^ m * lam ^ (2 * (m - 1)) / (N : ℝ) ^ (m - 1)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = C₂ * C₁ ^ m * lam ^ (2 * (m - 1)) := by field_simp
    exact le_of_tendsto hT hev

/-! ### Uniform constants -/

theorem MsfBound.mono {p : ℕ} {f : ℕ → ℝ} {C C' lam : ℝ} (h : MsfBound p f C lam) (hC : 0 < C)
    (hCC' : C ≤ C') (hlam : 0 ≤ lam) : MsfBound p f C' lam := by
  refine ⟨h.1, fun k hk2 hkp => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k hk2 hkp
  have hpow : 0 ≤ lam ^ (2 * (k - 1)) := pow_nonneg hlam _
  exact ⟨le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hC hCC') hpow) h1,
    h2.trans (mul_le_mul_of_nonneg_right hCC' hpow)⟩

theorem KmultBound.mono {p : ℕ} {f : (ℕ →₀ ℕ) → ℝ} {C C' lam : ℝ} (h : KmultBound p f C lam)
    (hCC' : C ≤ C') (hlam : 0 < lam) : KmultBound p f C' lam := fun X hX hV =>
  (h X hX hV).trans (mul_le_mul_of_nonneg_right hCC' (zpow_pos hlam _).le)

/-- **Item (1), uniform form**: one constant `C` and one `λ₀` such that (2.47) and (2.48) hold
for all sizes and subpartitions at once, together with `𝗆(1) = 1`. -/
theorem coefficient_bounds_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p : ℕ}
    (hpS : (p : ℕ∞) ≤ pStar β) (hG1 : ∀ k ∈ Finset.Icc 2 p, MsfGateAt χ β M k)
    (hG2 : ∀ k, k ≤ p → KmultGateAt χ β M k) (hS : MsfLimits χ β M msf)
    (hX : KmultLimits χ β M kmult) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      MsfBound p (msf lam) C lam ∧ KmultBound p (kmult lam) C lam := by
  obtain ⟨Cm, hCm, lm, hlm, hlm1, hm⟩ := msfBound_uniform (p := p) (msf := msf)
    (fun lam hlam hlam1 => msf_one hχ hβ hS hlam hlam1)
    (fun k hk2 hkp => msf_bound hk2 ((Nat.cast_le.mpr hkp).trans hpS)
      (hG1 k (Finset.mem_Icc.mpr ⟨hk2, hkp⟩)) hS)
  obtain ⟨Ck, hCk, lk, hlk, -, hkb⟩ := kmultBound_uniform (p := p) (kmult := kmult)
    (fun X hX' hV => kmult_bound hχ hpS hG1 hG2 hX hX' hV)
  refine ⟨max Cm Ck, lt_max_of_lt_left hCm, min lm lk, lt_min hlm hlk,
    (min_le_left _ _).trans hlm1, fun lam hlam hlaml => ⟨?_, ?_⟩⟩
  · exact MsfBound.mono (hm lam hlam (lt_of_lt_of_le hlaml (min_le_left _ _))) hCm (le_max_left _ _)
      hlam.le
  · exact KmultBound.mono (hkb lam hlam (lt_of_lt_of_le hlaml (min_le_right _ _))) (le_max_right _ _) hlam

end TheoremTwo

end MultipoleBKT

end
