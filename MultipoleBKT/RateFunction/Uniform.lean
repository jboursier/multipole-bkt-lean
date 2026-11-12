/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Minimizer

/-!
# Uniform constants in (2.47) and (2.48)

The frozen Theorem 2(1) states (2.47) with its own `C, λ₀` for each `k` and (2.48) with its own
`C, λ₀` for each subpartition `X`. The analytic facts about the rate function
(`MultipoleBKT.rateSeries_summable_and_bound`, `MultipoleBKT.rateCluster_smooth`,
`MultipoleBKT.rateFunction_minimizer`, `MultipoleBKT.rateFunction_inf_comparison`) use one
uniform constant. Since there are finitely many sizes `2 ≤ k ≤ p` and finitely many block
profiles of subpartitions with `|V_X| ≤ p`, and `|X|` is determined by the block profile, the
per-index constants can be made uniform (`MultipoleBKT.kmultBound_uniform`,
`MultipoleBKT.msfBound_uniform`).
-/

@[expose] public section

namespace MultipoleBKT

open Finset

/-- Finitely many statements, each monotone in `(C, λ₀)` (larger `C`, smaller `λ₀`), hold with
common constants. -/
theorem exists_uniform_constants {ι : Type*} (T : Finset ι) (Q : ι → ℝ → ℝ → Prop)
    (hmono : ∀ i C C' l l', Q i C l → C ≤ C' → 0 < l' → l' ≤ l → Q i C' l')
    (h : ∀ i ∈ T, ∃ C : ℝ, 0 < C ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ Q i C l) :
    ∃ C : ℝ, 0 < C ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ ∀ i ∈ T, Q i C l := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 1, one_pos, le_rfl, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a T ha ih =>
    obtain ⟨C₁, hC₁, l₁, hl₁, hl₁1, hQ₁⟩ := ih fun i hi => h i (mem_insert_of_mem hi)
    obtain ⟨C₂, hC₂, l₂, hl₂, hl₂1, hQ₂⟩ := h a (mem_insert_self a T)
    refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, min l₁ l₂, lt_min hl₁ hl₂,
      (min_le_left _ _).trans hl₁1, fun i hi => ?_⟩
    rcases mem_insert.mp hi with rfl | hi
    · exact hmono i C₂ _ l₂ _ hQ₂ (le_max_right _ _) (lt_min hl₁ hl₂) (min_le_right _ _)
    · exact hmono i C₁ _ l₁ _ (hQ₁ i hi) (le_max_left _ _) (lt_min hl₁ hl₂) (min_le_left _ _)

section Profiles

/-- The block profile determines the number of blocks. -/
theorem card_eq_of_blockProfile_eq {X Y : Finset (Finset ℕ)}
    (h : blockProfile X = blockProfile Y) : X.card = Y.card := by
  have h' : X.val.map Finset.card = Y.val.map Finset.card := Multiset.toFinsupp.injective h
  have := congrArg Multiset.card h'
  simpa using this

/-- The multiset of block sizes of a subpartition `X` with `|V_X| ≤ p` is bounded by
`p • {0, 1, …, p}`. -/
theorem map_card_le_of_isSubpartition {p : ℕ} {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hV : (X.biUnion id).card ≤ p) :
    X.val.map Finset.card ≤ p • Multiset.range (p + 1) := by
  classical
  have hcardX : X.card ≤ p := by
    have h1 : X.card ≤ ∑ S ∈ X, S.card :=
      card_eq_sum_ones X ▸ sum_le_sum fun S hS => card_pos.mpr (hX.1 S hS)
    have h2 : (X.biUnion id).card = ∑ S ∈ X, S.card := by
      rw [card_biUnion]
      · rfl
      · intro S hS T hT hST
        exact hX.2 hS hT hST
    omega
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul]
  by_cases ha : a < p + 1
  · rw [Multiset.count_eq_one_of_mem (Multiset.nodup_range _) (Multiset.mem_range.mpr ha),
      mul_one]
    calc Multiset.count a (X.val.map Finset.card) ≤ Multiset.card (X.val.map Finset.card) :=
          Multiset.count_le_card _ _
      _ = X.card := by simp
      _ ≤ p := hcardX
  · rw [Multiset.count_eq_zero.mpr (fun h => ha (Multiset.mem_range.mp h)), mul_zero,
      Nat.le_zero, Multiset.count_eq_zero]
    intro hmem
    obtain ⟨S, hS, rfl⟩ := Multiset.mem_map.mp hmem
    have : S.card ≤ (X.biUnion id).card := card_le_card (subset_biUnion_of_mem id hS)
    omega

/-- The finite set of possible block profiles of subpartitions `X` with `|V_X| ≤ p`. -/
noncomputable def profileBound (p : ℕ) : Finset (ℕ →₀ ℕ) :=
  (p • Multiset.range (p + 1)).powerset.toFinset.image Multiset.toFinsupp

theorem blockProfile_mem_profileBound {p : ℕ} {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hV : (X.biUnion id).card ≤ p) : blockProfile X ∈ profileBound p := by
  classical
  rw [profileBound, mem_image]
  exact ⟨X.val.map Finset.card, Multiset.mem_toFinset.mpr
    (Multiset.mem_powerset.mpr (map_card_le_of_isSubpartition hX hV)), rfl⟩

end Profiles

/-- **Uniform (2.48).** From the per-subpartition form of (2.48) in the frozen Theorem 2(1)
(own `C, λ₀` for each `X`), one constant `C` and one `λ₀` work for all `X`. -/
theorem kmultBound_uniform {p : ℕ} {kmult : ℝ → (ℕ →₀ ℕ) → ℝ}
    (h : ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        |kmult lam (blockProfile X)| ≤ C * lam ^ (2 * ((X.card : ℤ) - 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      KmultBound p (kmult lam) C lam := by
  classical
  let Q : (ℕ →₀ ℕ) → ℝ → ℝ → Prop := fun f C l =>
    ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ p → blockProfile X = f →
      ∀ lam : ℝ, 0 < lam → lam < l → |kmult lam f| ≤ C * lam ^ (2 * ((X.card : ℤ) - 1))
  have hmono : ∀ f C C' l l', Q f C l → C ≤ C' → 0 < l' → l' ≤ l → Q f C' l' := by
    intro f C C' l l' hQ hCC' _ hll' X hX hV hf lam hlam hlaml
    refine (hQ X hX hV hf lam hlam (lt_of_lt_of_le hlaml hll')).trans ?_
    exact mul_le_mul_of_nonneg_right hCC' (zpow_nonneg hlam.le _)
  have hT : ∀ f ∈ profileBound p, ∃ C : ℝ, 0 < C ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ Q f C l := by
    intro f _
    by_cases hex : ∃ X₀ : Finset (Finset ℕ), IsSubpartition X₀ ∧ (X₀.biUnion id).card ≤ p ∧
        blockProfile X₀ = f
    · obtain ⟨X₀, hX₀, hV₀, hf₀⟩ := hex
      obtain ⟨C, hC, l, hl, hl1, hb⟩ := h X₀ hX₀ hV₀
      refine ⟨C, hC, l, hl, hl1, fun X _ _ hf lam hlam hlaml => ?_⟩
      have hcard : X.card = X₀.card := card_eq_of_blockProfile_eq (hf.trans hf₀.symm)
      rw [hcard, ← hf₀]
      exact hb lam hlam hlaml
    · refine ⟨1, one_pos, 1, one_pos, le_rfl, fun X hX hV hf => absurd ⟨X, hX, hV, hf⟩ hex⟩
  obtain ⟨C, hC, l, hl, hl1, hQ⟩ := exists_uniform_constants (profileBound p) Q hmono hT
  refine ⟨C, hC, l, hl, hl1, fun lam hlam hlaml X hX hV => ?_⟩
  exact hQ _ (blockProfile_mem_profileBound hX hV) X hX hV rfl lam hlam hlaml

/-- **Uniform (2.47).** From the per-size form of (2.47) in the frozen Theorem 2(1) and
`𝗆(1) = 1`, one constant `C` and one `λ₀` work for all `2 ≤ k ≤ p`. -/
theorem msfBound_uniform {p : ℕ} {msf : ℝ → ℕ → ℝ}
    (h1 : ∀ lam : ℝ, 0 < lam → lam < 1 → msf lam 1 = 1)
    (h : ∀ k : ℕ, 2 ≤ k → k ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        C⁻¹ * lam ^ (2 * (k - 1)) ≤ msf lam k ∧ msf lam k ≤ C * lam ^ (2 * (k - 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      MsfBound p (msf lam) C lam := by
  let Q : ℕ → ℝ → ℝ → Prop := fun k C l => 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam < l →
    C⁻¹ * lam ^ (2 * (k - 1)) ≤ msf lam k ∧ msf lam k ≤ C * lam ^ (2 * (k - 1))
  have hmono : ∀ k C C' l l', Q k C l → C ≤ C' → 0 < l' → l' ≤ l → Q k C' l' := by
    intro k C C' l l' hQ hCC' _ hll'
    refine ⟨hQ.1.trans_le hCC', fun lam hlam hlaml => ?_⟩
    obtain ⟨h₁, h₂⟩ := hQ.2 lam hlam (lt_of_lt_of_le hlaml hll')
    have hpow : 0 ≤ lam ^ (2 * (k - 1)) := pow_nonneg hlam.le _
    refine ⟨le_trans ?_ h₁, h₂.trans (mul_le_mul_of_nonneg_right hCC' hpow)⟩
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hQ.1 hCC') hpow
  have hT : ∀ k ∈ Finset.Icc 2 p, ∃ C : ℝ, 0 < C ∧ ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ Q k C l := by
    intro k hk
    obtain ⟨hk2, hkp⟩ := Finset.mem_Icc.mp hk
    obtain ⟨C, hC, l, hl, hl1, hb⟩ := h k hk2 hkp
    exact ⟨C, hC, l, hl, hl1, hC, hb⟩
  obtain ⟨C, hC, l, hl, hl1, hQ⟩ := exists_uniform_constants (Finset.Icc 2 p) Q hmono hT
  refine ⟨C, hC, l, hl, hl1, fun lam hlam hlaml => ⟨h1 lam hlam (lt_of_lt_of_le hlaml hl1),
    fun k hk2 hkp => (hQ k (Finset.mem_Icc.mpr ⟨hk2, hkp⟩)).2 lam hlam hlaml⟩⟩

end MultipoleBKT

end
