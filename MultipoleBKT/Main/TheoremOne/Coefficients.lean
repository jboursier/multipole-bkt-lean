/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.Exchange
public import MultipoleBKT.Frozen.PStar

/-!
# Theorem 1 from the gates: the coefficients `𝗄^dip` and item (2)

Item (2) of Theorem 1, equation (2.39), follows from Proposition 4.23: the bound
(4.41) `|𝖪^dip(V)| ≤ C λ^{2(k-1)} N^{1-k}` passes to the limit `𝗄^dip(k) = lim N^{k-1} 𝖪^dip(V)`.

* `abs_le_of_tendsto_of_activity_bound`: the passage to the limit;
* `item_two`: (2.39) for every `2 ≤ k ≤ p*(β)`, with the constants of (4.41);
* `exists_uniform_of_forall_mem`: constants uniform over a finite set of sizes `k`;
* `exists_uniform_dipoleActivity_bound`, `exists_uniform_coefficient_bound`: (4.41) and (2.39)
  with one constant `C₀` for all `2 ≤ k ≤ p`, as needed by Lemma 4.53.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace TheoremOne

variable {χ : ℂ → ℝ} {β : ℝ}

/-- Passage to the limit in (4.41): if `N^{k-1} 𝖪^dip([k]) → L` and
`|𝖪^dip([k])| ≤ C λ^{2(k-1)} N^{1-k}` for `N` large, then `|L| ≤ C λ^{2(k-1)}`. -/
theorem abs_le_of_tendsto_of_activity_bound {N₀ k : ℕ} {L C lam : ℝ}
    (hT : Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam (range k)) atTop
      (𝓝 L))
    (hb : ∀ N : ℕ, N₀ ≤ N →
      |dipoleActivity χ N β lam (range k)| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) :
    |L| ≤ C * lam ^ (2 * (k - 1)) := by
  refine le_of_tendsto hT.abs ?_
  filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 1] with N hN hN1
  have hpos : 0 < (N : ℝ) ^ (k - 1) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  rw [abs_mul, abs_of_pos hpos]
  calc (N : ℝ) ^ (k - 1) * |dipoleActivity χ N β lam (range k)|
      ≤ (N : ℝ) ^ (k - 1) * (C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (hb N hN) hpos.le
    _ = C * lam ^ (2 * (k - 1)) := by field_simp

/-- **Item (2)** of Theorem 1, eq. (2.39): from (4.41) and the limits (2.34). -/
theorem item_two
    (h439 : ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
            |dipoleActivity χ N β lam V| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1))
    {kdip : ℝ → ℕ → ℝ}
    (hlim : ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
          (𝓝 (kdip lam k))) :
    ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → |kdip lam k| ≤ C * lam ^ (2 * (k - 1)) := by
  intro k hk2 hkS
  obtain ⟨C, hC, lam₀, hlam₀, hlam₀1, h⟩ := h439 k hk2 hkS
  refine ⟨C, hC, lam₀, hlam₀, hlam₀1, fun lam hlam hlaml => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam hlaml
  refine abs_le_of_tendsto_of_activity_bound (N₀ := max N₀ k)
    (hlim lam hlam (hlaml.trans_le hlam₀1) k hk2 hkS (range k) (card_range k)) fun N hN => ?_
  exact hN₀ N ((le_max_left _ _).trans hN) (range k)
    (range_subset_range.mpr ((le_max_right _ _).trans hN)) (card_range k)

/-- Constants uniform over a finite set of indices `k`: if each `k ∈ s` has its own `C, λ₀`
(and the property is monotone in `C`), then one `C, λ₀` serves all `k ∈ s`. -/
theorem exists_uniform_of_forall_mem {s : Finset ℕ} {Q : ℕ → ℝ → ℝ → Prop}
    (hmono : ∀ k C C' lam, C ≤ C' → Q k C lam → Q k C' lam)
    (h : ∀ k ∈ s, ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → Q k C lam) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ k ∈ s, Q k C lam := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 1, one_pos, le_rfl, fun _ _ _ k hk => absurd hk (notMem_empty k)⟩
  | insert a s ha ih =>
    obtain ⟨C₁, hC₁, l₁, hl₁, hl₁1, h₁⟩ := h a (mem_insert_self a s)
    obtain ⟨C₂, hC₂, l₂, hl₂, -, h₂⟩ := ih fun k hk => h k (mem_insert_of_mem hk)
    refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, min l₁ l₂, lt_min hl₁ hl₂,
      (min_le_left _ _).trans hl₁1, fun lam hlam hlaml k hk => ?_⟩
    rcases mem_insert.mp hk with rfl | hk
    · exact hmono _ _ _ _ (le_max_left _ _) (h₁ lam hlam (hlaml.trans_le (min_le_left _ _)))
    · exact hmono _ _ _ _ (le_max_right _ _)
        (h₂ lam hlam (hlaml.trans_le (min_le_right _ _)) k hk)

/-- **(4.41) with a uniform constant** for all sizes `2 ≤ k ≤ p` (`p ≤ p*(β)`). -/
theorem exists_uniform_dipoleActivity_bound
    (h439 : ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
            |dipoleActivity χ N β lam V| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1))
    {p : ℕ} (hpS : (p : ℕ∞) ≤ pStar β) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ V : Finset ℕ, V ⊆ Finset.range N → 2 ≤ V.card → V.card ≤ p →
          |dipoleActivity χ N β lam V| ≤ C₀ * (lam ^ 2 / N) ^ (V.card - 1) := by
  obtain ⟨C₀, hC₀, lam₀, hlam₀, hlam₀1, h⟩ := exists_uniform_of_forall_mem
    (s := Icc 2 p) (Q := fun k C lam => ∀ᶠ N : ℕ in atTop,
      ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
        |dipoleActivity χ N β lam V| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1))
    (fun k C C' lam hCC' hQ => hQ.mono fun N hN V hV hVk =>
      (hN V hV hVk).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC' ((even_two_mul (k - 1)).pow_nonneg lam))
        (pow_nonneg (Nat.cast_nonneg N) _)))
    (fun k hk => by
      obtain ⟨hk2, hkp⟩ := mem_Icc.mp hk
      obtain ⟨C, hC, lam₀, hlam₀, hlam₀1, h⟩ :=
        h439 k hk2 ((Nat.cast_le.mpr hkp).trans hpS)
      exact ⟨C, hC, lam₀, hlam₀, hlam₀1, fun lam hlam hlaml =>
        eventually_atTop.mpr (h lam hlam hlaml)⟩)
  refine ⟨C₀, hC₀, lam₀, hlam₀, hlam₀1, fun lam hlam hlaml => ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((eventually_all_finset (Icc 2 p)).mpr
    (h lam hlam hlaml))
  refine ⟨N₀, fun N hN V hV hV2 hVp => ?_⟩
  have := hN₀ N hN V.card (mem_Icc.mpr ⟨hV2, hVp⟩) V hV rfl
  rwa [div_pow, ← pow_mul, ← mul_div_assoc]

/-- **(2.39) with a uniform constant** for all sizes `2 ≤ j ≤ p`, from the uniform (4.41). -/
theorem exists_uniform_coefficient_bound {p : ℕ} {C₀ lam₀ : ℝ} (hlam₀1 : lam₀ ≤ 1)
    (hb : ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ V : Finset ℕ, V ⊆ Finset.range N → 2 ≤ V.card → V.card ≤ p →
          |dipoleActivity χ N β lam V| ≤ C₀ * (lam ^ 2 / N) ^ (V.card - 1))
    {kdip : ℝ → ℕ → ℝ}
    (hlim : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ j : ℕ, 2 ≤ j → j ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (j - 1) * dipoleActivity χ N β lam (range j)) atTop
        (𝓝 (kdip lam j)))
    {lam : ℝ} (hlam : 0 < lam) (hlaml : lam < lam₀) :
    ∀ j : ℕ, 2 ≤ j → j ≤ p → |kdip lam j| ≤ C₀ * lam ^ (2 * (j - 1)) := by
  intro j hj2 hjp
  obtain ⟨N₀, hN₀⟩ := hb lam hlam hlaml
  refine abs_le_of_tendsto_of_activity_bound (N₀ := max N₀ j)
    (hlim lam hlam (hlaml.trans_le hlam₀1) j hj2 hjp) fun N hN => ?_
  have := hN₀ N ((le_max_left _ _).trans hN) (range j)
    (range_subset_range.mpr ((le_max_right _ _).trans hN)) (by rw [card_range]; exact hj2)
    (by rw [card_range]; exact hjp)
  rwa [card_range, div_pow, ← pow_mul, ← mul_div_assoc] at this

end TheoremOne

end MultipoleBKT

end
