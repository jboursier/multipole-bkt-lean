/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Ring.Abs
public import MultipoleBKT.Appendix.GeneralExpansion.Pointwise

/-!
# Algebra for the control of activity errors (Proposition 4.24)

The proof of Proposition 4.24. Real-number lemmas used to assemble the estimates (4.42), (4.43), (4.44)
and (4.45):

* `abs_mul_pow_sub_mul_pow_le`: the decomposition (eq. (4.75), proof of Proposition 4.24)
  `a^k J₁ - b^k J₂ = a^k (J₁ - J₂) + ((a/b)^k - 1) b^k J₂`, in absolute value;
* `abs_pow_sub_one_le`: `|x^k - 1| ≤ k 2^{k-1} |x - 1|` for `0 ≤ x ≤ 2`;
* `abs_prod_sub_one_le`: `|∏_{S ∈ X} r_S - 1| ≤ B^{|X|} |X| η` for `0 ≤ r_S ≤ B`, `|r_S - 1| ≤ η`
  (the telescoping of the products, proof of Proposition 4.24);
* `exists_uniform`: estimates of the form `∃ C, ∃ λ₀, ∀ λ < λ₀, ∃ N₀, ∀ N ≥ N₀, P s C λ N`,
  monotone in `C`, for each block size `1 ≤ s ≤ k`, hold with common constants for all
  `1 ≤ s ≤ k`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open Finset

/-- **The decomposition (4.75)** (proof of Proposition 4.24): for `a, b > 0`,
`|a^k J₁ - b^k J₂| ≤ a^k |J₁ - J₂| + |(a/b)^k - 1| |b^k J₂|`. -/
theorem abs_mul_pow_sub_mul_pow_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (J₁ J₂ : ℝ) :
    |a ^ k * J₁ - b ^ k * J₂| ≤ a ^ k * |J₁ - J₂| + |(a / b) ^ k - 1| * |b ^ k * J₂| := by
  have hsplit : a ^ k * J₁ - b ^ k * J₂ =
      a ^ k * (J₁ - J₂) + ((a / b) ^ k - 1) * (b ^ k * J₂) := by
    rw [div_pow]
    field_simp
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (pow_pos ha k)]

/-- `|x^k - 1| ≤ k 2^{k-1} |x - 1|` for `0 ≤ x ≤ 2`. -/
theorem abs_pow_sub_one_le {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (k : ℕ) :
    |x ^ k - 1| ≤ k * 2 ^ (k - 1) * |x - 1| := by
  have h := abs_pow_sub_pow_le (a := x) (b := 1) (n := k)
  rw [one_pow] at h
  have hmax : max |x| |(1 : ℝ)| ≤ 2 := by
    rw [abs_of_nonneg hx0, abs_one]
    exact max_le hx2 (by norm_num)
  have h0 : 0 ≤ max |x| |(1 : ℝ)| := le_max_of_le_right (abs_nonneg _)
  have hp : max |x| |(1 : ℝ)| ^ (k - 1) ≤ 2 ^ (k - 1) := pow_le_pow_left₀ h0 hmax _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc |x ^ k - 1| ≤ |x - 1| * k * max |x| |(1 : ℝ)| ^ (k - 1) := h
    _ ≤ |x - 1| * k * 2 ^ (k - 1) := by gcongr
    _ = k * 2 ^ (k - 1) * |x - 1| := by ring

/-- **Telescoping of products** (proof of Proposition 4.24): for `0 ≤ r_S ≤ B` with `B ≥ 1` and
`|r_S - 1| ≤ η`, `|∏_{S ∈ X} r_S - 1| ≤ B^{|X|} |X| η`. -/
theorem abs_prod_sub_one_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {r : ι → ℝ} {B η : ℝ}
    (hB : 1 ≤ B) (hr0 : ∀ i ∈ s, 0 ≤ r i) (hrB : ∀ i ∈ s, r i ≤ B)
    (hη : ∀ i ∈ s, |r i - 1| ≤ η) :
    |∏ i ∈ s, r i - 1| ≤ B ^ s.card * (s.card * η) := by
  have h := GeneralExpansion.abs_prod_sub_prod_le s (g := fun _ => (1 : ℝ)) hB hr0 hrB
    (fun _ _ => zero_le_one) (fun _ _ => hB)
  rw [prod_const_one] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (zero_le_one.trans hB) _))
  calc ∑ i ∈ s, |r i - 1| ≤ ∑ _i ∈ s, η := sum_le_sum hη
    _ = s.card * η := by rw [sum_const, nsmul_eq_mul]

/-- `∏_{S ∈ X} r_S ≤ B^{|X|}` for `0 ≤ r_S ≤ B`. -/
theorem prod_le_pow_card_of_nonneg {ι : Type*} (s : Finset ι) {r : ι → ℝ} {B : ℝ}
    (hr0 : ∀ i ∈ s, 0 ≤ r i) (hrB : ∀ i ∈ s, r i ≤ B) : ∏ i ∈ s, r i ≤ B ^ s.card := by
  calc ∏ i ∈ s, r i ≤ ∏ _i ∈ s, B := prod_le_prod₀ hr0 hrB
    _ = B ^ s.card := prod_const B

/-- **Common constants for the block sizes `1 ≤ s ≤ k`.** If for each `1 ≤ s ≤ k` there are
`C > 0`, `λ₀ > 0` and, for `λ ∈ (0, λ₀)`, an `N₀` with `P s C λ N` for `N ≥ N₀`, and `P` is
monotone in `C`, then one `C`, one `λ₀` and one `N₀(λ)` serve all `1 ≤ s ≤ k`. -/
theorem exists_uniform (P : ℕ → ℝ → ℝ → ℕ → Prop)
    (hmono : ∀ s C C' lam N, C ≤ C' → P s C lam N → P s C' lam N) :
    ∀ k : ℕ, (∀ s, 1 ≤ s → s ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P s C lam N) →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ s, 1 ≤ s → s ≤ k → P s C lam N := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, one_pos, 1, one_pos, fun _ _ _ => ⟨0, fun _ _ s hs hsk => by omega⟩⟩
  | succ k ih =>
    intro h
    obtain ⟨C₁, hC₁, l₁, hl₁, h₁⟩ := ih fun s hs hsk => h s hs (by omega)
    obtain ⟨C₂, hC₂, l₂, hl₂, h₂⟩ := h (k + 1) (by omega) le_rfl
    refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, min l₁ l₂, lt_min hl₁ hl₂,
      fun lam hlam hlt => ?_⟩
    obtain ⟨N₁, hN₁⟩ := h₁ lam hlam (hlt.trans_le (min_le_left _ _))
    obtain ⟨N₂, hN₂⟩ := h₂ lam hlam (hlt.trans_le (min_le_right _ _))
    refine ⟨max N₁ N₂, fun N hN s hs hsk => ?_⟩
    rcases Nat.lt_or_ge s (k + 1) with hlt' | hge
    · exact hmono s C₁ _ lam N (le_max_left _ _)
        (hN₁ N (le_trans (le_max_left _ _) hN) s hs (by omega))
    · have hs' : s = k + 1 := by omega
      subst hs'
      exact hmono _ C₂ _ lam N (le_max_right _ _) (hN₂ N (le_trans (le_max_right _ _) hN))

end ExpansionErrors

end MultipoleBKT

end
