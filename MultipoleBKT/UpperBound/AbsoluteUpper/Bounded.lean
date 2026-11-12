/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.Inputs

/-!
# Bounded clusters and hatted activities (steps of the proof of Proposition 5.20)

The paper: proof of Proposition 5.20.

* `zeroPartitionFunction_singleton`: `𝖬^0_{ε₀}({i}) = 1` (the singleton bounds in the proof of Proposition 5.18).
* `abs_le_of_gamma_bound`: **the bounded-activity majorant**: if `|V_X| = k ≤ p*(β)`,
  `|K(X)| ≤ C γ_{β,λ,k} / (𝖬^0(X) N^{k-1})` (eq. (5.67)) and every block satisfies the lower
  bound (4.38), `𝖬^0(S) ≥ λ^{2(|S|-1)} / (C_m N^{|S|-1})`, then
  `|K(X)| ≤ C C_m^{|X|} (λ²/N)^{|X|-1}`. This uses `γ_{β,λ,k} = λ^{2(k-1)}` for `k ≤ p*(β)` and
  `∑_{S ∈ X} (|S| - 1) = |V_X| - |X|` (the computation the paper leaves implicit).
* `abs_hatActivity_le`: `|𝖪̂^{+,Z}(X)| ≤ |𝖪^{+,Z}(X)|` when `g^Z(S) ≥ 1` for the blocks of `X`
  (eq. (5.101)).
* `exists_lam_N_forall_le`: "`λ` small and `N` large" for finitely many statements at once.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

open Hierarchical

/-! ### `𝖬^0_{ε₀}` of a singleton -/

section Singleton

open scoped Classical in
/-- The multipole partition function of a single dipole is `1` for `ψ = 1`. -/
theorem modelPartitionFunction_of_card_eq_one {ρ : Measure (ℂ × ℂ)} [IsProbabilityMeasure ρ]
    (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) {S : Finset ℕ} (hS : S.card = 1) :
    modelPartitionFunction ρ β w (fun _ => 1) M lam S = 1 := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hS
  have : Subsingleton ({a} : Finset ℕ) := ⟨fun i j => Subtype.ext (by
    rw [Finset.mem_singleton.1 i.2, Finset.mem_singleton.1 j.2])⟩
  have : Nonempty ({a} : Finset ℕ) := ⟨⟨a, Finset.mem_singleton_self a⟩⟩
  unfold modelPartitionFunction
  have hc : ∀ c : ({a} : Finset ℕ) → ℂ × ℂ,
      (SimpleGraph.fromRel fun i j : ({a} : Finset ℕ) =>
        MultipoleLinked M lam (c i) (c j)).Connected := fun c =>
    { preconnected := SimpleGraph.Preconnected.of_subsingleton }
  calc _ = ∫ _c : ({a} : Finset ℕ) → ℂ × ℂ, (1 : ℝ) ∂Measure.pi fun _ => ρ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
        dsimp only
        rw [ite_eq_left (hc c), Finset.prod_const_one, mul_one, one_mul]
        exact Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => by
          rw [Subsingleton.elim i j, ite_eq_right (lt_irrefl j)]
    _ = 1 := by simp

open scoped Classical in
/-- The multipole partition function of a model with `ψ ≥ 0` is nonnegative. -/
theorem modelPartitionFunction_nonneg {ρ : MeasureTheory.Measure (ℂ × ℂ)} (β : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) {ψ : ℂ × ℂ → ℝ} (hψ : ∀ d, 0 ≤ ψ d) (M lam : ℝ) (S : Finset ℕ) :
    0 ≤ modelPartitionFunction ρ β w ψ M lam S := by
  unfold modelPartitionFunction
  refine integral_nonneg fun c => mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) ?_)
    (prod_nonneg fun i _ => hψ _)
  refine prod_nonneg fun i _ => prod_nonneg fun j _ => ?_
  split_ifs <;> first | exact zero_le_one | exact le_rfl | exact (Real.exp_pos _).le

/-- `𝖬^0_{ε₀}(X) ≥ 0`. -/
theorem zeroPartitionFunction_nonneg (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ : ℝ)
    (X : Finset (Finset ℕ)) : 0 ≤ zeroPartitionFunction χ N p₀ β lam M ε₀ X :=
  prod_nonneg fun S _ => modelPartitionFunction_nonneg β _ (fun _ => zero_le_one) M lam S

/-- `𝖬^0_{ε₀}({i}) = 1` (for `N ≥ 1`, `λ > 0`, `ε₀ > 0`). -/
theorem zeroPartitionFunction_singleton {χ : ℂ → ℝ} (hχ : IsMollifier χ) {N p₀ : ℕ}
    {β lam M ε₀ : ℝ} (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {S : Finset ℕ}
    (hS : S.card = 1) : zeroPartitionFunction χ N p₀ β lam M ε₀ {S} = 1 := by
  have := isProbabilityMeasure_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
  rw [zeroPartitionFunction, Finset.prod_singleton]
  exact modelPartitionFunction_of_card_eq_one β _ M lam hS

end Singleton

/-! ### The bounded-activity majorant -/

section Majorant

/-- `∑_{S ∈ X} (|S| - 1) + |X| = |V_X|` for a subpartition. -/
theorem sum_card_sub_one_add_card {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    ∑ S ∈ X, (S.card - 1) + X.card = (X.biUnion id).card := by
  rw [card_biUnion fun S hS T hT hST => hX.2 hS hT hST, card_eq_sum_ones X, ← sum_add_distrib]
  refine sum_congr rfl fun S hS => ?_
  have := (hX.1 S hS).card_pos
  simp only [id]
  omega

/-- `γ_{β,λ,k} = λ^{2(k-1)}` for `1 ≤ k ≤ p*(β)` (Definition 4.22, first case). -/
theorem gammaBeta_of_le_pStar {p₀ : ℕ} {β lam : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) : Appendix.gammaBeta p₀ β lam k = lam ^ (2 * (k - 1)) := by
  rw [Appendix.gammaBeta, ite_eq_left hkp]
  have : (2 * ((k : ℤ) - 1)) = ((2 * (k - 1) : ℕ) : ℤ) := by push_cast [hk]; ring
  rw [this, zpow_natCast]

/-- **The bounded-activity majorant** (proof of Proposition 5.20): from `|K| ≤ C λ^{2(k-1)} / (∏_{S ∈ X} m_S N^{k-1})`, `k = |V_X|`, and
`m_S ≥ λ^{2(|S|-1)} / (C_m N^{|S|-1})` for the blocks of `X`, `|K| ≤ C C_m^{|X|} (λ²/N)^{|X|-1}`. -/
theorem abs_le_of_gamma_bound {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (hX1 : 1 ≤ X.card)
    {K C Cm lam : ℝ} {N : ℕ} {m : Finset ℕ → ℝ} (hN : 0 < (N : ℝ)) (hlam : 0 < lam)
    (hCm : 0 < Cm) (hC : 0 ≤ C)
    (hm : ∀ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤ m S)
    (hK : |K| ≤ C * lam ^ (2 * ((X.biUnion id).card - 1)) /
      ((∏ S ∈ X, m S) * (N : ℝ) ^ ((X.biUnion id).card - 1))) :
    |K| ≤ C * Cm ^ X.card * (lam ^ 2 / N) ^ (X.card - 1) := by
  set a := X.card
  set k := (X.biUnion id).card
  set s := ∑ S ∈ X, (S.card - 1) with hs
  have hsk : s + a = k := sum_card_sub_one_add_card hX
  have hQ : lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s) ≤ ∏ S ∈ X, m S := by
    calc lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s)
        = ∏ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) := by
          rw [prod_div_distrib, prod_mul_distrib, prod_const, prod_pow_eq_pow_sum,
            prod_pow_eq_pow_sum, hs, mul_sum]
      _ ≤ ∏ S ∈ X, m S := prod_le_prod₀ (fun S _ => by positivity) hm
  have hQ0 : 0 < lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s) := by positivity
  have hk1 : k - 1 = s + (a - 1) := by omega
  calc |K| ≤ C * lam ^ (2 * (k - 1)) / ((∏ S ∈ X, m S) * (N : ℝ) ^ (k - 1)) := hK
    _ ≤ C * lam ^ (2 * (k - 1)) /
          (lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s) * (N : ℝ) ^ (k - 1)) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        exact mul_le_mul_of_nonneg_right hQ (by positivity)
    _ = C * Cm ^ a * (lam ^ 2 / N) ^ (a - 1) := by
        rw [hk1, mul_add, pow_add, pow_add, div_pow, ← pow_mul]
        field_simp
end Majorant

/-! ### The hatted activities -/

section Hat

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- `|𝖪̂^{+,Z}(X)| ≤ |𝖪^{+,Z}(X)|` when `g^Z(S) ≥ 1` for every block of `X` (proof of Proposition 5.18). -/
theorem abs_hatActivity_le {X : Finset (Finset ℕ)}
    (hg : ∀ S ∈ X, 1 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S) :
    |hatActivity χ N p₀ β lam M ε₀ L V Z X| ≤ |plusActivity χ N p₀ β lam M ε₀ L V Z X| := by
  have hP : 1 ≤ ∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S :=
    one_le_prod₀ hg
  rw [hatActivity, abs_div, abs_of_pos (zero_lt_one.trans_le hP)]
  exact div_le_self (abs_nonneg _) hP

end Hat

/-! ### Finitely many statements for `λ` small and `N` large -/

/-- If, for each `k ≤ K`, a statement holds for `λ` small and then `N` large, they hold together. -/
theorem exists_lam_N_forall_le {P : ℕ → ℝ → ℕ → Prop} (K : ℕ)
    (h : ∀ k ≤ K, ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P k lam N) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k ≤ K, P k lam N := by
  induction K with
  | zero =>
    obtain ⟨lam₀, hlam₀, h0⟩ := h 0 le_rfl
    refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
    obtain ⟨N₀, hN₀⟩ := h0 lam hlam hlt
    exact ⟨N₀, fun N hN k hk => by
      rw [Nat.le_zero.1 hk]
      exact hN₀ N hN⟩
  | succ K ih =>
    obtain ⟨lam₁, hlam₁, h1⟩ := ih fun k hk => h k (hk.trans (Nat.le_succ K))
    obtain ⟨lam₂, hlam₂, h2⟩ := h (K + 1) le_rfl
    refine ⟨min lam₁ lam₂, lt_min hlam₁ hlam₂, fun lam hlam hlt => ?_⟩
    obtain ⟨N₁, hN₁⟩ := h1 lam hlam (hlt.trans_le (min_le_left _ _))
    obtain ⟨N₂, hN₂⟩ := h2 lam hlam (hlt.trans_le (min_le_right _ _))
    refine ⟨max N₁ N₂, fun N hN k hk => ?_⟩
    rcases Nat.lt_or_ge k (K + 1) with hkK | hkK
    · exact hN₁ N ((le_max_left _ _).trans hN) k (by omega)
    · rw [show k = K + 1 by omega]
      exact hN₂ N ((le_max_right _ _).trans hN)

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
