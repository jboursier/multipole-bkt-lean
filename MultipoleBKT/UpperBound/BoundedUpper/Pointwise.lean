/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.ComponentZ

/-!
# Shared estimates for the separated upper activity bound

The paper: Proposition 5.18. These elementary estimates bound finite products and even bonds,
combine the component tails into the tail of `J`, and expand the absolute value
of a reduced term. They are used by the separated pointwise proof in `RouteRaw`
and by the nonempty-mark estimates.
-/

@[expose] public section

open Finset SimpleGraph
open scoped NNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Peeling CoreForest Quadratic Parity Hierarchical Multipole SetPartition

/-! ### Elementary bounds -/

section Elementary

theorem prod_le_pow_of_le {ι : Type*} (s : Finset ι) {f : ι → ℝ} {C : ℝ} (hC : 1 ≤ C) {k : ℕ}
    (hk : s.card ≤ k) (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ C) : ∏ i ∈ s, f i ≤ C ^ k := by
  refine (Finset.prod_le_prod₀ h0 h).trans ?_
  rw [Finset.prod_const]
  exact pow_le_pow_right₀ hC hk

theorem card_pairsOn_le (U : Finset ℕ) : (pairsOn U).card ≤ U.card * U.card := by
  unfold pairsOn
  exact (Finset.card_filter_le _ _).trans (Finset.card_product U U).le

/-- `t / max(m, t) ≤ R / max(m, R)` for `0 ≤ t ≤ R`, `0 ≤ m`, `R > 0`. -/
theorem div_max_le_div_max {t R m : ℝ} (ht : 0 ≤ t) (htR : t ≤ R) (hm : 0 ≤ m) (hR : 0 < R) :
    t / max m t ≤ R / max m R := by
  rcases le_total m t with h | h
  · rw [max_eq_right h, max_eq_right (h.trans htR), div_self hR.ne']
    rcases ht.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [div_self h0.ne']
  · rw [max_eq_left h]
    rcases le_total m R with h' | h'
    · rw [max_eq_right h', div_self hR.ne']
      rcases hm.eq_or_lt with h0 | h0
      · rw [← h0, div_zero]; exact zero_le_one
      · rw [div_le_one h0]; exact h
    · rw [max_eq_left h']
      exact div_le_div_of_nonneg_right htR hm

theorem compTail_le_one (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) (T : SimpleGraph (Y.biUnion id)) :
    compTail c Y T ≤ 1 := by
  unfold compTail
  refine pow_le_one₀ (div_nonneg (blockRad_nonneg c _) (le_max_of_le_right (blockRad_nonneg c _)))
    ?_
  exact div_le_one_of_le₀ (le_max_right _ _) (le_max_of_le_right (blockRad_nonneg c _))

open scoped Classical in
/-- **The tails of the odd components combine into the tail of `J`**: for `X_l ⊆ X` and
`max_{V_X} r > 0`, `∏_l (r_{V_{X_l}} / max(max_{T_l} d, r_{V_{X_l}}))² ≤
(r_{V_X} / max(max_l max_{T_l} d, r_{V_X}))²`. -/
theorem prod_compTail_le_jTail (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id)) (hpos : 0 < blockRad c (X.biUnion id)) :
    ∏ l, compTail c (Xs l) (Ta l) ≤ jTail c X Xs Ta := by
  set R := blockRad c (X.biUnion id)
  by_cases hn : (univ : Finset (Fin n)).Nonempty
  · obtain ⟨l₀, -, hl₀⟩ := Finset.exists_mem_eq_sup univ hn fun l => maxEdgeDist c (Ta l)
    have h1 : ∏ l, compTail c (Xs l) (Ta l) ≤ compTail c (Xs l₀) (Ta l₀) := by
      rw [← Finset.mul_prod_erase univ _ (mem_univ l₀)]
      refine mul_le_of_le_one_right (compTail_nonneg c _ _) ?_
      exact prod_le_one₀ (fun l _ => compTail_nonneg c _ _) fun l _ => compTail_le_one c _ _
    refine h1.trans ?_
    unfold compTail jTail
    rw [hl₀]
    refine pow_le_pow_left₀ (div_nonneg (blockRad_nonneg c _)
      (le_max_of_le_right (blockRad_nonneg c _))) ?_ 2
    exact div_max_le_div_max (blockRad_nonneg c _)
      (blockRad_mono c (Finset.biUnion_subset_biUnion_of_subset_left _ (hXs l₀)))
      (NNReal.coe_nonneg _) hpos
  · rw [Finset.not_nonempty_iff_eq_empty] at hn
    unfold jTail
    rw [hn, Finset.prod_empty, Finset.sup_empty]
    simp only [bot_eq_zero', NNReal.coe_zero]
    rw [max_eq_right hpos.le, div_self hpos.ne', one_pow]

theorem absEvenLift_nonneg {W : Finset ℕ} (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (e : Sym2 W) :
    0 ≤ absEvenLift M lam ε₀ R c e := by
  induction e using Sym2.ind with
  | h i j => exact absEvenWeight_nonneg M lam ε₀ R _ _

theorem keptLift_nonneg {W : Finset ℕ} (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (e : Sym2 W) :
    0 ≤ keptLift M lam ε₀ R c e :=
  keptWeight_nonneg' (cutOn_nonneg M lam ε₀ R _) e

theorem jIntegrand_nonneg (M lam ε₀ R : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ) :
    0 ≤ jIntegrand M lam ε₀ R X Xs Ta Tb c := by
  classical
  unfold jIntegrand
  refine mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) ?_) ?_) ?_
  · exact prod_nonneg fun l _ => radialExceptMax_nonneg c _
  · exact prod_nonneg fun l _ => prod_nonneg fun e _ => keptLift_nonneg M lam ε₀ R c e
  · exact prod_nonneg fun e _ => absEvenLift_nonneg M lam ε₀ R c e

end Elementary

/-! ### The absolute value of a reduced term -/

section Reduced

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

theorem abs_reducedTerm_eq (X : Finset (Finset ℕ)) (E E₁ : Finset (ℕ × ℕ)) (V₁ : Finset ℕ)
    (c : ℕ → ℂ × ℂ) :
    |reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ c| =
      ((∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
        ∏ i ∈ V₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
      (∏ p ∈ E \ E₁, |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
      ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) := by
  unfold reducedTerm
  rw [abs_mul, abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod, Finset.abs_prod,
    Finset.abs_prod]
  have h1 : ∏ i ∈ V₁, |-Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| =
      ∏ i ∈ V₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
    Finset.prod_congr rfl fun i _ => abs_neg _
  have h2 : ∏ i ∈ X.biUnion id \ V₁, |Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| =
      ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) :=
    Finset.prod_congr rfl fun i _ => abs_of_pos (Real.cosh_pos _)
  rw [h1, h2]
  ring

end Reduced

end BoundedUpper

end UpperBound

end MultipoleBKT

end
