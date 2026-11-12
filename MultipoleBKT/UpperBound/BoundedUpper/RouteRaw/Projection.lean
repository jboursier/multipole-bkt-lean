/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.Expansion

/-!
# Reversal projection before regrouping the raw terms

The paper: Corollary 5.24, and Proposition 5.18. Successive averages over block reversals remove the
non-parity terms of the nested marked expansion. Linearity then permits
regrouping the surviving terms for the coefficient-one estimate.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity NonEmptyMarks
open scoped Classical

/-- Successively average a function over each of a list of symmetries. -/
noncomputable def reversalAverage {α ι : Type*} (τ : ι → α → α) : List ι → (α → ℝ) → α → ℝ
  | [], f => f
  | S :: Ss, f => reversalAverage τ Ss (fun c => (f c + f (τ S c)) / 2)

/-- Averaging commutes with finite sums, so it can be applied inside the raw expansion. -/
theorem reversalAverage_sum {α ι κ : Type*} (τ : ι → α → α) (Ss : List ι)
    (s : Finset κ) (f : κ → α → ℝ) :
    reversalAverage τ Ss (fun c => ∑ i ∈ s, f i c) =
      fun c => ∑ i ∈ s, reversalAverage τ Ss (f i) c := by
  induction Ss generalizing f with
  | nil => rfl
  | cons S Ss ih =>
    simp only [reversalAverage]
    rw [show (fun c => ((∑ i ∈ s, f i c) + ∑ i ∈ s, f i (τ S c)) / 2) =
      (fun c => ∑ i ∈ s, (f i c + f i (τ S c)) / 2) by
        funext c
        rw [← sum_add_distrib, sum_div]]
    exact ih _

theorem reversalAverage_mul {α ι : Type*} (τ : ι → α → α) (Ss : List ι)
    (a : ℝ) (f : α → ℝ) :
    reversalAverage τ Ss (fun c => a * f c) = fun c => a * reversalAverage τ Ss f c := by
  induction Ss generalizing f with
  | nil => rfl
  | cons S Ss ih =>
    simp only [reversalAverage]
    rw [show (fun c => (a * f c + a * f (τ S c)) / 2) =
      (fun c => a * ((f c + f (τ S c)) / 2)) by funext c; ring]
    exact ih _

/-- A simultaneous eigenfunction survives exactly when every block has even degree. -/
theorem reversalAverage_eigen {α ι : Type*} (τ : ι → α → α) (Ss : List ι)
    (d : ι → ℕ) (f : α → ℝ)
    (hf : ∀ S ∈ Ss, ∀ c, f (τ S c) = (-1) ^ d S * f c) :
    reversalAverage τ Ss f = if ∀ S ∈ Ss, Even (d S) then f else fun _ => 0 := by
  induction Ss with
  | nil => simp [reversalAverage]
  | cons S Ss ih =>
    have hzero : reversalAverage τ Ss (fun _ => 0) = fun _ => 0 := by
      have := reversalAverage_mul τ Ss 0 f
      simpa only [zero_mul] using this
    by_cases hd : Even (d S)
    · have hav : (fun c => (f c + f (τ S c)) / 2) = f := by
        funext c
        rw [hf S (List.mem_cons_self ..) c, hd.neg_one_pow]
        ring
      simp only [reversalAverage, hav]
      rw [ih (fun T hT => hf T (List.mem_cons_of_mem S hT))]
      simp only [List.mem_cons, forall_eq_or_imp, hd, true_and]
    · have hav : (fun c => (f c + f (τ S c)) / 2) = fun _ => 0 := by
        funext c
        rw [hf S (List.mem_cons_self ..) c, (Nat.not_even_iff_odd.1 hd).neg_one_pow]
        ring
      simp only [reversalAverage, hav, hzero]
      rw [ite_eq_right (by simpa only [List.mem_cons, forall_eq_or_imp, not_and_or] using Or.inl hd)]

/-- Applied to a raw marked term, reversal removes precisely its non-parity cases. -/
theorem reversalAverage_markedTerm {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ} (hM : 1 ≤ M)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) (U U₁ : Finset ℕ)
    (E₁ : Finset (ℕ × ℕ)) :
    reversalAverage (flipOn Prod.swap) X.toList
        (markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁) =
      if IsParityPair X E₁ U₁ then markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁
      else fun _ => 0 := by
  have h := reversalAverage_eigen (flipOn Prod.swap) X.toList
    (fun S => blockDeg E₁ S + (S ∩ U₁).card)
    (markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁)
    (fun S _ c => markedTerm_flipOn hM Xs Es F U U₁ E₁ S c)
  have heq : (∀ S ∈ X.toList, Even (blockDeg E₁ S + (S ∩ U₁).card)) ↔
      IsParityPair X E₁ U₁ := by simp only [Finset.mem_toList, IsParityPair]
  by_cases hp : IsParityPair X E₁ U₁
  · simpa only [ite_eq_left (heq.mpr hp), ite_eq_left hp] using h
  · simpa only [ite_eq_right (heq.not.mpr hp), ite_eq_right hp] using h

/-- The same projection reads the already regrouped reduced terms. -/
theorem reversalAverage_reducedTerm {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ} (hM : 1 ≤ M)
    (X : Finset (Finset ℕ)) (E E₁ : Finset (ℕ × ℕ)) (U₁ : Finset ℕ) :
    reversalAverage (flipOn Prod.swap) X.toList
        (reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁) =
      if IsParityPair X E₁ U₁ then reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁
      else fun _ => 0 := by
  have h := reversalAverage_eigen (flipOn Prod.swap) X.toList
    (fun S => blockDeg E₁ S + (S ∩ U₁).card)
    (reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁)
    (fun S _ c => reducedTerm_flipOn hM X E E₁ U₁ S c)
  have heq : (∀ S ∈ X.toList, Even (blockDeg E₁ S + (S ∩ U₁).card)) ↔
      IsParityPair X E₁ U₁ := by simp only [Finset.mem_toList, IsParityPair]
  by_cases hp : IsParityPair X E₁ U₁
  · simpa only [ite_eq_left (heq.mpr hp), ite_eq_left hp] using h
  · simpa only [ite_eq_right (heq.not.mpr hp), ite_eq_right hp] using h

/-- Corollary 5.24 applied inside one raw marked group.
No connected-graph regrouping precedes this cancellation. -/
theorem reversalAverage_clusterTerm_mul {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ} (hM : 1 ≤ M)
    (X : Finset (Finset ℕ)) {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    (F : Finset (ℕ × ℕ)) (U : Finset ℕ) :
    reversalAverage (flipOn Prod.swap) X.toList (fun c =>
      clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F c *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (c i)) =
      fun c => ∑ E₁ ∈ (univ.biUnion Es).powerset,
        ∑ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
          markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c := by
  have heq := funext (clusterTerm_mul_eq_sum (χ := χ) (p₀ := p₀) (β := β)
    (lam := lam) (M := M) (ε₀ := ε₀) (V := V) (Z := Z) hEs F U)
  rw [heq, reversalAverage_sum]
  simp_rw [reversalAverage_sum, reversalAverage_markedTerm hM]
  funext c
  apply sum_congr rfl
  intro E₁ _
  simp only [Finset.sum_filter, ite_apply]

/-- The external even and unused marks can be summed while the raw groups
and their parity restriction are retained. -/
noncomputable def rawProjectedTerm {N : ℕ} (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ))
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ))
    (F : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ U ∈ (X.biUnion id).powerset, ∑ E₁ ∈ (univ.biUnion Es).powerset,
    ∑ U₁ ∈ U.powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
      markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c

theorem reversalAverage_raw {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}
    {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ} (hM : 1 ≤ M)
    (X : Finset (Finset ℕ)) {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    (F : Finset (ℕ × ℕ)) :
    reversalAverage (flipOn Prod.swap) X.toList (fun c =>
      clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F c *
        ∏ i ∈ X.biUnion id, (1 + externalBondZ χ p₀ β lam ε₀ V Z (c i))) =
      rawProjectedTerm χ p₀ β lam M ε₀ V Z X Xs Es F := by
  simp_rw [Finset.prod_one_add, Finset.mul_sum]
  rw [reversalAverage_sum]
  simp_rw [reversalAverage_clusterTerm_mul hM X hEs]
  rfl

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
