/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.ScreenIntegral
public import MultipoleBKT.LowerBound.RouteBounded.GroupedIntegral

/-!
# The grouped bounded activity from the separate tree integrals

The proof of Proposition 4.23. The grouped identity, parity, odd-component peeling and
independent even tree precede the J integration and normalization.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical

/-- Internal adapter from the literal radial density and tree integrals of Lemma A.4
to the grouped activity. All model-specific estimates are discharged by
the finite-cutoff and infinite-cutoff consumers. -/
theorem prod_mul_abs_activity_screen_le {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {ρ : Measure (ℂ × ℂ)} {β M lam ε₀ R : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K)
    (hρ : MeasurePreserving Prod.swap ρ ρ) (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C)
    (hlam : 0 < lam) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) {k N : ℕ} (hk : (X.biUnion id).card = k)
    (D : ℂ × ℂ → ℝ) (hDm : Measurable D) (hD0 : ∀ d, 0 ≤ D d)
    (hDK : ∀ y ∈ boxConfig (X.biUnion id) N, (∏ i, D (y i)) ≠ 0 → ∀ i, y i ∈ K)
    {Q : ℝ} (hQ : 0 < Q)
    (hπ : ∀ f : (X.biUnion id → ℂ × ℂ) → ℝ,
      ∫ y, f y ∂Measure.pi (fun _ : X.biUnion id => ρ) =
        Q⁻¹ ^ k * ∫ y in boxConfig (X.biUnion id) N, f y * ∏ i, D (y i))
    {Wb Ψ Cab : ℝ} (hWb : 1 ≤ Wb) (hΨ : 1 ≤ Ψ) (hCab : 1 ≤ Cab)
    (hstab : ∀ d ∈ K, ∀ e ∈ K, stableWeight β w d e ≤ Wb)
    (hψb : ∀ d ∈ K, ψ d ≤ Ψ)
    (hb : ∀ d ∈ K, ∀ e ∈ K,
      |oddBondUnlinked β w M lam d e| ≤ Cab * absOddWeight M lam ε₀ R d e ∧
      |evenBondMult β w M lam d e| ≤ Cab * absEvenWeight M lam ε₀ R d e)
    {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hTree : ∀ {n : ℕ} (Ys : Fin n → Finset (Finset ℕ)),
      (∀ l, Ys l ⊆ X) → (∀ l j, l ≠ j → Disjoint (Ys l) (Ys j)) →
      ∀ Ta : ∀ l, SimpleGraph ((Ys l).biUnion id), (∀ l, IsRelTree (Ys l) (Ta l)) →
      ∀ Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Ys)) Tb →
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        (jIntegrand M lam ε₀ R X Ys Ta Tb (extendConfig (X.biUnion id) y) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
          ∏ i, D (y i))) ≤ ENNReal.ofReal Ct) :
    (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) * |modelActivity ρ β w ψ M lam X| ≤
      parityCount k * (Q⁻¹ ^ k * (Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k)) *
        (2 ^ (k * k * k) * Ct)) := by
  have hB : 0 ≤ Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k) * (2 ^ (k * k * k) * Ct) := by positivity
  have hbnd := prod_mul_abs_activity_of_grouped_integrals h hρ hw₁ hw₂ hψ hwb hM hX h2 hk D hDm hD0 hQ hπ hB
    (fun Xs hXs Es hEs F hF A hAE hA =>
      screen_grouped_integral_le hχ h hlam hM hX hk D hDm hD0 hDK hWb hΨ hCab hstab hψb hb
        hXs hEs hF hAE hA hCt hTree)
  apply hbnd.trans_eq
  ring

end MultipoleBKT.LowerBound.RouteBounded

end
