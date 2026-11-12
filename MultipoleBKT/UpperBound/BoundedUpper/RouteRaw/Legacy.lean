/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.RouteRaw.RawIntegral

/-!
# The activity sum bound from the raw expansion

The paper: Proposition 5.18. The proof first applies Corollary 5.24
to the nested marked terms. Regrouping under that projection preserves the
coefficient-one statement. The paper estimate of `prop_5_18`
continues with the separated raw terms and the replacement-tree families.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper

open MeasureTheory Finset Hierarchical Multipole Parity

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

open scoped Classical in
/-- The coefficient-one compatibility bound for Proposition 5.18, derived
from the raw marked expansion and its reversal cancellation: for a subpartition `X` with `|X| ≥ 2`, `M ≥ 1` and
`𝖬^{+,Z}_{ε₀}(S) ≠ 0` (`S ∈ X`),
`|𝖪^{+,Z}_{ε₀}(X)| ≤ ∑_{E ∈ 𝖤_0^X} ∑_{E₁ ⊆ E} ∑_{V₁ ⊆ V_X, E₁ ∈ Eul^X(V₁)}
  𝔼_{𝖯^{+,ε₀,Z}_X}[|reducedTerm X E E₁ V₁|]`. -/
theorem abs_plusActivity_le (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) (hM0 : ∀ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ≠ 0) :
    |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
      ∑ E ∈ relEdgeSets₀ X, ∑ E₁ ∈ E.powerset,
        ∑ V₁ ∈ (X.biUnion id).powerset.filter (fun V₁ => IsParityPair X E₁ V₁),
          ∫ y, |reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ (extendConfig (X.biUnion id) y)|
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  classical
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  have hint : ∀ E ∈ relEdgeSets₀ X, ∀ E₁ ∈ E.powerset,
      ∀ U₁ ∈ (X.biUnion id).powerset.filter (fun U₁ => IsParityPair X E₁ U₁),
      Integrable (fun y => reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁
        (extendConfig (X.biUnion id) y)) (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
    intro E hE E₁ hE₁ U₁ hU₁
    exact h.integrable_comp_extendConfig (measurable_reducedTerm hχ hlam X E E₁ U₁)
      (boundedOn_reducedTerm hχ hlam X E E₁ U₁)
      (dependsOn_reducedTerm (mem_relEdgeSets₀.1 hE).1 (mem_powerset.1 hE₁)
        (mem_powerset.1 (mem_filter.1 hU₁).1))
  rw [RouteRaw.plusActivity_eq_integral_rawProjectedSum hχ hlam hε₀ hN hM hX h2 hM0]
  -- Parity has already been cancelled separately in the raw marked groups.
  simp_rw [RouteRaw.rawProjectedSum_eq_reduced hM hX h2]
  rw [integral_finsetSum _ fun E hE => integrable_finsetSum _ fun E₁ hE₁ =>
    integrable_finsetSum _ fun U₁ hU₁ => hint E hE E₁ hE₁ U₁ hU₁]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun E hE => ?_)
  rw [integral_finsetSum _ fun E₁ hE₁ => integrable_finsetSum _ fun U₁ hU₁ =>
    hint E hE E₁ hE₁ U₁ hU₁]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun E₁ hE₁ => ?_)
  rw [integral_finsetSum _ fun U₁ hU₁ => hint E hE E₁ hE₁ U₁ hU₁]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun U₁ _ => abs_integral_le_integral_abs)

end MultipoleBKT.UpperBound.BoundedUpper

end
