/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.JGraphs
public import MultipoleBKT.LowerBound.Peeling.Quadratic
public import MultipoleBKT.LowerBound.Peeling.Dipole

/-!
# The J integrals and their hatted variants

See Lemma A.4, (A.17).
The hatted integrals remove the spatial cutoffs, then the radial cutoff.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps

section Defs

variable {V : Type*} [Fintype V]

/-- The tail factor `min(max_i r_i / max_{e ∈ T^a} d_e, 1)²` of (A.17), with the paper's
convention `max_∅ d_e = 0⁺` (the factor is `1` for `T^a = ∅`). -/
noncomputable def tailJ (r : V → ℝ) (d : Sym2 V → ℝ) (Ta : Finset (Sym2 V)) : ℝ :=
  if h : Ta.Nonempty then min (univ.fold max 0 r / Ta.sup' h d) 1 ^ 2 else 1

end Defs

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- **The integrand of `J`** (eq. (A.17)), for the groups `Xs`, the trees `Ta l` (relative to
`Xs l`) and `Tb` (relative to the coarsening), the selection `hatS` of the blocks `Ŝ_l`, at the
configuration `z` of the dipoles of `V_X`. -/
noncomputable def integrandJ (χ : ℂ → ℝ) (β lam M ε₀ : ℝ) (p₀ : ℕ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) (z : X.biUnion id → ℂ × ℂ) : ℝ :=
  tailJ (fun i => dipoleLength (z i)) (dipoleDistOn z)
      (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) *
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hatS l z),
      blockRadius hX (fun i => dipoleLength (z i)) S ^ 2) *
    (∏ e ∈ univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset,
      keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ (truncationScale p₀ β lam) z) e) *
    (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset,
      (absWeight (fun i => dipoleLength (z i)) (dipoleDistOn z)
        (absIndicator M lam ε₀ (truncationScale p₀ β lam) z) e ^ 2 + linkE M lam z e)) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) z) S) then 1 else 0) *
    ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (z i)

/-- **The integral `J`** of eq. (A.17), over `(Λ²)^{V_X}`, `Λ = Λ_N`. -/
noncomputable def integralJ (χ : ℂ → ℝ) (β lam M ε₀ : ℝ) (p₀ N : ℕ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) : ENNReal :=
  ∫⁻ z in boxConfig (X.biUnion id) N,
    ENNReal.ofReal (integrandJ χ β lam M ε₀ p₀ hX Xs Ta Tb hatS z)

open scoped Classical in
/-- **The integrand of `Ĵ`**, Lemma A.4, for the groups `Xs`, the trees `Ta l` (relative to
`Xs l`) and `Tb` (relative to the coarsening), the selection `hatS` of the blocks `Ŝ_l`, at the
configuration `z` of the dipoles of `V_X`. -/
noncomputable def integrandHatJ (χ : ℂ → ℝ) (β lam M ε₀ : ℝ) (p₀ : ℕ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) (z : X.biUnion id → ℂ × ℂ) : ℝ :=
  tailJ (fun i => dipoleLength (z i)) (dipoleDistOn z)
      (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) *
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hatS l z),
      blockRadius hX (fun i => dipoleLength (z i)) S ^ 2) *
    (∏ e ∈ univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset,
      keptE M lam z e) *
    (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset,
      (aSqE M lam z e + linkE M lam z e)) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) z) S) then 1 else 0) *
    ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (z i)

/-- **The integral `Ĵ`**, with spatial cutoffs removed and hatted even weights, over `(Λ²)^{V_X}`, `Λ = Λ_N`. -/
noncomputable def integralHatJ (χ : ℂ → ℝ) (β lam M ε₀ : ℝ) (p₀ N : ℕ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) : ENNReal :=
  ∫⁻ z in boxConfig (X.biUnion id) N,
    ENNReal.ofReal (integrandHatJ χ β lam M ε₀ p₀ hX Xs Ta Tb hatS z)

open scoped Classical in
/-- **The integrand of `Ĵ_∞`**, Lemma A.4, for the groups `Xs`, the trees `Ta l` (relative to
`Xs l`) and `Tb` (relative to the coarsening), the selection `hatS` of the blocks `Ŝ_l`, at the
configuration `z` of the dipoles of `V_X`. -/
noncomputable def integrandHatJInfinity (χ : ℂ → ℝ) (β lam M : ℝ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) (z : X.biUnion id → ℂ × ℂ) : ℝ :=
  tailJ (fun i => dipoleLength (z i)) (dipoleDistOn z)
      (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) *
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hatS l z),
      blockRadius hX (fun i => dipoleLength (z i)) S ^ 2) *
    (∏ e ∈ univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset,
      keptE M lam z e) *
    (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset,
      (aSqE M lam z e + linkE M lam z e)) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) z) S) then 1 else 0) *
    ∏ i, pairDensity χ β lam (z i)

/-- The hatted integral with both spatial and radial cutoffs removed.
See Lemma A.4. -/
noncomputable def integralHatJInfinity (χ : ℂ → ℝ) (β lam M : ℝ) (N : ℕ)
    (hX : IsSubpartition X) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) : ENNReal :=
  ∫⁻ z in boxConfig (X.biUnion id) N,
    ENNReal.ofReal (integrandHatJInfinity χ β lam M hX Xs Ta Tb hatS z)

end MultipoleBKT.SmallIntegral

end
