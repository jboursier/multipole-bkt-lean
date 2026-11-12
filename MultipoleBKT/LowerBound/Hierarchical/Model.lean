/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.DipoleMeasure
public import MultipoleBKT.Multipole.Composition
public import MultipoleBKT.Cluster.Relative
public import MultipoleBKT.LowerBound.Parity.MayerBond

/-!
# The hierarchical models and their activities (Definitions 4.13–4.15)

Definitions 4.13–4.15.

All the objects of Section 4.5 are instances of one construction, parametrized by a reference measure
`ρ` for one dipole, an interaction `w = (w_ij)` (a function of two dipoles, the lower label first)
and a one-body weight `ψ`:

* `modelPartitionFunction ρ β w ψ M λ S = 𝔼_{ρ^{⊗ S}}[𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β w_ij} 𝟙_{𝒜_ij}
  ∏_{i ∈ S} ψ(x_i, y_i)]`;
* `modelHierarchical ρ β w ψ M λ X`, the measure on `(ℂ × ℂ)^{V_X}` with density
  `∏_{S ∈ X} 𝖬(S)⁻¹ 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} ψ(x_i, y_i)` with respect to
  `ρ^{⊗ V_X}` (as for the frozen `hierarchicalModel`);
* `modelActivity ρ β w ψ M λ X`, zero for `|X| ≤ 1` and otherwise the series of
  Definition 4.15: `∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{Eₗ ∈ 𝖤^{Xₗ}}
  ∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}} 𝔼_{𝖯_X}[∏_{ij ∈ ∪ Eₗ} f^w_ij ∏_{ij ∈ ∪ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c}
  ∏_{ij ∈ F} (-𝟙_{𝓑_ij})]`, with the Mayer bond `f^w_ij = e^{-β w_ij} 𝟙_{𝒜_ij} - 1`
  (`MultipoleBKT.Parity.mayerBondOf`, Definition 4.14).

Edge sets are finite sets of pairs `(i, j)`, `i < j`, of labels (`MultipoleBKT.Multipole.EdgeSets`):
`𝖤^X` is `relEdgeSets X` (the `E ⊆ ℰ^inter(X)` with at least one edge such that
`E ∪ ℰ^intra(X)` connects `V_X`, Definition 4.10(4)) and `𝖤_0^X` is `relEdgeSets₀ X` (the same
without the nonemptiness, so that `𝖤_0^{{S}} = {∅}`, Definition 4.10(6); `relEdgeSets₀_eq`).
`Coarse_X(X₁, …, Xₙ)` is `MultipoleBKT.coarsen X {X₁, …, Xₙ}` (Definition 4.9). A configuration
`y` of `V_X` is read on all labels through `MultipoleBKT.Multipole.extendConfig`.

The paper's objects, for `ε₀ ∈ (0, 1)`, the truncated dipole measure `μ_{β,λ,ε₀}` and the constant
`L` of (3.53), with `R̄ = R̄_{β,λ}`:

* `zeroPartitionFunction`, `zeroModel`, `zeroActivity`: `𝖬^0_{ε₀}(X) = ∏_{S ∈ X} 𝖬^0_{ε₀}(S)`
  (eq. (4.17)), `𝖯_X^{0,ε₀}` (eq. (4.16)), `𝖪^0_{ε₀}` (Definition 4.15), with
  `ρ = μ_{β,λ,ε₀}`, `w = v` and `ψ = 1`;
* `minusPartitionFunction`, `minusModel`, `minusActivity`: `𝖬^-_{ε₀}(X)` (eq. (4.19)),
  `𝖯_X^{-,ε₀}` (eq. (4.18)), `𝖪^-_{ε₀}` (eq. (4.21)), with `ρ = μ_{β,λ,ε₀}`,
  `w = ṽ` (`MultipoleBKT.upperBoundInteraction`, Definition 3.11, screening radius `8 ε₀ R̄`)
  and `ψ(x, y) = e^{-L |x - y|² / (ε₀ R̄)²}` (`gaussianWeight`);
* `zeroActivityInf`: `𝖪^0_∞`, with `ρ = μ_{β,λ}` (the frozen `dipoleMeasure`), `w = v`, `ψ = 1`.

For `ε₀ = ∞` (and `L = 0`, interaction `v`) the constructions are the frozen ones:
`modelPartitionFunction_dipoleMeasure` (`𝖬^0_∞(S) = 𝖬_{β,λ}(S)`) and
`modelHierarchical_dipoleMeasure` (`𝖯_X^{0,∞} = 𝖯^X_{β,λ}`); the identity `𝖪^0_∞ = 𝖪^mult`
(Corollary 4.61) is `MultipoleBKT.Hierarchical.zeroActivityInf_eq_multipoleActivity`.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

/-! ### The generic constructions -/

section Generic

variable (ρ : Measure (ℂ × ℂ)) (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)

open scoped Classical in
/-- The multipole partition function of the model `(ρ, w, ψ)`:
`𝖬(S) = 𝔼_{ρ^{⊗ S}}[𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} ψ(x_i, y_i)]`
(eqs. (4.17) and (4.19), Definition 4.13). -/
noncomputable def modelPartitionFunction (S : Finset ℕ) : ℝ :=
  ∫ c : S → ℂ × ℂ,
    (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
      then 1 else 0) *
    (∏ i : S, ∏ j : S,
      if i < j then
        (if IsStableDipolePair (c i) (c j) then Real.exp (-β * w (c i) (c j)) else 0)
      else 1) *
    ∏ i : S, ψ (c i)
    ∂Measure.pi fun _ : S => ρ

open scoped Classical in
/-- The hierarchical model `𝖯_X` of the model `(ρ, w, ψ)` on `(ℂ × ℂ)^{V_X}`: the measure with
density `∏_{S ∈ X} 𝖬(S)⁻¹ 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} ψ(x_i, y_i)` with
respect to `ρ^{⊗ V_X}` (eqs. (4.16) and (4.18), Definition 4.13). -/
noncomputable def modelHierarchical (X : Finset (Finset ℕ)) : Measure (X.biUnion id → ℂ × ℂ) :=
  (Measure.pi fun _ : X.biUnion id => ρ).withDensity fun c =>
    ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction ρ β w ψ M lam S)⁻¹ *
      ((if ((SimpleGraph.fromRel fun i j : X.biUnion id =>
            MultipoleLinked M lam (c i) (c j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected
          then 1 else 0) *
        (∏ i : X.biUnion id, ∏ j : X.biUnion id,
          if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
            (if IsStableDipolePair (c i) (c j) then Real.exp (-β * w (c i) (c j)) else 0)
          else 1) *
        ∏ i : X.biUnion id, if (i : ℕ) ∈ S then ψ (c i) else 1))

end Generic

/-! ### Edge sets relative to a subpartition -/

section EdgeSets

open scoped Classical

/-- `𝖤^X` (Definition 4.10(4)): the edge sets `E ⊆ ℰ^inter(X)` with at least one
edge such that `(V_X, E ∪ ℰ^intra(X))` is connected. -/
noncomputable def relEdgeSets (X : Finset (Finset ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (interPairs X).powerset.filter fun E => E.Nonempty ∧ ConnOn (X.biUnion id) (E ∪ intraPairs X)

/-- `𝖤_0^X` (Definition 4.10(6)): the edge sets `E ⊆ ℰ^inter(X)` such that
`(V_X, E ∪ ℰ^intra(X))` is connected; it is `𝖤^X` except that `𝖤_0^{{S}} = {∅}`
(`relEdgeSets₀_eq`). -/
noncomputable def relEdgeSets₀ (X : Finset (Finset ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  (interPairs X).powerset.filter fun E => ConnOn (X.biUnion id) (E ∪ intraPairs X)

theorem mem_relEdgeSets {X : Finset (Finset ℕ)} {E : Finset (ℕ × ℕ)} :
    E ∈ relEdgeSets X ↔
      E ⊆ interPairs X ∧ E.Nonempty ∧ ConnOn (X.biUnion id) (E ∪ intraPairs X) := by
  rw [relEdgeSets, Finset.mem_filter, Finset.mem_powerset]

theorem mem_relEdgeSets₀ {X : Finset (Finset ℕ)} {E : Finset (ℕ × ℕ)} :
    E ∈ relEdgeSets₀ X ↔ E ⊆ interPairs X ∧ ConnOn (X.biUnion id) (E ∪ intraPairs X) := by
  rw [relEdgeSets₀, Finset.mem_filter, Finset.mem_powerset]

/-- `relConnSum g X = ∑_{E ∈ 𝖤_0^X} ∏_{p ∈ E} g(p)`. -/
theorem relConnSum_eq_sum_relEdgeSets₀ {R : Type*} [CommSemiring R] (g : ℕ × ℕ → R)
    (X : Finset (Finset ℕ)) : relConnSum g X = ∑ E ∈ relEdgeSets₀ X, ∏ p ∈ E, g p := rfl

theorem relEdgeSets_subset_relEdgeSets₀ (X : Finset (Finset ℕ)) :
    relEdgeSets X ⊆ relEdgeSets₀ X := by
  intro E hE
  rw [mem_relEdgeSets] at hE
  exact mem_relEdgeSets₀.2 ⟨hE.1, hE.2.2⟩

/-- A family with at most one block has no inter-block pairs. -/
theorem interPairs_eq_empty_of_card_le_one {X : Finset (Finset ℕ)} (h : X.card ≤ 1) :
    interPairs X = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨B, hB, B', hB', hBB', -, -⟩ := exists_of_mem_interPairs hp
  exact hBB' (Finset.card_le_one.1 h B hB B' hB')

/-- `𝖤^X = ∅` for `|X| ≤ 1`. -/
theorem relEdgeSets_eq_empty_of_card_le_one {X : Finset (Finset ℕ)} (h : X.card ≤ 1) :
    relEdgeSets X = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro E hE
  rw [mem_relEdgeSets, interPairs_eq_empty_of_card_le_one h, Finset.subset_empty] at hE
  obtain ⟨rfl, hne, -⟩ := hE
  exact Finset.not_nonempty_empty hne

/-- For `|X| ≥ 2`, `𝖤_0^X = 𝖤^X`. -/
theorem relEdgeSets₀_eq_of_two_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) : relEdgeSets₀ X = relEdgeSets X := by
  ext E
  rw [mem_relEdgeSets₀, mem_relEdgeSets]
  refine ⟨fun h => ⟨h.1, ?_, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [Finset.nonempty_iff_ne_empty]
  rintro rfl
  have := card_le_one_of_connOn_intraPairs hX (by simpa using h.2)
  omega

/-- `𝖤_0^X` is `𝖤^X`, except that `𝖤_0^{{S}} = {∅}` (Definition 4.10(6)). -/
theorem relEdgeSets₀_eq {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    relEdgeSets₀ X = if X.card = 1 then {∅} else relEdgeSets X := by
  split_ifs with h1
  · obtain ⟨S, rfl⟩ := Finset.card_eq_one.1 h1
    have hS : S.Nonempty := hX.1 S (Finset.mem_singleton_self S)
    ext E
    rw [mem_relEdgeSets₀, Finset.mem_singleton, interPairs_singleton, Finset.subset_empty]
    constructor
    · exact fun h => h.1
    · rintro rfl
      refine ⟨rfl, ?_⟩
      have hint : intraPairs ({S} : Finset (Finset ℕ)) = pairsOn S := Finset.singleton_biUnion
      have hU : ({S} : Finset (Finset ℕ)).biUnion id = S := by simp
      rw [hU, hint, Finset.empty_union]
      exact connOn_pairsOn hS
  · rcases Nat.lt_or_ge X.card 2 with h | h
    · have h0 : X.card = 0 := by omega
      rw [Finset.card_eq_zero] at h0
      subst h0
      ext E
      rw [mem_relEdgeSets₀, mem_relEdgeSets]
      simp [ConnOn]
    · exact relEdgeSets₀_eq_of_two_le hX h

end EdgeSets

/-! ### The activity -/

section Activity

variable (ρ : Measure (ℂ × ℂ)) (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)

open scoped Classical in
/-- The term of the activity series (Definition 4.15) for the groups `X₁, …, Xₙ`, the edge sets
`Eₗ ∈ 𝖤^{Xₗ}` and `F`, at a configuration `c` of all labels:
`∏_{ij ∈ E₁ ∪ ⋯ ∪ Eₙ} f^w_ij ∏_{ij ∈ ℰ^inter(X₁) ∪ ⋯ ∪ ℰ^inter(Xₙ)} 𝟙_{𝓑_ij^c}
∏_{ij ∈ F} (-𝟙_{𝓑_ij})`. -/
noncomputable def clusterTerm {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ Finset.univ.biUnion Es, mayerBondOf β w (c p.1) (c p.2)) *
    (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
      if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1) *
    ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)

open scoped Classical in
/-- **The activity** of the model `(ρ, w, ψ)` (Definition 4.15): `0` for `|X| ≤ 1` and, for `|X| ≥ 2`,
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{E₁ ∈ 𝖤^{X₁}} ⋯ ∑_{Eₙ ∈ 𝖤^{Xₙ}}
∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}} 𝔼_{𝖯_X}[∏_{ij ∈ E₁ ∪ ⋯ ∪ Eₙ} f^w_ij
∏_{ij ∈ ℰ^inter(X₁) ∪ ⋯ ∪ ℰ^inter(Xₙ)} 𝟙_{𝓑_ij^c} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})]`. -/
noncomputable def modelActivity (X : Finset (Finset ℕ)) : ℝ :=
  if X.card ≤ 1 then 0 else
    ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
          ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
              ∂modelHierarchical ρ β w ψ M lam X

theorem modelActivity_eq_zero_of_card_le_one {X : Finset (Finset ℕ)} (h : X.card ≤ 1) :
    modelActivity ρ β w ψ M lam X = 0 := by
  rw [modelActivity, ite_eq_left h]

end Activity

/-! ### the paper's models -/

section Source

variable (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ L : ℝ)

/-- The Gaussian damping `e^{-L |x - y|² / (ε₀ R̄_{β,λ})²}` of the lower-bound model
(eq. (4.18)). -/
noncomputable def gaussianWeight (d : ℂ × ℂ) : ℝ :=
  Real.exp (-L * (‖d.1 - d.2‖ ^ 2 / (ε₀ * truncationScale p₀ β lam) ^ 2))

/-- `𝖬^0_{ε₀}(X) = ∏_{S ∈ X} 𝔼_{μ_{β,λ,ε₀}^{⊗ |S|}}[𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}]`,
eq. (4.17) (Definition 4.13); `𝖬^0_{ε₀}(S) = 𝖬^0_{ε₀}({S})`. -/
noncomputable def zeroPartitionFunction (X : Finset (Finset ℕ)) : ℝ :=
  ∏ S ∈ X, modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (dipoleInteraction χ lam)
    (fun _ => 1) M lam S

/-- `𝖬^-_{ε₀}(X) = ∏_{S ∈ X} 𝔼_{μ_{β,λ,ε₀}^{⊗ |S|}}[𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β ṽ_ij} 𝟙_{𝒜_ij}
∏_{i ∈ S} e^{-L |x_i - y_i|² / (ε₀ R̄)²}]`, eq. (4.19) (Definition 4.13). -/
noncomputable def minusPartitionFunction (X : Finset (Finset ℕ)) : ℝ :=
  ∏ S ∈ X, modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
    (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam ε₀ L)
    M lam S

/-- The multipole measure `𝖯_X^{0,ε₀}`, eq. (4.16) (Definition 4.13). -/
noncomputable def zeroModel (X : Finset (Finset ℕ)) : Measure (X.biUnion id → ℂ × ℂ) :=
  modelHierarchical (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (dipoleInteraction χ lam)
    (fun _ => 1) M lam X

/-- The lower-bound multipole measure `𝖯_X^{-,ε₀}`, eq. (4.18) (Definition 4.13). -/
noncomputable def minusModel (X : Finset (Finset ℕ)) : Measure (X.biUnion id → ℂ × ℂ) :=
  modelHierarchical (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
    (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam ε₀ L)
    M lam X

/-- The activity `𝖪^0_{ε₀}` (Definition 4.15, first display, Definition 4.15). -/
noncomputable def zeroActivity (X : Finset (Finset ℕ)) : ℝ :=
  modelActivity (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (dipoleInteraction χ lam) (fun _ => 1)
    M lam X

/-- The activity `𝖪^-_{ε₀}`, eq. (4.21) (Definition 4.15). -/
noncomputable def minusActivity (X : Finset (Finset ℕ)) : ℝ :=
  modelActivity (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
    (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam ε₀ L)
    M lam X

/-- The activity `𝖪^0_∞` (Definition 4.15 with `ε₀ = ∞`: the dipole measure `μ_{β,λ}`, no length
cutoff, Definition 4.11). -/
noncomputable def zeroActivityInf (X : Finset (Finset ℕ)) : ℝ :=
  modelActivity (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1) M lam X

end Source

/-! ### `ε₀ = ∞`: the frozen objects -/

section Infinity

variable (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)

/-- `𝖬^0_∞(S) = 𝖬_{β,λ}(S)`: at `ε₀ = ∞`, with `w = v` and `ψ = 1`, the multipole partition
function of the model is the frozen `multipolePartitionFunction`. -/
theorem modelPartitionFunction_dipoleMeasure (S : Finset ℕ) :
    modelPartitionFunction (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1) M
      lam S = multipolePartitionFunction χ N β lam M S := by
  simp only [modelPartitionFunction, Finset.prod_const_one, mul_one]
  rfl

/-- `𝖯_X^{0,∞} = 𝖯^X_{β,λ}`: at `ε₀ = ∞`, with `w = v` and `ψ = 1`, the hierarchical model is the
frozen `hierarchicalModel`. -/
theorem modelHierarchical_dipoleMeasure (X : Finset (Finset ℕ)) :
    modelHierarchical (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1) M lam X =
      hierarchicalModel χ N β lam M X := by
  simp only [modelHierarchical, modelPartitionFunction_dipoleMeasure, ite_self,
    Finset.prod_const_one, mul_one]
  rfl

end Infinity

end Hierarchical

end MultipoleBKT

end
