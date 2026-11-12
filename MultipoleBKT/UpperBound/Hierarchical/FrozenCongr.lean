/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.FrozenData

/-!
# The frozen-bad-point objects depend only on the bad dipoles

The objects of `MultipoleBKT.UpperBound.Hierarchical.FrozenData` are functions of a set `V` of bad
labels and a configuration `Z : Fin N → ℂ × ℂ`; they depend on `Z` only through `(Z j)_{j ∈ V}`,
in accordance with the paper's `Z ∈ (Λ²)^{|V_bad|}` (the paper, Definition 5.13). `extendBad V Z'` turns a configuration `Z' : V → ℂ × ℂ` of the bad labels into a
configuration of `Fin N` (by `0` off `V`); `extendBad_restrict_eq_on` and the `_congr` lemmas
identify the objects at `Z` with those at `extendBad V (Z|_V)`.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

variable {N : ℕ}

/-- A configuration of the bad labels `V`, extended by `0` to `Fin N`. -/
def extendBad (V : Finset (Fin N)) (Z' : V → ℂ × ℂ) : Fin N → ℂ × ℂ :=
  fun i => if h : i ∈ V then Z' ⟨i, h⟩ else 0

theorem extendBad_apply_of_mem (V : Finset (Fin N)) (Z' : V → ℂ × ℂ) {i : Fin N} (hi : i ∈ V) :
    extendBad V Z' i = Z' ⟨i, hi⟩ := by
  simp [extendBad, hi]

/-- `Z` and `extendBad V (Z|_V)` agree on `V`. -/
theorem extendBad_restrict_eq_on (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    ∀ i ∈ V, Z i = extendBad V (fun j : V => Z j) i := fun i hi => by
  simp [extendBad, hi]

section Congr

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z Z' : Fin N → ℂ × ℂ}

theorem badDistZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) (e : ℂ × ℂ) :
    badDistZ p₀ β lam ε₀ V Z e = badDistZ p₀ β lam ε₀ V Z' e := by
  unfold badDistZ
  exact Finset.fold_congr fun j hj => by rw [hZ j hj]

theorem goodRadiusZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) (e : ℂ × ℂ) :
    goodRadiusZ p₀ β lam ε₀ V Z e = goodRadiusZ p₀ β lam ε₀ V Z' e := by
  unfold goodRadiusZ
  rw [badDistZ_congr hZ]

theorem badRadiiZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) (j : Fin N) :
    badRadiiZ p₀ β lam ε₀ V Z j = badRadiiZ p₀ β lam ε₀ V Z' j := by
  unfold badRadiiZ
  rw [badRadiusPlusOn_congr hZ, badRadiusMinusOn_congr hZ]

theorem interactionGoodZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) :
    interactionGoodZ χ p₀ β lam ε₀ V Z = interactionGoodZ χ p₀ β lam ε₀ V Z' := by
  funext d e
  unfold interactionGoodZ
  rw [goodRadiusZ_congr hZ, goodRadiusZ_congr hZ]

theorem interactionExtZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) (d : ℂ × ℂ) {j : Fin N} (hj : j ∈ V) :
    interactionExtZ χ p₀ β lam ε₀ V Z d j = interactionExtZ χ p₀ β lam ε₀ V Z' d j := by
  unfold interactionExtZ
  rw [goodRadiusZ_congr hZ, badRadiiZ_congr hZ, hZ j hj]

theorem interactionBadZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) {i j : Fin N} (hi : i ∈ V)
    (hj : j ∈ V) :
    interactionBadZ χ p₀ β lam ε₀ V Z i j = interactionBadZ χ p₀ β lam ε₀ V Z' i j := by
  unfold interactionBadZ
  rw [badRadiiZ_congr hZ, badRadiiZ_congr hZ, hZ i hi, hZ j hj]

theorem isGoodZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) (e : ℂ × ℂ) :
    IsGoodZ p₀ β lam M ε₀ V Z e ↔ IsGoodZ p₀ β lam M ε₀ V Z' e := by
  unfold IsGoodZ
  rw [typeOneOn_congr hZ, typeTwoOn_congr hZ, typeThreeOn_congr hZ]
  have h12 : typeOneOn p₀ β lam ε₀ V Z' ∪ typeTwoOn p₀ β lam M ε₀ V Z' ⊆ V :=
    Finset.union_subset typeOneOn_subset typeTwoOn_subset
  refine and_congr (forall₂_congr fun j hj => ?_) (forall₂_congr fun j hj => ?_)
  · rw [hZ j (h12 hj)]
  · rw [hZ j (typeThreeOn_subset hj)]

theorem dipoleWeightZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) :
    dipoleWeightZ p₀ β lam M ε₀ L V Z = dipoleWeightZ p₀ β lam M ε₀ L V Z' := by
  classical
  funext e
  unfold dipoleWeightZ
  rw [goodRadiusZ_congr hZ]
  congr 1
  exact if_congr (isGoodZ_congr hZ e) rfl rfl

theorem hatDipoleWeightZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) :
    hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z = hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z' := by
  funext e
  unfold hatDipoleWeightZ
  rw [dipoleWeightZ_congr hZ]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by rw [interactionExtZ_congr hZ e hj]

theorem externalBondZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) :
    externalBondZ χ p₀ β lam ε₀ V Z = externalBondZ χ p₀ β lam ε₀ V Z' := by
  funext d
  unfold externalBondZ
  rw [Finset.prod_congr rfl fun j hj => by rw [interactionExtZ_congr hZ d hj]]

theorem badWeightZ_congr (hZ : ∀ i ∈ V, Z i = Z' i) :
    badWeightZ χ p₀ β lam M ε₀ V Z = badWeightZ χ p₀ β lam M ε₀ V Z' := by
  classical
  have h1 : (∏ i ∈ V, ∏ j ∈ V with i < j,
      if IsStableDipolePair (Z i) (Z j) then Real.exp (-β * interactionBadZ χ p₀ β lam ε₀ V Z i j)
      else 0) =
      ∏ i ∈ V, ∏ j ∈ V with i < j,
        if IsStableDipolePair (Z' i) (Z' j) then
          Real.exp (-β * interactionBadZ χ p₀ β lam ε₀ V Z' i j) else 0 := by
    refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
    have hjV := (Finset.mem_filter.1 hj).1
    rw [hZ i hi, hZ j hjV, interactionBadZ_congr hZ hi hjV]
  have h2 : (∏ i ∈ V, 1 / (badRadiusPlusOn p₀ β lam ε₀ V Z i ^ (β / 2) *
      badRadiusMinusOn p₀ β lam ε₀ V Z i ^ (β / 2))) =
      ∏ i ∈ V, 1 / (badRadiusPlusOn p₀ β lam ε₀ V Z' i ^ (β / 2) *
        badRadiusMinusOn p₀ β lam ε₀ V Z' i ^ (β / 2)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [badRadiusPlusOn_congr hZ, badRadiusMinusOn_congr hZ]
  unfold badWeightZ
  rw [badPointsOn_congr hZ, h1, h2]

end Congr

end UpperBound

end MultipoleBKT

end
