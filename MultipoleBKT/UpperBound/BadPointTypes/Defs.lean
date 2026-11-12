/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Clustering
public import MultipoleBKT.Frozen.BadPoints
public import MultipoleBKT.Frozen.IsStableDipolePair
public import MultipoleBKT.Frozen.SmearedKernel
public import MultipoleBKT.Frozen.ClusterThreshold
public import MultipoleBKT.Frozen.TruncationScale
public import TwoComponentCoulomb.Frozen.Box
public import TwoComponentCoulomb.Gibbs.Basic

/-!
# The partition functions of the bad points of types 1, 2, 3

The paper: Sections 5.12–5.14 (reduction to bad points of types 1 and 2,
and their control).

**Frozen-configuration convention** (Section 5.3): the bad sets and
radii of a family of `n` dipoles `d : Fin n → ℂ × ℂ` are computed from `d` alone (clustering,
multipoles), "keeping `N` in the count thresholds": the threshold `ε₀^{-α(β)} N λ^{2(k-1)}` of
the bad points of type `(2,2,k)` (Definition 5.3) uses the ambient number `N` of dipoles, and the
positions range over the ambient box `Λ = box N`. The type-1 sets do not involve `N`. Hence:

* `typeTwoOneBad` (`I^{2,1}_bad`), `typeTwoTwoBad Nₐ k` (`I^{2,2,k}_bad` with the ambient
  threshold `Nₐ`), `typeTwoBad Nₐ` (`I^2_bad`) and `typeThreeBad Nₐ` (`I^3_bad`); for `n = Nₐ` they
  are the frozen `badPointsTypeTwo`, `badPointsTypeThree` (`typeTwoBad_self`,
  `typeThreeBad_self`, by `rfl`).
* `typeOneWeight`: `∏_i (τ_i^+ τ_i^-)^{-β/2}`, with `τ_i^± = max(λ, removal value)` the radii of
  the `q(β)`-clusterings (Definition 5.1); these are the radii `τ_i^{±,Z}` of the bad points
  (Definition 5.8), and every point is bad in the integrals below.
* The partition functions (all as Lebesgue integrals in `[0, ∞]` over `(Λ²)^n`, `Λ = box Nₐ`):
  - `typeOnePartitionFunction` `= Z^{(1)}_{bad,n}`, eq. (5.116);
  - `typeTwoPartitionFunction` `= Z^{(2)}_{bad,n}`, eq. (5.117);
  - `typeTwoOnePartitionFunction` `= Z^{(2,1)}_{bad,n}`, eq. (5.133);
  - `typeTwoTwoPartitionFunction k` `= Z^{(2,2,k)}_{bad,n}`, eq. (5.134);
  - `typedBadPartitionFunction V₁ V₂ V₃` `= Z_{bad,N₁,N₂,N₃}`, eq. (5.114), for disjoint label sets `V₁, V₂, V₃` covering `Fin n` (the paper's
    "arbitrary disjoint sets"; keeping them as parameters avoids the symmetry argument).
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)
open UpperBound (clusterRadius)

variable {n : ℕ}

/-! ### Bad sets with the ambient count threshold -/

open scoped Classical in
/-- `I^{2,1}_bad` (Definition 5.3): the labels of `U = [n] ∖ I^1_bad` whose
multipole class computed on `U` has more than `p(β)` elements. -/
noncomputable def typeTwoOneBad (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    Finset (Fin n) :=
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  U.filter fun i => pBeta p₀ β < (multipoleClassOn M lam d U i).card

open scoped Classical in
/-- `I^{2,2,k}_bad` (Definition 5.3) with the ambient count threshold
`ε₀^{-α(β)} Nₐ λ^{2(k-1)}` (frozen-configuration convention). -/
noncomputable def typeTwoTwoBad (Nₐ k : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    Finset (Fin n) :=
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  if ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (k - 1)) <
      ((U.filter fun i => (multipoleClassOn M lam d U i).card = k).card : ℝ)
  then U.filter fun i => (multipoleClassOn M lam d U i).card = k
  else ∅

/-- `I^2_bad = I^{2,1}_bad ∪ ⋃_{k ∈ [p(β)]} I^{2,2,k}_bad` (Definition 5.3) with
the ambient count threshold. -/
noncomputable def typeTwoBad (Nₐ : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    Finset (Fin n) :=
  typeTwoOneBad p₀ β lam M ε₀ d ∪
    (Finset.Icc 1 (pBeta p₀ β)).biUnion fun k => typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d

open scoped Classical in
/-- `I^3_bad` (Definition 5.4) with `I^2_bad` computed with the ambient count
threshold. -/
noncomputable def typeThreeBad (Nₐ : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    Finset (Fin n) :=
  let I₁₂ := badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d
  let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
  let J₃ := (Finset.univ \ I₁₂).filter fun i => ∃ j ∈ I₁₂,
    min (min ‖(d i).1 - (d j).1‖ ‖(d i).1 - (d j).2‖) (min ‖(d i).2 - (d j).1‖ ‖(d i).2 - (d j).2‖)
      ≤ M * max ‖(d i).1 - (d i).2‖ lam
  (Finset.univ \ I₁₂).filter fun i => (multipoleClassOn M lam d U i ∩ J₃).Nonempty

/-- With the ambient number equal to the number of dipoles, `typeTwoBad` is the frozen
`badPointsTypeTwo`. -/
theorem typeTwoBad_self (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    typeTwoBad n p₀ β lam M ε₀ d = badPointsTypeTwo p₀ β lam M ε₀ d := by
  unfold typeTwoBad typeTwoOneBad typeTwoTwoBad badPointsTypeTwo
  rfl

/-- With the ambient number equal to the number of dipoles, `typeThreeBad` is the frozen
`badPointsTypeThree`. -/
theorem typeThreeBad_self (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    typeThreeBad n p₀ β lam M ε₀ d = badPointsTypeThree p₀ β lam M ε₀ d := by
  unfold typeThreeBad badPointsTypeThree
  rw [typeTwoBad_self]

/-! ### Weights -/

/-- The cutoff `h = ε₀ R̄_{β,λ}` of the clustering (Definition 5.1). -/
noncomputable abbrev cutoff (p₀ : ℕ) (β lam ε₀ : ℝ) : ℝ := ε₀ * truncationScale p₀ β lam

/-- The dipole lengths `r_i = |x_i - y_i|`. -/
noncomputable abbrev dipoleLength (d : Fin n → ℂ × ℂ) (i : Fin n) : ℝ := ‖(d i).1 - (d i).2‖

/-- `τ_i^+ = max(λ, removal value)` of the `q(β)`-clustering of the positive charges
(Definition 5.1, cutoff `ε₀ R̄`). -/
noncomputable abbrev radiusPlus (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin n → ℂ × ℂ) (i : Fin n) : ℝ :=
  clusterRadius (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) lam (fun k => (d k).1)
    (dipoleLength d) i

/-- `τ_i^- = max(λ, removal value)` of the `q(β)`-clustering of the negative charges. -/
noncomputable abbrev radiusMinus (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin n → ℂ × ℂ) (i : Fin n) : ℝ :=
  clusterRadius (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) lam (fun k => (d k).2)
    (dipoleLength d) i

/-- The weight `∏_i (τ_i^{+,Z})^{-β/2} (τ_i^{-,Z})^{-β/2}` of bad points (eq. (5.113)), with `τ_i^{±,Z} = max(τ_i^±, λ)` (Definition 5.8). -/
noncomputable def typeOneWeight (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin n → ℂ × ℂ) : ℝ :=
  ∏ i, (radiusPlus p₀ β lam ε₀ d i * radiusMinus p₀ β lam ε₀ d i) ^ (-(β / 2))

/-- The weight `∏_i e^{β g_λ(x_i - y_i)}`. -/
noncomputable def dipoleWeight (χ : ℂ → ℝ) (β lam : ℝ) (d : Fin n → ℂ × ℂ) : ℝ :=
  ∏ i, Real.exp (β * smearedKernel χ lam ((d i).1 - (d i).2))

/-- The matching constraint `∏_{i<j} 𝟙_{𝒜_ij}`. -/
def StablePairs (d : Fin n → ℂ × ℂ) : Prop :=
  ∀ i j : Fin n, i < j → IsStableDipolePair (d i) (d j)

/-- The configuration space `(Λ²)^n`, `Λ = box Nₐ`. -/
abbrev boxPi (Nₐ n : ℕ) : Set (Fin n → ℂ × ℂ) := Set.univ.pi fun _ => box Nₐ ×ˢ box Nₐ

theorem measurableSet_boxPi (Nₐ n : ℕ) : MeasurableSet (boxPi Nₐ n) :=
  MeasurableSet.univ_pi fun _ =>
    (TwoComponentCoulomb.measurableSet_box Nₐ).prod (TwoComponentCoulomb.measurableSet_box Nₐ)

/-! ### The partition functions -/

open scoped Classical in
/-- **`Z^{(1)}_{bad,n}`**, eq. (5.116):
`∫_{(Λ²)^n} 𝟙_{I^1_bad = [n]} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i (τ_i^{+,Z} τ_i^{-,Z})^{-β/2} dx dy`, the bad
sets and radii computed from the `n` dipoles alone, `Λ = box Nₐ`. -/
noncomputable def typeOnePartitionFunction (p₀ : ℕ) (β lam ε₀ : ℝ) (Nₐ n : ℕ) : ℝ≥0∞ :=
  ∫⁻ d in boxPi Nₐ n,
    (if badPointsTypeOne p₀ β lam ε₀ d = Finset.univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d)

open scoped Classical in
/-- **`Z^{(2)}_{bad,n}`**, eq. (5.117):
`∫_{(Λ²)^n} 𝟙_{I^2_bad = [n]} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i e^{β g_λ(x_i - y_i)} dx dy`. -/
noncomputable def typeTwoPartitionFunction (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ n : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ d in boxPi Nₐ n,
    (if typeTwoBad Nₐ p₀ β lam M ε₀ d = Finset.univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (dipoleWeight χ β lam d)

open scoped Classical in
/-- **`Z^{(2,1)}_{bad,n}`**, eq. (5.133):
`∫_{(Λ²)^n} 𝟙_{I^{2,1}_bad = [n]} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i e^{β g_λ(x_i - y_i)} dx dy`. -/
noncomputable def typeTwoOnePartitionFunction (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (Nₐ n : ℕ) : ℝ≥0∞ :=
  ∫⁻ d in boxPi Nₐ n,
    (if typeTwoOneBad p₀ β lam M ε₀ d = Finset.univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (dipoleWeight χ β lam d)

open scoped Classical in
/-- **`Z^{(2,2,k)}_{bad,n}`**, eq. (5.134):
`∫_{(Λ²)^n} 𝟙_{I^{2,2,k}_bad = [n]} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i e^{β g_λ(x_i - y_i)} dx dy`, with the
ambient count threshold `ε₀^{-α(β)} Nₐ λ^{2(k-1)}`. -/
noncomputable def typeTwoTwoPartitionFunction (χ : ℂ → ℝ) (k : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (Nₐ n : ℕ) : ℝ≥0∞ :=
  ∫⁻ d in boxPi Nₐ n,
    (if typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = Finset.univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (dipoleWeight χ β lam d)

open scoped Classical in
/-- **`Z_{bad,N₁,N₂,N₃}`**, eq. (5.114), for label sets `V₁, V₂, V₃`
of `Fin n` (the paper's arbitrary disjoint sets of cardinalities `N₁, N₂, N₃`):
`∫_{(Λ²)^n} ∏_{i=1}^3 𝟙_{I^i_bad = V_i} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i (τ_i^{+,Z} τ_i^{-,Z})^{-β/2} dx dy`. -/
noncomputable def typedBadPartitionFunction (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ n : ℕ)
    (V₁ V₂ V₃ : Finset (Fin n)) : ℝ≥0∞ :=
  ∫⁻ d in boxPi Nₐ n,
    (if badPointsTypeOne p₀ β lam ε₀ d = V₁ ∧ typeTwoBad Nₐ p₀ β lam M ε₀ d = V₂ ∧
        typeThreeBad Nₐ p₀ β lam M ε₀ d = V₃ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d)

/-! ### Basic facts -/

theorem typeTwoOneBad_subset (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    typeTwoOneBad p₀ β lam M ε₀ d ⊆ Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d := by
  unfold typeTwoOneBad
  exact Finset.filter_subset _ _

theorem typeTwoTwoBad_subset (Nₐ k p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d ⊆ Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d := by
  unfold typeTwoTwoBad
  dsimp only
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

/-- If `I^{2,1}_bad` is everything, there are no bad points of type 1. -/
theorem badPointsTypeOne_eq_empty_of_typeTwoOneBad {p₀ : ℕ} {β lam M ε₀ : ℝ}
    {d : Fin n → ℂ × ℂ} (h : typeTwoOneBad p₀ β lam M ε₀ d = Finset.univ) :
    badPointsTypeOne p₀ β lam ε₀ d = ∅ := by
  have hs := typeTwoOneBad_subset p₀ β lam M ε₀ d
  rw [h] at hs
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  exact (Finset.mem_sdiff.1 (hs (Finset.mem_univ i))).2 hi

/-- If `I^{2,2,k}_bad` is everything, there are no bad points of type 1. -/
theorem badPointsTypeOne_eq_empty_of_typeTwoTwoBad {Nₐ k p₀ : ℕ} {β lam M ε₀ : ℝ}
    {d : Fin n → ℂ × ℂ} (h : typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = Finset.univ) :
    badPointsTypeOne p₀ β lam ε₀ d = ∅ := by
  have hs := typeTwoTwoBad_subset Nₐ k p₀ β lam M ε₀ d
  rw [h] at hs
  refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
  exact (Finset.mem_sdiff.1 (hs (Finset.mem_univ i))).2 hi

theorem typeOneWeight_nonneg (p₀ : ℕ) (β : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) (ε₀ : ℝ)
    (d : Fin n → ℂ × ℂ) : 0 ≤ typeOneWeight p₀ β lam ε₀ d := by
  unfold typeOneWeight
  refine Finset.prod_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg ?_ ?_) _
  · exact hlam.trans (UpperBound.le_clusterRadius lam i)
  · exact hlam.trans (UpperBound.le_clusterRadius lam i)

theorem dipoleWeight_nonneg (χ : ℂ → ℝ) (β lam : ℝ) (d : Fin n → ℂ × ℂ) :
    0 ≤ dipoleWeight χ β lam d :=
  Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le

end BadPointTypes

end MultipoleBKT

end
