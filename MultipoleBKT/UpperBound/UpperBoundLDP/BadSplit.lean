/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.RouteCount.Sum
public import MultipoleBKT.UpperBound.UpperBoundLDP.BadRelabel
public import MultipoleBKT.UpperBound.UpperBoundLDP.TypeTwoSplit

/-!
# The splitting of the bad points into the three types (eq. (5.115))

The paper: eq. (5.115): the partition
function of the bad points is split according to the types,

  `Z_{bad,m} ≤ ∑_{f : [m] → {1, 2, 3}} Z_{bad,|f⁻¹(1)|,|f⁻¹(2)|,|f⁻¹(3)|}`

(`badPartitionFunction_le_sum`; the paper writes the sum over the `3^m` labellings as `3^m` times
a maximum of multinomial terms), where the type sets `I^1_bad`, `I^2_bad`, `I^3_bad` are disjoint
by Definitions 5.2–5.4.

The labellings are grouped by their class counts by `RouteCount.sum_counts`.
The resulting multinomial coefficients are absorbed by the factorial entropy
estimate of `RouteCount.multinomial_entropy_factorial`, retaining the outer
factorial for `binom(N,m)` as in Proposition 5.38.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset TheoremTwo BadPointTypes UpperBound
open scoped ENNReal

variable {m : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {Nₐ : ℕ}

/-! ### The three types -/

section ThreeTypes

theorem typeTwoBad_subset_compl (Nₐ : ℕ) (d : Fin m → ℂ × ℂ) :
    typeTwoBad Nₐ p₀ β lam M ε₀ d ⊆ univ \ badPointsTypeOne p₀ β lam ε₀ d := by
  intro i hi
  exact ((mem_typeTwoBad_iff Nₐ).1 hi).1

theorem typeThreeBad_subset_compl (Nₐ : ℕ) (d : Fin m → ℂ × ℂ) :
    typeThreeBad Nₐ p₀ β lam M ε₀ d ⊆
      univ \ (badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d) := by
  unfold typeThreeBad
  exact Finset.filter_subset _ _

/-- The set of configurations whose type sets are the fibres of `f`. -/
def typedLabelSet (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ : ℕ) (f : Fin m → Fin 3) :
    Set (Fin m → ℂ × ℂ) :=
  {d | (badPointsTypeOne p₀ β lam ε₀ d, typeTwoBad Nₐ p₀ β lam M ε₀ d,
    typeThreeBad Nₐ p₀ β lam M ε₀ d) = (fiber f 0, fiber f 1, fiber f 2)}

theorem measurableSet_typedLabelSet (f : Fin m → Fin 3) :
    MeasurableSet (typedLabelSet p₀ β lam M ε₀ Nₐ f) :=
  fiberMeasurable_typedSets Nₐ p₀ β lam M ε₀ _

open scoped Classical in
theorem exists_typedLabelSet {d : Fin m → ℂ × ℂ}
    (h : badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d ∪
      typeThreeBad Nₐ p₀ β lam M ε₀ d = univ) :
    ∃ f : Fin m → Fin 3, d ∈ typedLabelSet p₀ β lam M ε₀ Nₐ f := by
  set I1 := badPointsTypeOne p₀ β lam ε₀ d
  set I2 := typeTwoBad Nₐ p₀ β lam M ε₀ d
  set I3 := typeThreeBad Nₐ p₀ β lam M ε₀ d
  have h2 : ∀ a ∈ I2, a ∉ I1 := fun a ha => (mem_sdiff.1 (typeTwoBad_subset_compl Nₐ d ha)).2
  have h3 : ∀ a ∈ I3, a ∉ I1 ∪ I2 := fun a ha =>
    (mem_sdiff.1 (typeThreeBad_subset_compl Nₐ d ha)).2
  have hcov : ∀ a, a ∈ I1 ∨ a ∈ I2 ∨ a ∈ I3 := by
    intro a
    have : a ∈ I1 ∪ I2 ∪ I3 := h ▸ mem_univ a
    simp only [mem_union] at this
    tauto
  set f : Fin m → Fin 3 := fun a => if a ∈ I1 then 0 else if a ∈ I2 then 1 else 2
  refine ⟨f, ?_⟩
  simp only [typedLabelSet, Set.mem_ofPred_eq, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ext a <;> rw [mem_fiber] <;> simp only [f]
  · split_ifs with ha1 ha2
    · exact ⟨fun _ => rfl, fun _ => ha1⟩
    · exact ⟨fun h => absurd h ha1, fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd h ha1, fun h => absurd h (by decide)⟩
  · split_ifs with ha1 ha2
    · exact ⟨fun h => absurd ha1 (h2 a h), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => ha2⟩
    · exact ⟨fun h => absurd h ha2, fun h => absurd h (by decide)⟩
  · split_ifs with ha1 ha2
    · exact ⟨fun h => absurd (mem_union_left _ ha1) (h3 a h), fun h => absurd h (by decide)⟩
    · exact ⟨fun h => absurd (mem_union_right _ ha2) (h3 a h), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => ((hcov a).resolve_left ha1).resolve_left ha2⟩

open scoped Classical in
/-- **Eq. (5.115)** : `Z_{bad,m}` is at most the sum over the labellings
`f : [m] → {1, 2, 3}` of `Z_{bad,N₁,N₂,N₃}` for the fibres of `f`. -/
theorem badPartitionFunction_le_sum (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ m : ℕ) :
    badPartitionFunction p₀ β lam M ε₀ Nₐ m ≤
      ∑ f : Fin m → Fin 3,
        typedBadPartitionFunction p₀ β lam M ε₀ Nₐ m (fiber f 0) (fiber f 1) (fiber f 2) := by
  set g : (Fin m → ℂ × ℂ) → ℝ≥0∞ := (boxPi Nₐ m).indicator fun d =>
    (if badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d ∪
        typeThreeBad Nₐ p₀ β lam M ε₀ d = univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d) with hg
  set E : (Fin m → Fin 3) → Set (Fin m → ℂ × ℂ) := typedLabelSet p₀ β lam M ε₀ Nₐ
  set S : Option (Fin m → Fin 3) → Set (Fin m → ℂ × ℂ) := fun o => o.elim (⋃ f, E f)ᶜ E with hS
  have hSm : ∀ o, MeasurableSet (S o) := by
    rintro (_ | f)
    · exact (MeasurableSet.iUnion fun f => measurableSet_typedLabelSet f).compl
    · exact measurableSet_typedLabelSet f
  have hcov : (⋃ o, S o) = Set.univ := by
    ext d
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hd : d ∈ ⋃ f, E f
    · obtain ⟨f, hf⟩ := Set.mem_iUnion.1 hd
      exact ⟨some f, hf⟩
    · exact ⟨none, hd⟩
  have hnone : ∫⁻ d in S none, g d = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ d in S none, g d ≤ ∫⁻ _d in S none, 0 := setLIntegral_mono' (hSm none) fun d hd => by
          simp only [hS, Option.elim_none, Set.mem_compl_iff] at hd
          simp only [hg]
          by_cases hbox : d ∈ boxPi Nₐ m
          · rw [Set.indicator_of_mem hbox]
            split_ifs with h
            · obtain ⟨f, hf⟩ := exists_typedLabelSet h.1
              exact absurd (Set.mem_iUnion.2 ⟨f, hf⟩) hd
            · rw [zero_mul]
          · rw [Set.indicator_of_notMem hbox]
      _ = 0 := lintegral_zero
  have hsome : ∀ f : Fin m → Fin 3, ∫⁻ d in S (some f), g d ≤
      typedBadPartitionFunction p₀ β lam M ε₀ Nₐ m (fiber f 0) (fiber f 1) (fiber f 2) := by
    intro f
    rw [typedBadPartitionFunction_eq_lintegral]
    refine le_trans ?_ (setLIntegral_le_lintegral (S (some f)) _)
    refine setLIntegral_mono' (hSm _) fun d hd => ?_
    simp only [hS, Option.elim_some] at hd
    have hd' : badPointsTypeOne p₀ β lam ε₀ d = fiber f 0 ∧
        typeTwoBad Nₐ p₀ β lam M ε₀ d = fiber f 1 ∧
        typeThreeBad Nₐ p₀ β lam M ε₀ d = fiber f 2 := by
      have := hd
      simp only [E, typedLabelSet, Set.mem_ofPred_eq, Prod.mk.injEq] at this
      exact this
    simp only [hg]
    unfold typedIntegrand
    by_cases hbox : d ∈ boxPi Nₐ m
    · rw [Set.indicator_of_mem hbox, Set.indicator_of_mem hbox]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd ⟨hd'.1, hd'.2.1, hd'.2.2, h1.2⟩ h2
      · rw [zero_mul]; exact zero_le
      · exact le_rfl
    · rw [Set.indicator_of_notMem hbox, Set.indicator_of_notMem hbox]
  calc badPartitionFunction p₀ β lam M ε₀ Nₐ m = ∫⁻ d, g d := by
        unfold badPartitionFunction
        rw [hg, lintegral_indicator (measurableSet_boxPi Nₐ m)]
    _ = ∫⁻ d in ⋃ o, S o, g d := by rw [hcov, setLIntegral_univ]
    _ ≤ ∑' o, ∫⁻ d in S o, g d := lintegral_iUnion_le S g
    _ = ∑ f : Fin m → Fin 3, ∫⁻ d in S (some f), g d := by
        rw [tsum_fintype, Fintype.sum_option, hnone, zero_add]
    _ ≤ _ := Finset.sum_le_sum fun f _ => hsome f

end ThreeTypes

end UpperBoundLDP

end MultipoleBKT

end
