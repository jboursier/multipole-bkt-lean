/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.Defs
public import MultipoleBKT.Main.TheoremTwo.MeasurableBadPoints

/-!
# Measurability of the bad sets with an ambient count threshold

The decompositions of the partition function of the bad points in the proof of
Proposition 5.38 (equations (5.115) and (5.132)) split the configuration space
of `n` dipoles according to the values of the bad sets `I^1_bad`, `I^2_bad`, `I^3_bad` and of
the type-2 classes `I^{2,1}_bad`, `I^{2,2,k}_bad` (with the ambient count threshold `Nₐ`,
`MultipoleBKT.BadPointTypes.typeTwoBad`). These sets have measurable fibres
(`MultipoleBKT.TheoremTwo.FiberMeasurable`): they depend on the configuration only through the
type-1 set (whose fibres are measurable, `MultipoleBKT.TheoremTwo.fiberMeasurable_badPointsTypeOne`)
and through finitely many measurable relations between the dipoles.

* `fiberMeasurable_typeTwoOneBad`, `fiberMeasurable_typeTwoTwoBad`, `fiberMeasurable_typeTwoBad`,
  `fiberMeasurable_typeThreeBad`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset TheoremTwo BadPointTypes

variable {n : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-! ### Congruence -/

section Congr

variable {d e : Fin n → ℂ × ℂ}

theorem typeTwoOneBad_congr (h1 : badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e)
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j)) :
    typeTwoOneBad p₀ β lam M ε₀ d = typeTwoOneBad p₀ β lam M ε₀ e := by
  have hcls : multipoleClassOn M lam d = multipoleClassOn M lam e :=
    funext fun U => funext fun i => multipoleClassOn_congr hL U i
  unfold typeTwoOneBad
  rw [h1, hcls]

theorem typeTwoTwoBad_congr (Nₐ k : ℕ)
    (h1 : badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e)
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j)) :
    typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = typeTwoTwoBad Nₐ k p₀ β lam M ε₀ e := by
  have hcls : multipoleClassOn M lam d = multipoleClassOn M lam e :=
    funext fun U => funext fun i => multipoleClassOn_congr hL U i
  unfold typeTwoTwoBad
  rw [h1, hcls]

theorem typeTwoBad_congr (Nₐ : ℕ)
    (h1 : badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e)
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j)) :
    typeTwoBad Nₐ p₀ β lam M ε₀ d = typeTwoBad Nₐ p₀ β lam M ε₀ e := by
  unfold typeTwoBad
  rw [typeTwoOneBad_congr h1 hL]
  congr 1
  exact Finset.biUnion_congr rfl fun k _ => typeTwoTwoBad_congr Nₐ k h1 hL

theorem typeThreeBad_congr (Nₐ : ℕ)
    (h1 : badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e)
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j))
    (hnear : ∀ j l, min (min ‖(d j).1 - (d l).1‖ ‖(d j).1 - (d l).2‖)
        (min ‖(d j).2 - (d l).1‖ ‖(d j).2 - (d l).2‖) ≤ M * max ‖(d j).1 - (d j).2‖ lam ↔
      min (min ‖(e j).1 - (e l).1‖ ‖(e j).1 - (e l).2‖)
        (min ‖(e j).2 - (e l).1‖ ‖(e j).2 - (e l).2‖) ≤ M * max ‖(e j).1 - (e j).2‖ lam) :
    typeThreeBad Nₐ p₀ β lam M ε₀ d = typeThreeBad Nₐ p₀ β lam M ε₀ e := by
  have h2 := typeTwoBad_congr (M := M) Nₐ h1 hL
  have hcls : multipoleClassOn M lam d = multipoleClassOn M lam e :=
    funext fun U => funext fun i => multipoleClassOn_congr hL U i
  unfold typeThreeBad
  simp only [h1, h2, hcls, hnear]

end Congr

/-! ### Measurable fibres -/

open scoped Classical in
/-- The data on which the bad sets depend: the type-1 set, the relation `↔` and the near
relation of Definition 5.4. -/
noncomputable def badData (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin n → ℂ × ℂ) :
    Finset (Fin n) × (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) :=
  (badPointsTypeOne p₀ β lam ε₀ d,
    fun i j => decide (MultipoleLinked M lam (d i) (d j)),
    fun j l => decide (min (min ‖(d j).1 - (d l).1‖ ‖(d j).1 - (d l).2‖)
      (min ‖(d j).2 - (d l).1‖ ‖(d j).2 - (d l).2‖) ≤ M * max ‖(d j).1 - (d j).2‖ lam))

open scoped Classical in
theorem fiberMeasurable_badData (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ => badData p₀ β lam M ε₀ d := by
  have h1 := fiberMeasurable_badPointsTypeOne (d := fun d : Fin n → ℂ × ℂ => d) measurable_id
    p₀ β lam ε₀
  have hL : FiberMeasurable fun (d : Fin n → ℂ × ℂ) (i j : Fin n) =>
      decide (MultipoleLinked M lam (d i) (d j)) :=
    FiberMeasurable.pi fun i => FiberMeasurable.pi fun j => fiberMeasurable_decide
      (measurableSet_setOf_multipoleLinked M lam i j)
  have hnear : FiberMeasurable fun (d : Fin n → ℂ × ℂ) (j l : Fin n) =>
      decide (min (min ‖(d j).1 - (d l).1‖ ‖(d j).1 - (d l).2‖)
        (min ‖(d j).2 - (d l).1‖ ‖(d j).2 - (d l).2‖) ≤ M * max ‖(d j).1 - (d j).2‖ lam) := by
    refine FiberMeasurable.pi fun j => FiberMeasurable.pi fun l => fiberMeasurable_decide ?_
    have hx := measurable_dipole_fst (d := fun d : Fin n → ℂ × ℂ => d) measurable_id
    have hy := measurable_dipole_snd (d := fun d : Fin n → ℂ × ℂ => d) measurable_id
    refine measurableSet_le ?_ (measurable_const.mul
      ((measurable_dipole_length (d := fun d : Fin n → ℂ × ℂ => d) measurable_id j).max
        measurable_const))
    exact ((((hx j).sub (hx l)).norm.min ((hx j).sub (hy l)).norm).min
      (((hy j).sub (hx l)).norm.min ((hy j).sub (hy l)).norm))
  exact h1.prodMk (hL.prodMk hnear)

open scoped Classical in
theorem badData_eq_imp {d e : Fin n → ℂ × ℂ}
    (h : badData p₀ β lam M ε₀ d = badData p₀ β lam M ε₀ e) :
    badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e ∧
      (∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j)) ∧
      (∀ j l, min (min ‖(d j).1 - (d l).1‖ ‖(d j).1 - (d l).2‖)
          (min ‖(d j).2 - (d l).1‖ ‖(d j).2 - (d l).2‖) ≤ M * max ‖(d j).1 - (d j).2‖ lam ↔
        min (min ‖(e j).1 - (e l).1‖ ‖(e j).1 - (e l).2‖)
          (min ‖(e j).2 - (e l).1‖ ‖(e j).2 - (e l).2‖) ≤ M * max ‖(e j).1 - (e j).2‖ lam) := by
  simp only [badData, Prod.mk.injEq] at h
  obtain ⟨h1, hL, hN⟩ := h
  refine ⟨h1, fun i j => ?_, fun j l => ?_⟩
  · have := congrFun (congrFun hL i) j
    simpa only [decide_eq_decide] using this
  · have := congrFun (congrFun hN j) l
    simpa only [decide_eq_decide] using this

theorem fiberMeasurable_typeTwoOneBad (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ => typeTwoOneBad p₀ β lam M ε₀ d :=
  (fiberMeasurable_badData p₀ β lam M ε₀).of_factor fun _ _ h => by
    obtain ⟨h1, hL, -⟩ := badData_eq_imp h
    exact typeTwoOneBad_congr h1 hL

theorem fiberMeasurable_typeTwoTwoBad (Nₐ k : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ => typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d :=
  (fiberMeasurable_badData p₀ β lam M ε₀).of_factor fun _ _ h => by
    obtain ⟨h1, hL, -⟩ := badData_eq_imp h
    exact typeTwoTwoBad_congr Nₐ k h1 hL

theorem fiberMeasurable_typeTwoBad (Nₐ : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ => typeTwoBad Nₐ p₀ β lam M ε₀ d :=
  (fiberMeasurable_badData p₀ β lam M ε₀).of_factor fun _ _ h => by
    obtain ⟨h1, hL, -⟩ := badData_eq_imp h
    exact typeTwoBad_congr Nₐ h1 hL

theorem fiberMeasurable_typeThreeBad (Nₐ : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ => typeThreeBad Nₐ p₀ β lam M ε₀ d :=
  (fiberMeasurable_badData p₀ β lam M ε₀).of_factor fun _ _ h => by
    obtain ⟨h1, hL, hN⟩ := badData_eq_imp h
    exact typeThreeBad_congr Nₐ h1 hL hN

/-- The three bad sets jointly have measurable fibres. -/
theorem fiberMeasurable_typedSets (Nₐ : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ =>
      (badPointsTypeOne p₀ β lam ε₀ d, typeTwoBad Nₐ p₀ β lam M ε₀ d,
        typeThreeBad Nₐ p₀ β lam M ε₀ d) :=
  (fiberMeasurable_badData p₀ β lam M ε₀).of_factor fun _ _ h => by
    obtain ⟨h1, hL, hN⟩ := badData_eq_imp h
    rw [h1, typeTwoBad_congr Nₐ h1 hL, typeThreeBad_congr Nₐ h1 hL hN]

/-- The type-2 classes jointly have measurable fibres. -/
theorem fiberMeasurable_typeTwoClasses (Nₐ : ℕ) (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun d : Fin n → ℂ × ℂ =>
      (typeTwoOneBad p₀ β lam M ε₀ d, fun k : ℕ => typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d) :=
  (fiberMeasurable_badData p₀ β lam M ε₀).of_factor fun _ _ h => by
    obtain ⟨h1, hL, -⟩ := badData_eq_imp h
    rw [typeTwoOneBad_congr h1 hL]
    congr 1
    funext k
    exact typeTwoTwoBad_congr Nₐ k h1 hL

end UpperBoundLDP

end MultipoleBKT

end
