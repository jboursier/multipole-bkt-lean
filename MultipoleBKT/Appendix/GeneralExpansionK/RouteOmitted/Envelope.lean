/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Configuration

/-!
# Finite summation over the original long marks

See Lemma A.7. Complete original shapes and
long even marks enter a fixed finite sum before integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- A complete original tree with either its quadratic gain or an original even mark. -/
structure OmittedChoice (W : Type*) [Fintype W] [DecidableEq W] where
  shape : JointShape W
  mark : Option (Sym2 W)
  mark_mem : ∀ m, mark = some m → m ∈ shape.even

instance {W : Type*} [Fintype W] [DecidableEq W] : Finite (OmittedChoice W) := by
  apply Finite.of_injective (fun s : OmittedChoice W => (s.shape,s.mark))
  intro s t h
  cases s
  cases t
  cases h
  rfl

noncomputable instance {W : Type*} [Fintype W] [DecidableEq W] : Fintype (OmittedChoice W) := Fintype.ofFinite _

/-- The number of long marks is controlled before epsilon and all configurations. -/
theorem card_omittedChoice_le {W : Type*} [Fintype W] [DecidableEq W] :
    Fintype.card (OmittedChoice W) ≤
      (2^((Fintype.card W+1).choose 2))^4 * ((Fintype.card W+1).choose 2+1) := by
  have hi : Function.Injective (fun s : OmittedChoice W => (s.shape,s.mark)) := by
    intro s t h
    cases s
    cases t
    cases h
    rfl
  exact (Fintype.card_le_of_injective _ hi).trans (by
    rw [Fintype.card_prod,Fintype.card_option,Sym2.card]
    exact Nat.mul_le_mul_right _ card_jointShape_le)

/-- Fixed finite envelope for both omitted alternatives, including their common density. -/
noncomputable def omittedEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam h : ℝ) (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  ∑ s : OmittedChoice W, omittedTree M lam (17*h) s.shape.odd s.shape.even s.shape.near s.mark c *
    activityDensity χ β lam h c

/-- Every selected long mark is included before configuration integration. -/
theorem le_omittedEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam h : ℝ) (s : OmittedChoice W) (c : W → ℂ × ℂ) :
    omittedTree M lam (17*h) s.shape.odd s.shape.even s.shape.near s.mark c * activityDensity χ β lam h c ≤
      omittedEnvelope χ β M lam h c := by
  exact single_le_sum (f := fun s : OmittedChoice W =>
    omittedTree M lam (17*h) s.shape.odd s.shape.even s.shape.near s.mark c * activityDensity χ β lam h c)
    (fun _ _ => bot_le) (mem_univ s)

/-- The omitted configuration envelope has the paper's final area bound.
The coefficient precedes epsilon, lambda and the label carrier. -/
theorem omittedEnvelope_bound {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ)
    (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps lam : ℝ, 0 < lam → lam ≤ eps → eps ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n, omittedEnvelope χ β M lam (eps*truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*n*lam^((2-β)*k)*truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := omittedTree_bound hχ hβ hM p₀ hk
  let D : ℝ := (2^((k+1).choose 2))^4 * ((k+1).choose 2+1) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro eps lam hlam hle heps W _ _ _ hW n
  unfold omittedEnvelope
  have hm (s : OmittedChoice W) : Measurable (fun c : W → ℂ × ℂ =>
      omittedTree M lam (17*(eps*truncationScale p₀ β lam)) s.shape.odd s.shape.even s.shape.near s.mark c *
        activityDensity χ β lam (eps*truncationScale p₀ β lam) c) :=
    (measurable_omittedTree _ _ _ _ _ _ _).mul (measurable_activityDensity hχ hlam _ _)
  rw [lintegral_finsetSum _ (fun s _ => hm s)]
  let V := A*eps^(-2:ℝ)*n*lam^((2-β)*k)*truncationScale p₀ β lam^(-2:ℝ)
  have ht := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have heps0 := hlam.trans_le hle
  have hV : 0 ≤ V := by dsimp [V]; positivity
  calc
    _ ≤ ∑ _s : OmittedChoice W, ENNReal.ofReal V := sum_le_sum fun s _ =>
      ha eps lam hlam hle heps W hW s.shape.tree s.shape.isTree _ _ _ s.shape.partition
        s.shape.disjoint_odd s.shape.disjoint_even s.mark s.mark_mem n
    _ = ENNReal.ofReal ((Fintype.card (OmittedChoice W) : ℝ)*V) := by
      rw [sum_const,card_univ,nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (D*V) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
      have hc := card_omittedChoice_le (W := W)
      rw [hW] at hc
      dsimp [D]
      exact_mod_cast (hc.trans (Nat.le_add_right _ 1))) hV)
    _ = _ := by congr 1; dsimp [V]; ring

/-- Sum the original marks with epsilon fixed before the coefficient. -/
theorem omittedEnvelope_bound_at {χ : ℂ → ℝ} {β M : ℝ} (hχ : IsMollifier χ)
    (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ) {k : ℕ} (hk : 1 ≤ k)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k → ∀ n : ℕ,
      (∫⁻ c in boxConfig W n, omittedEnvelope χ β M lam (eps*truncationScale p₀ β lam) c) ≤
        ENNReal.ofReal (C*eps^(-2:ℝ)*n*lam^((2-β)*k)*truncationScale p₀ β lam^(-2:ℝ)) := by
  obtain ⟨A,hA,ha⟩ := omittedTree_bound_at hχ hβ hM p₀ hk heps
  let D : ℝ := (2^((k+1).choose 2))^4 * ((k+1).choose 2+1) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*A,mul_pos hD hA,?_⟩
  intro lam hlam hle hlam1 W _ _ _ hW n
  unfold omittedEnvelope
  have hm (s : OmittedChoice W) : Measurable (fun c : W → ℂ × ℂ =>
      omittedTree M lam (17*(eps*truncationScale p₀ β lam)) s.shape.odd s.shape.even s.shape.near s.mark c *
        activityDensity χ β lam (eps*truncationScale p₀ β lam) c) :=
    (measurable_omittedTree _ _ _ _ _ _ _).mul (measurable_activityDensity hχ hlam _ _)
  rw [lintegral_finsetSum _ (fun s _ => hm s)]
  let V := A*eps^(-2:ℝ)*n*lam^((2-β)*k)*truncationScale p₀ β lam^(-2:ℝ)
  have ht := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have heps0 := hlam.trans_le hle
  have hV : 0 ≤ V := by dsimp [V]; positivity
  calc
    _ ≤ ∑ _s : OmittedChoice W, ENNReal.ofReal V := sum_le_sum fun s _ =>
      ha lam hlam hle hlam1 W hW s.shape.tree s.shape.isTree _ _ _ s.shape.partition
        s.shape.disjoint_odd s.shape.disjoint_even s.mark s.mark_mem n
    _ = ENNReal.ofReal ((Fintype.card (OmittedChoice W) : ℝ)*V) := by
      rw [sum_const,card_univ,nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (D*V) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
      have hc := card_omittedChoice_le (W := W)
      rw [hW] at hc
      dsimp [D]
      exact_mod_cast (hc.trans (Nat.le_add_right _ 1))) hV)
    _ = _ := by congr 1; dsimp [V]; ring

end MultipoleBKT.ExpansionK.RouteOmitted

end
