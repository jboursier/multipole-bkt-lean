/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Gibbs.Activities
public import Mathlib.Probability.ProductMeasure

/-!
# Configurations of all labels and factorization over disjoint blocks

The activities of the paper are integrals against `μ_{β,λ}^{⊗ U}` for various
finite label sets `U ⊆ ℕ` ("all subset integrals use the same box `Λ` and measure `μ_{β,λ}`"). To compare them we integrate against the product `μ_{β,λ}^{⊗ ℕ}` of the dipole measure
over all labels (`dipoleField`, a probability measure for `N ≥ 1`, `λ > 0`):

* `integral_pi_eq_integral_dipoleField`: `∫ f dμ^{⊗ U} = ∫ f(c|_U) dμ^{⊗ ℕ}`;
* `integral_mul_of_dependsOn`: functions of the configurations on disjoint finite label sets are
  independent, `∫ Φ Ψ = ∫ Φ ∫ Ψ`;
* `BoxBounded`: functions bounded on the configurations with every dipole in `Λ²`, which are
  integrable (`integrable_of_boxBounded`), with the closure properties needed for the activity
  integrands.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace Multipole

variable {χ : ℂ → ℝ} {N : ℕ} {β lam : ℝ}

/-- The product `μ_{β,λ}^{⊗ ℕ}` of the dipole measure over all labels. -/
noncomputable def dipoleField (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) : Measure (ℕ → ℂ × ℂ) :=
  Measure.infinitePi fun _ : ℕ => dipoleMeasure χ N β lam

/-- The extension of a configuration of the labels of `U` by the origin. -/
def extendConfig (U : Finset ℕ) (y : U → ℂ × ℂ) : ℕ → ℂ × ℂ :=
  fun i => if h : i ∈ U then y ⟨i, h⟩ else 0

theorem measurable_extendConfig (U : Finset ℕ) : Measurable (extendConfig U) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i ∈ U
  · simp only [extendConfig, h, dite_true]
    exact measurable_pi_apply _
  · simp only [extendConfig, h, dite_false]
    exact measurable_const

theorem extendConfig_restrict_apply {U : Finset ℕ} (c : ℕ → ℂ × ℂ) {i : ℕ} (hi : i ∈ U) :
    extendConfig U (U.restrict c) i = c i := by
  simp [extendConfig, hi]

theorem apply_extendConfig_restrict {U : Finset ℕ} {Φ : (ℕ → ℂ × ℂ) → ℝ}
    (hΦ : DependsOn Φ (U : Set ℕ)) (c : ℕ → ℂ × ℂ) : Φ (extendConfig U (U.restrict c)) = Φ c :=
  hΦ fun _ hi => extendConfig_restrict_apply c hi

section Probability

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
include hχ hlam hN

theorem isProbabilityMeasure_dipoleField (β : ℝ) :
    IsProbabilityMeasure (dipoleField χ N β lam) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  unfold dipoleField
  infer_instance

/-- **Restriction.** An integral against `μ^{⊗ U}` is an integral against `μ^{⊗ ℕ}`. -/
theorem integral_pi_eq_integral_dipoleField (β : ℝ) {U : Finset ℕ} {f : (U → ℂ × ℂ) → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂Measure.pi (fun _ : U => dipoleMeasure χ N β lam) =
      ∫ c, f (U.restrict c) ∂dipoleField χ N β lam := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  exact (integral_restrict_infinitePi (fun _ : ℕ => dipoleMeasure χ N β lam)
    hf.aestronglyMeasurable).symm

/-- An integral against `μ^{⊗ ℕ}` of a function of the labels of `U` is an integral against
`μ^{⊗ U}`. -/
theorem integral_dipoleField_eq_pi (β : ℝ) {U : Finset ℕ} {Φ : (ℕ → ℂ × ℂ) → ℝ}
    (hΦ : Measurable Φ) (hdep : DependsOn Φ (U : Set ℕ)) :
    ∫ c, Φ c ∂dipoleField χ N β lam =
      ∫ y, Φ (extendConfig U y) ∂Measure.pi (fun _ : U => dipoleMeasure χ N β lam) := by
  rw [integral_pi_eq_integral_dipoleField hχ hlam hN β (f := fun y => Φ (extendConfig U y))
    (hΦ.comp (measurable_extendConfig U))]
  simp only [apply_extendConfig_restrict hdep]

/-- **Factorization.** Functions of the configurations on disjoint finite label sets are
independent under `μ^{⊗ ℕ}`. -/
theorem integral_mul_of_dependsOn (β : ℝ) {C D : Finset ℕ} (hCD : Disjoint C D)
    {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hΦC : DependsOn Φ (C : Set ℕ)) (hΨD : DependsOn Ψ (D : Set ℕ)) :
    ∫ c, Φ c * Ψ c ∂dipoleField χ N β lam =
      (∫ c, Φ c ∂dipoleField χ N β lam) * ∫ c, Ψ c ∂dipoleField χ N β lam := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  have hdep : DependsOn (fun c => Φ c * Ψ c) ((C ∪ D : Finset ℕ) : Set ℕ) := by
    intro c c' h
    simp only
    rw [hΦC fun i hi => h i (by simp [Finset.mem_coe.1 hi]),
      hΨD fun i hi => h i (by simp [Finset.mem_coe.1 hi])]
  rw [integral_dipoleField_eq_pi hχ hlam hN β (Φ := fun c => Φ c * Ψ c) (hΦ.mul hΨ) hdep,
    integral_dipoleField_eq_pi hχ hlam hN β hΦ hΦC, integral_dipoleField_eq_pi hχ hlam hN β hΨ hΨD]
  have hmp := measurePreserving_piFinsetUnion hCD (fun _ : ℕ => dipoleMeasure χ N β lam)
  refine (hmp.integral_comp'
    (fun y => Φ (extendConfig (C ∪ D) y) * Ψ (extendConfig (C ∪ D) y))).symm.trans ?_
  have h1 : ∀ x : (C → ℂ × ℂ) × (D → ℂ × ℂ),
      Φ (extendConfig (C ∪ D) (MeasurableEquiv.piFinsetUnion (fun _ : ℕ => ℂ × ℂ) hCD x)) =
        Φ (extendConfig C x.1) := by
    intro x
    refine hΦC fun i hi => ?_
    have hi' : i ∈ C := Finset.mem_coe.1 hi
    simp only [extendConfig, hi', Finset.mem_union, true_or, dite_true]
    obtain ⟨x₁, x₂⟩ := x
    exact Equiv.piFinsetUnion_left (fun _ : ℕ => ℂ × ℂ) hCD hi' _
  have h2 : ∀ x : (C → ℂ × ℂ) × (D → ℂ × ℂ),
      Ψ (extendConfig (C ∪ D) (MeasurableEquiv.piFinsetUnion (fun _ : ℕ => ℂ × ℂ) hCD x)) =
        Ψ (extendConfig D x.2) := by
    intro x
    refine hΨD fun i hi => ?_
    have hi' : i ∈ D := Finset.mem_coe.1 hi
    simp only [extendConfig, hi', Finset.mem_union, or_true, dite_true]
    obtain ⟨x₁, x₂⟩ := x
    exact Equiv.piFinsetUnion_right (fun _ : ℕ => ℂ × ℂ) hCD hi' _
  simp only [h1, h2]
  exact integral_prod_mul (fun y => Φ (extendConfig C y)) (fun y => Ψ (extendConfig D y))

/-- Almost every configuration has all its dipoles in `Λ²`. -/
theorem ae_dipoleField_mem_box (β : ℝ) :
    ∀ᵐ c ∂dipoleField χ N β lam, ∀ i, c i ∈ box N ×ˢ box N := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [ae_all_iff]
  intro i
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => dipoleMeasure χ N β lam) i)
  exact h.quasiMeasurePreserving.ae (ae_mem_box_dipoleMeasure χ N β lam)

end Probability

/-! ### Functions bounded on `Λ²` -/

/-- `Φ` is bounded on the configurations with every dipole in `Λ²`. -/
def BoxBounded (N : ℕ) (Φ : (ℕ → ℂ × ℂ) → ℝ) : Prop :=
  ∃ B : ℝ, ∀ c : ℕ → ℂ × ℂ, (∀ i, c i ∈ box N ×ˢ box N) → |Φ c| ≤ B

namespace BoxBounded

theorem const (N : ℕ) (a : ℝ) : BoxBounded N fun _ => a :=
  ⟨|a|, fun _ _ => le_rfl⟩

theorem add {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoxBounded N Φ) (hΨ : BoxBounded N Ψ) :
    BoxBounded N fun c => Φ c + Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  exact ⟨A + B, fun c hc => (abs_add_le _ _).trans (add_le_add (hA c hc) (hB c hc))⟩

theorem mul {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoxBounded N Φ) (hΨ : BoxBounded N Ψ) :
    BoxBounded N fun c => Φ c * Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  refine ⟨|A| * |B|, fun c hc => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hA c hc).trans (le_abs_self A)) ((hB c hc).trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)

theorem sub {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoxBounded N Φ) (hΨ : BoxBounded N Ψ) :
    BoxBounded N fun c => Φ c - Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  exact ⟨A + B, fun c hc => (abs_sub _ _).trans (add_le_add (hA c hc) (hB c hc))⟩

theorem sum {ι : Type*} (s : Finset ι) {Φ : ι → (ℕ → ℂ × ℂ) → ℝ}
    (h : ∀ i ∈ s, BoxBounded N (Φ i)) : BoxBounded N fun c => ∑ i ∈ s, Φ i c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const N 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) {Φ : ι → (ℕ → ℂ × ℂ) → ℝ}
    (h : ∀ i ∈ s, BoxBounded N (Φ i)) : BoxBounded N fun c => ∏ i ∈ s, Φ i c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const N 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ite {P : (ℕ → ℂ × ℂ) → Prop} [DecidablePred P] {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ}
    (hΦ : BoxBounded N Φ) (hΨ : BoxBounded N Ψ) :
    BoxBounded N fun c => if P c then Φ c else Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  refine ⟨max A B, fun c hc => ?_⟩
  dsimp only
  split_ifs
  · exact (hA c hc).trans (le_max_left _ _)
  · exact (hB c hc).trans (le_max_right _ _)

end BoxBounded

theorem boxBounded_stablePairWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (N : ℕ)
    (i j : ℕ) : BoxBounded N fun c => stablePairWeight χ β lam (c i) (c j) := by
  obtain ⟨W, -, hW⟩ := exists_pairWeight_bound hχ hlam β 0 N
  refine ⟨W, fun c hc => ?_⟩
  rw [abs_of_nonneg (stablePairWeight_nonneg _ _ _ _ _)]
  exact (hW _ (hc i) _ (hc j)).1

theorem boxBounded_unlinkedPairWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (N : ℕ)
    (i j : ℕ) : BoxBounded N fun c => unlinkedPairWeight χ β lam M (c i) (c j) := by
  obtain ⟨W, -, hW⟩ := exists_pairWeight_bound hχ hlam β M N
  refine ⟨W, fun c hc => ?_⟩
  rw [abs_of_nonneg (unlinkedPairWeight_nonneg _ _ _ _ _ _)]
  exact (hW _ (hc i) _ (hc j)).2

/-- A measurable function bounded on `(Λ²)^ℕ` is integrable against `μ^{⊗ ℕ}`. -/
theorem integrable_of_boxBounded (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N) (β : ℝ)
    {Φ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : Measurable Φ) (hb : BoxBounded N Φ) :
    Integrable Φ (dipoleField χ N β lam) := by
  have := isProbabilityMeasure_dipoleField hχ hlam hN β
  obtain ⟨B, hB⟩ := hb
  refine Integrable.of_bound hΦ.aestronglyMeasurable B ?_
  filter_upwards [ae_dipoleField_mem_box hχ hlam hN β] with c hc
  rw [Real.norm_eq_abs]
  exact hB c hc

end Multipole

end MultipoleBKT

end
