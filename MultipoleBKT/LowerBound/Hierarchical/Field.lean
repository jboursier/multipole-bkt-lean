/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Compact
public import Mathlib.Probability.ProductMeasure

/-!
# Integration against products of a reference measure

The activities of Section 4.5 are integrals against `ρ^{⊗ U}` for a
reference measure `ρ` of one dipole (the truncated dipole measure `μ_{β,λ,ε₀}` or the dipole
measure `μ_{β,λ}`) and various finite label sets `U ⊆ ℕ`. As in
`MultipoleBKT.Multipole.Factorization` (written there for `ρ = μ_{β,λ}`), we integrate against the
product `ρ^{⊗ ℕ}` over all labels (`labelField ρ`, for a probability measure `ρ`):

* `integral_pi_eq_integral_labelField`: `∫ f dρ^{⊗ U} = ∫ f(c|_U) dρ^{⊗ ℕ}`;
* `integral_mul_of_dependsOn'`: functions of the configurations on disjoint label sets are
  independent;
* `BoundedOn K Φ`: `Φ` is bounded on the configurations with every dipole in `K`; if `ρ` is
  concentrated on `K`, a measurable such `Φ` is integrable (`integrable_of_boundedOn`);
* `clusterIntegralOf ρ h φ X = ∫ (∏_{B ∈ X} h_B) ∏_{ij ∈ ℰ^inter(X)} (1 + φ_ij) dρ^{⊗ ℕ}` satisfies
  the root recursion and is the partition sum of the connected integrals
  (`clusterIntegralOf_eq_partitionSum`): the cluster expansion relative to blocks
  (Steps 5–8 of Lemma 4.18, (4.32)), as in
  `MultipoleBKT.Multipole.clusterIntegral_eq_partitionSum`.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition

variable {ρ : Measure (ℂ × ℂ)}

/-! ### The product over all labels -/

/-- The product `ρ^{⊗ ℕ}` of the reference measure over all labels (Mathlib's
`Measure.infinitePi`, the zero measure unless `ρ` is a probability measure). For `ρ = μ_{β,λ}` it is
`MultipoleBKT.Multipole.dipoleField` (`labelField_dipoleMeasure`). -/
noncomputable def labelField (ρ : Measure (ℂ × ℂ)) : Measure (ℕ → ℂ × ℂ) :=
  Measure.infinitePi fun _ : ℕ => ρ

theorem labelField_dipoleMeasure (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) :
    labelField (dipoleMeasure χ N β lam) = Multipole.dipoleField χ N β lam := rfl

section Probability

variable [IsProbabilityMeasure ρ]

instance : IsProbabilityMeasure (labelField ρ) := by
  unfold labelField
  infer_instance

/-- **Restriction.** An integral against `ρ^{⊗ U}` is an integral against `ρ^{⊗ ℕ}`. -/
theorem integral_pi_eq_integral_labelField {U : Finset ℕ} {f : (U → ℂ × ℂ) → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂Measure.pi (fun _ : U => ρ) = ∫ c, f (U.restrict c) ∂labelField ρ :=
  (integral_restrict_infinitePi (fun _ : ℕ => ρ) hf.aestronglyMeasurable).symm

/-- An integral against `ρ^{⊗ ℕ}` of a function of the labels of `U` is an integral against
`ρ^{⊗ U}`. -/
theorem integral_labelField_eq_pi {U : Finset ℕ} {Φ : (ℕ → ℂ × ℂ) → ℝ}
    (hΦ : Measurable Φ) (hdep : DependsOn Φ (U : Set ℕ)) :
    ∫ c, Φ c ∂labelField ρ =
      ∫ y, Φ (extendConfig U y) ∂Measure.pi (fun _ : U => ρ) := by
  rw [integral_pi_eq_integral_labelField (f := fun y => Φ (extendConfig U y))
    (hΦ.comp (measurable_extendConfig U))]
  simp only [apply_extendConfig_restrict hdep]

/-- **Factorization.** Functions of the configurations on disjoint finite label sets are
independent under `ρ^{⊗ ℕ}`. -/
theorem integral_mul_of_dependsOn' {C D : Finset ℕ} (hCD : Disjoint C D)
    {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hΦC : DependsOn Φ (C : Set ℕ)) (hΨD : DependsOn Ψ (D : Set ℕ)) :
    ∫ c, Φ c * Ψ c ∂labelField ρ = (∫ c, Φ c ∂labelField ρ) * ∫ c, Ψ c ∂labelField ρ := by
  have hdep : DependsOn (fun c => Φ c * Ψ c) ((C ∪ D : Finset ℕ) : Set ℕ) := by
    intro c c' h
    simp only
    rw [hΦC fun i hi => h i (by simp [Finset.mem_coe.1 hi]),
      hΨD fun i hi => h i (by simp [Finset.mem_coe.1 hi])]
  rw [integral_labelField_eq_pi (Φ := fun c => Φ c * Ψ c) (hΦ.mul hΨ) hdep,
    integral_labelField_eq_pi hΦ hΦC, integral_labelField_eq_pi hΨ hΨD]
  have hmp := measurePreserving_piFinsetUnion hCD (fun _ : ℕ => ρ)
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

/-- If `ρ` is concentrated on `K`, almost every configuration has all its dipoles in `K`. -/
theorem ae_labelField_mem {K : Set (ℂ × ℂ)} (hK : ∀ᵐ p ∂ρ, p ∈ K) :
    ∀ᵐ c ∂labelField ρ, ∀ i, c i ∈ K := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => ρ) i).quasiMeasurePreserving.ae hK

/-- If `ρ` is concentrated on `K`, almost every configuration of `ρ^{⊗ ι}` has all its dipoles
in `K`. -/
theorem ae_pi_mem {ι : Type*} [Fintype ι] {K : Set (ℂ × ℂ)} (hK : ∀ᵐ p ∂ρ, p ∈ K) :
    ∀ᵐ c ∂Measure.pi fun _ : ι => ρ, ∀ i, c i ∈ K := by
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually hK

end Probability

/-! ### Functions bounded on configurations in a set -/

/-- `Φ` is bounded on the configurations with every dipole in `K`. -/
def BoundedOn (K : Set (ℂ × ℂ)) (Φ : (ℕ → ℂ × ℂ) → ℝ) : Prop :=
  ∃ B : ℝ, ∀ c : ℕ → ℂ × ℂ, (∀ i, c i ∈ K) → |Φ c| ≤ B

namespace BoundedOn

variable {K : Set (ℂ × ℂ)}

theorem const (K : Set (ℂ × ℂ)) (a : ℝ) : BoundedOn K fun _ => a :=
  ⟨|a|, fun _ _ => le_rfl⟩

theorem add {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoundedOn K Φ) (hΨ : BoundedOn K Ψ) :
    BoundedOn K fun c => Φ c + Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  exact ⟨A + B, fun c hc => (abs_add_le _ _).trans (add_le_add (hA c hc) (hB c hc))⟩

theorem mul {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoundedOn K Φ) (hΨ : BoundedOn K Ψ) :
    BoundedOn K fun c => Φ c * Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  refine ⟨|A| * |B|, fun c hc => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hA c hc).trans (le_abs_self A)) ((hB c hc).trans (le_abs_self B))
    (abs_nonneg _) (abs_nonneg _)

theorem neg {Φ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoundedOn K Φ) : BoundedOn K fun c => -Φ c := by
  obtain ⟨A, hA⟩ := hΦ
  exact ⟨A, fun c hc => by rw [abs_neg]; exact hA c hc⟩

theorem sub {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : BoundedOn K Φ) (hΨ : BoundedOn K Ψ) :
    BoundedOn K fun c => Φ c - Ψ c := by
  simpa [sub_eq_add_neg] using hΦ.add hΨ.neg

theorem sum {ι : Type*} (s : Finset ι) {Φ : ι → (ℕ → ℂ × ℂ) → ℝ}
    (h : ∀ i ∈ s, BoundedOn K (Φ i)) : BoundedOn K fun c => ∑ i ∈ s, Φ i c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const K 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem prod {ι : Type*} (s : Finset ι) {Φ : ι → (ℕ → ℂ × ℂ) → ℝ}
    (h : ∀ i ∈ s, BoundedOn K (Φ i)) : BoundedOn K fun c => ∏ i ∈ s, Φ i c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const K 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ite {P : (ℕ → ℂ × ℂ) → Prop} [DecidablePred P] {Φ Ψ : (ℕ → ℂ × ℂ) → ℝ}
    (hΦ : BoundedOn K Φ) (hΨ : BoundedOn K Ψ) :
    BoundedOn K fun c => if P c then Φ c else Ψ c := by
  obtain ⟨A, hA⟩ := hΦ
  obtain ⟨B, hB⟩ := hΨ
  refine ⟨max A B, fun c hc => ?_⟩
  dsimp only
  split_ifs
  · exact (hA c hc).trans (le_max_left _ _)
  · exact (hB c hc).trans (le_max_right _ _)

/-- A pair function bounded on `K × K`. -/
theorem pair {φ : ℂ × ℂ → ℂ × ℂ → ℝ} (h : ∃ B, ∀ d ∈ K, ∀ e ∈ K, |φ d e| ≤ B) (i j : ℕ) :
    BoundedOn K fun c => φ (c i) (c j) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun c hc => hB _ (hc i) _ (hc j)⟩

/-- A one-body function bounded on `K`. -/
theorem single {ψ : ℂ × ℂ → ℝ} (h : ∃ B, ∀ d ∈ K, |ψ d| ≤ B) (i : ℕ) :
    BoundedOn K fun c => ψ (c i) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, fun c hc => hB _ (hc i)⟩

end BoundedOn

/-- A measurable function bounded on `K^ℕ` is integrable against `ρ^{⊗ ℕ}`, if `ρ` is a
probability measure concentrated on `K`. -/
theorem integrable_of_boundedOn [IsProbabilityMeasure ρ] {K : Set (ℂ × ℂ)}
    (hK : ∀ᵐ p ∂ρ, p ∈ K) {Φ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : Measurable Φ) (hb : BoundedOn K Φ) :
    Integrable Φ (labelField ρ) := by
  obtain ⟨B, hB⟩ := hb
  refine Integrable.of_bound hΦ.aestronglyMeasurable B ?_
  filter_upwards [ae_labelField_mem hK] with c hc
  rw [Real.norm_eq_abs]
  exact hB c hc

/-! ### The cluster expansion relative to blocks, for a general reference measure -/

section Cluster

variable [IsProbabilityMeasure ρ]

/-- `Ξ(X) = ∫ (∏_{B ∈ X} h_B) ∏_{ij ∈ ℰ^inter(X)} (1 + φ_ij) dρ^{⊗ ℕ}`. -/
noncomputable def clusterIntegralOf (ρ : Measure (ℂ × ℂ))
    (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ) (X : Finset (Finset ℕ)) : ℝ :=
  ∫ c, clusterWeight h φ X c ∂labelField ρ

/-- `κ(Y) = ∫ (∏_{B ∈ Y} h_B) ∑_{E ∈ 𝖤_0^Y} ∏_{ij ∈ E} φ_ij dρ^{⊗ ℕ}`. -/
noncomputable def connIntegralOf (ρ : Measure (ℂ × ℂ))
    (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ) (Y : Finset (Finset ℕ)) : ℝ :=
  ∫ c, connWeight h φ Y c ∂labelField ρ

variable {h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ} {φ : ℂ × ℂ → ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}

theorem boundedOn_clusterWeight (hh : ∀ B, BoundedOn K (h B))
    (hφ : ∀ i j, BoundedOn K fun c => φ (c i) (c j)) (X : Finset (Finset ℕ)) :
    BoundedOn K (clusterWeight h φ X) :=
  (BoundedOn.prod _ fun B _ => hh B).mul
    (BoundedOn.prod _ fun p _ => (BoundedOn.const K 1).add (hφ p.1 p.2))

theorem boundedOn_connWeight (hh : ∀ B, BoundedOn K (h B))
    (hφ : ∀ i j, BoundedOn K fun c => φ (c i) (c j)) (Y : Finset (Finset ℕ)) :
    BoundedOn K (connWeight h φ Y) :=
  (BoundedOn.prod _ fun B _ => hh B).mul
    (BoundedOn.sum _ fun _ _ => BoundedOn.prod _ fun p _ => hφ p.1 p.2)

variable (hK : ∀ᵐ p ∂ρ, p ∈ K)
variable (hhm : ∀ B, Measurable (h B)) (hhd : ∀ B, DependsOn (h B) (B : Set ℕ))
  (hhb : ∀ B, BoundedOn K (h B)) (hφm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => φ q.1 q.2)
  (hφb : ∀ i j, BoundedOn K fun c => φ (c i) (c j))
include hK hhm hhd hhb hφm hφb

/-- **Root recursion of `Ξ`.** -/
theorem clusterIntegralOf_root {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {B₀ : Finset ℕ} (hB₀ : B₀ ∈ X) :
    clusterIntegralOf ρ h φ X =
      ∑ Y ∈ X.powerset.filter (B₀ ∈ ·),
        connIntegralOf ρ h φ Y * clusterIntegralOf ρ h φ (X \ Y) := by
  unfold clusterIntegralOf connIntegralOf
  rw [show (fun c => clusterWeight h φ X c) = fun c => ∑ Y ∈ X.powerset.filter (B₀ ∈ ·),
      connWeight h φ Y c * clusterWeight h φ (X \ Y) c from
    funext fun c => clusterWeight_root h φ hX hB₀ c]
  rw [integral_finsetSum (f := fun Y c => connWeight h φ Y c * clusterWeight h φ (X \ Y) c) _
    fun Y _ => integrable_of_boundedOn hK
    ((measurable_connWeight hhm hφm Y).mul (measurable_clusterWeight hhm hφm (X \ Y)))
    ((boundedOn_connWeight hhb hφb Y).mul (boundedOn_clusterWeight hhb hφb (X \ Y)))]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hYX : Y ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hY).1
  exact integral_mul_of_dependsOn' (disjoint_biUnion_sdiff hX hYX)
    (measurable_connWeight hhm hφm Y) (measurable_clusterWeight hhm hφm (X \ Y))
    (dependsOn_connWeight hhd Y) (dependsOn_clusterWeight hhd (X \ Y))

omit hK hhm hhd hhb hφm hφb in
theorem clusterIntegralOf_empty : clusterIntegralOf ρ h φ ∅ = 1 := by
  have hint : interPairs (∅ : Finset (Finset ℕ)) = ∅ := by
    simp [interPairs, pairsOn]
  simp [clusterIntegralOf, clusterWeight, hint]

/-- `Ξ` is the partition sum of `κ` on the subfamilies of a subpartition. -/
theorem clusterIntegralOf_eq_partitionSum {X₀ : Finset (Finset ℕ)} (hX₀ : IsSubpartition X₀) :
    ∀ X ⊆ X₀, clusterIntegralOf ρ h φ X = partitionSum (connIntegralOf ρ h φ) X :=
  eq_partitionSum_of_root _ X₀ clusterIntegralOf_empty
    fun _ hX _ hB₀ => clusterIntegralOf_root hK hhm hhd hhb hφm hφb
      (isSubpartition_mono hX₀ hX) hB₀

end Cluster

end Hierarchical

end MultipoleBKT

end
