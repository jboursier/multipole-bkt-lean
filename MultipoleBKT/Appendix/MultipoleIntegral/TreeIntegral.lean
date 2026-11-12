/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import MultipoleBKT.Appendix.OrderingTree

/-!
# Tree integrals and dipole coordinates

Measure-theoretic tools for Lemma A.3: integrating the positions of a cluster of
dipoles along a rooted tree (the change of variables (A.10)) and the
change of variables `(x_i, y_i)_i ↦ ((y_i)_i, (x_i - y_i)_i)` from the two charges of each dipole
to its negative charge and its dipole vector.

* `lmarginal_mul_left_of_indep`: a factor that does not depend on the integrated coordinates
  comes out of `lmarginal`;
* `lintegral_pi_prod_eq`: `∫ ∏ᵢ fᵢ(xᵢ) dx = ∏ᵢ ∫ fᵢ` on `ι → ℂ`;
* `IsParentMap`, `exists_parent_of_connected`: a connected graph has, for every root `r`, a parent
  map `par` (each `c ≠ r` is adjacent to `par c`) decreasing a rank function;
* `lintegral_parent_eq`: for a parent map `par` with root `r`,
  `∫ h(x_r) ∏_{c ≠ r} ψ_c(x_c, x_{par c}) dx = (∫ h) ∏_{c ≠ r} K_c` whenever
  `∫ ψ_c(t, y) dt = K_c` for every `y`;
* `lintegral_dipole_coords`: `∫ F(c) dc = ∫_r ∫_y F((y_i + r_i, y_i)_i) dy dr` on `ι → ℂ × ℂ`.
-/

@[expose] public section

namespace MultipoleBKT

namespace MultipoleIntegral

open MeasureTheory Finset Function
open scoped ENNReal

section Marginal

variable {δ : Type*} [DecidableEq δ] {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)}

/-- A factor that does not depend on the coordinates in `s` comes out of the marginal integral
over `s`. -/
theorem lmarginal_mul_left_of_indep {s : Finset δ} (g h : (∀ i, X i) → ℝ≥0∞)
    (hh : Measurable h) (hg : ∀ x y, (∀ i ∉ s, x i = y i) → g x = g y) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => g y * h y) ∂μ) x = g x * (∫⋯∫⁻_s, h ∂μ) x := by
  unfold lmarginal
  have : ∀ y : ∀ i : s, X i, g (updateFinset x s y) = g x := fun y =>
    hg _ _ fun i hi => by simp [updateFinset_def, hi]
  simp_rw [this]
  exact lintegral_const_mul _ (hh.comp measurable_updateFinset)

variable [∀ i, SigmaFinite (μ i)]

/-- The marginal integral over `s` of `∏_{i ∈ s} fᵢ(yᵢ)` is `∏_{i ∈ s} ∫ fᵢ`. -/
theorem lmarginal_prod_eq (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (s : Finset δ)
    (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => ∏ i ∈ s, f i (y i)) ∂μ) x = ∏ i ∈ s, ∫⁻ t, f i t ∂μ i := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert a s ha ih =>
    have hm : ∀ t : Finset δ, Measurable fun y : ∀ i, X i => ∏ i ∈ t, f i (y i) := fun t =>
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    rw [lmarginal_insert _ (hm _) ha]
    simp_rw [Finset.prod_insert ha]
    have key : ∀ z : ∀ i, X i,
        (∫⋯∫⁻_s, (fun y => f a (y a) * ∏ i ∈ s, f i (y i)) ∂μ) z =
          f a (z a) * ∏ i ∈ s, ∫⁻ t, f i t ∂μ i := by
      intro z
      rw [lmarginal_mul_left_of_indep (fun y => f a (y a)) _ (hm s)
        (fun x y hxy => by rw [hxy a ha]), ih]
    simp_rw [key, Function.update_self]
    exact lintegral_mul_const _ (hf a)

end Marginal

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `∫ ∏ᵢ fᵢ(xᵢ) dx = ∏ᵢ ∫ fᵢ` for `x : ι → ℂ`. -/
theorem lintegral_pi_prod_eq (f : ι → ℂ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → ℂ, ∏ i, f i (x i) = ∏ i, ∫⁻ t, f i t := by
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => (0 : ℂ)), lmarginal_prod_eq f hf]

end Pi

section Parent

variable {ι : Type*}

/-- `par` is a parent map with root `r`: some rank function strictly decreases from every
`c ≠ r` to its parent `par c`. -/
def IsParentMap (r : ι) (par : ι → ι) : Prop :=
  ∃ rank : ι → ℕ, ∀ c, c ≠ r → rank (par c) < rank c

/-- A connected graph has, for every root `r`, a parent map along its edges: every `c ≠ r` is
adjacent to its parent (the parent is one step closer to `r`). -/
theorem exists_parent_of_connected {G : SimpleGraph ι} (hG : G.Connected) (r : ι) :
    ∃ par : ι → ι, IsParentMap r par ∧ ∀ c, c ≠ r → G.Adj c (par c) := by
  have h : ∀ c, ∃ y, c ≠ r → G.Adj c y ∧ G.dist y r + 1 = G.dist c r := by
    intro c
    by_cases hc : c = r
    · exact ⟨c, fun h => absurd hc h⟩
    · obtain ⟨y, hy1, hy2⟩ := Connected.exists_adj_dist_add_one hG hc
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
  choose par hpar using h
  refine ⟨par, ⟨fun c => G.dist c r, fun c hc => ?_⟩, fun c hc => (hpar c hc).1⟩
  have := (hpar c hc).2
  dsimp only
  omega

variable [Fintype ι] [DecidableEq ι]

/-- **Integration along a rooted tree.** Let `par` be a parent map with root `r`, and let the
edge weights `ψ_c` satisfy `∫ ψ_c(t, y) dt = K_c` for every `y` and every `c ≠ r`. Then
`∫ h(x_r) ∏_{c ≠ r} ψ_c(x_c, x_{par c}) dx = (∫ h) ∏_{c ≠ r} K_c`. The leaves are integrated
first (a vertex of minimal rank among the remaining ones is integrated last). -/
theorem lintegral_parent_eq {r : ι} {par : ι → ι} (hpar : IsParentMap r par)
    (ψ : ι → ℂ → ℂ → ℝ≥0∞) (hψ : ∀ c, Measurable (Function.uncurry (ψ c))) (K : ι → ℝ≥0∞)
    (hK : ∀ c, c ≠ r → ∀ y, ∫⁻ t, ψ c t y = K c) (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x : ι → ℂ, h (x r) * ∏ c ∈ univ.erase r, ψ c (x c) (x (par c)) =
      (∫⁻ t, h t) * ∏ c ∈ univ.erase r, K c := by
  obtain ⟨rank, hrank⟩ := hpar
  set μ : ι → Measure ℂ := fun _ => volume
  let f : Finset ι → (ι → ℂ) → ℝ≥0∞ := fun s x => ∏ c ∈ s, ψ c (x c) (x (par c))
  have hf : ∀ s, Measurable (f s) := fun s =>
    Finset.measurable_prod _ fun c _ =>
      (hψ c).comp (f := fun x : ι → ℂ => (x c, x (par c))) (by fun_prop)
  -- the inductive claim, on sets of non-root vertices closed under taking children
  have key : ∀ s : Finset ι, s ⊆ univ.erase r →
      (∀ c ∈ s, ∀ c', c' ≠ r → par c' = c → c' ∈ s) →
      ∀ x, (∫⋯∫⁻_s, f s ∂μ) x = ∏ c ∈ s, K c := by
    intro s
    induction s using Finset.induction_on_min_value rank with
    | empty => intro _ _ x; simp [f]
    | insert a s ha hmin ih =>
      intro hsub hcl x
      have har : a ≠ r := (mem_erase.1 (hsub (mem_insert_self a s))).1
      have hpa_s : par a ∉ s := fun hp => by
        have := hmin _ hp
        have := hrank a har
        omega
      have hpa_a : par a ≠ a := fun hp => by
        have := hrank a har
        rw [hp] at this
        exact lt_irrefl _ this
      have hcl' : ∀ c ∈ s, ∀ c', c' ≠ r → par c' = c → c' ∈ s := by
        intro c hc c' hc' hpc
        rcases mem_insert.1 (hcl c (mem_insert_of_mem hc) c' hc' hpc) with h1 | h1
        · exfalso
          rw [h1] at hpc
          exact hpa_s (hpc ▸ hc)
        · exact h1
      have ih' := ih (fun c hc => hsub (mem_insert_of_mem hc)) hcl'
      rw [lmarginal_insert _ (hf _) ha]
      have hsplit : f (insert a s) = fun y => ψ a (y a) (y (par a)) * f s y := by
        funext y
        simp only [f, prod_insert ha]
      have hinner : ∀ z : ι → ℂ, (∫⋯∫⁻_s, f (insert a s) ∂μ) z =
          ψ a (z a) (z (par a)) * ∏ c ∈ s, K c := by
        intro z
        rw [hsplit, lmarginal_mul_left_of_indep (fun y => ψ a (y a) (y (par a))) (f s) (hf s)
          (fun x y hxy => by rw [hxy a ha, hxy (par a) hpa_s]), ih']
      simp_rw [hinner, Function.update_self, Function.update_of_ne hpa_a]
      have hm : Measurable fun t : ℂ => ψ a t (x (par a)) :=
        (hψ a).comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const _ hm, hK a har, prod_insert ha]
  have hfull := key (univ.erase r) subset_rfl
    (fun c _ c' hc' _ => mem_erase.2 ⟨hc', mem_univ _⟩)
  have hF : Measurable fun x : ι → ℂ => h (x r) * f (univ.erase r) x :=
    (hh.comp (measurable_pi_apply r)).mul (hf _)
  have hins := lmarginal_insert (μ := μ) _ hF (notMem_erase r univ) (fun _ => (0 : ℂ))
  rw [insert_erase (mem_univ r)] at hins
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => (0 : ℂ))]
  refine hins.trans ?_
  have hinner : ∀ z : ι → ℂ, (∫⋯∫⁻_(univ.erase r), (fun x => h (x r) * f (univ.erase r) x) ∂μ) z =
      h (z r) * ∏ c ∈ univ.erase r, K c := by
    intro z
    rw [lmarginal_mul_left_of_indep (fun x => h (x r)) (f (univ.erase r)) (hf _)
      (fun x y hxy => by rw [hxy r (notMem_erase r univ)]), hfull]
  simp_rw [hinner, Function.update_self]
  exact lintegral_mul_const _ hh

end Parent

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- **Dipole coordinates.** For a configuration `c = (x_i, y_i)_i` of dipoles, the change of
variables to the negative charges `y_i` and the dipole vectors `r_i = x_i - y_i` preserves
Lebesgue measure: `∫ F(c) dc = ∫_r ∫_y F((y_i + r_i, y_i)_i) dy dr`. -/
theorem lintegral_dipole_coords {F : (ι → ℂ × ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ c, F c = ∫⁻ r : ι → ℂ, ∫⁻ y : ι → ℂ, F (fun i => (y i + r i, y i)) := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ ι
  have hmp := measurePreserving_arrowProdEquivProdArrow ℂ ℂ ι (fun _ => (volume : Measure ℂ))
    (fun _ => (volume : Measure ℂ))
  have hvol : (volume : Measure (ι → ℂ × ℂ)) =
      Measure.pi fun _ : ι => (volume : Measure ℂ).prod volume := by
    rw [volume_pi]
    rfl
  have h1 : ∫⁻ c, F c = ∫⁻ p : (ι → ℂ) × (ι → ℂ), F (e.symm p)
      ∂(Measure.pi fun _ : ι => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : ι => (volume : Measure ℂ)) := by
    rw [hvol, ← hmp.lintegral_comp_emb e.measurableEmbedding]
    simp [e]
  have hG : Measurable fun p : (ι → ℂ) × (ι → ℂ) => F (e.symm p) := hF.comp e.symm.measurable
  rw [h1, lintegral_prod_symm _ hG.aemeasurable, ← volume_pi]
  have h2 : ∀ y : ι → ℂ, ∫⁻ x : ι → ℂ, F (e.symm (x, y)) =
      ∫⁻ r : ι → ℂ, F (fun i => (y i + r i, y i)) := by
    intro y
    rw [← lintegral_add_left_eq_self (fun x : ι → ℂ => F (e.symm (x, y))) y]
    rfl
  simp_rw [h2]
  refine lintegral_lintegral_swap ?_
  have hm : Measurable fun q : (ι → ℂ) × (ι → ℂ) => fun i => (q.1 i + q.2 i, q.1 i) := by
    fun_prop
  exact (hF.comp hm).aemeasurable

end Coordinates

end MultipoleIntegral

end MultipoleBKT

end
