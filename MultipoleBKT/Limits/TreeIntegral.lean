/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.BoxAverage
public import MultipoleBKT.Appendix.OrderingTree
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree integrals

The tree changes of variables in the proofs of
Lemma A.5 and Lemma 4.26: integrating the
positions of the dipoles of a cluster along a spanning tree, each edge contributes the integral
of its weight in the relative position of its endpoints.

* `lintegral_pi_prod`: `∫ ∏ᵢ fᵢ(xᵢ) = ∏ᵢ ∫ fᵢ` for products over a finite index type;
* `lintegral_parent_le`: for a rooted tree given by a parent map `par` decreasing a depth
  function, `∫ h(x_r) ∏_{c ≠ r} ψ_c(x_c, x_{par c}) dx ≤ (∫ h) ∏_{c ≠ r} K_c` whenever
  `∫ ψ_c(t, y) dt ≤ K_c` for every `y`;
* `lintegral_tree_le`: the same for a tree `T : SimpleGraph ι` and symmetric edge weights;
* `lintegral_eq_lintegral_pos_vec`: the change of variables
  `(xᵢ, yᵢ)ᵢ ↦ ((xᵢ)ᵢ, (yᵢ - xᵢ)ᵢ)` (positions and dipole vectors).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Finset Function
open scoped ENNReal

section Marginal

variable {δ : Type*} [DecidableEq δ] {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
  {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]

omit [∀ i, SigmaFinite (μ i)] in
/-- A factor that does not depend on the integrated coordinates comes out of `lmarginal`. -/
theorem lmarginal_mul_left_of_forall {s : Finset δ} (g h : (∀ i, X i) → ℝ≥0∞)
    (hh : Measurable h) (hg : ∀ x y, (∀ i ∉ s, x i = y i) → g x = g y) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => g y * h y) ∂μ) x = g x * (∫⋯∫⁻_s, h ∂μ) x := by
  unfold lmarginal
  have : ∀ y : ∀ i : s, X i, g (updateFinset x s y) = g x := fun y =>
    hg _ _ fun i hi => by simp [updateFinset_def, hi]
  simp_rw [this]
  exact lintegral_const_mul _ (hh.comp measurable_updateFinset)

/-- `∫⋯∫_s ∏_{i ∈ s} fᵢ(xᵢ) = ∏_{i ∈ s} ∫ fᵢ`. -/
theorem lmarginal_prod (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (s : Finset δ)
    (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => ∏ i ∈ s, f i (y i)) ∂μ) x = ∏ i ∈ s, ∫⁻ t, f i t ∂μ i := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | insert a s ha ih =>
    have hm : Measurable fun y : ∀ i, X i => ∏ i ∈ insert a s, f i (y i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    rw [lmarginal_insert _ hm ha]
    simp_rw [Finset.prod_insert ha]
    have hm' : Measurable fun y : ∀ i, X i => ∏ i ∈ s, f i (y i) :=
      Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)
    have : ∀ z : ∀ i, X i,
        (∫⋯∫⁻_s, (fun y => f a (y a) * ∏ i ∈ s, f i (y i)) ∂μ) z =
          f a (z a) * ∏ i ∈ s, ∫⁻ t, f i t ∂μ i := by
      intro z
      rw [lmarginal_mul_left_of_forall (fun y => f a (y a)) _ hm'
        (fun x y hxy => by rw [hxy a ha]), ih]
    simp_rw [this, Function.update_self]
    exact lintegral_mul_const _ (hf a)

end Marginal

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [MeasurableSpace α]

/-- `∫ ∏ᵢ fᵢ(xᵢ) d(⊗ᵢ μᵢ) = ∏ᵢ ∫ fᵢ dμᵢ`. -/
theorem lintegral_pi_prod (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] (f : ι → α → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → α, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ t, f i t ∂μ i := by
  by_cases hα : Nonempty α
  · obtain ⟨a⟩ := hα
    rw [lintegral_eq_lmarginal_univ (fun _ => a), lmarginal_prod f hf]
  · have hι : IsEmpty α := not_nonempty_iff.1 hα
    by_cases hι' : IsEmpty ι
    · simp
    · obtain ⟨i⟩ := not_isEmpty_iff.1 hι'
      have : IsEmpty (ι → α) := ⟨fun x => hι.elim (x i)⟩
      rw [lintegral_of_isEmpty]
      refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
      rw [lintegral_of_isEmpty]

end Pi

section Parent

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Tree integral along a parent map.** Let `r` be a root, `par` a parent map and `dep` a depth
function with `dep (par c) < dep c` for `c ≠ r`. If every edge weight satisfies
`∫ ψ_c(t, y) dt ≤ K_c` for all `y`, then
`∫ h(x_r) ∏_{c ≠ r} ψ_c(x_c, x_{par c}) dx ≤ (∫ h) ∏_{c ≠ r} K_c`. -/
theorem lintegral_parent_le (r : ι) (par : ι → ι) (dep : ι → ℕ)
    (hdep : ∀ c, c ≠ r → dep (par c) < dep c) (ψ : ι → ℂ → ℂ → ℝ≥0∞)
    (hψ : ∀ c, Measurable (Function.uncurry (ψ c))) (K : ι → ℝ≥0∞)
    (hK : ∀ c, c ≠ r → ∀ y, ∫⁻ t, ψ c t y ≤ K c) (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x : ι → ℂ, h (x r) * ∏ c ∈ univ.erase r, ψ c (x c) (x (par c)) ≤
      (∫⁻ t, h t) * ∏ c ∈ univ.erase r, K c := by
  set μ : ι → Measure ℂ := fun _ => volume
  let f : Finset ι → (ι → ℂ) → ℝ≥0∞ := fun s x => ∏ c ∈ s, ψ c (x c) (x (par c))
  have hf : ∀ s, Measurable (f s) := fun s =>
    Finset.measurable_prod _ fun c _ =>
      (hψ c).comp (f := fun x : ι → ℂ => (x c, x (par c))) (by fun_prop)
  -- the inductive claim on child-closed sets of non-root vertices
  have key : ∀ s : Finset ι, s ⊆ univ.erase r →
      (∀ c ∈ s, ∀ c', c' ≠ r → par c' = c → c' ∈ s) →
      ∀ x, (∫⋯∫⁻_s, f s ∂μ) x ≤ ∏ c ∈ s, K c := by
    intro s
    induction s using Finset.induction_on_min_value dep with
    | empty => intro _ _ x; simp [f]
    | insert a s ha hmin ih =>
      intro hsub hcl x
      have har : a ≠ r := (mem_erase.1 (hsub (mem_insert_self a s))).1
      have hpar_s : par a ∉ s := fun hp => by
        have := hmin _ hp
        have := hdep a har
        omega
      have hpar_a : par a ≠ a := fun hp => by
        have := hdep a har
        rw [hp] at this
        exact lt_irrefl _ this
      have hcl' : ∀ c ∈ s, ∀ c', c' ≠ r → par c' = c → c' ∈ s := by
        intro c hc c' hc' hpc
        rcases mem_insert.1 (hcl c (mem_insert_of_mem hc) c' hc' hpc) with h1 | h1
        · exfalso
          have h2 := hdep c' hc'
          rw [hpc, h1] at h2
          have := hmin c hc
          omega
        · exact h1
      have ih' := ih (fun c hc => hsub (mem_insert_of_mem hc)) hcl'
      rw [lmarginal_insert _ (hf _) ha]
      have hfa : f (insert a s) = fun y => ψ a (y a) (y (par a)) * f s y := funext fun y => by
        simp only [f, prod_insert ha]
      rw [hfa]
      have hpull : ∀ z, (∫⋯∫⁻_s, (fun y => ψ a (y a) (y (par a)) * f s y) ∂μ) z =
          ψ a (z a) (z (par a)) * (∫⋯∫⁻_s, f s ∂μ) z := fun z =>
        lmarginal_mul_left_of_forall (fun y => ψ a (y a) (y (par a))) _ (hf s)
          (fun x y hxy => by rw [hxy a ha, hxy (par a) hpar_s]) z
      simp_rw [hpull]
      calc ∫⁻ t, ψ a (update x a t a) (update x a t (par a)) *
            (∫⋯∫⁻_s, f s ∂μ) (update x a t)
          ≤ ∫⁻ t, ψ a t (x (par a)) * ∏ c ∈ s, K c := by
            refine lintegral_mono fun t => ?_
            rw [update_self, update_of_ne hpar_a]
            exact mul_le_mul_right (ih' _) _
        _ = (∫⁻ t, ψ a t (x (par a))) * ∏ c ∈ s, K c :=
            lintegral_mul_const _ ((hψ a).comp (measurable_id.prodMk measurable_const))
        _ ≤ K a * ∏ c ∈ s, K c := by
            gcongr
            exact hK a har _
        _ = ∏ c ∈ insert a s, K c := (prod_insert ha).symm
  have hall := key (univ.erase r) subset_rfl (fun c _ c' hc' _ => mem_erase.2 ⟨hc', mem_univ _⟩)
  set S := univ.erase r with hS
  have hroot : r ∉ S := fun h => (mem_erase.1 h).1 rfl
  have huniv : insert r S = (univ : Finset ι) := insert_erase (mem_univ r)
  have hm : Measurable fun x : ι → ℂ => h (x r) * f S x :=
    (hh.comp (measurable_pi_apply r)).mul (hf _)
  change ∫⁻ x : ι → ℂ, h (x r) * f S x ≤ _
  rw [volume_pi, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0 : ℂ)), ← huniv,
    lmarginal_insert _ hm hroot]
  have hpull : ∀ z, (∫⋯∫⁻_S, (fun y => h (y r) * f S y) ∂μ) z =
      h (z r) * (∫⋯∫⁻_S, f S ∂μ) z := fun z =>
    lmarginal_mul_left_of_forall (fun y => h (y r)) _ (hf _)
      (fun x y hxy => by rw [hxy r hroot]) z
  simp_rw [hpull]
  calc ∫⁻ t, h (update (fun _ => (0 : ℂ)) r t r) *
        (∫⋯∫⁻_S, f S ∂μ) (update (fun _ => 0) r t)
      ≤ ∫⁻ t, h t * ∏ c ∈ S, K c := by
        refine lintegral_mono fun t => ?_
        rw [update_self]
        gcongr
        exact hall _
    _ = (∫⁻ t, h t) * ∏ c ∈ S, K c := lintegral_mul_const _ hh

/-- A rooted spanning tree as a parent map: every vertex `c ≠ r` has a neighbour one step closer
to `r`, and `c ↦ {c, par c}` is a bijection from the non-root vertices onto the edges. -/
theorem exists_parent_of_isTree {T : SimpleGraph ι} [DecidableRel T.Adj] (hT : T.IsTree) (r : ι) :
    ∃ par : ι → ι, (∀ c, c ≠ r → T.Adj c (par c) ∧ T.dist (par c) r < T.dist c r) ∧
      Set.InjOn (fun c => s(c, par c)) (univ.erase r : Finset ι) ∧
      (univ.erase r).image (fun c => s(c, par c)) = T.edgeFinset := by
  have hpar : ∀ c, ∃ y, c ≠ r → T.Adj c y ∧ T.dist y r + 1 = T.dist c r := by
    intro c
    by_cases hc : c = r
    · exact ⟨c, fun h => absurd hc h⟩
    · obtain ⟨y, hy1, hy2⟩ := Connected.exists_adj_dist_add_one hT.connected hc
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
  choose par hpar using hpar
  have hinj : Set.InjOn (fun c => s(c, par c)) (univ.erase r : Finset ι) := by
    intro a ha b hb hab
    have ha' : a ≠ r := (mem_erase.mp ha).1
    have hb' : b ≠ r := (mem_erase.mp hb).1
    by_contra hne
    have hab' : s(a, par a) = s(b, par b) := hab
    rw [Sym2.eq_iff] at hab'
    rcases hab' with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact hne h1
    · have e1 := (hpar a ha').2
      have e2 := (hpar b hb').2
      rw [h2] at e1
      rw [← h1] at e2
      lia
  refine ⟨par, fun c hc => ⟨(hpar c hc).1, by have := (hpar c hc).2; lia⟩, hinj, ?_⟩
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact (hpar c (mem_erase.mp hc).1).1
  · have h1 := hT.card_edgeFinset
    rw [card_image_of_injOn hinj, card_erase_of_mem (mem_univ _), card_univ]
    lia

/-- **Tree integral.** Let `T` be a tree on `ι`, `r` a root and `w e` an edge weight depending
only on the positions of the endpoints of `e`, with `∫ w_{ij}(x) dxᵢ ≤ K_{ij}` for every edge
and every position of the other points. Then
`∫ h(x_r) ∏_{e ∈ T} w_e(x) dx ≤ (∫ h) ∏_{e ∈ T} K_e`. -/
theorem lintegral_tree_le {T : SimpleGraph ι} [DecidableRel T.Adj] (hT : T.IsTree) (r : ι)
    (w : Sym2 ι → (ι → ℂ) → ℝ≥0∞) (hw : ∀ e, Measurable (w e))
    (hdep : ∀ i j, T.Adj i j → ∀ x y : ι → ℂ, x i = y i → x j = y j → w s(i, j) x = w s(i, j) y)
    (K : Sym2 ι → ℝ≥0∞) (hK : ∀ i j, T.Adj i j → ∀ x, ∫⁻ t, w s(i, j) (update x i t) ≤ K s(i, j))
    (h : ℂ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ x : ι → ℂ, h (x r) * ∏ e ∈ T.edgeFinset, w e x ≤ (∫⁻ t, h t) * ∏ e ∈ T.edgeFinset, K e := by
  obtain ⟨par, hpar, hinj, himg⟩ := exists_parent_of_isTree hT r
  have hne : ∀ c, c ≠ r → par c ≠ c := fun c hc h => by
    have := (hpar c hc).1
    rw [h] at this
    exact T.irrefl this
  let ψ : ι → ℂ → ℂ → ℝ≥0∞ := fun c a b => w s(c, par c) (update (fun _ => b) c a)
  have hψx : ∀ c, c ≠ r → ∀ x : ι → ℂ, w s(c, par c) x = ψ c (x c) (x (par c)) := by
    intro c hc x
    refine hdep c (par c) (hpar c hc).1 _ _ (by simp) ?_
    rw [update_of_ne (hne c hc)]
  have hprod : ∀ x : ι → ℂ, ∏ e ∈ T.edgeFinset, w e x =
      ∏ c ∈ univ.erase r, ψ c (x c) (x (par c)) := by
    intro x
    rw [← himg, prod_image hinj]
    exact prod_congr rfl fun c hc => hψx c (mem_erase.1 hc).1 x
  have hKprod : ∏ e ∈ T.edgeFinset, K e = ∏ c ∈ univ.erase r, K s(c, par c) := by
    rw [← himg, prod_image hinj]
  simp_rw [hprod]
  rw [hKprod]
  refine lintegral_parent_le r par (fun c => T.dist c r) (fun c hc => (hpar c hc).2) ψ
    (fun c => (hw _).comp (by fun_prop)) (fun c => K s(c, par c)) (fun c hc y => ?_) h hh
  have := hK c (par c) (hpar c hc).1 (fun _ => y)
  simpa [ψ] using this

end Parent

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- **Positions and dipole vectors.** `∫ F(c) dc = ∫ (∫ F((xᵢ, xᵢ + uᵢ)ᵢ) dx) du`. -/
theorem lintegral_eq_lintegral_pos_vec (F : (ι → ℂ × ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ∫⁻ u : ι → ℂ, ∫⁻ x : ι → ℂ, F (fun i => (x i, x i + u i)) := by
  have hshear : MeasurePreserving (fun c : ι → ℂ × ℂ => fun i => ((c i).1, (c i).1 + (c i).2))
      volume volume :=
    measurePreserving_pi (fun _ : ι => (volume : Measure (ℂ × ℂ)))
      (fun _ : ι => (volume : Measure (ℂ × ℂ)))
      fun _ => measurePreserving_prod_add (volume : Measure ℂ) (volume : Measure ℂ)
  rw [← hshear.lintegral_comp hF]
  have he := volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ ι
  have hG : Measurable fun c : ι → ℂ × ℂ => F (fun i => ((c i).1, (c i).1 + (c i).2)) :=
    hF.comp hshear.measurable
  rw [← he.symm.lintegral_comp hG, Measure.volume_eq_prod]
  exact lintegral_prod_symm _ (hG.comp (MeasurableEquiv.measurable _)).aemeasurable

end Coordinates


end Limits

end MultipoleBKT

end
