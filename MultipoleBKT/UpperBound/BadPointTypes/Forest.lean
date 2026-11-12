/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.TreeIntegral

/-!
# Integrals along a rooted forest

The integrations of the proofs of Lemmas 5.39 and 5.40  integrate each charge relative
to a parent charge (a cluster centre, the partner of a good charge, the parent of a nonseed),
the roots ranging over the box. `lintegral_forest_le`: for a set `R` of roots and a parent map
`par` decreasing a depth function off `R`, if `∫ ψ_c(t, y) dt ≤ K_c` for every `y`, then
`∫ ∏_{r ∈ R} h_r(x_r) ∏_{c ∉ R} ψ_c(x_c, x_{par c}) dx ≤ ∏_{r ∈ R} ∫ h_r · ∏_{c ∉ R} K_c`.
This extends `Limits.lintegral_parent_le` (one root) to forests.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset Function MultipoleIntegral
open scoped ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [MeasureSpace α]
  [SigmaFinite (volume : Measure α)] [Nonempty α]

/-- **Integral along a rooted forest.** -/
theorem lintegral_forest_le (R : Finset ι) (par : ι → ι) (dep : ι → ℕ)
    (hdep : ∀ c, c ∉ R → dep (par c) < dep c) (ψ : ι → α → α → ℝ≥0∞)
    (hψ : ∀ c, Measurable (Function.uncurry (ψ c))) (K : ι → ℝ≥0∞)
    (hK : ∀ c, c ∉ R → ∀ y, ∫⁻ t, ψ c t y ≤ K c) (h : ι → α → ℝ≥0∞)
    (hh : ∀ r, Measurable (h r)) :
    ∫⁻ x : ι → α, (∏ r ∈ R, h r (x r)) * ∏ c ∈ Rᶜ, ψ c (x c) (x (par c)) ≤
      (∏ r ∈ R, ∫⁻ t, h r t) * ∏ c ∈ Rᶜ, K c := by
  set μ : ι → Measure α := fun _ => volume
  let f : Finset ι → (ι → α) → ℝ≥0∞ := fun s x => ∏ c ∈ s, ψ c (x c) (x (par c))
  have hf : ∀ s, Measurable (f s) := fun s =>
    Finset.measurable_prod _ fun c _ =>
      (hψ c).comp (f := fun x : ι → α => (x c, x (par c))) (by fun_prop)
  -- the inductive claim on child-closed sets of non-root vertices
  have key : ∀ s : Finset ι, s ⊆ Rᶜ →
      (∀ c ∈ s, ∀ c', c' ∉ R → par c' = c → c' ∈ s) →
      ∀ x, (∫⋯∫⁻_s, f s ∂μ) x ≤ ∏ c ∈ s, K c := by
    intro s
    induction s using Finset.induction_on_min_value dep with
    | empty => intro _ _ x; simp [f]
    | insert a s ha hmin ih =>
      intro hsub hcl x
      have har : a ∉ R := mem_compl.1 (hsub (mem_insert_self a s))
      have hpar_s : par a ∉ s := fun hp => by
        have := hmin _ hp
        have := hdep a har
        omega
      have hpar_a : par a ≠ a := fun hp => by
        have := hdep a har
        rw [hp] at this
        exact lt_irrefl _ this
      have hcl' : ∀ c ∈ s, ∀ c', c' ∉ R → par c' = c → c' ∈ s := by
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
        lmarginal_mul_left_of_indep (fun y => ψ a (y a) (y (par a))) _ (hf s)
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
  have hall := key Rᶜ subset_rfl (fun c _ c' hc' _ => mem_compl.2 hc')
  have hdisj : Disjoint R Rᶜ := disjoint_compl_right
  have huniv : R ∪ Rᶜ = (univ : Finset ι) := union_compl R
  have hgR : Measurable fun x : ι → α => ∏ r ∈ R, h r (x r) :=
    Finset.measurable_prod _ fun r _ => (hh r).comp (measurable_pi_apply r)
  have hm : Measurable fun x : ι → α => (∏ r ∈ R, h r (x r)) * f Rᶜ x := hgR.mul (hf _)
  change ∫⁻ x : ι → α, (∏ r ∈ R, h r (x r)) * f Rᶜ x ≤ _
  set x₀ : ι → α := fun _ => Classical.arbitrary α
  rw [volume_pi, lintegral_eq_lmarginal_univ (μ := μ) x₀, ← huniv,
    lmarginal_union μ _ hm hdisj]
  have hpull : ∀ z, (∫⋯∫⁻_Rᶜ, (fun y => (∏ r ∈ R, h r (y r)) * f Rᶜ y) ∂μ) z =
      (∏ r ∈ R, h r (z r)) * (∫⋯∫⁻_Rᶜ, f Rᶜ ∂μ) z := fun z =>
    lmarginal_mul_left_of_indep (fun y => ∏ r ∈ R, h r (y r)) _ (hf _)
      (fun x y hxy => prod_congr rfl fun r hr => by rw [hxy r (by simpa using hr)]) z
  calc (∫⋯∫⁻_R, ∫⋯∫⁻_Rᶜ, (fun x => (∏ r ∈ R, h r (x r)) * f Rᶜ x) ∂μ ∂μ) x₀
      ≤ (∫⋯∫⁻_R, (fun y => (∏ r ∈ R, h r (y r)) * ∏ c ∈ Rᶜ, K c) ∂μ) x₀ := by
        refine lmarginal_mono (fun z => ?_) _
        rw [hpull]
        gcongr
        exact hall z
    _ = (∫⋯∫⁻_R, (fun y => ∏ r ∈ R, h r (y r)) ∂μ) x₀ * ∏ c ∈ Rᶜ, K c := by
        unfold lmarginal
        exact lintegral_mul_const _ (hgR.comp measurable_updateFinset)
    _ = (∏ r ∈ R, ∫⁻ t, h r t) * ∏ c ∈ Rᶜ, K c := by
        rw [lmarginal_prod_eq h hh R]

end BadPointTypes

end MultipoleBKT

end
