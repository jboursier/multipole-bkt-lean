/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.UpperBound

/-!
# Star integrals and connected linking graphs

See Lemma A.6. Tonelli along a star keeps the
largest radius as the outer variable in the cutoff-tail calculation.
The connected-linking indicator and its measurability are shared by the
logarithmic weighted-root estimates and the activity-error integrals.
-/

@[expose] public section

namespace MultipoleBKT

namespace GeneralExpansion

open MeasureTheory Set Finset Function
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral

variable {M lam : ℝ}

section Root

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The marginal over a set `s` not containing `j` of a product of functions of `y_c` and `y_j`. -/
theorem lmarginal_prod_param (s : Finset ι) {j : ι} (hj : j ∉ s) (g : ℂ → ℂ → ℝ≥0∞)
    (hg : Measurable (uncurry g)) (z : ι → ℂ) :
    (∫⋯∫⁻_s, (fun y : ι → ℂ => ∏ c ∈ s, g (y c) (y j)) ∂fun _ => (volume : Measure ℂ)) z =
      ∏ _c ∈ s, ∫⁻ t, g t (z j) := by
  have hfix : (∫⋯∫⁻_s, (fun y : ι → ℂ => ∏ c ∈ s, g (y c) (y j)) ∂fun _ => (volume : Measure ℂ))
      z = (∫⋯∫⁻_s, (fun y : ι → ℂ => ∏ c ∈ s, g (y c) (z j)) ∂fun _ => (volume : Measure ℂ)) z := by
    unfold lmarginal
    congr 1
    funext y
    have : updateFinset z s y j = z j := by simp [updateFinset_def, hj]
    dsimp only
    rw [this]
  rw [hfix]
  exact lmarginal_prod_eq (fun _ t => g t (z j))
    (fun _ => hg.comp (measurable_id.prodMk measurable_const)) s z

/-- **The star integral** (Tonelli along a star centred at `j₀`):
`∫ f(r_{j₀}) ∏_{c ≠ j₀} g(r_c, r_{j₀}) dr = ∫ f(t) (∫ g(s, t) ds)^{|ι| - 1} dt`. -/
theorem lintegral_star (j₀ : ι) (f : ℂ → ℝ≥0∞) (hf : Measurable f) (g : ℂ → ℂ → ℝ≥0∞)
    (hg : Measurable (uncurry g)) :
    ∫⁻ r : ι → ℂ, f (r j₀) * ∏ c ∈ univ.erase j₀, g (r c) (r j₀) =
      ∫⁻ t, f t * (∫⁻ s, g s t) ^ (Fintype.card ι - 1) := by
  set μ : ι → Measure ℂ := fun _ => volume
  have hgm : ∀ c, Measurable fun y : ι → ℂ => g (y c) (y j₀) := fun c => by
    have := hg.comp (f := fun y : ι → ℂ => (y c, y j₀))
      ((measurable_pi_apply c).prodMk (measurable_pi_apply j₀))
    exact this
  have hP : Measurable fun y : ι → ℂ => ∏ c ∈ univ.erase j₀, g (y c) (y j₀) :=
    Finset.measurable_prod _ fun c _ => hgm c
  have hF : Measurable fun y : ι → ℂ => f (y j₀) * ∏ c ∈ univ.erase j₀, g (y c) (y j₀) :=
    (hf.comp (measurable_pi_apply j₀)).mul hP
  have hinner : ∀ z : ι → ℂ, (∫⋯∫⁻_(univ.erase j₀),
      (fun y : ι → ℂ => f (y j₀) * ∏ c ∈ univ.erase j₀, g (y c) (y j₀)) ∂μ) z =
      f (z j₀) * (∫⁻ s, g s (z j₀)) ^ (Fintype.card ι - 1) := by
    intro z
    rw [lmarginal_mul_left_of_indep (fun y => f (y j₀)) _ hP
      (fun x y hxy => by rw [hxy j₀ (notMem_erase j₀ univ)]),
      lmarginal_prod_param (univ.erase j₀) (notMem_erase j₀ univ) g hg z, prod_const,
      card_erase_of_mem (mem_univ j₀), card_univ]
  have hins := lmarginal_insert (μ := μ) _ hF (notMem_erase j₀ univ) (fun _ => (0 : ℂ))
  rw [insert_erase (mem_univ j₀)] at hins
  rw [volume_pi, lintegral_eq_lmarginal_univ (fun _ => (0 : ℂ))]
  refine hins.trans ?_
  simp_rw [hinner, Function.update_self]
  rfl

end Root

/-! ### Connected linking graphs in the configuration coordinates -/

section Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The indicator `𝟙_{𝓑}` of a connected linking graph, in the configuration coordinates. -/
noncomputable def connInd (M lam : ℝ) (c : ι → ℂ × ℂ) : ℝ≥0∞ := by
  classical
  exact if (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j)).Connected then 1
    else 0

omit [Fintype ι] [DecidableEq ι] in
theorem connInd_le_one (c : ι → ℂ × ℂ) : connInd M lam c ≤ 1 := by
  unfold connInd
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem connInd_dipole (y r : ι → ℂ) :
    connInd M lam (fun i => (y i + r i, y i)) = connectedIndicator M lam y r := by
  unfold connInd connectedIndicator
  congr

omit [DecidableEq ι] in
theorem measurable_connInd (M lam : ℝ) : Measurable (connInd (ι := ι) M lam) := by
  classical
  unfold connInd
  exact Measurable.ite (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
    measurable_const measurable_const


end Config

end GeneralExpansion

end MultipoleBKT

end
