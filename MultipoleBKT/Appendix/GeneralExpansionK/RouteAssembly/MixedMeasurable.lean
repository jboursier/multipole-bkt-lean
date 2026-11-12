/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.FrozenUniform

/-!
# Measurability of the written five-subset terms

See (A.51). These facts justify integrating each of the finite
correction subsets before summing the bounds of cases A–E.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Limits Hierarchical Multipole SmallIntegral
open UpperBound BoundedUpper RouteCases
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- The whole five-subset integrand is measurable for measurable model data. -/
theorem measurable_mixedIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {u v : ℂ × ℂ → ℝ}
    (hw : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (hu : Measurable u) (hv : Measurable v) (h : ℝ) (blk : I → B)
    (Dn Dz Df O : Finset (Sym2 I)) (P : FiveSubsets (Sym2 I) I) :
    Measurable fun c : I → ℂ × ℂ => mixedIntegrand χ β lam M h w u v blk Dn Dz Df O c P := by
  have hw₀ := measurable_dipoleInteraction hχ hlam
  have hord (w') (hw' : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w' q.1 q.2) (i j : I) :
      Measurable fun c : I → ℂ × ℂ => wOrd w' c i j := by
    unfold wOrd
    split_ifs
    · exact hw'.comp (show Measurable (fun c : I → ℂ × ℂ => (c i,c j)) by fun_prop)
    · exact hw'.comp (show Measurable (fun c : I → ℂ × ℂ => (c j,c i)) by fun_prop)
  have hparts (w') (hw' : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w' q.1 q.2) (e : Sym2 I) :
      Measurable (fun c : I → ℂ × ℂ => gammaW β w' M lam c e) ∧
      Measurable (fun c : I → ℂ × ℂ => alphaW β w' M lam c e + linkIndE M lam c e) := by
    induction e using Sym2.ind with
    | h i j =>
      simp only [gammaW,alphaW,symmLift_mk]
      have hs := measurableSet_multipoleLinked_apply M lam i j
      exact ⟨Measurable.ite hs measurable_const ((Real.measurable_sinh.comp
        (measurable_const.mul (hord w' hw' i j))).neg),
        (Measurable.ite hs measurable_const ((Real.measurable_cosh.comp
          (measurable_const.mul (hord w' hw' i j))).sub_const 1)).add
            (measurable_linkIndE M lam s(i,j))⟩
  have hq (e : Sym2 I) : Measurable fun c : I → ℂ × ℂ =>
      intraRatio β w (dipoleInteraction χ lam) c e := by
    induction e using Sym2.ind with
    | h i j =>
      simp only [intraRatio,symmLift_mk]
      exact Real.measurable_exp.comp (measurable_const.mul ((hord _ hw₀ i j).sub (hord _ hw i j)))
  have hG : Measurable (clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz) := by
    unfold clusterG
    exact ((Finset.measurable_prod _ fun _ _ => measurable_blockWW hw₀ measurable_const blk _).mul
      (Finset.measurable_prod _ fun e _ => measurable_farInd M lam e)).mul
        (Finset.measurable_prod _ fun e _ => (measurable_linkIndE M lam e).neg)
  have hden : Measurable (mixedDensity χ β lam h Df : (I → ℂ × ℂ) → ℝ) :=
    ((Finset.measurable_prod _ fun i _ => (measurable_pairDensity hχ hlam β).comp
      (measurable_pi_apply i)).mul (measurable_cutInd h)).mul (measurable_shortInd (17*h) Df)
  have hOdd := (Finset.measurable_prod P.1 fun e _ => (hparts w hw e).1.sub
    (hparts _ hw₀ e).1).mul (Finset.measurable_prod (O \ P.1) fun e _ => (hparts _ hw₀ e).1)
  have hEven := (Finset.measurable_prod P.2.1 fun e _ => (hparts w hw e).2.sub
    (hparts _ hw₀ e).2).mul (Finset.measurable_prod ((Df \ O) \ P.2.1) fun e _ => (hparts _ hw₀ e).2)
  have hIntra := Finset.measurable_prod P.2.2.1 fun e _ => (hq e).sub_const 1
  have hU := Finset.measurable_prod P.2.2.2.1 fun i _ => hu.comp (measurable_pi_apply (X := fun _ : I => ℂ × ℂ) i)
  have hV := Finset.measurable_prod P.2.2.2.2 fun i _ => hv.comp (measurable_pi_apply (X := fun _ : I => ℂ × ℂ) i)
  exact (hG.mul ((((hOdd.mul hEven).mul hIntra).mul hU).mul hV)).mul hden

/-- The extended frozen screening radius is continuous on its whole carrier. -/
theorem continuous_routeFrozenRadius {N : ℕ} (p₀ : ℕ) (β lam eps : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    Continuous (routeFrozenRadius p₀ β lam eps V Z) :=
  (continuous_goodRadiusZ p₀ β lam eps V Z).max ((continuous_fst.sub continuous_snd).norm.div_const 4)

/-- The extended frozen interaction is measurable before imposing the cutoff. -/
theorem measurable_routeFrozenInteraction {N : ℕ} (p₀ : ℕ) (β eps : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => routeFrozenInteraction χ p₀ β lam eps V Z q.1 q.2 := by
  have hτ := (continuous_routeFrozenRadius p₀ β lam eps V Z).measurable
  have hpos (d : ℂ × ℂ) : 0 < routeFrozenRadius p₀ β lam eps V Z d :=
    hlam.trans_le (routeFrozenRadius_lower p₀ β lam eps V Z d).1
  have hτ1 : Measurable (fun q : (ℂ × ℂ) × (ℂ × ℂ) => routeFrozenRadius p₀ β lam eps V Z q.1) := hτ.comp measurable_fst
  have hτ2 : Measurable (fun q : (ℂ × ℂ) × (ℂ × ℂ) => routeFrozenRadius p₀ β lam eps V Z q.2) := hτ.comp measurable_snd
  have hg := (continuous_smearedKernel hχ hlam).measurable
  have hK : ∀ {w : (ℂ × ℂ) × (ℂ × ℂ) → ℂ}, Measurable w →
      Measurable fun q => twoRadiusKernel χ
        (routeFrozenRadius p₀ β lam eps V Z q.1) (routeFrozenRadius p₀ β lam eps V Z q.2) (w q) :=
    fun hw => measurable_twoRadiusKernel_comp hχ hτ1 hτ2 hw (fun q => hpos _) (fun q => hpos _)
  unfold routeFrozenInteraction pairInteraction
  exact ((hg.comp (by fun_prop)).sub (hK (by fun_prop))).sub
    ((hg.comp (by fun_prop)).sub (hK (by fun_prop))) |>.sub
      (((hg.comp (by fun_prop)).sub (hK (by fun_prop))).sub
        ((hg.comp (by fun_prop)).sub (hK (by fun_prop))))

/-- Every original frozen mixed term is measurable, including bad-label terms. -/
theorem measurable_frozen_mixed {N : ℕ} (p₀ : ℕ) (eps L h : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (hχ : IsMollifier χ) (hlam : 0 < lam)
    (blk : I → B) (Dn Dz Df O : Finset (Sym2 I)) (P : FiveSubsets (Sym2 I) I) :
    Measurable fun c : I → ℂ × ℂ => mixedIntegrand χ β lam M h
      (routeFrozenInteraction χ p₀ β lam eps V Z) (routeFrozenQuadratic p₀ β lam eps L V Z)
      (routeFrozenBad p₀ β lam M eps V Z) blk Dn Dz Df O c P := by
  apply measurable_mixedIntegrand hχ hlam (measurable_routeFrozenInteraction p₀ β eps V Z hχ hlam)
  · unfold routeFrozenQuadratic
    have ht := (continuous_routeFrozenRadius p₀ β lam eps V Z).measurable
    fun_prop
  · exact Measurable.ite (measurableSet_isGoodZ p₀ β lam M eps V Z) measurable_const measurable_const

/-- The nonnegative absolute mixed term used in the finite integral sum. -/
theorem measurable_frozen_mixed_abs {N : ℕ} (p₀ : ℕ) (eps L h : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (hχ : IsMollifier χ) (hlam : 0 < lam)
    (blk : I → B) (Dn Dz Df O : Finset (Sym2 I)) (P : FiveSubsets (Sym2 I) I) :
    Measurable fun c : I → ℂ × ℂ => ENNReal.ofReal |mixedIntegrand χ β lam M h
      (routeFrozenInteraction χ p₀ β lam eps V Z) (routeFrozenQuadratic p₀ β lam eps L V Z)
      (routeFrozenBad p₀ β lam M eps V Z) blk Dn Dz Df O c P| := by
  exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (measurable_frozen_mixed p₀ eps L h V Z hχ hlam blk Dn Dz Df O P))

end MultipoleBKT.ExpansionK.RouteAssembly

end
