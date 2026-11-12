/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.PlusModel
public import MultipoleBKT.Appendix.MultipoleIntegral.Basic

/-!
# The multipole integral with frozen bad points, `I^{+,Z}_{mult,ε₀}(S)`

See equation (A.4) for the model
`(w, τ, L, Z) = (v^Z, τ^Z, L, Z)`: `I^{+,Z}_{mult,ε₀}(S) = I_{mult,ε₀}(S; v^Z, τ^Z, L, Z)`, and the
normalization identity `I^{+,Z}_{mult,ε₀}(S) = (N C_{β,λ,ε₀})^{|S|} 𝖬^{+,Z}_{ε₀}(S)`. The frozen configuration is `(V, Z)` as in
`MultipoleBKT.UpperBound.Hierarchical.FrozenData`; good labels are natural numbers.

* `plusIntegrand`: `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
  ∏_{i ∈ S} e^{L r_i²/(τ_i^Z)²} 𝟙_{i ∈ I_good^Z} e^{β g_λ(x_i - y_i)} 𝟙_{r_i ≤ ε₀ R̄}`;
* `multipoleIntegralPlus`: its integral over `(Λ²)^S`;
* `plusPartitionFunction_eq_multipoleIntegralPlus`: `𝖬^{+,Z}_{ε₀}(S) =
  (N C_{β,λ,ε₀})^{-|S|} I^{+,Z}_{mult,ε₀}(S)` for `λ, ε₀ > 0`, `N ≥ 1`;
* measurability and nonnegativity of the integrand.
-/

@[expose] public section

open MeasureTheory Set Finset Metric
open TwoComponentCoulomb (box)

namespace MultipoleBKT

open UpperBound Hierarchical

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

open scoped Classical in
/-- The integrand of `I^{+,Z}_{mult,ε₀}(S)` (eq. (A.4), for `(w, τ) = (v^Z, τ^Z)`):
`𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
∏_{i ∈ S} e^{L r_i²/(τ_i^Z)²} 𝟙_{i ∈ I_good^Z} e^{β g_λ(x_i - y_i)} 𝟙_{r_i ≤ ε₀ R̄}`. -/
noncomputable def plusIntegrand (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ L : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) {S : Finset ℕ} (c : S → ℂ × ℂ) : ℝ :=
  (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
      then 1 else 0) *
    (∏ i : S, ∏ j : S, if i < j then
      (if IsStableDipolePair (c i) (c j) then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) *
    ∏ i : S, (dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) *
      (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2))

/-- **The multipole integral with frozen bad points** `I^{+,Z}_{mult,ε₀}(S) =
I_{mult,ε₀}(S; v^Z, τ^Z, L, Z)` (eq. (A.4)):
`∫_{(Λ²)^{|S|}} ∏_{i ∈ S} 𝟙_{i ∈ I_good^Z} 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
∏_{i ∈ S} e^{L r_i²/(τ_i^Z)²} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄} dx_i dy_i`. -/
noncomputable def multipoleIntegralPlus (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ L : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (S : Finset ℕ) : ℝ :=
  ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), plusIntegrand χ p₀ β lam M ε₀ L V Z c

namespace MultipoleIntegralZ

open scoped Classical in
/-- The pair factor `e^{-β v^Z_ij} 𝟙_{𝒜_ij}` is nonnegative. -/
theorem plusPair_nonneg (d e : ℂ × ℂ) :
    0 ≤ (if IsStableDipolePair d e then
      Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z d e) else 0) := by
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem plusDipole_nonneg (p : ℂ × ℂ) :
    0 ≤ dipoleWeightZ p₀ β lam M ε₀ L V Z p *
      (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2) :=
  mul_nonneg (dipoleWeightZ_nonneg p) (cutoffDensity_nonneg β _ p)

theorem plusIntegrand_nonneg {S : Finset ℕ} (c : S → ℂ × ℂ) :
    0 ≤ plusIntegrand χ p₀ β lam M ε₀ L V Z c := by
  classical
  unfold plusIntegrand
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun i _ =>
    prod_nonneg fun j _ => ?_)) (prod_nonneg fun i _ => plusDipole_nonneg _)
  by_cases h : i < j
  · simp only [h, ↓reduceIte]
    exact plusPair_nonneg _ _
  · simp only [h, ↓reduceIte]
    exact zero_le_one

theorem measurable_plusIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) {S : Finset ℕ} :
    Measurable (plusIntegrand (S := S) χ p₀ β lam M ε₀ L V Z) := by
  classical
  have hw := measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam
  have hpair : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      (if IsStableDipolePair q.1 q.2 then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z q.1 q.2) else 0) :=
    Measurable.ite measurableSet_isStableDipolePair
      (Real.measurable_exp.comp (hw.const_mul (-β))) measurable_const
  have hdip : Measurable fun p : ℂ × ℂ => dipoleWeightZ p₀ β lam M ε₀ L V Z p *
      (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) (p.1 - p.2) :=
    (measurable_dipoleWeightZ p₀ β lam M ε₀ L V Z).mul (measurable_cutoffDensity hχ hlam β _)
  have hconn : Measurable fun c : S → ℂ × ℂ =>
      (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
        then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
      measurable_const measurable_const
  have hpairs : Measurable fun c : S → ℂ × ℂ => ∏ i : S, ∏ j : S, (if i < j then
      (if IsStableDipolePair (c i) (c j) then
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j)) else 0) else 1) := by
    refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases h : i < j
    · simp only [h, ↓reduceIte]
      have hm := hpair.comp (f := fun c : S → ℂ × ℂ => (c i, c j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact hm
    · simp only [h, ↓reduceIte]
      exact measurable_const
  exact (hconn.mul hpairs).mul (Finset.measurable_prod _ fun i _ =>
    hdip.comp (measurable_pi_apply i))

end MultipoleIntegralZ

open MultipoleIntegralZ

/-- **The normalization identity** (the display after (A.4)):
`𝖬^{+,Z}_{ε₀}(S) = (N C_{β,λ,ε₀})^{-|S|} I^{+,Z}_{mult,ε₀}(S)`, for `λ > 0`, `ε₀ > 0`, `N ≥ 1`. -/
theorem plusPartitionFunction_eq_multipoleIntegralPlus (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) (S : Finset ℕ) :
    plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ S.card *
        multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
  classical
  have hC := natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN
  set R := truncationScale p₀ β lam
  have hd : Measurable fun c : S → ℂ × ℂ =>
      ∏ i, ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2)) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
      (((measurable_cutoffDensity hχ hlam β _).comp (measurable_pi_apply i)).const_mul _)
  rw [plusPartitionFunction, modelPartitionFunction, pi_cutoffDipoleMeasure_eq hχ hlam β hε₀ hN,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun c => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top),
    multipoleIntegralPlus, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have hti : ∀ i, (ENNReal.ofReal ((N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
      (closedBall (0 : ℂ) (ε₀ * R)).indicator
        (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2))).toReal =
      (N * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ *
        (closedBall (0 : ℂ) (ε₀ * R)).indicator
          (fun w => Real.exp (β * smearedKernel χ lam w)) ((c i).1 - (c i).2) := fun i =>
    ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.2 hC.le) (cutoffDensity_nonneg β _ _))
  simp_rw [hti]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  unfold plusIntegrand
  rw [Finset.prod_mul_distrib (s := Finset.univ)
    (f := fun i : S => dipoleWeightZ p₀ β lam M ε₀ L V Z (c i))]
  simp only [R]
  have key : ∀ a P Q D : ℝ, (a * D) * (P * Q) = a * (P * (Q * D)) := fun _ _ _ _ => by ring
  convert key _ _ _ _ using 3
  congr

end MultipoleBKT

end
