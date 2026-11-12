/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.GoodBad
public import MultipoleBKT.UpperBound.Hierarchical.Expansion
public import MultipoleBKT.LowerBound.Hierarchical.Euler

/-!
# The external normalization `g^Z_{ε₀}(S)` (eq. (5.101))

The paper: proof of Proposition 5.18:
"Reversing all dipoles in `S` preserves `𝖯^{+,ε₀,Z}_{{S}}` and reverses the sign of their
interaction with `Z`. Hence, by (5.26),
`1 ≤ g^Z_{ε₀}(S) = 𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[cosh(β ∑_{i ∈ S, j ∈ V_bad} v^Z_ij)] ≤ C`, where `C` depends on
`β`, `p(β)` and `|S|`. In particular, `|𝖪̂^{+,Z}_{ε₀}(X)| ≤ |𝖪^{+,Z}_{ε₀}(X)|`.".

* `interactionGoodZ_swap_left`, `interactionGoodZ_swap_right`, `dipoleWeightZ_swap`,
  `interactionExtZ_swap`: the interaction `v^Z` of two good dipoles is odd in each dipole, the
  one-body weight of `𝖯^{+,ε₀,Z}` is invariant, and the interaction with the bad points is odd,
  under the reversal `(x, y) ↦ (y, x)` of a good dipole (the radius `τ^Z` and `I_good^Z` depend on
  the dipole only through the set `{x, y}`);
* `ae_plusModel`: under `𝖯^{+,ε₀,Z}_X` almost every dipole lies in `Λ² ∩ {r ≤ ε₀ R̄}` and in
  `I_good^Z`;
* `integral_one_plusModel`: `𝖯^{+,ε₀,Z}_X` has mass `1` when every `𝖬^{+,Z}_{ε₀}(S)`, `S ∈ X`, is
  positive;
* `one_le_externalNormalization`, `externalNormalization_le`: **eq. (5.101)**,
  `1 ≤ g^Z_{ε₀}(S) ≤ e^{β C_gb |S|}` with `C_gb` the constant of
  `MultipoleBKT.UpperBound.BoundedUpper.sum_abs_interactionExtZ_le`.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Multipole Parity

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-! ### Reversal of a good dipole -/

section Swap

theorem dipoleDist_swap_left (d e : ℂ × ℂ) : dipoleDist d.swap e = dipoleDist d e := by
  unfold dipoleDist
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact min_comm _ _

theorem dipoleDist_swap_right (d e : ℂ × ℂ) : dipoleDist d e.swap = dipoleDist d e := by
  unfold dipoleDist
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [min_comm ‖d.1 - e.2‖, min_comm ‖d.2 - e.2‖]

theorem norm_swap_sub (d : ℂ × ℂ) : ‖d.swap.1 - d.swap.2‖ = ‖d.1 - d.2‖ := by
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact norm_sub_rev _ _

theorem badDistZ_swap (d : ℂ × ℂ) :
    badDistZ p₀ β lam ε₀ V Z d.swap = badDistZ p₀ β lam ε₀ V Z d := by
  unfold badDistZ
  simp only [dipoleDist_swap_left]

theorem goodRadiusZ_swap (d : ℂ × ℂ) :
    goodRadiusZ p₀ β lam ε₀ V Z d.swap = goodRadiusZ p₀ β lam ε₀ V Z d := by
  unfold goodRadiusZ
  rw [badDistZ_swap]

theorem isGoodZ_swap (d : ℂ × ℂ) :
    IsGoodZ p₀ β lam M ε₀ V Z d.swap ↔ IsGoodZ p₀ β lam M ε₀ V Z d := by
  unfold IsGoodZ
  simp only [dipoleDist_swap_left, norm_swap_sub]

theorem dipoleWeightZ_swap (d : ℂ × ℂ) :
    dipoleWeightZ p₀ β lam M ε₀ L V Z d.swap = dipoleWeightZ p₀ β lam M ε₀ L V Z d := by
  classical
  unfold dipoleWeightZ
  rw [norm_swap_sub, goodRadiusZ_swap]
  simp only [isGoodZ_swap]

/-- `v^Z` is odd under the reversal of the first dipole when its two radii are equal. -/
theorem pairInteraction_swap_left (χ : ℂ → ℝ) (lam : ℝ) (d e : ℂ × ℂ) (τ : ℝ) (tb : ℝ × ℝ) :
    pairInteraction χ lam d.swap e (τ, τ) tb = -pairInteraction χ lam d e (τ, τ) tb := by
  unfold pairInteraction
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

/-- `v^Z` is odd under the reversal of the second dipole when its two radii are equal. -/
theorem pairInteraction_swap_right (χ : ℂ → ℝ) (lam : ℝ) (d e : ℂ × ℂ) (ta : ℝ × ℝ) (τ : ℝ) :
    pairInteraction χ lam d e.swap ta (τ, τ) = -pairInteraction χ lam d e ta (τ, τ) := by
  unfold pairInteraction
  simp only [Prod.fst_swap, Prod.snd_swap]
  ring

theorem interactionGoodZ_swap_left (d e : ℂ × ℂ) :
    interactionGoodZ χ p₀ β lam ε₀ V Z d.swap e = -interactionGoodZ χ p₀ β lam ε₀ V Z d e := by
  unfold interactionGoodZ
  rw [goodRadiusZ_swap, pairInteraction_swap_left]

theorem interactionGoodZ_swap_right (d e : ℂ × ℂ) :
    interactionGoodZ χ p₀ β lam ε₀ V Z d e.swap = -interactionGoodZ χ p₀ β lam ε₀ V Z d e := by
  unfold interactionGoodZ
  rw [goodRadiusZ_swap, pairInteraction_swap_right]

theorem interactionExtZ_swap (d : ℂ × ℂ) (j : Fin N) :
    interactionExtZ χ p₀ β lam ε₀ V Z d.swap j = -interactionExtZ χ p₀ β lam ε₀ V Z d j := by
  unfold interactionExtZ
  rw [goodRadiusZ_swap, pairInteraction_swap_left]

end Swap

/-! ### The support of `𝖯^{+,ε₀,Z}_X` -/

section Support

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

open scoped Classical in
/-- Under `𝖯^{+,ε₀,Z}_X`, almost every dipole lies in `Λ² ∩ {r ≤ ε₀ R̄}` and in `I_good^Z`. -/
theorem ae_plusModel {X : Finset (Finset ℕ)} :
    ∀ᵐ y ∂plusModel χ N p₀ β lam M ε₀ L V Z X, ∀ i,
      y i ∈ supportSet N p₀ β lam ε₀ ∧ IsGoodZ p₀ β lam M ε₀ V Z (y i) := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hdm : Measurable fun y : X.biUnion id → ℂ × ℂ =>
      ∏ S ∈ X, ENNReal.ofReal ((modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
        (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam S)⁻¹ *
        hierBlockWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z)
          M lam X S y) := h.measurable_modelHierarchicalDensity (M := M) (lam := lam) X
  have hK : ∀ᵐ y ∂plusModel χ N p₀ β lam M ε₀ L V Z X, ∀ i, y i ∈ supportSet N p₀ β lam ε₀ := by
    have hac : plusModel χ N p₀ β lam M ε₀ L V Z X ≪
        Measure.pi fun _ : X.biUnion id => cutoffDipoleMeasure χ N p₀ β lam ε₀ := by
      rw [plusModel, modelHierarchical_eq]
      exact withDensity_absolutelyContinuous _ _
    exact hac.ae_le (ae_pi_mem (ι := X.biUnion id) h.ae_mem)
  have hG : ∀ᵐ y ∂plusModel χ N p₀ β lam M ε₀ L V Z X, ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (y i) := by
    rw [plusModel, modelHierarchical_eq, ae_withDensity_iff hdm]
    refine Filter.Eventually.of_forall fun y hy i => ?_
    by_contra hi
    apply hy
    obtain ⟨S, hS, hiS⟩ := Finset.mem_biUnion.1 i.2
    refine Finset.prod_eq_zero hS ?_
    have hw : hierBlockWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam X S y = 0 := by
      unfold hierBlockWeight
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      rw [ite_eq_left (show ((i : ℕ) ∈ S) from hiS)]
      unfold dipoleWeightZ
      rw [ite_eq_right hi, mul_zero]
    rw [hw, mul_zero, ENNReal.ofReal_zero]
  filter_upwards [hK, hG] with y h1 h2 i using ⟨h1 i, h2 i⟩

/-- `𝖯^{+,ε₀,Z}_{{S}}` has mass `1` when `𝖬^{+,Z}_{ε₀}(S) > 0`. -/
theorem integral_one_plusModel {S : Finset ℕ}
    (hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) :
    ∫ _y, (1 : ℝ) ∂plusModel χ N p₀ β lam M ε₀ L V Z {S} = 1 := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have key := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := {S})
    (f := fun _ => (1 : ℝ)) measurable_const
  simp only [mul_one, Finset.prod_singleton] at key
  rw [← h.modelPartitionFunction_eq_integral_labelField] at key
  have key' : plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
      ∫ _y, (1 : ℝ) ∂plusModel χ N p₀ β lam M ε₀ L V Z {S} =
      plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S * 1 := by
    rw [mul_one]
    exact key
  exact mul_left_cancel₀ hpos.ne' key'

end Support

/-! ### Eq. (5.101) -/

section External

/-- The interaction of the dipoles of `S` with the frozen bad points,
`∑_{i ∈ S} ∑_{j ∈ V_bad} v^Z_ij`, at a configuration of `V_{{S}}`. -/
noncomputable def extSum (χ : ℂ → ℝ) (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (S : Finset ℕ) (y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ) : ℝ :=
  ∑ i : ({S} : Finset (Finset ℕ)).biUnion id, ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j

theorem measurable_extSum (hχ : IsMollifier χ) (hlam : 0 < lam) (S : Finset ℕ) :
    Measurable (extSum χ p₀ β lam ε₀ V Z S) :=
  Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
    (measurable_interactionExtZ p₀ β lam ε₀ V Z hχ hlam j).comp (measurable_pi_apply i)

/-- Reversing all the dipoles of `S` changes the sign of their interaction with the bad points. -/
theorem extSum_flipOn (S : Finset ℕ) (y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ) :
    extSum χ p₀ β lam ε₀ V Z S (flipOn Prod.swap (blockSet {S} S) y) =
      -extSum χ p₀ β lam ε₀ V Z S y := by
  unfold extSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i ∈ blockSet {S} S := by
    rw [mem_blockSet]
    obtain ⟨S', hS', hiS'⟩ := Finset.mem_biUnion.1 i.2
    rw [Finset.mem_singleton.1 hS'] at hiS'
    exact hiS'
  rw [flipOn_apply_of_mem hi, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => interactionExtZ_swap _ j

/-- The bound `|∑_{i ∈ S} ∑_{j ∈ V} v^Z_ij| ≤ C |S|` on the support of `𝖯^{+,ε₀,Z}_{{S}}`. -/
theorem abs_extSum_le (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ (S : Finset ℕ)
      (y : ({S} : Finset (Finset ℕ)).biUnion id → ℂ × ℂ),
      (∀ i, y i ∈ supportSet N p₀ β lam ε₀ ∧ IsGoodZ p₀ β lam M ε₀ V Z (y i)) →
        |extSum χ p₀ β lam ε₀ V Z S y| ≤ C * S.card := by
  obtain ⟨C, hC, hgb⟩ := sum_abs_interactionExtZ_le hχ p₀ β
  refine ⟨C, hC, fun {N} lam M ε₀ V Z hlam hlamh hM hM3 hVZ S y hy => ?_⟩
  have hcard : Fintype.card (({S} : Finset (Finset ℕ)).biUnion id) = S.card := by
    rw [Fintype.card_coe]
    simp
  have hterm : ∀ i, |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j| ≤ C := by
    intro i
    obtain ⟨hK, hG⟩ := hy i
    have hr : ‖(y i).1 - (y i).2‖ ≤ ε₀ * truncationScale p₀ β lam := hK.2
    have h1 := hgb lam M ε₀ V Z hlam hlamh hM hM3 hVZ (y i) hG hr
    have hd := lam_le_badDistZ hlam hlamh hM hVZ hG hr
    have hd0 : 0 < badDistZ p₀ β lam ε₀ V Z (y i) := hlam.trans_le hd
    have hrd := norm_le_badDistZ hlam hlamh hM hVZ hG hr
    calc |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j|
        ≤ ∑ j ∈ V, |interactionExtZ χ p₀ β lam ε₀ V Z (y i) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ C * ‖(y i).1 - (y i).2‖ / badDistZ p₀ β lam ε₀ V Z (y i) := h1
      _ ≤ C := by
          rw [mul_div_assoc]
          exact mul_le_of_le_one_right hC.le ((div_le_one hd0).2 hrd)
  unfold extSum
  calc |∑ i : ({S} : Finset (Finset ℕ)).biUnion id, ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j|
      ≤ ∑ i : ({S} : Finset (Finset ℕ)).biUnion id,
          |∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ({S} : Finset (Finset ℕ)).biUnion id, C := Finset.sum_le_sum fun i _ => hterm i
    _ = C * S.card := by rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_comm]

/-- `g^Z_{ε₀}(S) = 𝔼_{𝖯_{{S}}}[e^{-β T}] = 𝔼_{𝖯_{{S}}}[e^{β T}]`, `T = ∑_{i ∈ S, j ∈ V} v^Z_ij`
(**the reversal symmetry**). -/
theorem externalNormalization_eq_integral_exp (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {S : Finset ℕ} (hS : S.Nonempty) :
    externalNormalization χ N p₀ β lam M ε₀ L V Z S =
      ∫ y, Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y) ∂plusModel χ N p₀ β lam M ε₀ L V Z {S} := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have := h.isProbabilityMeasure
  have hX : IsSubpartition ({S} : Finset (Finset ℕ)) :=
    ⟨fun S' hS' => by rw [Finset.mem_singleton.1 hS']; exact hS, by
      intro a ha b hb hab
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab⟩
  have hmp := measurePreserving_flipOn_modelHierarchical (β := β) (M := M) (lam := lam)
    (w := interactionGoodZ χ p₀ β lam ε₀ V Z) (ψ := dipoleWeightZ p₀ β lam M ε₀ L V Z)
    (fun d e => interactionGoodZ_swap_left d e) (fun d e => interactionGoodZ_swap_right d e)
    (fun d => dipoleWeightZ_swap d) (measurePreserving_swap_cutoffDipoleMeasure hχ N p₀ β lam ε₀)
    hX (Finset.mem_singleton_self S)
  have hcomp := hmp.integral_comp (flipOnEquiv measurable_swap Prod.swap_swap _).measurableEmbedding
    (fun y => Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y))
  unfold externalNormalization plusModel
  rw [← hcomp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [extSum_flipOn, mul_neg, ← neg_mul]
  rfl

/-- **Eq. (5.101), lower bound**: `g^Z_{ε₀}(S) ≥ 1` when `𝖬^{+,Z}_{ε₀}(S) > 0`
(`g = 𝔼[cosh(β T)] ≥ 1`). -/
theorem one_le_externalNormalization (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hM3 : 3 ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {S : Finset ℕ} (hS : S.Nonempty)
    (hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) :
    1 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S := by
  obtain ⟨C, hC, hT⟩ := abs_extSum_le hχ p₀ β
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have : IsFiniteMeasure (plusModel χ N p₀ β lam M ε₀ L V Z {S}) :=
    h.isFiniteMeasure_modelHierarchical (M := M) (lam := lam) {S}
  set P := plusModel χ N p₀ β lam M ε₀ L V Z {S}
  have hTae : ∀ᵐ y ∂P, |extSum χ p₀ β lam ε₀ V Z S y| ≤ C * S.card := by
    filter_upwards [ae_plusModel hχ hlam hε₀ hN] with y hy
    exact hT lam M ε₀ V Z hlam hlamh hM hM3 hVZ S y hy
  have hint : ∀ s : ℝ, Integrable (fun y => Real.exp (s * extSum χ p₀ β lam ε₀ V Z S y)) P := by
    intro s
    refine Integrable.of_bound (Real.measurable_exp.comp
      (measurable_const.mul (measurable_extSum hχ hlam S))).aestronglyMeasurable
      (Real.exp (|s| * (C * S.card))) ?_
    filter_upwards [hTae] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg s)
  have h1 := externalNormalization_eq_integral_exp (L := L) (M := M) hχ hlam hε₀ hN (p₀ := p₀)
    (β := β) (V := V) (Z := Z) hS
  have h2 : externalNormalization χ N p₀ β lam M ε₀ L V Z S =
      ∫ y, Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y) ∂P := rfl
  have hsum : 2 * externalNormalization χ N p₀ β lam M ε₀ L V Z S =
      ∫ y, (Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y) +
        Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y)) ∂P := by
    rw [integral_add (hint _) (hint _), ← h2, ← h1]
    ring
  have hge : ∫ _y, (2 : ℝ) ∂P ≤ ∫ y, (Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y) +
      Real.exp (β * extSum χ p₀ β lam ε₀ V Z S y)) ∂P := by
    refine integral_mono (integrable_const _) ((hint _).add (hint _)) fun y => ?_
    have := Real.add_one_le_exp (β * extSum χ p₀ β lam ε₀ V Z S y)
    have := Real.add_one_le_exp (-β * extSum χ p₀ β lam ε₀ V Z S y)
    simp only
    linarith
  have hone := integral_one_plusModel hχ hlam hε₀ hN hpos (L := L)
  have h2' : ∫ _y, (2 : ℝ) ∂P = 2 := by
    rw [show (2 : ℝ) = 2 * 1 by norm_num, integral_const_mul]
    simp only [P]
    rw [hone, mul_one]
  rw [h2', ← hsum] at hge
  linarith

/-- **Eq. (5.101), upper bound**: there is `C > 0` (depending on `χ` and `q(β)`)
such that `g^Z_{ε₀}(S) ≤ e^{β C |S|}` when `𝖬^{+,Z}_{ε₀}(S) > 0`. -/
theorem externalNormalization_le (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (lam M ε₀ L : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → 0 < ε₀ → 1 ≤ N → lam ≤ ε₀ * truncationScale p₀ β lam →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M → V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ S : Finset ℕ, 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S →
        externalNormalization χ N p₀ β lam M ε₀ L V Z S ≤ Real.exp (β * (C * S.card)) := by
  obtain ⟨C, hC, hT⟩ := abs_extSum_le hχ p₀ β
  refine ⟨C, hC, fun {N} lam M ε₀ L V Z hlam hε₀ hN hlamh hM hM3 hVZ S hpos => ?_⟩
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN
  have : IsFiniteMeasure (plusModel χ N p₀ β lam M ε₀ L V Z {S}) :=
    h.isFiniteMeasure_modelHierarchical (M := M) (lam := lam) {S}
  have hae : ∀ᵐ y ∂plusModel χ N p₀ β lam M ε₀ L V Z {S},
      ‖Real.exp (-β * extSum χ p₀ β lam ε₀ V Z S y)‖ ≤ Real.exp (β * (C * S.card)) := by
    filter_upwards [ae_plusModel hχ hlam hε₀ hN] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.2 ?_
    have := hT lam M ε₀ V Z hlam hlamh hM hM3 hVZ S y hy
    have h' := neg_abs_le (extSum χ p₀ β lam ε₀ V Z S y)
    nlinarith
  have hn := norm_integral_le_of_norm_le_const hae
  have hone : (plusModel χ N p₀ β lam M ε₀ L V Z {S}).real Set.univ = 1 := by
    have := integral_one_plusModel hχ hlam hε₀ hN hpos
    rwa [integral_const, smul_eq_mul, mul_one] at this
  rw [hone, mul_one] at hn
  exact (le_abs_self _).trans hn

end External

end BoundedUpper

end UpperBound

end MultipoleBKT

end
