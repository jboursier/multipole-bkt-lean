/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.ActivityIntegral
public import MultipoleBKT.LowerBound.Hierarchical.DipoleMeasure
public import MultipoleBKT.UpperBound.Hierarchical.FrozenBounds

/-!
# The hierarchical model with frozen bad points (Definitions 5.13–5.15)

The paper: Section 5.3,
Definitions 5.13–5.15. A frozen configuration
of bad points is a set `V : Finset (Fin N)` of bad labels with a configuration `Z : Fin N → ℂ × ℂ`
(only `(Z j)_{j ∈ V}` is used; `MultipoleBKT.UpperBound.Hierarchical.FrozenData`); good labels are
natural numbers (`S, X` are finite sets of labels and subpartitions, as in the frozen
`multipoleActivity`). With the truncated dipole measure `μ_{β,λ,ε₀}`
(`MultipoleBKT.Hierarchical.cutoffDipoleMeasure`, Definition 4.11), the interaction
`v^Z` of two good dipoles (`interactionGoodZ`) and the one-body weight
`e^{L r_i² / (τ_i^Z)²} 𝟙_{i ∈ I_good^Z}` (`dipoleWeightZ`), the paper's objects are instances of the
generic hierarchical model of `MultipoleBKT.Hierarchical` (`MultipoleBKT.LowerBound.Hierarchical`, model of
Section 4):

* `plusPartitionFunction S = 𝖬^{+,Z}_{ε₀}(S)` (eq. (5.53))
* `plusModel X = 𝖯^{+,ε₀,Z}_X` (eq. (5.52)), in the density form of the frozen
  `hierarchicalModel`;
* `plusActivity X = 𝖪^{+,Z}_{ε₀}(X)` (Definition 5.15): `0` for `|X| ≤ 1` and otherwise
  `∑_{V^∞ ⊆ V_X} ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{Eₗ ∈ 𝖤^{Xₗ}}
  ∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}} 𝔼_{𝖯_X^{+,ε₀,Z}}[∏_{ij ∈ ∪ Eₗ} f^{v^Z}_ij
  ∏_{ij ∈ ∪ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c} ∏_{ij ∈ F} (-𝟙_{𝓑_ij}) ∏_{i ∈ V^∞} f^{v^Z}_{i∞}]`;
* `externalNormalization S = g^Z_{ε₀}(S) = 𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[e^{-β ∑_{i ∈ S, j ∈ V_bad} v^Z_ij}]`
  (eq. (5.54));
* `hatPartitionFunction S = 𝖬̂^{+,Z}_{ε₀}(S) = 𝖬^{+,Z}_{ε₀}(S) g^Z_{ε₀}(S)`,
  `hatPartitionFunctions X = ∏_{S ∈ X} 𝖬̂^{+,Z}_{ε₀}(S)` and
  `hatActivity X = 𝖪̂^{+,Z}_{ε₀}(X) = 𝖪^{+,Z}_{ε₀}(X) / ∏_{S ∈ X} g^Z_{ε₀}(S)`
  (eq. (5.55));
* `clusterSeriesW π = W(Z) = ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint} ∏ₗ 𝖪̂^{+,Z}_{ε₀}(Xₗ)`
  (eq. (5.59), Lemma 5.16).

The constant `L` of eq. (5.50) is a parameter of the definitions; Lemma 5.16 uses `L = β L₀` with
the `L₀` of `MultipoleBKT.UpperBound.eq_b1`.

API (for `N ≥ 1`, `λ > 0`, `ε₀ > 0`, `χ` a mollifier):
`modelHyp_plus` and `modelHyp_hat` (the hypotheses `MultipoleBKT.Hierarchical.ModelHyp` for
the weights `dipoleWeightZ` and `hatDipoleWeightZ`, on `K = Λ² ∩ {|x - y| ≤ ε₀ R̄}`), hence
measurability, boundedness and integrability of all integrands. Positivity
(`plusPartitionFunction_nonneg`, `hatPartitionFunction_nonneg`) and the case `V_bad = ∅` are in
`MultipoleBKT.UpperBound.Hierarchical.Expansion`. The stronger bound `g^Z ≥ 1` in the paper
parameter range is `BoundedUpper.one_le_externalNormalization`.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBound

open Hierarchical Multipole SetPartition Parity

/-! ### The definitions -/

section Definitions

variable (χ : ℂ → ℝ) (N : ℕ) (p₀ : ℕ) (β lam M ε₀ L : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)

/-- **`𝖬^{+,Z}_{ε₀}(S)`** (eq. (5.53), Definition 5.13):
`𝔼_{μ_{β,λ,ε₀}^{⊗|S|}}[𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
∏_{i ∈ S} e^{L r_i²/(τ_i^Z)²} 𝟙_{i ∈ I_good^Z}]`. -/
noncomputable def plusPartitionFunction (S : Finset ℕ) : ℝ :=
  modelPartitionFunction (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
    (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam S


/-- **`𝖯^{+,ε₀,Z}_X`** (eq. (5.52), Definition 5.13), the probability measure
on `(Λ²)^{V_X}` with density `∏_{S ∈ X} 𝖬^{+,Z}(S)⁻¹ 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
∏_{i ∈ S} e^{L r_i²/(τ_i^Z)²} 𝟙_{i ∈ I_good^Z}` with respect to `μ_{β,λ,ε₀}^{⊗ V_X}`. -/
noncomputable def plusModel (X : Finset (Finset ℕ)) : Measure (X.biUnion id → ℂ × ℂ) :=
  modelHierarchical (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
    (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam X

open scoped Classical in
/-- **`𝖪^{+,Z}_{ε₀}(X)`** (Definition 5.15): `0` for
`|X| ≤ 1` and, for `|X| ≥ 2`, the series
`∑_{V^∞ ⊆ V_X} ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{E₁ ∈ 𝖤^{X₁}} ⋯ ∑_{Eₙ ∈ 𝖤^{Xₙ}}
∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}} 𝔼_{𝖯_X^{+,ε₀,Z}}[∏_{ij ∈ E₁ ∪ ⋯ ∪ Eₙ} f^{v^Z}_ij
∏_{ij ∈ ∪ₗ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c} ∏_{ij ∈ F} (-𝟙_{𝓑_ij}) ∏_{i ∈ V^∞} f^{v^Z}_{i∞}]`. -/
noncomputable def plusActivity (X : Finset (Finset ℕ)) : ℝ :=
  if X.card ≤ 1 then 0 else
    ∑ U ∈ (X.biUnion id).powerset,
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset fun l => relEdgeSets (Xs l),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
              ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
                  (extendConfig (X.biUnion id) y) *
                ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
                ∂plusModel χ N p₀ β lam M ε₀ L V Z X

/-- **`g^Z_{ε₀}(S)`** (eq. (5.54)):
`𝔼_{𝖯^{+,ε₀,Z}_{{S}}}[e^{-β ∑_{i ∈ S, j ∈ V_bad} v^Z_ij}]`. -/
noncomputable def externalNormalization (S : Finset ℕ) : ℝ :=
  ∫ y, Real.exp (-β * ∑ i : ({S} : Finset (Finset ℕ)).biUnion id,
      ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z (y i) j)
    ∂plusModel χ N p₀ β lam M ε₀ L V Z {S}

/-- **`𝖬̂^{+,Z}_{ε₀}(S) = 𝖬^{+,Z}_{ε₀}(S) g^Z_{ε₀}(S)`** (eq. (5.54)). -/
noncomputable def hatPartitionFunction (S : Finset ℕ) : ℝ :=
  plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S *
    externalNormalization χ N p₀ β lam M ε₀ L V Z S

/-- `𝖬̂^{+,Z}_{ε₀}(X) = ∏_{S ∈ X} 𝖬̂^{+,Z}_{ε₀}(S)` (eq. (5.55)). -/
noncomputable def hatPartitionFunctions (X : Finset (Finset ℕ)) : ℝ :=
  ∏ S ∈ X, hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S

/-- **`𝖪̂^{+,Z}_{ε₀}(X) = 𝖪^{+,Z}_{ε₀}(X) / ∏_{S ∈ X} g^Z_{ε₀}(S)`** (eq. (5.55)). -/
noncomputable def hatActivity (X : Finset (Finset ℕ)) : ℝ :=
  plusActivity χ N p₀ β lam M ε₀ L V Z X /
    ∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S

/-- **`W(Z)`** (eq. (5.59), Lemma 5.16):
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ∈ 𝒫(π) disjoint} 𝖪̂^{+,Z}_{ε₀}(X₁) ⋯ 𝖪̂^{+,Z}_{ε₀}(Xₙ)`. -/
noncomputable def clusterSeriesW (π : Finset (Finset ℕ)) : ℝ :=
  ∑' n : ℕ, 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∏ i, hatActivity χ N p₀ β lam M ε₀ L V Z (Xs i)

end Definitions

theorem plusActivity_eq_zero_of_card_le_one {N : ℕ} (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ L : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) {X : Finset (Finset ℕ)} (h : X.card ≤ 1) :
    plusActivity χ N p₀ β lam M ε₀ L V Z X = 0 := by
  rw [plusActivity, ite_eq_left h]

theorem hatActivity_eq_zero_of_card_le_one {N : ℕ} (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ L : ℝ)
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) {X : Finset (Finset ℕ)} (h : X.card ≤ 1) :
    hatActivity χ N p₀ β lam M ε₀ L V Z X = 0 := by
  rw [hatActivity, plusActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h, zero_div]

/-! ### The hypotheses of the generic model -/

section Hyp

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- The support `K = Λ² ∩ {|x - y| ≤ ε₀ R̄}` of `μ_{β,λ,ε₀}`. -/
def supportSet (N p₀ : ℕ) (β lam ε₀ : ℝ) : Set (ℂ × ℂ) :=
  {p | p ∈ box N ×ˢ box N ∧ ‖p.1 - p.2‖ ≤ ε₀ * truncationScale p₀ β lam}

theorem norm_le_of_mem_box {z : ℂ} (hz : z ∈ box N) : ‖z‖ ≤ 2 * Real.sqrt N := by
  rw [box, Complex.mem_reProdIm] at hz
  have hre : |z.re| ≤ Real.sqrt N := abs_le.2 ⟨by linarith [hz.1.1, Real.sqrt_nonneg N], hz.1.2⟩
  have him : |z.im| ≤ Real.sqrt N := abs_le.2 ⟨by linarith [hz.2.1, Real.sqrt_nonneg N], hz.2.2⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * Real.sqrt N := by linarith

theorem norm_sub_le_of_mem_box' {z w : ℂ} (hz : z ∈ box N) (hw : w ∈ box N) :
    ‖z - w‖ ≤ 2 * Real.sqrt N :=
  norm_sub_le_of_mem_box (p := (z, w)) ⟨hz, hw⟩

/-- `|v^Z|` of two dipoles of `Λ²` is bounded. -/
theorem exists_abs_interactionGoodZ_le (hχ : IsMollifier χ) (hlam : 0 < lam) :
    ∃ B, ∀ d ∈ supportSet N p₀ β lam ε₀, ∀ e ∈ supportSet N p₀ β lam ε₀,
      |interactionGoodZ χ p₀ β lam ε₀ V Z d e| ≤ B := by
  set R := max (ε₀ * truncationScale p₀ β lam) lam
  have hR : lam ≤ R := le_max_right _ _
  have hτ : ∀ e : ℂ × ℂ, lam ≤ goodRadiusZ p₀ β lam ε₀ V Z e ∧
      goodRadiusZ p₀ β lam ε₀ V Z e ≤ R := fun e => ⟨lam_le_goodRadiusZ e, goodRadiusZ_le e⟩
  refine ⟨8 * kernelBound χ lam R (2 * Real.sqrt N), fun d hd e he => ?_⟩
  obtain ⟨⟨hd1, hd2⟩, -⟩ := hd
  obtain ⟨⟨he1, he2⟩, -⟩ := he
  exact abs_pairInteraction_le hχ hlam hR (hτ d) (hτ d) (hτ e) (hτ e)
    (norm_sub_le_of_mem_box' hd1 he1) (norm_sub_le_of_mem_box' hd2 he1)
    (norm_sub_le_of_mem_box' hd1 he2) (norm_sub_le_of_mem_box' hd2 he2)

/-- `|v^Z|` of a dipole of `Λ²` with a bad label `j ∈ V` is bounded. -/
theorem exists_abs_interactionExtZ_le (hχ : IsMollifier χ) (hlam : 0 < lam) :
    ∃ B, ∀ d ∈ supportSet N p₀ β lam ε₀, ∀ j ∈ V,
      |interactionExtZ χ p₀ β lam ε₀ V Z d j| ≤ B := by
  set R := max (ε₀ * truncationScale p₀ β lam) lam
  have hR : lam ≤ R := le_max_right _ _
  have hτ : ∀ e : ℂ × ℂ, lam ≤ goodRadiusZ p₀ β lam ε₀ V Z e ∧
      goodRadiusZ p₀ β lam ε₀ V Z e ≤ R := fun e => ⟨lam_le_goodRadiusZ e, goodRadiusZ_le e⟩
  have hb : ∀ j ∈ V, (lam ≤ (badRadiiZ p₀ β lam ε₀ V Z j).1 ∧ (badRadiiZ p₀ β lam ε₀ V Z j).1 ≤ R) ∧
      (lam ≤ (badRadiiZ p₀ β lam ε₀ V Z j).2 ∧ (badRadiiZ p₀ β lam ε₀ V Z j).2 ≤ R) :=
    fun j hj => ⟨⟨lam_le_badRadiusPlusOn j, (badRadiusPlusOn_le hj).trans (by
      rw [max_comm])⟩, ⟨lam_le_badRadiusMinusOn j, (badRadiusMinusOn_le hj).trans (by
      rw [max_comm])⟩⟩
  set D := 2 * Real.sqrt N + ∑ j ∈ V, (‖(Z j).1‖ + ‖(Z j).2‖)
  have hZ : ∀ j ∈ V, ‖(Z j).1‖ + ‖(Z j).2‖ ≤ ∑ j ∈ V, (‖(Z j).1‖ + ‖(Z j).2‖) := fun j hj =>
    Finset.single_le_sum (f := fun j => ‖(Z j).1‖ + ‖(Z j).2‖) (fun _ _ => by positivity) hj
  refine ⟨8 * kernelBound χ lam R D, fun d hd j hj => ?_⟩
  obtain ⟨⟨hd1, hd2⟩, -⟩ := hd
  have hj1 := hZ j hj
  have hn : ∀ {u : ℂ}, u ∈ box N → ∀ {v : ℂ}, ‖v‖ ≤ ‖(Z j).1‖ + ‖(Z j).2‖ → ‖u - v‖ ≤ D :=
    fun hu v hv => (norm_sub_le _ _).trans (by
      have := norm_le_of_mem_box hu
      simp only [D]
      linarith)
  exact abs_pairInteraction_le hχ hlam hR (hτ d) (hτ d) (hb j hj).1 (hb j hj).2
    (hn hd1 (by linarith [norm_nonneg (Z j).2])) (hn hd2 (by linarith [norm_nonneg (Z j).2]))
    (hn hd1 (by linarith [norm_nonneg (Z j).1])) (hn hd2 (by linarith [norm_nonneg (Z j).1]))

theorem dipoleWeightZ_le (hlam : 0 < lam) (hε₀ : 0 < ε₀) {e : ℂ × ℂ}
    (he : e ∈ supportSet N p₀ β lam ε₀) :
    dipoleWeightZ p₀ β lam M ε₀ L V Z e ≤
      Real.exp (|L| * ((ε₀ * truncationScale p₀ β lam) / lam) ^ 2) := by
  classical
  have hR : 0 < ε₀ * truncationScale p₀ β lam :=
    mul_pos hε₀ (Appendix.truncationScale_pos hlam)
  have hτ := lam_le_goodRadiusZ (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V) (Z := Z) e
  have hτ0 : 0 < goodRadiusZ p₀ β lam ε₀ V Z e := hlam.trans_le hτ
  have hr : ‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e ≤ (ε₀ * truncationScale p₀ β lam) / lam :=
    div_le_div₀ hR.le he.2 hlam hτ
  have hsq : (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2 ≤
      ((ε₀ * truncationScale p₀ β lam) / lam) ^ 2 :=
    pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hτ0.le) hr 2
  unfold dipoleWeightZ
  have hexp : Real.exp (L * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2) ≤
      Real.exp (|L| * ((ε₀ * truncationScale p₀ β lam) / lam) ^ 2) := by
    refine Real.exp_le_exp.2 ((le_abs_self L |>.trans_eq rfl |> fun h =>
      mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans ?_)
    exact mul_le_mul_of_nonneg_left hsq (abs_nonneg L)
  split_ifs
  · rw [mul_one]
    exact hexp
  · rw [mul_zero]
    exact (Real.exp_pos _).le

theorem ae_supportSet (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) :
    ∀ᵐ p ∂cutoffDipoleMeasure χ N p₀ β lam ε₀, p ∈ supportSet N p₀ β lam ε₀ :=
  ae_cutoffDipoleMeasure χ N p₀ β lam ε₀

/-- The generic hypotheses for `(μ_{β,λ,ε₀}, v^Z, e^{L r²/τ²} 𝟙_{I_good^Z})`. -/
theorem modelHyp_plus (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) :
    ModelHyp (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) (supportSet N p₀ β lam ε₀) where
  isProbabilityMeasure := isProbabilityMeasure_cutoffDipoleMeasure hχ hlam β hε₀ hN
  ae_mem := ae_supportSet χ N p₀ β lam ε₀
  measurable_w := measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam
  measurable_ψ := measurable_dipoleWeightZ p₀ β lam M ε₀ L V Z
  nonneg_ψ := dipoleWeightZ_nonneg
  bdd_w := by
    obtain ⟨B, hB⟩ := exists_abs_interactionGoodZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
      (Z := Z) hχ hlam
    refine ⟨|β| * B, fun d hd e he => ?_⟩
    have h := hB d hd e he
    calc -β * interactionGoodZ χ p₀ β lam ε₀ V Z d e
        ≤ |-β * interactionGoodZ χ p₀ β lam ε₀ V Z d e| := le_abs_self _
      _ = |β| * |interactionGoodZ χ p₀ β lam ε₀ V Z d e| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * B := mul_le_mul_of_nonneg_left h (abs_nonneg β)
  bdd_ψ := ⟨_, fun d hd => dipoleWeightZ_le hlam hε₀ hd⟩

/-- The generic hypotheses for `(μ_{β,λ,ε₀}, v^Z, e^{L r²/τ²} 𝟙_{I_good^Z} ∏_{j ∈ V} e^{-β v^Z_ij})`. -/
theorem modelHyp_hat (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N) :
    ModelHyp (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) (supportSet N p₀ β lam ε₀) where
  isProbabilityMeasure := isProbabilityMeasure_cutoffDipoleMeasure hχ hlam β hε₀ hN
  ae_mem := ae_supportSet χ N p₀ β lam ε₀
  measurable_w := measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam
  measurable_ψ := measurable_hatDipoleWeightZ p₀ β lam M ε₀ L V Z hχ hlam
  nonneg_ψ := hatDipoleWeightZ_nonneg
  bdd_w := (modelHyp_plus (M := M) (L := L) hχ hlam hε₀ hN).bdd_w
  bdd_ψ := by
    obtain ⟨B, hB⟩ := exists_abs_interactionExtZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
      (Z := Z) hχ hlam
    refine ⟨Real.exp (|L| * ((ε₀ * truncationScale p₀ β lam) / lam) ^ 2) *
      ∏ _j ∈ V, Real.exp (|β| * B), fun d hd => ?_⟩
    unfold hatDipoleWeightZ
    refine mul_le_mul (dipoleWeightZ_le hlam hε₀ hd) (Finset.prod_le_prod₀
      (fun _ _ => (Real.exp_pos _).le) fun j hj => Real.exp_le_exp.2 ?_)
      (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le) (Real.exp_pos _).le
    calc -β * interactionExtZ χ p₀ β lam ε₀ V Z d j
        ≤ |-β * interactionExtZ χ p₀ β lam ε₀ V Z d j| := le_abs_self _
      _ = |β| * |interactionExtZ χ p₀ β lam ε₀ V Z d j| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * B := mul_le_mul_of_nonneg_left (hB d hd j hj) (abs_nonneg β)

end Hyp

end UpperBound

end MultipoleBKT

end
