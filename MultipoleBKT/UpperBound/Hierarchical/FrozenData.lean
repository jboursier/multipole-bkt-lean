/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.BadSetOn
public import MultipoleBKT.UpperBound.BadPoints.Radii

/-!
# The data of a frozen configuration of bad points (Section 5.3)

The paper, Section 5.3: "frozen configurations
`Z` satisfy `I_bad^{V_bad} = V_bad` and `⋂_{i<j ∈ V_bad} 𝒜_ij`. The bad sets and radii are computed
from `Z`, keeping `N` in the count thresholds". A frozen configuration is given here by a
set `V : Finset (Fin N)` of bad labels and a configuration `Z : Fin N → ℂ × ℂ` of which only the
dipoles `Z j`, `j ∈ V`, are used; every object below depends only on `(Z j)_{j ∈ V}`
(`MultipoleBKT.UpperBound.badPointsOn_congr`, …). The good dipoles are arbitrary points `e ∈ ℂ × ℂ`.

Pair interaction (eqs. (5.6), (5.7), (5.8)), for dipoles `a = (x_a, y_a)`,
`b = (x_b, y_b)` with radii `t_a = (τ_a^+, τ_a^-)`, `t_b = (τ_b^+, τ_b^-)`:

* `pairInteraction χ λ a b t_a t_b = v^Z_{ab,+} - v^Z_{ab,-}`, with
  `v_{ab,+} = (g_λ - g * δ^{(τ_a^+)} * δ^{(τ_b^+)})(x_a - x_b) - (g_λ - g * δ^{(τ_a^-)} * δ^{(τ_b^+)})(y_a - x_b)`
  and `v_{ab,-}` the same with `y_b` and `τ_b^-`; symmetric (`pairInteraction_comm`).

The frozen-configuration objects (Definitions 5.7, 5.8, 5.13, 5.14):

* `badDistZ V Z e = min(dist({x_e, y_e}, {x_j, y_j : j ∈ V}), 4 ε₀ R̄)` (eq. (5.3) with
  `Z_bad = Z`) and `goodRadiusZ V Z e = max(badDistZ/4, λ)` (eq. (5.5), `τ_i^Z` for a good `i`);
* `badRadiiZ V Z j = (τ_j^{+,Z}, τ_j^{-,Z})` for `j ∈ V` (computed from `Z` on `V`,
  `MultipoleBKT.UpperBound.badRadiusPlusOn`);
* `interactionGoodZ`, `interactionExtZ`, `interactionBadZ`: `v^Z_ij` for two good dipoles, a good
  dipole and a bad label, and two bad labels;
* `externalBondZ V Z e = ∏_{j ∈ V} e^{-β v^Z_{ej}} - 1`: `f^{v^Z}_{i∞}` (Definition 5.14,
  Definition 5.14);
* `IsGoodZ V Z e`: `e ∈ I_good^Z` (eq. (5.51)): `d_ej > M max(r_e, λ)` for
  every `j ∈ I^1_bad ∪ I^2_bad` and `d_ej > M max(min(r_e, r_j), λ)` for every `j ∈ I^3_bad`, the
  bad sets being computed from `Z` on `V`;
* `dipoleWeightZ L V Z e = e^{L r_e² / (τ_e^Z)²} 𝟙_{e ∈ I_good^Z}`, the one-body weight of
  `𝖯^{+,ε₀,Z}` (eq. (5.52)), and `hatDipoleWeightZ = dipoleWeightZ · ∏_{j ∈ V} e^{-β v^Z_{ej}}`;
* `badWeightZ V Z = 𝟙_{I_bad^V(Z) = V} ∏_{i<j ∈ V} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
  ∏_{i ∈ V} (τ_i^{+,Z})^{-β/2} (τ_i^{-,Z})^{-β/2}`, the bad-point factor of the integrand of
  eq. (5.58) (Lemma 5.16).

For the full configuration, the interaction `interactionZ` of `MultipoleBKT.UpperBound.Radii`
(Definition 5.8) is `pairInteraction` with the radii `τ^{±,Z}` (`interactionZ_eq_pairInteraction`,
by `rfl`).
-/

@[expose] public section

open Finset
open TwoComponentCoulomb (logKernel)

namespace MultipoleBKT

namespace UpperBound

variable {N : ℕ}

/-! ### The pair interaction with given radii -/

/-- **The interaction `v^Z_ij = v^Z_{i,j,+} - v^Z_{i,j,-}`** (eqs. (5.6), (5.7), (5.8), eq. (3.6) of Prop 3.3) of the dipoles `a = (x_i, y_i)`,
`b = (x_j, y_j)` with radii `t_a = (τ_i^+, τ_i^-)` and `t_b = (τ_j^+, τ_j^-)`. -/
noncomputable def pairInteraction (χ : ℂ → ℝ) (lam : ℝ) (a b : ℂ × ℂ) (ta tb : ℝ × ℝ) : ℝ :=
  ((smearedKernel χ lam (a.1 - b.1) - twoRadiusKernel χ ta.1 tb.1 (a.1 - b.1)) -
      (smearedKernel χ lam (a.2 - b.1) - twoRadiusKernel χ ta.2 tb.1 (a.2 - b.1))) -
    ((smearedKernel χ lam (a.1 - b.2) - twoRadiusKernel χ ta.1 tb.2 (a.1 - b.2)) -
      (smearedKernel χ lam (a.2 - b.2) - twoRadiusKernel χ ta.2 tb.2 (a.2 - b.2)))

/-- `v_ab = v_ba` (`MultipoleBKT.UpperBound.interactionZ_comm`). -/
theorem pairInteraction_comm {χ : ℂ → ℝ} (hχ : IsMollifier χ) (lam : ℝ) (a b : ℂ × ℂ)
    (ta tb : ℝ × ℝ) : pairInteraction χ lam a b ta tb = pairInteraction χ lam b a tb ta := by
  unfold pairInteraction
  have eg : ∀ u v : ℂ, smearedKernel χ lam (u - v) = smearedKernel χ lam (v - u) := fun u v => by
    rw [← neg_sub v u, smearedKernel_neg hχ]
  have eK : ∀ α η : ℝ, ∀ u v : ℂ, twoRadiusKernel χ α η (u - v) = twoRadiusKernel χ η α (v - u) :=
    fun α η u v => by rw [← neg_sub v u, twoRadiusKernel_neg hχ, twoRadiusKernel_comm hχ]
  rw [eg a.1 b.1, eg a.2 b.2, eg a.2 b.1, eg a.1 b.2, eK ta.1 tb.1 a.1 b.1, eK ta.2 tb.2 a.2 b.2,
    eK ta.2 tb.1 a.2 b.1, eK ta.1 tb.2 a.1 b.2]
  ring

/-- `v^Z_ij` of the full configuration (`MultipoleBKT.UpperBound.interactionZ`) is
`pairInteraction` with the radii `(τ_i^{+,Z}, τ_i^{-,Z})`, `(τ_j^{+,Z}, τ_j^{-,Z})`. -/
theorem interactionZ_eq_pairInteraction (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (d : Fin N → ℂ × ℂ) (i j : Fin N) :
    interactionZ χ p₀ β lam M ε₀ d i j =
      pairInteraction χ lam (d i) (d j)
        (radiusPlusZ p₀ β lam M ε₀ d i, radiusMinusZ p₀ β lam M ε₀ d i)
        (radiusPlusZ p₀ β lam M ε₀ d j, radiusMinusZ p₀ β lam M ε₀ d j) :=
  rfl

/-! ### Frozen bad points -/

section Frozen

variable (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ L : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ)

/-- **`d_{i,bad}` for a frozen configuration** (eq. (5.3), Definition 5.7, with
`Z_bad = {x_j, y_j : j ∈ V}`): `min(dist({x_e, y_e}, Z_bad), 4 ε₀ R̄)` for a good dipole `e`, as a
fold of `min` starting from the cap `4 ε₀ R̄`. -/
noncomputable def badDistZ (e : ℂ × ℂ) : ℝ :=
  V.fold min (4 * (ε₀ * truncationScale p₀ β lam)) fun j => dipoleDist e (Z j)

/-- **`τ_i^Z` for a good dipole** (eq. (5.5)):
`τ_i^{+,Z} = τ_i^{-,Z} = max(d_{i,bad}/4, λ)`. -/
noncomputable def goodRadiusZ (e : ℂ × ℂ) : ℝ :=
  max (badDistZ p₀ β lam ε₀ V Z e / 4) lam

/-- **`(τ_j^{+,Z}, τ_j^{-,Z})` for a bad label** (Definition 5.8), computed from `Z`
on `V`. -/
noncomputable def badRadiiZ (j : Fin N) : ℝ × ℝ :=
  (badRadiusPlusOn p₀ β lam ε₀ V Z j, badRadiusMinusOn p₀ β lam ε₀ V Z j)

/-- `v^Z_ij` for two good dipoles `d`, `e` (radii `τ^Z`). -/
noncomputable def interactionGoodZ (d e : ℂ × ℂ) : ℝ :=
  pairInteraction χ lam d e (goodRadiusZ p₀ β lam ε₀ V Z d, goodRadiusZ p₀ β lam ε₀ V Z d)
    (goodRadiusZ p₀ β lam ε₀ V Z e, goodRadiusZ p₀ β lam ε₀ V Z e)

/-- `v^Z_ij` for a good dipole `d` and a bad label `j`. -/
noncomputable def interactionExtZ (d : ℂ × ℂ) (j : Fin N) : ℝ :=
  pairInteraction χ lam d (Z j) (goodRadiusZ p₀ β lam ε₀ V Z d, goodRadiusZ p₀ β lam ε₀ V Z d)
    (badRadiiZ p₀ β lam ε₀ V Z j)

/-- `v^Z_ij` for two bad labels `i`, `j`. -/
noncomputable def interactionBadZ (i j : Fin N) : ℝ :=
  pairInteraction χ lam (Z i) (Z j) (badRadiiZ p₀ β lam ε₀ V Z i) (badRadiiZ p₀ β lam ε₀ V Z j)

/-- **`f^{v^Z}_{i∞}`** (Definition 5.14): the external bond
`∏_{j ∈ V_bad} e^{-β v^Z_ij} - 1` of a good dipole with the frozen bad points. -/
noncomputable def externalBondZ (d : ℂ × ℂ) : ℝ :=
  ∏ j ∈ V, Real.exp (-β * interactionExtZ χ p₀ β lam ε₀ V Z d j) - 1

/-- **`i ∈ I_good^Z`** (eq. (5.51), Definition 5.13) for the dipole `e` of `i`:
`d_ij > M max(r_i, λ)` for `j ∈ I^1_bad ∪ I^2_bad` and `d_ij > M max(min(r_i, r_j), λ)` for
`j ∈ I^3_bad`, the bad sets being computed from `Z` on `V`. -/
def IsGoodZ (e : ℂ × ℂ) : Prop :=
  (∀ j ∈ typeOneOn p₀ β lam ε₀ V Z ∪ typeTwoOn p₀ β lam M ε₀ V Z,
      M * max ‖e.1 - e.2‖ lam < dipoleDist e (Z j)) ∧
    ∀ j ∈ typeThreeOn p₀ β lam M ε₀ V Z,
      M * max (min ‖e.1 - e.2‖ ‖(Z j).1 - (Z j).2‖) lam < dipoleDist e (Z j)

open scoped Classical in
/-- The one-body weight `e^{L r_i² / (τ_i^Z)²} 𝟙_{i ∈ I_good^Z}` of the hierarchical model with
frozen bad points (eq. (5.52)), `L` the constant of eq. (5.50). -/
noncomputable def dipoleWeightZ (e : ℂ × ℂ) : ℝ :=
  Real.exp (L * (‖e.1 - e.2‖ / goodRadiusZ p₀ β lam ε₀ V Z e) ^ 2) *
    if IsGoodZ p₀ β lam M ε₀ V Z e then 1 else 0

/-- The one-body weight times the interaction with the frozen bad points,
`e^{L r_i² / (τ_i^Z)²} 𝟙_{i ∈ I_good^Z} ∏_{j ∈ V_bad} e^{-β v^Z_ij}`: the weight of the model whose
partition function is `𝖬̂^{+,Z}_{ε₀}` (eq. (5.54)). -/
noncomputable def hatDipoleWeightZ (e : ℂ × ℂ) : ℝ :=
  dipoleWeightZ p₀ β lam M ε₀ L V Z e * ∏ j ∈ V, Real.exp (-β * interactionExtZ χ p₀ β lam ε₀ V Z e j)

open scoped Classical in
/-- **The bad-point factor** of the integrand of eq. (5.58) (Lemma 5.16):
`𝟙_{I_bad^V(Z) = V} ∏_{i<j ∈ V} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
∏_{i ∈ V} (τ_i^{+,Z})^{-β/2} (τ_i^{-,Z})^{-β/2}`. -/
noncomputable def badWeightZ : ℝ :=
  (if badPointsOn p₀ β lam M ε₀ V Z = V then 1 else 0) *
    (∏ i ∈ V, ∏ j ∈ V with i < j,
      if IsStableDipolePair (Z i) (Z j) then Real.exp (-β * interactionBadZ χ p₀ β lam ε₀ V Z i j)
      else 0) *
    ∏ i ∈ V, 1 / (badRadiusPlusOn p₀ β lam ε₀ V Z i ^ (β / 2) *
      badRadiusMinusOn p₀ β lam ε₀ V Z i ^ (β / 2))

end Frozen

/-! ### Elementary facts -/

section Facts

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- `1 + f^{v^Z}_{i∞} = ∏_{j ∈ V} e^{-β v^Z_ij} > 0`. -/
theorem one_add_externalBondZ (d : ℂ × ℂ) :
    1 + externalBondZ χ p₀ β lam ε₀ V Z d =
      ∏ j ∈ V, Real.exp (-β * interactionExtZ χ p₀ β lam ε₀ V Z d j) := by
  unfold externalBondZ
  ring

theorem one_add_externalBondZ_pos (d : ℂ × ℂ) : 0 < 1 + externalBondZ χ p₀ β lam ε₀ V Z d := by
  rw [one_add_externalBondZ]
  exact Finset.prod_pos fun j _ => Real.exp_pos _

theorem dipoleWeightZ_nonneg (e : ℂ × ℂ) : 0 ≤ dipoleWeightZ p₀ β lam M ε₀ L V Z e := by
  unfold dipoleWeightZ
  split_ifs <;> positivity

theorem hatDipoleWeightZ_nonneg (e : ℂ × ℂ) : 0 ≤ hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z e :=
  mul_nonneg (dipoleWeightZ_nonneg e) (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

theorem hatDipoleWeightZ_eq (e : ℂ × ℂ) :
    hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z e =
      dipoleWeightZ p₀ β lam M ε₀ L V Z e * (1 + externalBondZ χ p₀ β lam ε₀ V Z e) := by
  rw [one_add_externalBondZ]
  rfl

theorem lam_le_goodRadiusZ (e : ℂ × ℂ) : lam ≤ goodRadiusZ p₀ β lam ε₀ V Z e := le_max_right _ _

theorem goodRadiusZ_pos (hlam : 0 < lam) (e : ℂ × ℂ) : 0 < goodRadiusZ p₀ β lam ε₀ V Z e :=
  hlam.trans_le (lam_le_goodRadiusZ e)

/-- The fold defining `d_{i,bad}` is the minimum of the cap and the distances to `V`. -/
theorem badDistZ_le_cap (e : ℂ × ℂ) :
    badDistZ p₀ β lam ε₀ V Z e ≤ 4 * (ε₀ * truncationScale p₀ β lam) := by
  unfold badDistZ
  exact (Finset.fold_min_le _).2 (Or.inl le_rfl)

theorem badDistZ_le_dipoleDist (e : ℂ × ℂ) {j : Fin N} (hj : j ∈ V) :
    badDistZ p₀ β lam ε₀ V Z e ≤ dipoleDist e (Z j) := by
  unfold badDistZ
  exact (Finset.fold_min_le _).2 (Or.inr ⟨j, hj, le_rfl⟩)

theorem le_badDistZ {e : ℂ × ℂ} {a : ℝ} (hcap : a ≤ 4 * (ε₀ * truncationScale p₀ β lam))
    (hV : ∀ j ∈ V, a ≤ dipoleDist e (Z j)) : a ≤ badDistZ p₀ β lam ε₀ V Z e := by
  unfold badDistZ
  exact (Finset.le_fold_min _).2 ⟨hcap, hV⟩

/-- `goodRadiusZ ≤ max(ε₀ R̄, λ)`. -/
theorem goodRadiusZ_le (e : ℂ × ℂ) :
    goodRadiusZ p₀ β lam ε₀ V Z e ≤ max (ε₀ * truncationScale p₀ β lam) lam := by
  unfold goodRadiusZ
  refine max_le_max ?_ le_rfl
  have := badDistZ_le_cap (lam := lam) (V := V) (Z := Z) (p₀ := p₀) (β := β) (ε₀ := ε₀) e
  linarith

end Facts

end UpperBound

end MultipoleBKT

end
