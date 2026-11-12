/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ZParity

/-!
# Splitting the frozen comparison along the short-edge domain

See Lemma A.7. The model integrand vanishes outside the common short-edge domain.
The remaining baseline term is integrated through `RouteOmitted.API`
in `lemma_A8_plus`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset Metric SimpleGraph Filter
open scoped ENNReal
open TwoComponentCoulomb (box)
open Hierarchical Multipole Parity Limits SmallIntegral UpperBound BoundedUpper MultipoleIntegralZ
  Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Parts

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
/-- The integrands of the models `Z` and `0` with the cutoff are bounded (for fixed `λ`). -/
theorem plus_QH_bound (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    {N p₀ : ℕ} {ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM3 : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hVZ : badPointsOn p₀ β lam M ε₀ V Z = V) (blk : ι → β') (Dn Dz Df : Finset (Sym2 ι)) :
    ∃ B : ℝ, ∀ y : ι → ℂ × ℂ,
      |clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam
          blk Dn Dz Df y * ((∏ i, pairDensity χ β lam (y i)) *
            cutInd (ε₀ * truncationScale p₀ β lam) y)| ≤ B ∧
      |clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df y *
          ((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y)| ≤ B := by
  set k := Fintype.card ι
  set h := ε₀ * truncationScale p₀ β lam
  set Q₁ : (ι → ℂ × ℂ) → ℝ := clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
    (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df
  set Q₀ : (ι → ℂ × ℂ) → ℝ :=
    clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
  set H : (ι → ℂ × ℂ) → ℝ := fun y => (∏ i, pairDensity χ β lam (y i)) * cutInd h y
  set W := WZ hχ β
  have hW : 1 ≤ W := one_le_WZ hχ hβ0
  set Ψ := Real.exp (16 * |L|)
  have hΨ : 1 ≤ Ψ := Real.one_le_exp (by positivity)
  set Bq := (W ^ (k * k) * Ψ ^ k) ^ Fintype.card β' * (W + 1) ^ Df.card
  set Bp := (densConst hχ hβ0 * lam ^ (-β)) ^ k
  have hBq0 : 0 ≤ Bq := by
    have : 0 ≤ W := by linarith
    have : 0 ≤ Ψ := by linarith
    positivity
  have hBp0 : 0 ≤ Bp := by
    have := densConst_pos hχ hβ0
    have := Real.rpow_nonneg hlam.le (-β)
    positivity
  refine ⟨Bq * Bp, fun y => ?_⟩
  have hH0 : 0 ≤ H y := mul_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le)
    (cutInd_nonneg h y)
  rcases cutInd_eq_one_or h y with ⟨h1, hcut⟩ | h0
  · have hpd := prod_pairDensity_le hχ hβ0 hlam y
    have hH : H y ≤ Bp := by simp only [H, h1, mul_one]; exact hpd
    have hs₀ : ∀ i j, 0 ≤ stableWeight β (dipoleInteraction χ lam) (y i) (y j) ∧
        stableWeight β (dipoleInteraction χ lam) (y i) (y j) ≤ W := fun i j => by
      constructor
      · unfold stableWeight; split_ifs <;> positivity
      · unfold stableWeight
        split_ifs with hst
        · refine Real.exp_le_exp.2 ?_
          have h3 := neg_cbK_le hχ hlam hst (lam := lam)
          have := cbK_nonneg hχ
          have := c3Z_pos hχ
          nlinarith
        · linarith
    have hb₀ := abs_clusterQ_le (M := M) (lam := lam) (ψ := fun _ => 1) blk Dn Dz Df y hW hΨ hs₀
      (fun _ => ⟨zero_le_one, hΨ⟩)
    have hb₁ : |Q₁ y| ≤ Bq := by
      by_cases hgood : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (y i)
      · obtain ⟨-, hs₁, -, -, hψ, -⟩ :=
          plus_stable_facts (L := L) hχ hβ0 hlam hlh hM3 hVZ y hcut hgood
        exact abs_clusterQ_le (M := M) (lam := lam) blk Dn Dz Df y hW hΨ hs₁ hψ
      · push Not at hgood
        obtain ⟨i₀, hi₀⟩ := hgood
        have : Q₁ y = 0 := clusterQ_eq_zero_of (i₀ := i₀) blk Dn Dz Df y (by
          unfold dipoleWeightZ; rw [ite_eq_right hi₀, mul_zero])
        rw [this, abs_zero]; exact hBq0
    show |Q₁ y * H y| ≤ Bq * Bp ∧ |Q₀ y * H y| ≤ Bq * Bp
    rw [abs_mul (Q₁ y) (H y), abs_mul (Q₀ y) (H y), abs_of_nonneg hH0]
    exact ⟨mul_le_mul hb₁ hH hH0 hBq0, mul_le_mul hb₀ hH hH0 hBq0⟩
  · have : H y = 0 := by simp only [H, h0, mul_zero]
    show |Q₁ y * H y| ≤ Bq * Bp ∧ |Q₀ y * H y| ≤ Bq * Bp
    rw [this, mul_zero, mul_zero, abs_zero]
    exact ⟨mul_nonneg hBq0 hBp0, mul_nonneg hBq0 hBp0⟩

open scoped Classical in
/-- **The splitting along `𝒟`** (the domain split before Step 1 of the proof of Lemma A.7, giving
(A.51)): the integrand of the model `Z` vanishes off
`𝒟 = {d_e ≤ 17 h}`, so the difference of the cluster integrals is the integral on `𝒟` of the
difference minus the integral off `𝒟` of the integrand of `(v, 1)`. -/
theorem plus_split (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam) (hM1 : 1 ≤ M)
    {N p₀ : ℕ} {ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hlh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM3 : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hVZ : badPointsOn p₀ β lam M ε₀ V Z = V) (blk : ι → β') (Dn Dz Df : Finset (Sym2 ι)) :
    (∫ y in boxConfig ι N, clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df y *
        ((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y)) -
      (∫ y in boxConfig ι N, clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df y *
        ((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y)) =
    (∫ y in boxConfig ι N,
        (clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z) (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam
            blk Dn Dz Df y -
          clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df y) *
        (((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y) *
          shortInd (17 * (ε₀ * truncationScale p₀ β lam)) Df y)) -
      ∫ y in boxConfig ι N, clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df y *
        (((∏ i, pairDensity χ β lam (y i)) * cutInd (ε₀ * truncationScale p₀ β lam) y) *
          (1 - shortInd (17 * (ε₀ * truncationScale p₀ β lam)) Df y)) := by
  set h := ε₀ * truncationScale p₀ β lam
  set Q₁ : (ι → ℂ × ℂ) → ℝ := clusterQ β (interactionGoodZ χ p₀ β lam ε₀ V Z)
    (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam blk Dn Dz Df
  set Q₀ : (ι → ℂ × ℂ) → ℝ :=
    clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
  set H : (ι → ℂ × ℂ) → ℝ := fun y => (∏ i, pairDensity χ β lam (y i)) * cutInd h y
  set Sh : (ι → ℂ × ℂ) → ℝ := shortInd (17 * h) Df
  obtain ⟨B, hQH⟩ := plus_QH_bound (L := L) hχ hβ0 hlam hlh hM3 hVZ blk Dn Dz Df
  have hQ₁m : Measurable Q₁ := measurable_clusterQ
    (measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam)
    (measurable_dipoleWeightZ p₀ β lam M ε₀ L V Z) blk Dn Dz Df
  have hQ₀m : Measurable Q₀ := measurable_clusterQ (measurable_dipoleInteraction hχ hlam)
    measurable_const blk Dn Dz Df
  have hHm : Measurable H := (Finset.measurable_prod _ fun i _ =>
    (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)).mul (measurable_cutInd h)
  have hShm : Measurable Sh := measurable_shortInd (17 * h) Df
  have hSh0 : ∀ y, 0 ≤ Sh y := shortInd_nonneg (17 * h) Df
  have hSh1 : ∀ y, Sh y ≤ 1 := shortInd_le_one (17 * h) Df
  set F₁ : (ι → ℂ × ℂ) → ℝ := fun y => (Q₁ y - Q₀ y) * (H y * Sh y)
  set F₂ : (ι → ℂ × ℂ) → ℝ := fun y => Q₀ y * (H y * (1 - Sh y))
  have hsplit : ∀ y ∈ boxConfig ι N, Q₁ y * H y - Q₀ y * H y = F₁ y - F₂ y := by
    intro y hy
    have hbox : ∀ i, y i ∈ box N ×ˢ box N := fun i => hy i (Set.mem_univ i)
    have hvan : Q₁ y * H y * (1 - Sh y) = 0 := by
      rcases cutInd_eq_one_or h y with ⟨-, hcut⟩ | h0
      · rcases shortInd_eq_one_or (17 * h) Df y with ⟨h1, -⟩ | ⟨-, e₁, he₁, hlong⟩
        · simp only [Sh, h1, sub_self, mul_zero]
        · have hQ : Q₁ y = 0 := by
            by_cases hgood : ∀ i, IsGoodZ p₀ β lam M ε₀ V Z (y i)
            · obtain ⟨-, -, -, -, hvan0⟩ := plus_far_facts (M := M) hχ hlam hlh hM3 hVZ y hbox
                hcut hgood hlam (fun i => lam_le_goodRadiusZ _)
              simp only [Q₁, clusterQ]
              refine mul_eq_zero_of_right _ (prod_eq_zero he₁ ?_)
              induction e₁ using Sym2.ind with
              | h i j =>
                simp only [farBondW, symmLift_mk, farBondWij]
                split_ifs with hl
                · rfl
                · have hlong' : 17 * h < dipoleDist (y i) (y j) := hlong
                  rw [sOrd_of_not_linked hM1 _ y hl]
                  unfold wOrd
                  split_ifs
                  · rw [hvan0 i j hl hlong', mul_zero, Real.exp_zero, sub_self]
                  · rw [hvan0 j i (fun h' => hl (Limits.multipoleLinked_comm.1 h'))
                      (by rw [dipoleDist_comm]; exact hlong'), mul_zero, Real.exp_zero, sub_self]
            · push Not at hgood
              obtain ⟨i₀, hi₀⟩ := hgood
              exact clusterQ_eq_zero_of (i₀ := i₀) blk Dn Dz Df y (by
                unfold dipoleWeightZ; rw [ite_eq_right hi₀, mul_zero])
          rw [hQ, zero_mul, zero_mul]
      · simp only [H, h0, mul_zero, zero_mul]
    simp only [F₁, F₂]
    linear_combination hvan
  have hF₁m : Measurable F₁ := (hQ₁m.sub hQ₀m).mul (hHm.mul hShm)
  have hF₂m : Measurable F₂ := hQ₀m.mul (hHm.mul (measurable_const.sub hShm))
  have hF₁b : ∀ y, |F₁ y| ≤ 2 * B := by
    intro y
    have h1 := hQH y
    simp only [F₁]
    rw [show (Q₁ y - Q₀ y) * (H y * Sh y) = (Q₁ y * H y - Q₀ y * H y) * Sh y by ring, abs_mul,
      abs_of_nonneg (hSh0 y)]
    calc |Q₁ y * H y - Q₀ y * H y| * Sh y ≤ (|Q₁ y * H y| + |Q₀ y * H y|) * 1 :=
          mul_le_mul (abs_sub _ _) (hSh1 y) (hSh0 y) (by positivity)
      _ ≤ 2 * B := by linarith [h1.1, h1.2]
  have hF₂b : ∀ y, |F₂ y| ≤ B := by
    intro y
    have h1 := (hQH y).2
    simp only [F₂]
    rw [show Q₀ y * (H y * (1 - Sh y)) = Q₀ y * H y * (1 - Sh y) by ring, abs_mul,
      abs_of_nonneg (by linarith [hSh1 y] : (0 : ℝ) ≤ 1 - Sh y)]
    calc |Q₀ y * H y| * (1 - Sh y) ≤ B * 1 :=
          mul_le_mul h1 (by linarith [hSh0 y]) (by linarith [hSh1 y]) ((abs_nonneg _).trans h1)
      _ = B := mul_one _
  have hint₁ := integrableOn_boxConfig_of_bounded (F := fun y => F₁ y) hF₁m hF₁b N
  have hint₂ := integrableOn_boxConfig_of_bounded (F := fun y => F₂ y) hF₂m hF₂b N
  have hintQ₁ := integrableOn_boxConfig_of_bounded (F := fun y => Q₁ y * H y) (hQ₁m.mul hHm)
    (fun y => (hQH y).1) N
  have hintQ₀ := integrableOn_boxConfig_of_bounded (F := fun y => Q₀ y * H y) (hQ₀m.mul hHm)
    (fun y => (hQH y).2) N
  rw [← integral_sub hintQ₁ hintQ₀, ← integral_sub hint₁ hint₂]
  exact setIntegral_congr_fun (measurableSet_boxConfig N) hsplit

end Parts

end ExpansionK

end MultipoleBKT

end
