/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.ScreenedSupport
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.OmittedSupport

/-!
# Lemma A.7 for the screened model

See Lemma A.7. The estimate is also stated in the form used in Section 4. Shared lower infrastructure is in `RouteAssembly.MinusInfrastructure`.

Part I uses the original five-subset expansion and the written A–E bounds.
Part II uses the original omitted baseline and its quadratic long-edge bound.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open Hierarchical Multipole Parity Limits SmallIntegral Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Lemma A.7 for the model `(ṽ, τ̃)` -/

open scoped Classical in
/-- **Lemma A.7, eq. (A.49)** for `(w, τ) = (ṽ, τ̃)`,
`V_bad = ∅` and the damping `e^{-L r²/(ε₀ R̄)²}`: for `β > 2`, `k ≤ p*(β)`, `M ≥ 1`, `L` and
`ε₀ > 0` there are `C > 0` and `λ₀ > 0` such that for `0 < λ ≤ λ₀`, every `N`, every subpartition
`X ≠ ∅` with `|V_X| = k`, all `Xₗ ⊆ X`, `Eₗ ∈ 𝖤^{Xₗ}` and `F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}`:
`|I^-_{cl,ε₀} - I^0_{cl,ε₀}| ≤ C N λ^{(2-β)k} R̄^{-2}`. -/
theorem lemma_A8_minus (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) {k : ℕ}
    (hk : (k : ℕ∞) ≤ pStar β) (hM : 1 ≤ M) (L : ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      ∀ (N : ℕ) (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
        (X.biUnion id).card = k →
        ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
          ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            |ExpansionErrors.minusClusterIntegral χ N p₀ β lam M ε₀ L X Xs Es F -
                ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F| ≤
              C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  have hβ0 : (0 : ℝ) ≤ β := by linarith
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · refine ⟨1, one_pos, 1, one_pos, fun lam _ _ N X hX hXne hV => ?_⟩
    exfalso
    obtain ⟨S, hS⟩ := hXne
    obtain ⟨x, hx⟩ := hX.1 S hS
    have : x ∈ X.biUnion id := mem_biUnion.2 ⟨S, hS, hx⟩
    rw [Finset.card_eq_zero.1 hV] at this
    exact Finset.notMem_empty x this
  obtain ⟨A,hA,hAint⟩ := RouteAssembly.internal_screened_support_integral (β := β) (L := L)
    hχ hβ hM p₀ k hk1 ε₀ hε₀
  obtain ⟨Co, hCo, ho⟩ := RouteOmitted.screened_omitted_integral hχ hβ hM p₀ k hk1 hε₀
  set C₀ := (A + Co) * ε₀^(-2 : ℝ)
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨C₀ + 1, by linarith, min 1 ε₀, lt_min one_pos hε₀,
    fun lam hlam hlam₀ N X hX hXne hV n Xs hXs Es hEs F hF => ?_⟩
  have hlam1 : lam ≤ 1 := hlam₀.trans (min_le_left _ _)
  have hR1 := one_le_truncationScale (p₀ := p₀) hβ hlam hlam1
  set R := truncationScale p₀ β lam
  set h := ε₀ * R
  have hlh : lam ≤ h := (hlam₀.trans (min_le_right _ _)).trans (le_mul_of_one_le_right hε₀.le hR1)
  have hh0 : 0 < h := hlam.trans_le hlh
  -- the data on the labels
  set V := X.biUnion id
  have hEs' : ∀ l, Es l ∈ relEdgeSets (Xs l) := Fintype.mem_piFinset.1 hEs
  have hGX : ∀ Y ∈ Finset.univ.image Xs, Y ⊆ X := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
    exact hXs l
  have hEI : univ.biUnion Es ⊆ univ.biUnion fun l => interPairs (Xs l) := by
    intro p hp
    obtain ⟨l, -, hpl⟩ := mem_biUnion.1 hp
    exact mem_biUnion.2 ⟨l, mem_univ _, (mem_relEdgeSets.1 (hEs' l)).1 hpl⟩
  have hIX : (univ.biUnion fun l => interPairs (Xs l)) ⊆ interPairs X := by
    intro p hp
    obtain ⟨l, -, hpl⟩ := mem_biUnion.1 hp
    exact interPairs_subset_of_subset hX (hXs l) hpl
  have hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn V :=
    hIX.trans interPairs_subset_pairsOn
  have hFV : F ⊆ pairsOn V := by
    have := (mem_relEdgeSets₀.1 hF).1.trans interPairs_subset_pairsOn
    rwa [biUnion_coarsen hGX] at this
  have hcardV : Fintype.card V = k := by rw [Fintype.card_coe, hV]
  have : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcardV]
    exact hk1
  set blk := Limits.blockOf X
  set Dn := symOf V F
  set Dz := symOf V ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es)
  set Df := symOf V (univ.biUnion Es)
  set w₁ := upperBoundInteraction χ lam ε₀ R
  set ψ₁ := gaussianWeight p₀ β lam ε₀ L
  set Q₁ : (V → ℂ × ℂ) → ℝ := clusterQ β w₁ ψ₁ M lam blk Dn Dz Df
  set Q₀ : (V → ℂ × ℂ) → ℝ := clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df
  set H : (V → ℂ × ℂ) → ℝ := fun y => (∏ i, pairDensity χ β lam (y i)) * cutInd h y
  set Sh : (V → ℂ × ℂ) → ℝ := shortInd (17 * h) Df
  -- the integrals on the labels
  have hI1 : ExpansionErrors.minusClusterIntegral χ N p₀ β lam M ε₀ L X Xs Es F =
      ∫ y in boxConfig V N, Q₁ y * H y := by
    unfold ExpansionErrors.minusClusterIntegral ExpansionErrors.clusterIntegral
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [integrand_eq_clusterQ hX Xs Es F hEI hI hFV y, prod_cutoffWeight]
  have hI0 : ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F =
      ∫ y in boxConfig V N, Q₀ y * H y := by
    unfold ExpansionErrors.zeroClusterIntegral ExpansionErrors.clusterIntegral
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [integrand_eq_clusterQ hX Xs Es F hEI hI hFV y, prod_cutoffWeight]
  -- measurability and crude bounds
  have hw₁m : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w₁ q.1 q.2 :=
    measurable_screenedInteraction hχ hlam _
  have hw₀m : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => dipoleInteraction χ lam q.1 q.2 :=
    measurable_dipoleInteraction hχ hlam
  have hQ₁m : Measurable Q₁ := measurable_clusterQ hw₁m (measurable_gaussianWeight p₀ β lam ε₀ L)
    blk Dn Dz Df
  have hQ₀m : Measurable Q₀ := measurable_clusterQ hw₀m measurable_const blk Dn Dz Df
  have hHm : Measurable H := (Finset.measurable_prod _ fun i _ =>
    (measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)).mul (measurable_cutInd h)
  have hShm : Measurable Sh := measurable_shortInd (17 * h) Df
  set W := Wm hχ β
  have hW : 1 ≤ W := one_le_Wm hχ hβ0
  set Ψ := Real.exp |L|
  have hΨ : 1 ≤ Ψ := Real.one_le_exp (abs_nonneg L)
  set Bq := (W ^ (k * k) * Ψ ^ k) ^ Fintype.card X * (W + 1) ^ Df.card
  set Bp := (densConst hχ hβ0 * lam ^ (-β)) ^ k
  have hBq0 : 0 ≤ Bq := by
    have : 0 ≤ W := by linarith
    have : 0 ≤ Ψ := by linarith
    positivity
  have hBp0 : 0 ≤ Bp := by
    have := densConst_pos hχ hβ0
    have := Real.rpow_nonneg hlam.le (-β)
    positivity
  have hQH : ∀ (y : V → ℂ × ℂ), |Q₁ y * H y| ≤ Bq * Bp ∧ |Q₀ y * H y| ≤ Bq * Bp := by
    intro y
    have hH0 : 0 ≤ H y := mul_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le)
      (cutInd_nonneg h y)
    rcases cutInd_eq_one_or h y with ⟨h1, hcut⟩ | h0
    · have hpd := prod_pairDensity_le hχ hβ0 hlam y
      rw [hcardV] at hpd
      have hH : H y ≤ Bp := by simp only [H, h1, mul_one]; exact hpd
      obtain ⟨hs₁, hs₀, -⟩ := minus_stable_facts hχ hβ0 hlam hlh y hcut
      have hψ : ∀ i, 0 ≤ ψ₁ (y i) ∧ ψ₁ (y i) ≤ Ψ := fun i =>
        ⟨(gaussian_facts p₀ β lam ε₀ L hh0 (y i) (hcut i)).1,
          (gaussian_facts p₀ β lam ε₀ L hh0 (y i) (hcut i)).2.1⟩
      have hb₁ := abs_clusterQ_le (M := M) (lam := lam) blk Dn Dz Df y hW hΨ hs₁ hψ
      have hb₀ := abs_clusterQ_le (M := M) (lam := lam) (ψ := fun _ => 1) blk Dn Dz Df y hW hΨ hs₀
        (fun _ => ⟨zero_le_one, hΨ⟩)
      rw [hcardV] at hb₁ hb₀
      rw [abs_mul (Q₁ y) (H y), abs_mul (Q₀ y) (H y), abs_of_nonneg hH0]
      exact ⟨mul_le_mul hb₁ hH hH0 hBq0, mul_le_mul hb₀ hH hH0 hBq0⟩
    · have : H y = 0 := by simp only [H, h0, mul_zero]
      rw [this, mul_zero, mul_zero, abs_zero]
      exact ⟨mul_nonneg hBq0 hBp0, mul_nonneg hBq0 hBp0⟩
  -- the splitting along `𝒟`
  set F₁ : (V → ℂ × ℂ) → ℝ := fun y => (Q₁ y - Q₀ y) * (H y * Sh y)
  set F₂ : (V → ℂ × ℂ) → ℝ := fun y => Q₀ y * (H y * (1 - Sh y))
  have hsplit : ∀ y, Q₁ y * H y - Q₀ y * H y = F₁ y - F₂ y := by
    intro y
    have hvan : Q₁ y * H y * (1 - Sh y) = 0 := by
      rcases cutInd_eq_one_or h y with ⟨-, hcut⟩ | h0
      · rcases shortInd_eq_one_or (17 * h) Df y with ⟨h1, -⟩ | ⟨-, e₁, he₁, hlong⟩
        · simp only [Sh, h1, sub_self, mul_zero]
        · have hQ : Q₁ y = 0 := by
            simp only [Q₁, clusterQ]
            refine mul_eq_zero_of_right _ (prod_eq_zero he₁ ?_)
            induction e₁ using Sym2.ind with
            | h i j => exact farBondW_upper_eq_zero hχ hlam hM hlh y hcut hlong
          rw [hQ, zero_mul, zero_mul]
      · simp only [H, h0, mul_zero, zero_mul]
    simp only [F₁, F₂]
    linear_combination hvan
  have hSh0 : ∀ y, 0 ≤ Sh y := shortInd_nonneg (17 * h) Df
  have hSh1 : ∀ y, Sh y ≤ 1 := shortInd_le_one (17 * h) Df
  have hF₁m : Measurable F₁ := (hQ₁m.sub hQ₀m).mul (hHm.mul hShm)
  have hF₂m : Measurable F₂ := hQ₀m.mul (hHm.mul (measurable_const.sub hShm))
  have hF₁b : ∀ y, |F₁ y| ≤ 2 * (Bq * Bp) := by
    intro y
    have h1 := hQH y
    have hH0 : 0 ≤ H y := mul_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le)
      (cutInd_nonneg h y)
    simp only [F₁]
    rw [show (Q₁ y - Q₀ y) * (H y * Sh y) = (Q₁ y * H y - Q₀ y * H y) * Sh y by ring, abs_mul,
      abs_of_nonneg (hSh0 y)]
    calc |Q₁ y * H y - Q₀ y * H y| * Sh y ≤ (|Q₁ y * H y| + |Q₀ y * H y|) * 1 :=
          mul_le_mul (abs_sub _ _) (hSh1 y) (hSh0 y) (by positivity)
      _ ≤ 2 * (Bq * Bp) := by linarith [h1.1, h1.2]
  have hF₂b : ∀ y, |F₂ y| ≤ Bq * Bp := by
    intro y
    have h1 := (hQH y).2
    simp only [F₂]
    rw [show Q₀ y * (H y * (1 - Sh y)) = Q₀ y * H y * (1 - Sh y) by ring, abs_mul,
      abs_of_nonneg (by linarith [hSh1 y] : (0 : ℝ) ≤ 1 - Sh y)]
    calc |Q₀ y * H y| * (1 - Sh y) ≤ (Bq * Bp) * 1 :=
          mul_le_mul h1 (by linarith [hSh0 y]) (by linarith [hSh1 y]) (by positivity)
      _ = Bq * Bp := mul_one _
  have hint₁ := integrableOn_boxConfig_of_bounded (F := fun y => F₁ y) hF₁m hF₁b N
  have hint₂ := integrableOn_boxConfig_of_bounded (F := fun y => F₂ y) hF₂m hF₂b N
  have hintQ₁ := integrableOn_boxConfig_of_bounded (F := fun y => Q₁ y * H y) (hQ₁m.mul hHm)
    (fun y => (hQH y).1) N
  have hintQ₀ := integrableOn_boxConfig_of_bounded (F := fun y => Q₀ y * H y) (hQ₀m.mul hHm)
    (fun y => (hQH y).2) N
  have hdiff : ExpansionErrors.minusClusterIntegral χ N p₀ β lam M ε₀ L X Xs Es F -
      ExpansionErrors.zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F =
      (∫ y in boxConfig V N, F₁ y) - ∫ y in boxConfig V N, F₂ y := by
    rw [hI1, hI0, ← integral_sub hintQ₁ hintQ₀, ← integral_sub hint₁ hint₂]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  -- Part I: on `𝒟`
  have hpartI : |∫ y in boxConfig V N, F₁ y| ≤
      A*ε₀^(-2 : ℝ)*N*lam^((2-β)*k)*R^(-2 : ℝ) := by
    have hh := hAint lam hlam (hlam₀.trans (min_le_right _ _)) hlam1 X hX hXne hV N
      F (univ.biUnion Es) (RouteCases.cluster_far_subset hX Xs Es hXs hEs')
      (RouteCases.source_cluster_graph hX Xs Es F hXs hEs' hF hXne) Dz
      (2*(Bq*Bp)) hF₁m hF₁b
    exact hh
  -- Part II: the original omitted baseline, with the quadratic long-edge gain.
  have hpartII : |∫ y in boxConfig V N, F₂ y| ≤
      Co*ε₀^(-2 : ℝ)*N*lam^((2-β)*k)*R^(-2 : ℝ) := by
    apply RouteAssembly.internal_abs_integral_omitted_le hχ hβ0 hlam blk Dn Dz Df h
    · positivity
    · simpa only [V, R, h, blk, Dn, Dz, Df, hV] using ho X hX hXne hV lam hlam
        (hlam₀.trans (min_le_right _ _)) hlam1 Xs Es F hXs hEs' hF N
  -- Step 5: add the on-domain and omitted-domain estimates.
  have hT : 0 ≤ lam ^ ((2 - β) * k) * R ^ (-(2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg (truncationScale_pos hlam).le _)
  rw [hdiff]
  calc
    |(∫ y in boxConfig V N, F₁ y) - ∫ y in boxConfig V N, F₂ y|
      ≤ |∫ y in boxConfig V N, F₁ y| + |∫ y in boxConfig V N, F₂ y| := abs_sub _ _
    _ ≤ A*ε₀^(-2 : ℝ)*N*lam^((2-β)*k)*R^(-2 : ℝ) +
        Co*ε₀^(-2 : ℝ)*N*lam^((2-β)*k)*R^(-2 : ℝ) :=
      add_le_add hpartI hpartII
    _ = C₀*N*(lam^((2-β)*k)*R^(-2 : ℝ)) := by dsimp only [C₀]; ring
    _ ≤ (C₀+1)*N*(lam^((2-β)*k)*R^(-2 : ℝ)) := by gcongr; linarith

/-- **Lemma A.7, eq. (A.49)** in the form `MultipoleBKT.ExpansionErrors.LemmaA8MinusStatement`
used by Proposition 4.24 (for `M ≥ 1`). -/
theorem lemmaA8Minus_holds (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (L : ℝ) (p₀ : ℕ)
    {k : ℕ} (hk : (k : ℕ∞) ≤ pStar β) : ExpansionErrors.LemmaA8MinusStatement χ β M L p₀ k := by
  intro ε₀ hε₀ _
  obtain ⟨C, hC, lam₀, hlam₀, hA⟩ := lemma_A8_minus hχ hβ p₀ hk hM L hε₀
  refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ⟨0, fun N _ X hX _ hX2 hV n Xs hXs _ Es hEs F
    hF => ?_⟩⟩
  have hXne : X.Nonempty := Finset.card_pos.1 (by omega)
  exact hA lam hlam hlt.le N X hX hXne hV n Xs hXs Es hEs F hF

end ExpansionK

end MultipoleBKT

end
