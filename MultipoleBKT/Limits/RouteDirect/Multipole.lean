/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.IntegralBounds
public import MultipoleBKT.Limits.ProfileIndependence

/-!
# The direct multipole limits through the full logarithmic integrands

See Lemma 4.26 of the paper. Apply translation averaging to the full original block
average. Chain positivity makes each denominator nonzero. The profile
parameterization uses label exchangeability after the integrals converge.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Set Finset SimpleGraph Filter Topology
open scoped ENNReal

variable {χ : ℂ → ℝ} {β lam M : ℝ} {X : Finset (Finset ℕ)}

open scoped Classical in
/-- The literal coefficient in (4.51), with every translation
coordinate fixed and with the full original block averages. -/
noncomputable def relativeMultipoleCoefficient (χ : ℂ → ℝ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) (root : X.biUnion id) (roots : ∀ S : X, S.val) : ℝ :=
  (∑ E ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
      (∀ i j : X.biUnion id, E.Adj i j →
        ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
      E.edgeSet.Nonempty ∧
      (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
        ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected),
    ∫ p : RelativeCoordinates root, GdoublePrime χ β lam M (blockOf X) E root p) /
    ∏ S : X, ∫ p : RelativeCoordinates (roots S), Gsingle χ β lam M (roots S) p

open scoped Classical in
/-- Identification of both the numerator and denominator with the displayed
fixed-origin integrals. -/
theorem multipoleIntegralCoefficient_eq_relative (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hX : IsSubpartition X)
    (hk : ((X.biUnion id).card : ℕ∞) ≤ pStar β) (root : X.biUnion id)
    (roots : ∀ S : X, S.val) :
    multipoleIntegralCoefficient χ β lam M X root roots =
      relativeMultipoleCoefficient χ β lam M X root roots := by
  unfold multipoleIntegralCoefficient relativeMultipoleCoefficient
  apply congrArg₂ (fun a b : ℝ => a / b)
  · apply sum_congr
    · ext E
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro E hE
    obtain ⟨hinter, _, hconn⟩ := (Finset.mem_filter.mp hE).2
    exact integral_symBox_eq_GdoublePrime hχ hβ hlam hM
      (by simpa only [Fintype.card_coe] using hk) (blockOf X) (blockOf_surjective hX) E
      (adj_blockOf_ne hX hinter) (reachable_blockOf hX hinter hconn) root
  · apply prod_congr rfl
    intro S _
    have hkS : (Fintype.card (S : Finset ℕ) : ℕ∞) ≤ pStar β := by
      rw [Fintype.card_coe]
      have hcard : ((S : Finset ℕ).card : ℕ∞) ≤ ((X.biUnion id).card : ℕ∞) := by
        exact_mod_cast Finset.card_le_card (subset_biUnion_of_mem id S.property)
      exact hcard.trans hk
    convert integral_multipoleBox_eq_Gsingle hχ hβ hlam (by linarith : 0 ≤ M) hkS (roots S) using 1
    congr 3
    congr 1
    exact Subsingleton.elim _ _

open scoped Classical in
/-- The direct limit is the displayed coefficient of the full `G''` integrals. -/
theorem tendsto_multipoleActivity_relative (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hX : IsSubpartition X)
    (hk : ((X.biUnion id).card : ℕ∞) ≤ pStar β) (root : X.biUnion id)
    (roots : ∀ S : X, S.val) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X)
      atTop (𝓝 (relativeMultipoleCoefficient χ β lam M X root roots)) := by
  rw [← multipoleIntegralCoefficient_eq_relative hχ hβ hlam hM hX hk root roots]
  exact tendsto_multipoleActivity_integral hχ hβ hlam hM hX hk root roots

open scoped Classical in
/-- **Lemma 4.26, equation (4.54)**: existence follows from the explicit
integral coefficient, including the zero activity for at most one part. -/
theorem exists_tendsto_multipoleActivity (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 1 ≤ M) (hX : IsSubpartition X) (hk : ((X.biUnion id).card : ℕ∞) ≤ pStar β) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ ((X.card : ℤ) - 1) *
      multipoleActivity χ N β lam M X) atTop (𝓝 L) := by
  by_cases hX1 : X.card ≤ 1
  · refine ⟨0, tendsto_const_nhds.congr fun N => ?_⟩
    rw [multipoleActivity_eq_zero_of_card_le_one χ N β lam M hX1, mul_zero]
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨S, hS⟩ := hXne
  obtain ⟨i, hi⟩ := hX.1 S hS
  let root : X.biUnion id := ⟨i, mem_biUnion.mpr ⟨S, hS, hi⟩⟩
  let roots (S : X) : S.val := ⟨(hX.1 S S.property).choose, (hX.1 S S.property).choose_spec⟩
  exact ⟨relativeMultipoleCoefficient χ β lam M X root roots,
    tendsto_multipoleActivity_relative hχ hβ hlam hM hX hk root roots⟩

open scoped Classical in
/-- The multipole coefficients depend only on the block profile. -/
theorem exists_tendsto_multipoleActivity_blockProfile (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 1 ≤ M) :
    ∃ kmult : ℝ → (ℕ →₀ ℕ) → ℝ, ∀ lam : ℝ, 0 < lam →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
          (𝓝 (kmult lam (blockProfile X))) := by
  have key : ∀ (lam : ℝ) (P : ℕ →₀ ℕ), ∃ L : ℝ, 0 < lam →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
        blockProfile X = P →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop (𝓝 L) := by
    intro lam P
    by_cases h : 0 < lam ∧ ∃ X₀ : Finset (Finset ℕ), IsSubpartition X₀ ∧
        ((∑ S ∈ X₀, S.card : ℕ) : ℕ∞) ≤ pStar β ∧ blockProfile X₀ = P
    · obtain ⟨hlam, X₀, hX₀, hk₀, hP₀⟩ := h
      obtain ⟨L, hL⟩ := exists_tendsto_multipoleActivity hχ hβ hlam hM hX₀
        (by rwa [card_biUnion_eq_sum hX₀])
      refine ⟨L, fun _ X hX _ hP => ?_⟩
      have hprof : blockProfile X₀ = blockProfile X := hP₀.trans hP.symm
      have hc := card_eq_of_blockProfile_eq hprof
      refine hL.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [hc, multipoleActivity_eq_of_blockProfile_eq hχ hlam hN hX₀ hX hprof]
    · exact ⟨0, fun hlam X hX hk hP => absurd ⟨hlam, X, hX, hk, hP⟩ h⟩
  choose kmult hkmult using key
  exact ⟨kmult, fun lam hlam X hX hk => hkmult lam _ hlam X hX hk rfl⟩


end MultipoleBKT.Limits.RouteDirect

end
