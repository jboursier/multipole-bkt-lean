/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.ClusterIntegral
public import MultipoleBKT.LowerBound.RouteBounded.IntegralBound
public import MultipoleBKT.LowerBound.RouteBounded.Density

/-!
# The fixed numerator estimate (4.80)

(4.80),
proof of Proposition 4.24. Average each fixed term over block reversals, retain
its odd components and its separate even tree, and integrate using the
hatted infinite-cutoff estimate. No sum over expansion data is taken.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionErrors

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits SmallIntegral
open LowerBound.RouteBounded UpperBound.BoundedUpper
open scoped Classical

/-- Internal adapter for the reversal average of one fixed numerator.
Only the parity subsets of its own edge set are summed here. -/
theorem internal_fixed_numerator_le
    {ρ : Measure (ℂ × ℂ)} {β M lam : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K)
    (hρ : MeasurePreserving Prod.swap ρ ρ) (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (hM : 1 ≤ M)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {k N : ℕ}
    (hk : (X.biUnion id).card = k)
    (D : ℂ × ℂ → ℝ) (hDm : Measurable D) (hD0 : ∀ d, 0 ≤ D d)
    {Q : ℝ} (hQ : 0 < Q)
    (hπ : ∀ f : (X.biUnion id → ℂ × ℂ) → ℝ,
      ∫ y, f y ∂Measure.pi (fun _ : X.biUnion id => ρ) =
        Q⁻¹ ^ k * ∫ y in boxConfig (X.biUnion id) N, f y * ∏ i, D (y i))
    (hP : 0 < ∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l))
    {F : Finset (ℕ × ℕ)} (hF : F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)))
    {Ct : ℝ} (hCt : 0 ≤ Ct)
    (hterms : ∀ A : Finset (ℕ × ℕ), A ⊆ univ.biUnion Es → A ∈ relEulerianPairs X →
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        ((∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)) *
          |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F (extendConfig (X.biUnion id) y)| *
          ∏ i, D (y i))) ≤ ENNReal.ofReal Ct) :
    |clusterIntegral N β w ψ D M lam X Xs Es F| ≤ 2 ^ (k * k) * Ct := by
  let P := ∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S
  have hPpos : 0 < P := hP
  have hterm : ∀ A ∈ (univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X),
      |∫ y, eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F
        (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X| ≤
          P⁻¹ * (Q⁻¹ ^ k * Ct) := by
    intro A hA
    let t := eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F
    let bw := fun y : X.biUnion id → ℂ × ℂ =>
      ∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)
    have hbw0 (y) : 0 ≤ bw y := prod_nonneg fun S _ => blockWeightOf_nonneg M lam h.nonneg_ψ S _
    have htm : Measurable fun y : X.biUnion id → ℂ × ℂ => t (extendConfig (X.biUnion id) y) :=
      (measurable_eulerTerm h M lam Xs A (univ.biUnion Es \ A) F).comp (measurable_extendConfig _)
    have hbwm : Measurable bw := (Finset.measurable_prod _ fun S _ => h.measurable_blockWeightOf M lam S).comp
      (measurable_extendConfig _)
    have hm : Measurable fun y : X.biUnion id → ℂ × ℂ =>
        bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i) :=
      (hbwm.mul (continuous_abs.measurable.comp htm)).mul
        (Finset.measurable_prod _ fun i _ => hDm.comp (measurable_pi_apply i))
    have hn (y : X.biUnion id → ℂ × ℂ) :
        0 ≤ bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i) :=
      mul_nonneg (mul_nonneg (hbw0 y) (abs_nonneg _)) (prod_nonneg fun i _ => hD0 _)
    have hreal : (∫ y in boxConfig (X.biUnion id) N,
        bw y * |t (extendConfig (X.biUnion id) y)| * ∏ i, D (y i)) ≤ Ct := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hCt
        (hterms A (mem_powerset.1 (mem_filter.1 hA).1) (mem_filter.1 hA).2)
    apply (abs_integral_le_integral_abs).trans
    rw [integral_model_eq_finite h X, hπ]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hreal (by positivity)) (inv_nonneg.2 hP.le)
  have hcard : ((univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X)).card ≤ 2 ^ (k * k) := by
    apply (card_filter_le _ _).trans
    rw [card_powerset]
    apply Nat.pow_le_pow_right (by norm_num)
    have hs : univ.biUnion Es ⊆ pairsOn (X.biUnion id) := biUnion_subset.2 fun l _ =>
      (mem_relEdgeSets.1 (hEs l)).1.trans ((interPairs_subset_of_subset hX (hXs l)).trans
        interPairs_subset_pairsOn)
    exact (card_le_card hs).trans (by rw [← hk]; exact UpperBound.BoundedUpper.card_pairsOn_le _)
  have hpar := h.integral_clusterTerm_eq_sum_relEulerian (lam := lam) hρ hw₁ hw₂ hψ hwb hM hX hXs
    (fun l => (mem_relEdgeSets.1 (hEs l)).1) (mem_relEdgeSets₀.1 hF).1
  have hb : |∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
      ∂modelHierarchical ρ β w ψ M lam X| ≤ 2 ^ (k * k) * (P⁻¹ * (Q⁻¹ ^ k * Ct)) := by
    rw [hpar]
    apply (abs_sum_le_sum_abs _ _).trans
    apply (sum_le_sum hterm).trans
    rw [sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have heq : (∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
      ∂modelHierarchical ρ β w ψ M lam X) =
        P⁻¹ * (Q⁻¹ ^ k * clusterIntegral N β w ψ D M lam X Xs Es F) := by
    rw [integral_model_eq_finite h X, hπ]
    rfl
  rw [heq, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hP), abs_of_pos (pow_pos (inv_pos.2 hQ) _)] at hb
  have hcancel : 0 < P⁻¹ * Q⁻¹ ^ k := by positivity
  apply le_of_mul_le_mul_left (a := P⁻¹ * Q⁻¹ ^ k) _ hcancel
  convert hb using 1 <;> ring

/-- **(4.80)** for every valid fixed expansion datum. See the proof of Proposition 4.24. The bound precedes
summation over the expansion data, so it permits no cancellation among them.
The range is `M ≥ 1`, every `λ > 0`, and every `N ≥ 1`. -/
theorem bornI2 {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β M : ℝ} (hβ : 2 < β) (hM : 1 ≤ M)
    (k : ℕ) (hsize : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, 1 ≤ N →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card → (X.biUnion id).card = k →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l j, l ≠ j → Disjoint (Xs l) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
        |zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤
          C * N * (lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
  obtain ⟨CT, hCT, ht⟩ := exists_hatTreeIntegral_infinity_le hχ hβ hM k hsize
  obtain ⟨Cd, hCd0, hCd⟩ := dipoleBond_le hχ
  obtain ⟨Cw, hCw0, hCw⟩ := BoundedLowerEps.abs_dipoleInteraction_le_ahat hχ
  let Wb := Real.exp (β * Cd)
  let Cab := BoundedLowerEps.bondConst β Cw
  have hβ0 : 0 ≤ β := by linarith
  have hWb : 1 ≤ Wb := Real.one_le_exp (mul_nonneg hβ0 hCd0)
  have hCab : 1 ≤ Cab := BoundedLowerEps.one_le_bondConst hβ0 hCw0
  let A := Wb ^ (k * k) * Cab ^ (k * k) * (2 ^ (k * k * k) * CT)
  refine ⟨2 ^ (k * k) * A, by dsimp [A]; positivity, ?_⟩
  intro lam hlam N hN X hX h2 hk n Xs hXs _hdisj Es hEs F hF
  have h := modelHyp_infinity hχ hlam β hN
  have hg0 := gammaBeta_nonneg hlam 0 β k
  have hP : 0 < ∏ S ∈ X, modelPartitionFunction (dipoleMeasure χ N β lam) β
      (dipoleInteraction χ lam) (fun _ => 1) M lam S := by
    simp only [modelPartitionFunction_dipoleMeasure]
    exact prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β (by linarith) hN (hX.1 S hS)
  have hgamma : Appendix.gammaBeta 0 β lam k = lam ^ (2 * (k - 1)) := by
    have hxk : X.card ≤ k := hk ▸ card_le_card_biUnion hX
    have hk1 : 1 ≤ k := by omega
    unfold Appendix.gammaBeta
    have he : 2 * ((k : ℤ) - 1) = ((2 * (k - 1) : ℕ) : ℤ) := by omega
    rw [ite_eq_left hsize, he, zpow_natCast]
  have hb := internal_fixed_numerator_le h (measurePreserving_swap_dipoleMeasure hχ N β lam)
    (fun d e => Parity.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Parity.dipoleInteraction_swap_right d e hχ lam) (fun _ => rfl)
    (exists_abs_dipoleInteraction_le hχ hlam N) hM hX hk
    (pairDensity χ β lam) (measurable_pairDensity hχ hlam β) (fun d => (pairDensity_pos _ _ _ _).le)
    (natCast_mul_dipoleNormalization_pos hχ hlam β hN)
    (fun f => by simpa only [Fintype.card_coe, hk] using integral_pi_dipoleMeasure hχ hlam β hN f)
    hP hXs (Fintype.mem_piFinset.1 hEs) hF
    (show 0 ≤ Wb ^ (k * k) * 1 ^ k * Cab ^ (k * k) *
      (2 ^ (k * k * k) * (CT * N * (lam ^ ((2 - β) * k) * Appendix.gammaBeta 0 β lam k))) by positivity)
    (fun A hAE hA => grouped_integral_le hχ h hlam hM hX hk
      (pairDensity χ β lam) (measurable_pairDensity hχ hlam β) (fun d => (pairDensity_pos _ _ _ _).le)
      (fun y hy _ i => hy i (Set.mem_univ i)) hWb le_rfl hCab
      (fun d _ e _ => by unfold stableWeight; exact hCd β hβ0 lam hlam d e)
      (fun _ _ => le_rfl)
      (fun d _ e _ => BoundedLowerEps.abs_bonds_le hβ0 hM hCw0
        (fun hnl => hCw lam hlam M hM d e hnl)
        (fun hnl => BoundedLowerEps.ahat_le_one_of_not_linked hχ hlam hM hnl))
      hXs (Fintype.mem_piFinset.1 hEs) hF hAE hA (by positivity)
      (fun Ys hYs hdisj Ta hTa Tb hTb => ht X hX h2 hk Ys hYs hdisj Ta hTa Tb hTb 0 lam hlam N))
  rw [hgamma] at hb
  apply hb.trans_eq
  simp only [A, one_pow, mul_one]
  ring

end MultipoleBKT.ExpansionErrors

end
