/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Integral
public import MultipoleBKT.LowerBound.AbsoluteLower.RoutePosition.Logarithms

/-!
# The spatial estimate before summing any fixed groups or trees

The proof of Lemma 4.58, equation (A.67). The groups and both far-tree families remain parameters.
The output keeps the literal logarithm at each edge and the radius
quotient. The numerical factors in the regularized profiles are absorbed
into a constant to the power of the number of labels.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RoutePosition

open MeasureTheory Finset SimpleGraph Set Limits SmallIntegral Multipole SetPartition
open UpperBound.AbsoluteUpper (jLarge)
open scoped Classical ENNReal

/-- The radial integrand after position integration, with the paper logarithms. -/
noncomputable def sourceSpatialWeight {V : Type*} [Fintype V]
    (χ : ℂ → ℝ) (β lam h a : ℝ) (E : Finset (Sym2 V)) (u : V → ℂ) : ℝ :=
  radiusFactor lam u * (∏ i, sourceWeight χ β lam h a (u i)) *
    ∏ e ∈ E, Real.log (17 * h / edgeMin id (fun i => ‖u i‖) e)

/-- The radius cancellation (A.67) for fixed groups, fixed odd and even trees,
and a fixed near tree in every block. Apply radius allocation, which
uses `ordering_tree` on the coarse tree and then inside each original block. -/
theorem fixed_tree_radius_cancellation {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    [Nonempty (X.biUnion id)] {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (hXs : ∀ l, Xs l ⊆ X) (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ∈ relTreePairs (Xs l))
    (Tb : Finset (ℕ × ℕ)) (hTb : Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)))
    (c : X.biUnion id → ℂ × ℂ) (hat : Fin n → X)
    (hhat : ∀ l, hat l ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X),
        Peeling.blockRadius hX (fun i => Peeling.dipoleLength (c i)) S ≤
          Peeling.blockRadius hX (fun i => Peeling.dipoleLength (c i)) (hat l))
    (R : RouteJ.NearTreeFamily (Limits.blockOf X)) {lam : ℝ} (hlam : 0 < lam) :
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
      Peeling.blockRadius hX (fun i => Peeling.dipoleLength (c i)) S ^ 2) *
      (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset, RouteJ.minSq lam c e) *
      (∏ e ∈ RouteJ.nearForest (Limits.blockOf X) (fun S => (R S).val),
        RouteJ.minSq lam c e) ≤ radF lam c := by
  obtain ⟨i₀, hmax, halloc⟩ := RouteJ.source_radius_allocation hX Xs hXs hdisj Ta hTa Tb hTb
    (fun i => Peeling.dipoleLength (c i)) (fun _ => norm_nonneg _) hat hhat
    (fun S => (R S).val) (fun S => (R S).property) lam hlam
  change _ ≤ ∏ i ∈ univ.erase i₀, rhoD lam (c i) ^ 2 at halloc
  rw [← RouteJ.radialFactor_eq_erase hlam c i₀ hmax] at halloc
  have hRad : radF lam c = RouteJ.radialFactor lam c := by
    unfold radF RouteJ.radialFactor
    simp only [Real.rpow_two]
  rw [hRad]
  exact halloc

/-- Replace the regularized edge profiles by the literal logarithmic integrand.
This is an algebraic support comparison, prior to any radial integration. -/
theorem spatialWeight_le_source {V : Type*} [Fintype V] [DecidableEq V]
    {χ : ℂ → ℝ} {β lam h a : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h) (ha : 0 < a)
    (E : Finset (Sym2 V)) (hE : E.card ≤ Fintype.card V) (u : V → ℂ) :
    ENNReal.ofReal (radiusFactor lam u * ∏ i, dipoleWeight χ β lam h a (u i)) *
        ENNReal.ofReal (∏ e ∈ E, 8 * Real.pi * ell (17 * h)
          (edgeMin id (fun i => rho lam (u i)) e)) ≤
      ENNReal.ofReal (((17 : ℝ) ^ a *
        max 1 (8 * Real.pi * (1 + (Real.log 17)⁻¹))) ^ Fintype.card V) *
          ENNReal.ofReal (sourceSpatialWeight χ β lam h a E u) := by
  let K : ℝ := max 1 (8 * Real.pi * (1 + (Real.log 17)⁻¹))
  let L : Sym2 V → ℝ := fun e => Real.log (17 * h / edgeMin id (fun i => ‖u i‖) e)
  have hK : 1 ≤ K := le_max_left _ _
  have hprod : (∏ i, dipoleWeight χ β lam h a (u i)) =
      ((17 : ℝ) ^ a) ^ Fintype.card V * ∏ i, sourceWeight χ β lam h a (u i) := by
    simp_rw [dipoleWeight_eq_sourceWeight χ β lam hh a]
    rw [prod_mul_distrib, prod_const, card_univ]
  by_cases hu : ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h
  · have hL (e : Sym2 V) : 0 ≤ L e := by
      induction e using Sym2.ind with
      | h i j =>
        have hr := lt_min (hu i).1 (hu j).1
        have hrh : min ‖u i‖ ‖u j‖ ≤ h := (min_le_left _ _).trans (hu i).2
        apply Real.log_nonneg
        dsimp only [L, edgeMin_mk, id_eq]
        apply (one_le_div hr).mpr
        linarith [hr.trans_le hrh]
    have he (e : Sym2 V) : 8 * Real.pi * ell (17 * h)
        (edgeMin id (fun i => rho lam (u i)) e) ≤ K * L e := by
      induction e using Sym2.ind with
      | h i j =>
        have hr := lt_min (hu i).1 (hu j).1
        have hrh : min ‖u i‖ ‖u j‖ ≤ h := (min_le_left _ _).trans (hu i).2
        have hb := ell_le_source_log hr hrh
          (min_le_min (le_max_left ‖u i‖ lam) (le_max_left ‖u j‖ lam))
        exact (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 8 * Real.pi)).trans
          (by
            dsimp only [L, edgeMin_mk, id_eq]
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (hL s(i, j)))
    have hp : (∏ e ∈ E, 8 * Real.pi * ell (17 * h)
        (edgeMin id (fun i => rho lam (u i)) e)) ≤ K ^ Fintype.card V * ∏ e ∈ E, L e := by
      calc
        _ ≤ ∏ e ∈ E, K * L e := prod_le_prod₀
          (fun e _ => mul_nonneg (by positivity)
            (zero_le_one.trans (one_le_ell _ _))) (fun e _ => he e)
        _ = K ^ E.card * ∏ e ∈ E, L e := by rw [prod_mul_distrib, prod_const]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hE)
          (prod_nonneg fun e _ => hL e)
    have hrad := radiusFactor_nonneg hlam u
    have hD : 0 ≤ radiusFactor lam u * ∏ i, sourceWeight χ β lam h a (u i) :=
      mul_nonneg hrad (prod_nonneg fun i _ => sourceWeight_nonneg χ β lam hh a _)
    have hD17 : 0 ≤ radiusFactor lam u *
        (((17 : ℝ) ^ a) ^ Fintype.card V * ∏ i, sourceWeight χ β lam h a (u i)) :=
      mul_nonneg hrad (mul_nonneg (by positivity)
        (prod_nonneg fun i _ => sourceWeight_nonneg χ β lam hh a _))
    change _ ≤ ENNReal.ofReal (((17 : ℝ) ^ a * K) ^ Fintype.card V) * _
    rw [hprod, ← ENNReal.ofReal_mul hD17,
      ← ENNReal.ofReal_mul (pow_nonneg (mul_nonneg (by positivity) (zero_le_one.trans hK)) _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (radiusFactor lam u * (((17 : ℝ) ^ a) ^ Fintype.card V *
          ∏ i, sourceWeight χ β lam h a (u i))) *
          (K ^ Fintype.card V * ∏ e ∈ E, L e) := by
        exact mul_le_mul_of_nonneg_left hp hD17
      _ = _ := by unfold sourceSpatialWeight; rw [mul_pow]; ring
  · obtain ⟨i, hi⟩ := not_forall.mp hu
    have hz : sourceWeight χ β lam h a (u i) = 0 := by
      unfold sourceWeight
      by_cases hib : ‖u i‖ ≤ h
      · have hi0 : ‖u i‖ = 0 := le_antisymm (not_lt.mp (fun hp => hi ⟨hp, hib⟩)) (norm_nonneg _)
        rw [indicator_of_mem (show u i ∈ Metric.closedBall (0 : ℂ) h by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hib), hi0,
          div_zero, Real.zero_rpow ha.ne', mul_zero]
      · rw [indicator_of_notMem (show u i ∉ Metric.closedBall (0 : ℂ) h by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hib), mul_zero]
    have hp : (∏ i, sourceWeight χ β lam h a (u i)) = 0 := prod_eq_zero (mem_univ i) hz
    rw [hprod, hp, mul_zero, mul_zero, ENNReal.ofReal_zero, zero_mul]
    exact bot_le

/-- The fixed-group spatial integral in the paper, before either tree sum
or group sum. The radius quotient and one logarithm per odd or even edge are
visible in `sourceSpatialWeight`. See the proof of Lemma 4.58. -/
theorem fixed_groups_spatial_integral {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {p₀ : ℕ} {β lam M ε₀ C₀ : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M) (hC₀ : 0 < C₀)
    (hh : 0 ≤ ε₀ * truncationScale p₀ β lam) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (hXne : X.Nonempty) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p)
    (N : ℕ) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ∈ relTreePairs (Xs l))
    (Tb : Finset (ℕ × ℕ)) (hTb : Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs))) :
    jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb ≤
      (N : ℝ≥0∞) * ENNReal.ofReal
        ((2 ^ (p + 1) * max 1 (4 * Real.pi * M ^ 2) *
          ((17 : ℝ) ^ (C₀ / M) * max 1 (8 * Real.pi * (1 + (Real.log 17)⁻¹)))) ^
            (X.biUnion id).card) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal
          (sourceSpatialWeight χ β lam (ε₀ * truncationScale p₀ β lam) (C₀ / M)
            (univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Tb).edgeFinset) u) := by
  let E := univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
    (graphOf (X.biUnion id) Tb).edgeFinset
  have hF := flatHyp_of_relTree hX hXs hdisj hTa hTb
  obtain ⟨_, _, _, _, _, hc⟩ := flat_structure hX Xs hF.subset hF.disj Ta hF.inter hF.card
    Tb hF.inter_b hF.conn hF.count
  have hEV : E.card ≤ Fintype.card (X.biUnion id) := by
    have h1 := card_union_le
      (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
      (graphOf (X.biUnion id) Tb).edgeFinset
    have h2 := card_biUnion_le (s := univ)
      (t := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
    have h3 := Fintype.card_le_of_surjective _ (Limits.blockOf_surjective hX)
    dsimp only [E]
    omega
  have ha : 0 < C₀ / M := div_pos hC₀ (by linarith)
  refine (jLarge_fixed_groups_spatial_le hχ hlam hM hC₀ hh le_rfl hX hXne hXp N
    hXs hdisj hTa hTb).trans ?_
  let K : ℝ := (17 : ℝ) ^ (C₀ / M) * max 1 (8 * Real.pi * (1 + (Real.log 17)⁻¹))
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (zero_le_one.trans (le_max_left _ _))
  calc
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal
        ((2 ^ (p + 1) * max 1 (4 * Real.pi * M ^ 2)) ^ (X.biUnion id).card) *
        (ENNReal.ofReal (K ^ (X.biUnion id).card) * ∫⁻ u : X.biUnion id → ℂ,
          ENNReal.ofReal (sourceSpatialWeight χ β lam (ε₀ * truncationScale p₀ β lam)
            (C₀ / M) E u)) := by
      apply mul_le_mul' le_rfl
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro u
      simpa only [mul_assoc, Fintype.card_coe, K, E] using
        (spatialWeight_le_source (χ := χ) (β := β) hlam hh ha E hEV u)
    _ = _ := by
      rw [← mul_assoc, mul_assoc (N : ℝ≥0∞), ← ENNReal.ofReal_mul (by positivity), ← mul_pow]

end MultipoleBKT.AbsoluteLower.RoutePosition

end
