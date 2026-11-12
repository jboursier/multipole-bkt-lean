/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.CommonFactors
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SelectedProducts

/-!
# Uniform ordinary and selected correction controls

See (A.54),
(A.56), (A.61) and (A.36).
The coefficient is fixed before screening radii, lambda and frozen data.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Peeling SmallIntegral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The common actual mixed term, including all its invariant factors. -/
noncomputable def mixedIntegrand {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : ℂ → ℝ) (β lam M h : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ)
    (u v : ℂ × ℂ → ℝ) (blk : ι → κ) (Dn Dz Df O : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) (P : FiveSubsets (Sym2 ι) ι) : ℝ :=
  clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
    fiveTerm O (Df \ O) (intraEdges blk)
      (gammaW β w M lam c) (gammaW β (dipoleInteraction χ lam) M lam c)
      (fun e => alphaW β w M lam c e + linkIndE M lam c e)
      (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
      (intraRatio β w (dipoleInteraction χ lam) c) (u ∘ c) (v ∘ c) P *
        mixedDensity χ β lam h Df c

/-- Internal analytic input to the finite-product assembly. Concrete model
entry points prove every field, rather than asking a consumer for estimates. -/
structure InternalControls (K : ℝ) (r τ : ι → ℝ) (A B : Sym2 ι → ℝ)
    (a₁ a₀ b₁ b₀ q : Sym2 ι → ℝ) (u v : ι → ℝ) where
  coefficient : 1 ≤ K
  radius_nonneg : ∀ i, 0 ≤ r i
  screening_pos : ∀ i, 0 < τ i
  odd : ∀ e, |a₀ e| ≤ K * A e ∧ |a₁ e - a₀ e| ≤ K * A e
  even : ∀ e, |b₀ e| ≤ K * B e ∧ |b₁ e - b₀ e| ≤ K * B e
  intra : ∀ e, |q e - 1| ≤ K
  quadratic : ∀ i, |u i| ≤ K
  bad : ∀ i, |v i| ≤ K
  odd_error : ∀ i j, |a₁ s(i,j) - a₀ s(i,j)| ≤ K * (r i * r j / τ i ^ 2)
  even_error : ∀ i j, |b₁ s(i,j) - b₀ s(i,j)| ≤ K * (r i * r j / τ i ^ 2)
  intra_error : ∀ i j, |q s(i,j) - 1| ≤ K * (r i * r j / τ i ^ 2)
  quadratic_error : ∀ i, |u i| ≤ K * (r i ^ 2 / τ i ^ 2)

/-- Internal scalar selected-bond estimate. This is the termwise series bound
used in (A.56), with the even correction controlled at the same time. -/
theorem internal_selected_hyperbolic {a b β C D t : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (ha : |a| + |b| ≤ C) (hd : |a - b| ≤ D * t) :
    |Real.sinh (β * a) - Real.sinh (β * b)| ≤
      diffConst β C D * t ∧
    |Real.cosh (β * a) - Real.cosh (β * b)| ≤ diffConst β C D * t := by
  have hs : |β * a| + |β * b| ≤ β * C := by
    rw [abs_mul, abs_mul, abs_of_nonneg hβ, ← mul_add]
    exact mul_le_mul_of_nonneg_left ha hβ
  have hdelta : |β * a - β * b| ≤ β * D * t := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hβ]
    exact (mul_le_mul_of_nonneg_left hd hβ).trans_eq (by ring)
  have he := Real.exp_le_exp.2 hs
  have hp : 0 ≤ Real.exp (β * C) * β * D * t := by positivity
  constructor
  · calc _ ≤ Real.exp (|β * a| + |β * b|) * |β * a - β * b| := abs_sinh_sub_sinh_le _ _
         _ ≤ Real.exp (β * C) * (β * D * t) := mul_le_mul he hdelta (abs_nonneg _) (Real.exp_pos _).le
         _ ≤ _ := by unfold diffConst; nlinarith [mul_nonneg hp (mul_nonneg hβ hC)]
  · calc _ ≤ (|β * a| + |β * b|) * |β * a - β * b| * Real.exp (|β * a| + |β * b|) :=
           abs_cosh_sub_cosh_le _ _
         _ ≤ (β * C) * (β * D * t) * Real.exp (β * C) := by gcongr
         _ ≤ _ := by unfold diffConst; nlinarith

omit [Fintype ι] [DecidableEq ι] in
/-- Internal controls from the two interaction estimates. The parameter `D`
bounds the interaction error at the maximum of the endpoint screening radii.
The screening extension discharges the quarter-length condition. -/
theorem internal_controls_of_interactions {χ : ℂ → ℝ} {β L C D : ℝ}
    (hβ : 0 ≤ β) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {lam M : ℝ}, 0 < lam → 1 ≤ M →
      ∀ (w : ℂ × ℂ → ℂ × ℂ → ℝ) (τ : ι → ℝ) (c : ι → ℂ × ℂ) (v : ι → ℝ),
      (∀ i, 0 < τ i) → (∀ i, ‖(c i).1 - (c i).2‖ ≤ 4 * τ i) →
      (∀ i, |v i| ≤ 1) →
      (∀ i j, ¬ MultipoleLinked M lam (c i) (c j) →
        |w (c i) (c j)| ≤ C * ahat (c i) (c j) ∧
        |dipoleInteraction χ lam (c i) (c j)| ≤ C * ahat (c i) (c j)) →
      (∀ i j, |w (c i) (c j) - dipoleInteraction χ lam (c i) (c j)| ≤
        D * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τ i) (τ j) ^ 2) →
      InternalControls K (fun i => rhoD lam (c i)) τ
        (mixedOddWeight M lam c) (mixedEvenWeight M lam c)
        (gammaW β w M lam c) (gammaW β (dipoleInteraction χ lam) M lam c)
        (fun e => alphaW β w M lam c e + linkIndE M lam c e)
        (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
        (intraRatio β w (dipoleInteraction χ lam) c)
        (fun i => Real.exp (L * (‖(c i).1 - (c i).2‖ / τ i) ^ 2) - 1) v := by
  classical
  let Ka := partConst β C
  let Kd := diffConst β (2 * C) D
  let Kq := Real.exp (16 * β * D) * β * D
  let Ku := Real.exp (16 * |L|) * |L|
  let K := 1 + 2 * Ka + Kd + 16 * Kq + 16 * Ku
  have hKa : 0 ≤ Ka := zero_le_one.trans (one_le_partConst hβ hC)
  have hKd : 0 ≤ Kd := by dsimp [Kd, diffConst]; positivity
  have hKq : 0 ≤ Kq := by dsimp [Kq]; positivity
  have hKu : 0 ≤ Ku := by dsimp [Ku]; positivity
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hKaK : 2 * Ka ≤ K := by dsimp [K]; linarith
  have hKdK : Kd ≤ K := by dsimp [K]; linarith
  have hKqK : Kq ≤ K := by dsimp [K]; linarith
  have hKuK : Ku ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro lam M hlam hM w τ c v hτ hrτ hv hw herr
  let w₀ := dipoleInteraction χ lam
  have hr : ∀ i, 0 ≤ rhoD lam (c i) := fun i => (norm_nonneg _).trans (le_max_left _ _)
  have hn : ∀ i, ‖(c i).1 - (c i).2‖ ≤ rhoD lam (c i) := fun _ => le_max_left _ _
  have hdord : ∀ i j, |wOrd w c i j - wOrd w₀ c i j| ≤
      D * (‖(c i).1 - (c i).2‖ * ‖(c j).1 - (c j).2‖) / max (τ i) (τ j) ^ 2 := by
    intro i j
    unfold wOrd
    split_ifs
    · exact herr i j
    · simpa only [mul_comm ‖(c j).1 - (c j).2‖, max_comm (τ j)] using herr j i
  have hdglobal : ∀ i j, |wOrd w c i j - wOrd w₀ c i j| ≤ 16 * D := by
    intro i j
    have hm : 0 < max (τ i) (τ j) := (hτ i).trans_le (le_max_left _ _)
    have hi := (hrτ i).trans (mul_le_mul_of_nonneg_left (le_max_left (τ i) (τ j)) (by norm_num : (0:ℝ) ≤ 4))
    have hj := (hrτ j).trans (mul_le_mul_of_nonneg_left (le_max_right (τ i) (τ j)) (by norm_num : (0:ℝ) ≤ 4))
    apply (hdord i j).trans
    apply (div_le_iff₀ (pow_pos hm 2)).2
    nlinarith [mul_le_mul hi hj (norm_nonneg ((c j).1 - (c j).2)) (by positivity : 0 ≤ 4 * max (τ i) (τ j))]
  have hdroot : ∀ i j, |wOrd w c i j - wOrd w₀ c i j| ≤
      D * (rhoD lam (c i) * rhoD lam (c j) / τ i ^ 2) := by
    intro i j
    apply (hdord i j).trans
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hD
    exact div_le_div₀ (mul_nonneg (hr i) (hr j))
      (mul_le_mul (hn i) (hn j) (norm_nonneg _) (hr i)) (pow_pos (hτ i) 2)
      (pow_le_pow_left₀ (hτ i).le (le_max_left _ _) 2)
  have hparts := internal_bond_parts_geometric hβ hC hlam hM c (fun i j hf => (hw i j hf).1)
  have hparts₀ := internal_bond_parts_geometric hβ hC hlam hM c (fun i j hf => (hw i j hf).2)
  have hA0 : ∀ e, 0 ≤ mixedOddWeight M lam c e := fun e =>
    mul_nonneg (ahatE_nonneg c e) (farInd_nonneg c e)
  have hB0 : ∀ e, 0 ≤ mixedEvenWeight M lam c e := fun e =>
    mul_nonneg (sq_nonneg _) (farInd_nonneg c e)
  have hselected : ∀ i j,
      |gammaW β w M lam c s(i,j) - gammaW β w₀ M lam c s(i,j)| ≤ K * (rhoD lam (c i) * rhoD lam (c j) / τ i ^ 2) ∧
      |(alphaW β w M lam c s(i,j) + linkIndE M lam c s(i,j)) -
        (alphaW β w₀ M lam c s(i,j) + linkIndE M lam c s(i,j))| ≤ K * (rhoD lam (c i) * rhoD lam (c j) / τ i ^ 2) := by
    intro i j
    have ht : 0 ≤ rhoD lam (c i) * rhoD lam (c j) / τ i ^ 2 :=
      div_nonneg (mul_nonneg (hr i) (hr j)) (sq_nonneg _)
    by_cases hf : FarE M lam c s(i,j)
    · have ha1 := (far_facts hlam hM hf).2.2
      have hwo := abs_wOrd_le c (fun i j hf => (hw i j hf).1) hf
      have hwv := abs_wOrd_le c (fun i j hf => (hw i j hf).2) hf
      have ha : |wOrd w c i j| + |wOrd w₀ c i j| ≤ 2 * C := by
        nlinarith [ahat_nonneg (c i) (c j)]
      have hp := internal_selected_hyperbolic hβ (by positivity : 0 ≤ 2 * C) hD ht ha (hdroot i j)
      simp only [gammaW, alphaW, symmLift_mk, ite_eq_right hf]
      constructor
      · rw [show -Real.sinh (β * wOrd w c i j) - -Real.sinh (β * wOrd w₀ c i j) =
          -(Real.sinh (β * wOrd w c i j) - Real.sinh (β * wOrd w₀ c i j)) by ring, abs_neg]
        exact hp.1.trans (mul_le_mul_of_nonneg_right hKdK ht)
      · rw [show (Real.cosh (β * wOrd w c i j) - 1 + linkIndE M lam c s(i,j)) -
          (Real.cosh (β * wOrd w₀ c i j) - 1 + linkIndE M lam c s(i,j)) =
          Real.cosh (β * wOrd w c i j) - Real.cosh (β * wOrd w₀ c i j) by ring]
        exact hp.2.trans (mul_le_mul_of_nonneg_right hKdK ht)
    · simp only [gammaW_of_linked c hf, alphaW_add_linkIndE_of_linked c hf, sub_self, abs_zero]
      exact ⟨mul_nonneg (zero_le_one.trans hK) ht, mul_nonneg (zero_le_one.trans hK) ht⟩
  refine ⟨hK, hr, hτ, ?_, ?_, ?_, ?_, fun i => (hv i).trans hK,
    fun i j => (hselected i j).1, fun i j => (hselected i j).2, ?_, ?_⟩
  · intro e
    exact ⟨((hparts₀ e).1).trans (mul_le_mul_of_nonneg_right (by linarith) (hA0 e)),
      (abs_sub _ _).trans ((add_le_add (hparts e).1 (hparts₀ e).1).trans (by
        change Ka * _ + Ka * _ ≤ _; nlinarith [hA0 e]))⟩
  · intro e
    exact ⟨((hparts₀ e).2).trans (mul_le_mul_of_nonneg_right (by linarith) (hB0 e)),
      (abs_sub _ _).trans ((add_le_add (hparts e).2 (hparts₀ e).2).trans (by
        change Ka * _ + Ka * _ ≤ _; nlinarith [hB0 e]))⟩
  · intro e
    induction e using Sym2.ind with
    | h i j =>
      have harg : |β * (wOrd w₀ c i j - wOrd w c i j)| ≤ 16 * β * D := by
        rw [abs_mul, abs_of_nonneg hβ, abs_sub_comm]
        nlinarith [hdglobal i j]
      exact (exp_correction_le (by positivity) harg).trans (by dsimp [K, Kq]; nlinarith)
  · intro i
    exact (quadratic_correction_bounds (L := L) (norm_nonneg _) (hτ i) (hrτ i)).2.trans (by dsimp [K, Ku]; linarith)
  · intro i j
    have hpoint := GeneralExpansion.abs_exp_sub_exp_le (β * (wOrd w₀ c i j - wOrd w c i j)) 0
    rw [Real.exp_zero, sub_zero] at hpoint
    have harg : |β * (wOrd w₀ c i j - wOrd w c i j)| ≤ β * D * (rhoD lam (c i) * rhoD lam (c j) / τ i ^ 2) := by
      rw [abs_mul, abs_of_nonneg hβ, abs_sub_comm]
      exact (mul_le_mul_of_nonneg_left (hdroot i j) hβ).trans_eq (by ring)
    have hmax : max (β * (wOrd w₀ c i j - wOrd w c i j)) 0 ≤ 16 * β * D := by
      apply max_le _ (by positivity)
      calc _ ≤ |β * (wOrd w₀ c i j - wOrd w c i j)| := le_abs_self _
           _ ≤ _ := by rw [abs_mul, abs_of_nonneg hβ, abs_sub_comm]; nlinarith [hdglobal i j]
    change |Real.exp (β * (wOrd w₀ c i j - wOrd w c i j)) - 1| ≤ _
    exact hpoint.trans ((mul_le_mul (Real.exp_le_exp.2 hmax) harg (abs_nonneg _) (Real.exp_pos _).le).trans
      (by
        calc _ = Kq * (rhoD lam (c i) * rhoD lam (c j) / τ i ^ 2) := by dsimp [Kq]; ring
             _ ≤ _ := mul_le_mul_of_nonneg_right hKqK (div_nonneg (mul_nonneg (hr i) (hr j)) (sq_nonneg _))))
  · intro i
    have hp := (quadratic_correction_bounds (L := L) (norm_nonneg _) (hτ i) (hrτ i)).1
    have hrad : (‖(c i).1 - (c i).2‖ / τ i) ^ 2 ≤ rhoD lam (c i) ^ 2 / τ i ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hn i) 2) (sq_nonneg _)
    exact hp.trans ((mul_le_mul_of_nonneg_left hrad (by positivity)).trans
      (mul_le_mul_of_nonneg_right hKuK (div_nonneg (sq_nonneg _) (sq_nonneg _))))

end MultipoleBKT.ExpansionK.RouteCases

end
