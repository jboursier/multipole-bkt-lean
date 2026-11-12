/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Quadratic

/-!
# The two omitted spatial profiles

See Lemma A.7. Odd coordinates have one
unbounded maximum tail. A retained even mark uses the exterior quartic kernel.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- The separated odd, even and near distance families. -/
noncomputable def distanceFamily {W : Type*} [Fintype W]
    (A E N : Finset (Sym2 W)) (M a R : ℝ) (s t d : Sym2 W → ℝ) : ℝ≥0∞ :=
  jointOdd a R (fun e : A => (d e : ℂ)) *
    ((∏ e ∈ E, ENNReal.ofReal (spatialProfile true M (s e) (t e) (d e) / s e ^ 2)) *
      ∏ e ∈ N, ENNReal.ofReal (spatialProfile false M (s e) (t e) (d e) / s e ^ 2))

/-- Reindex the whole odd family and its complement without splitting its tail. -/
theorem distanceFamily_reindex {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (D A E N : Finset (Sym2 W)) (hpart : A ∪ (E ∪ N) = D)
    (hA : Disjoint A (E ∪ N)) (hEN : Disjoint E N) (f : I ≃ D)
    (M a R : ℝ) (s t d : Sym2 W → ℝ) :
    distanceFamily A E N M a R s t d =
      mixedDistanceProfile (fun i => (f i).val ∈ A)
        (fun i => if (f i.val).val ∈ E then true else false)
        (fun i => s (f i.val)) (fun i => t (f i.val)) M a R (fun i => d (f i)) := by
  have hs : A ⊆ D := by rw [← hpart]; exact subset_union_left
  rw [mixedDistanceProfile_reindex D A hs f (fun e => if e ∈ E then true else false) s t d M a R]
  rw [show D \ A = E ∪ N by rw [← hpart,union_sdiff_cancel_left hA],prod_union hEN]
  unfold distanceFamily
  congr 2
  · apply prod_congr rfl
    intro e he
    rw [ite_eq_left he]
  · apply prod_congr rfl
    intro e he
    rw [ite_eq_right (fun hh => Finset.disjoint_left.1 hEN hh he)]

/-- The normalized omitted tree on the original labels. The empty mark denotes
an odd or surplus long edge. A present mark is integrated outside `H`. -/
noncomputable def omittedTree {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (M lam H : ℝ) (A E N : Finset (Sym2 W)) (mark : Option (Sym2 W))
    (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  let s := edgeMin id (fun i => rhoD lam (c i))
  let t := radMax (fun i => rhoD lam (c i))
  match mark with
  | none => ENNReal.ofReal ((H ^ 2)⁻¹) *
      distanceFamily A E N M (minRad lam c) H s t (dipoleDistOn c)
  | some m => longEvenProfile 1 1 H (dipoleDistOn c m) *
      distanceFamily A (E.erase m) N M (minRad lam c) (maxRad lam c) s t (dipoleDistOn c)

/-- Configuration radii identify the separated ordinary edge profiles. -/
theorem distanceFamily_config {W : Type*} [Fintype W] [Nonempty W]
    (A E N : Finset (Sym2 W)) (M lam R : ℝ) (c : W → ℂ × ℂ) :
    distanceFamily A E N M (minRad lam c) R
      (edgeMin id (fun i => rhoD lam (c i))) (radMax (fun i => rhoD lam (c i))) (dipoleDistOn c) =
      jointOdd (minRad lam c) R (fun e : A => (dipoleDistOn c e : ℂ)) *
        ((∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam c e)) *
          ∏ e ∈ N, ENNReal.ofReal (edgeProfile false M lam c e)) := by
  unfold distanceFamily
  congr 2
  all_goals
    apply prod_congr rfl
    intro e _
    induction e using Sym2.ind with
    | h i j => rfl

/-- Measurability of the complete normalized omitted tree. -/
theorem measurable_omittedTree {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (M lam H : ℝ) (A E N : Finset (Sym2 W)) (mark : Option (Sym2 W)) :
    Measurable (omittedTree M lam H A E N mark) := by
  have hd (e : Sym2 W) : Measurable (fun c : W → ℂ × ℂ => dipoleDistOn c e) := by
    induction e using Sym2.ind with
    | h i j => exact measurable_dipoleDist.comp (show Measurable (fun c : W → ℂ × ℂ => (c i,c j)) by fun_prop)
  have hp (b : Bool) (e : Sym2 W) : Measurable (fun c : W → ℂ × ℂ => ENNReal.ofReal (edgeProfile b M lam c e)) := by
    induction e using Sym2.ind with
    | h i j =>
      have hdij : Measurable (fun c : W → ℂ × ℂ => dipoleDist (c i) (c j)) := by
        simpa only [dipoleDistOn_mk] using hd s(i,j)
      simp only [edgeProfile_mk]
      unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile rhoD
      split_ifs <;> apply Measurable.ennreal_ofReal <;>
        first | fun_prop | exact Measurable.div (Measurable.ite (measurableSet_le hdij (by fun_prop))
          measurable_const (by fun_prop)) (by fun_prop)
  have hf (E : Finset (Sym2 W)) (R : (W → ℂ × ℂ) → ℝ) (hR : Measurable R) :
      Measurable (fun c : W → ℂ × ℂ => distanceFamily A E N M (minRad lam c) (R c)
        (edgeMin id (fun i => rhoD lam (c i))) (radMax (fun i => rhoD lam (c i))) (dipoleDistOn c)) := by
    simp_rw [distanceFamily_config]
    exact (measurable_jointOdd_comp _ _ _ (measurable_minRad lam) hR
      (measurable_pi_iff.mpr fun e : A => Complex.measurable_ofReal.comp (hd e))).mul
      ((Finset.measurable_prod _ fun e _ => hp true e).mul (Finset.measurable_prod _ fun e _ => hp false e))
  cases mark with
  | none => exact measurable_const.mul (hf E (fun _ => H) measurable_const)
  | some m =>
    exact ((measurable_longEvenProfile 1 1 H).comp (hd m)).mul
      (hf (E.erase m) (maxRad lam) (measurable_maxRad lam))

/-- All endpoint sectors for the odd or surplus long-edge alternative.
The exact inverse-square cutoff and radial logarithm remain visible. -/
theorem lintegral_odd_tree {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W],
      Fintype.card W ≤ k+1 → ∀ (T : SimpleGraph W), T.IsTree →
      ∀ (A E N : Finset (Sym2 W)), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ (root : W) (u : W → ℂ) (lam H : ℝ),
      0 < lam → (∀ i, rho lam (u i) ≤ H) → ∀ n : ℕ,
      (∫⁻ x : W → ℂ, (TwoComponentCoulomb.box n).indicator 1 (x root) *
        omittedTree M lam H A E N none (ofPosVec x u)) ≤
        ENNReal.ofReal (C * n / H ^ 2 * (1 + Real.log (H / minRho lam u)) ^ k) := by
  obtain ⟨C,hC,hb⟩ := lintegral_normalized_mixed_profiles hM k
  refine ⟨4^k*C,by positivity,?_⟩
  intro W _ _ _ hW T hT A E N hpart hA hEN root u lam H hlam hu n
  let s := edgeMin id (fun i => rho lam (u i))
  let t := radMax (fun i => rho lam (u i))
  let odd (e : T.edgeFinset) := e.val ∈ A
  let Φ := mixedDistanceProfile odd (fun e => if e.val.val ∈ E then true else false)
    (fun e => s e.val) (fun e => t e.val) M (minRho lam u) H
  have hΦ : Measurable Φ := measurable_mixedDistanceProfile _ _ _ _ _ _ _
  have heq (x : W → ℂ) : omittedTree M lam H A E N none (ofPosVec x u) =
      ENNReal.ofReal ((H^2)⁻¹) * Φ (fun e => dipoleDistOn (ofPosVec x u) e) := by
    unfold omittedTree
    rw [minRad_ofPosVec_eq]
    have hr : (fun i => rhoD lam (ofPosVec x u i)) = fun i => rho lam (u i) := by
      funext i
      simp only [ofPosVec_apply,rhoD_mk]
    dsimp only
    rw [hr]
    rw [distanceFamily_reindex T.edgeFinset A E N hpart hA hEN (Equiv.refl _) ]
    rfl
  simp_rw [heq,show ∀ (x : ℝ≥0∞) y z, x * (y*z) = (x*z)*y by intros; ring]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  have hs := lintegral_coupled_tree_le T hT root u ((TwoComponentCoulomb.box n).indicator 1)
    (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box n)) Φ hΦ
  have hcount : Fintype.card T.edgeFinset ≤ k := by
    rw [Fintype.card_coe]
    have := hT.card_edgeFinset
    omega
  have ha := minRho_pos hlam u
  have haH : minRho lam u ≤ H := (minRho_le_rho lam u root).trans (hu root)
  have hL : 0 ≤ 1 + Real.log (H/minRho lam u) := by
    have := Real.log_nonneg ((one_le_div ha).2 haH)
    linarith
  have hi : (∫⁻ z : T.edgeFinset → ℂ, Φ (fun e => ‖z e‖)) ≤
      ENNReal.ofReal (C*(1+Real.log (H/minRho lam u))^k) := by
    dsimp only [Φ]
    simp_rw [mixedDistanceProfile_norm]
    apply hb _ hcount _ _ _ _ _ _ ha haH
    intro e
    induction e.val.val using Sym2.ind with
    | h i j => exact ⟨le_min (minRho_le_rho lam u i) (minRho_le_rho lam u j),min_le_max,max_le (hu i) (hu j)⟩
  rw [lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box n),TwoComponentCoulomb.volume_box] at hs
  refine (mul_le_mul' (hs.trans (mul_le_mul'
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 4) (by omega : Fintype.card W - 1 ≤ k))
    (mul_le_mul' le_rfl hi))) le_rfl).trans_eq ?_
  rw [show (4 : ℝ≥0∞)^k = ENNReal.ofReal ((4 : ℝ)^k) by rw [ENNReal.ofReal_pow (by norm_num)]; norm_num,
    ← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MultipoleBKT.ExpansionK.RouteOmitted

end
