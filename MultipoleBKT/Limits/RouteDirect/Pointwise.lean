/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.SpatialOdd
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.SpatialTree

/-!
# The tree majorant after radius cancellation

See Lemma A.5 of the paper. Normalize the even edges only after ordering the coarse
even tree. The remaining profile retains the single odd maximum tail.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph
open SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

variable {I B C : Type*} [Fintype I] [Fintype B] [Fintype C]
  [DecidableEq I] [DecidableEq B] [DecidableEq C] [Nonempty I]

omit [Nonempty I] in
/-- A largest regularized radius cancels the denominator of the radial factor. -/
theorem radialFactor_eq_erase_rho {lam : ℝ} (hlam : 0 < lam) (c : I → ℂ × ℂ)
    (i₀ : I) (hmax : ∀ i, rhoD lam (c i) ≤ rhoD lam (c i₀)) :
    radialFactor lam c = ∏ i ∈ univ.erase i₀, rhoD lam (c i) ^ 2 := by
  have hR : maxRad lam c = rhoD lam (c i₀) :=
    le_antisymm ((fold_max_le _).mpr ⟨le_max_right _ _, fun i _ => hmax i⟩)
      (rhoD_le_maxRad lam c i₀)
  unfold radialFactor
  rw [hR, Real.rpow_neg (rhoD_pos hlam _).le, Real.rpow_two,
    ← mul_prod_erase univ (fun i => rhoD lam (c i) ^ 2) (mem_univ i₀)]
  field_simp [(rhoD_pos hlam (c i₀)).ne']

omit [Fintype I] [DecidableEq I] [Nonempty I] in
/-- An even edge contributes its squared minimum times the normalized profile. -/
theorem paperEvenE_le_normalized {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (c : I → ℂ × ℂ) (e : Sym2 I) :
    paperEvenE M lam c e ≤ minSq lam c e * edgeProfile true M lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    rw [minSq_mk, edgeProfile_mk]
    rw [mul_div_cancel₀ _ (pow_pos (lt_min (rhoD_pos hlam _) (rhoD_pos hlam _)) 2).ne']
    exact hatEven_le_profile hM hlam _ _

omit [DecidableEq B] [DecidableEq C] in
/-- The full tree majorant is bounded by the common radial factor times the
near/odd/even profile. This uses both ordered radius allocations. -/
theorem paperTreeMajorant_le_profile {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (blk : I → B) (rep : B → I) (hrep : ∀ b, blk (rep b) = b)
    (grp : B → C) (root : C → B) (hroot : ∀ d, grp (root d) = d)
    (c : I → ℂ × ℂ)
    (hmax : ∀ i, rhoD lam (c i) ≤ rhoD lam (c (rep (blk i))))
    (hgroup : ∀ b, rhoD lam (c (rep b)) ≤ rhoD lam (c (rep (root (grp b)))))
    (NT A Bf : Finset (Sym2 I))
    (hnear : (∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) ≤
      ∏ i ∈ univ.filter (fun i => i ≠ rep (blk i)), sqPos (rhoD lam (c i)))
    (hB : (nodeGraph (Sym2.map grp ∘ Sym2.map blk) Bf).IsTree)
    (hBc : Bf.card + 1 = Fintype.card C) :
    ENNReal.ofReal (paperTreeMajorant M lam c (fun b => rhoD lam (c (rep b))) root NT A Bf) ≤
      ENNReal.ofReal (radialFactor lam c) * treeProfile M lam A Bf NT c := by
  have hC : Nonempty C := Nonempty.map (grp ∘ blk) inferInstance
  obtain ⟨d₀, _, hglobal⟩ := exists_max_image univ
    (fun d => rhoD lam (c (rep (root d)))) univ_nonempty
  have halloc := merged_radius_allocation blk rep hrep grp root hroot
    (fun i => rhoD lam (c i)) (fun i => rhoD_pos hlam _) hmax hgroup NT Bf hnear hB hBc d₀
      (fun d => hglobal d (mem_univ _))
  rw [← radialFactor_eq_erase_rho hlam c (rep (root d₀))
    (fun i => (hmax i).trans ((hgroup _).trans (hglobal _ (mem_univ _))))] at halloc
  have hmin (e : Sym2 I) : minSq lam c e = edgeMin sqPos (fun i => rhoD lam (c i)) e := by
    induction e using Sym2.ind with
    | h i j => rw [minSq_mk, edgeMin_mk, sqPos_of_nonneg (lt_min (rhoD_pos hlam _) (rhoD_pos hlam _)).le]
  have hprof (e : Sym2 I) (ev : Bool) : 0 ≤ edgeProfile ev M lam c e := by
    induction e using Sym2.ind with
    | h i j =>
      rw [edgeProfile_mk]
      unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
      split_ifs <;> positivity
  have hnearEq : (∏ e ∈ NT, nearE M lam c e) = ∏ e ∈ NT, edgeProfile false M lam c e := by
    simp_rw [nearE_eq_edgeProfile]
  have heven : (∏ e ∈ Bf, paperEvenE M lam c e) ≤
      (∏ e ∈ Bf, minSq lam c e) * ∏ e ∈ Bf, edgeProfile true M lam c e := by
    rw [← prod_mul_distrib]
    exact prod_le_prod₀ (fun e _ => paperEvenE_nonneg M lam c e)
      (fun e _ => paperEvenE_le_normalized hlam hM c e)
  have hrad0 : 0 ≤ radialFactor lam c := by
    unfold radialFactor
    exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
      (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam c)) _)
  let P := (∏ e ∈ NT, edgeMin sqPos (fun i => rhoD lam (c i)) e) *
    ∏ b ∈ univ.filter (fun b => b ∉ Set.range root), rhoD lam (c (rep b)) ^ 2
  have hP : 0 ≤ P := mul_nonneg
    (prod_nonneg fun e _ => Sym2.inductionOn e fun _ _ => sqPos_nonneg _)
    (prod_nonneg fun _ _ => sq_nonneg _)
  have hnormalized : P * (∏ e ∈ Bf, paperEvenE M lam c e) * (∏ e ∈ NT, nearE M lam c e) ≤
      radialFactor lam c * ((∏ e ∈ Bf, edgeProfile true M lam c e) *
        ∏ e ∈ NT, edgeProfile false M lam c e) := by
    rw [hnearEq]
    have h := mul_le_mul_of_nonneg_left heven hP
    have hh := mul_le_mul_of_nonneg_right h (prod_nonneg (s := NT) fun e _ => hprof e false)
    simp_rw [hmin] at hh
    calc
      _ ≤ (P * ∏ e ∈ Bf, edgeMin sqPos (fun i => rhoD lam (c i)) e) *
          ((∏ e ∈ Bf, edgeProfile true M lam c e) * ∏ e ∈ NT, edgeProfile false M lam c e) := by
        exact hh.trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_right halloc
        (mul_nonneg (prod_nonneg fun e _ => hprof e true) (prod_nonneg fun e _ => hprof e false))
  have hodd := globalTail_paperOdd_le hM hlam c A
  have hpaper : paperTreeMajorant M lam c (fun b => rhoD lam (c (rep b))) root NT A Bf =
      (globalTail (maxRad lam c) (paperDistE c) A * ∏ e ∈ A, paperOddE M lam c e) *
        (P * (∏ e ∈ Bf, paperEvenE M lam c e) * ∏ e ∈ NT, nearE M lam c e) := by
    unfold paperTreeMajorant P
    dsimp only
    simp only [Finset.prod_filter]
    ring_nf
  rw [hpaper, ENNReal.ofReal_mul (mul_nonneg (globalTail_nonneg _ _ _)
    (prod_nonneg fun e _ => paperOddE_nonneg M lam c e))]
  have hb := ENNReal.ofReal_le_ofReal hnormalized
  rw [ENNReal.ofReal_mul hrad0, ENNReal.ofReal_mul (prod_nonneg fun e _ => hprof e true),
    ENNReal.ofReal_prod_of_nonneg (fun e _ => hprof e true),
    ENNReal.ofReal_prod_of_nonneg (fun e _ => hprof e false)] at hb
  have hd : paperDistE c = Peeling.dipoleDistOn c := by
    funext e
    induction e using Sym2.ind with
    | h i j => rfl
  rw [hd] at hodd
  exact (mul_le_mul' hodd hb).trans_eq (by unfold treeProfile; ring)

end MultipoleBKT.Limits.RouteDirect

end
