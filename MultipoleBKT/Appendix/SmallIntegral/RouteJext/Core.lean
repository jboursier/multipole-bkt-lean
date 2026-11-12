/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Definitions
public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Spatial
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Measurability

/-!
# The retained trees and radius allocation for J_ext

See Lemma A.4 and (A.25).
Retain the odd and even trees and choose one near tree in each block.
The cutoff odd factors remain inverse squares, without an auxiliary power.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJext

open MeasureTheory Set Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps RouteJ
open scoped Classical ENNReal

/-- Dipole displacement vectors in the position and displacement coordinates. -/
def vectors {V : Type*} (c : V → ℂ × ℂ) (i : V) : ℂ := (c i).2 - (c i).1

theorem vectors_ofPosVec {V : Type*} (x u : V → ℂ) : vectors (ofPosVec x u) = u := by
  funext i
  simp [vectors, ofPosVec_apply]

/-- The cutoff tree profile, with each edge normalized by its allocated radius. -/
noncomputable def cutTree {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M lam h : ℝ) (A E F : Finset (Sym2 V)) (c : V → ℂ × ℂ) : ℝ≥0∞ :=
  ∏ e ∈ F ∪ (A ∪ E), ENNReal.ofReal
    (cutProfile A E M lam h (vectors c) e (dipoleDistOn c e))

theorem cutProfile_of_config {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M lam h : ℝ) (A E : Finset (Sym2 V)) (c : V → ℂ × ℂ) (e : Sym2 V) :
    cutProfile A E M lam h (vectors c) e (dipoleDistOn c e) =
      if e ∈ A then oddProfile (minRad lam c) h (dipoleDistOn c e)
      else edgeProfile (e ∈ E) M lam c e := by
  have hc : ofPosVec (fun i => (c i).1) (vectors c) = c := by
    funext i
    simp [ofPosVec_apply, vectors]
  have hmin : minRho lam (vectors c) = minRad lam c := by
    rw [← hc, minRad_ofPosVec_eq, vectors_ofPosVec]
  unfold cutProfile
  rw [hmin]
  split_ifs
  · rfl
  · induction e using Sym2.ind with
    | h i j =>
      simp only [edgeProfile_mk]
      simp only [edgeMin_mk, radMax_mk, id_eq, rho, vectors, rhoD, norm_sub_rev,
        dipoleDistOn_mk]

theorem measurable_cutTree {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (M lam h : ℝ) (A E F : Finset (Sym2 V)) : Measurable (cutTree M lam h A E F) := by
  unfold cutTree
  apply Finset.measurable_prod
  intro e _
  simp_rw [cutProfile_of_config]
  have hd : Measurable (fun c : V → ℂ × ℂ => dipoleDistOn c e) := by
    induction e using Sym2.ind with
    | h i j => exact measurable_dipoleDist.comp (show Measurable (fun c : V → ℂ × ℂ => (c i, c j)) by fun_prop)
  split_ifs
  · unfold oddProfile
    apply Measurable.ennreal_ofReal
    apply Measurable.ite
    · exact (measurableSet_lt (measurable_minRad lam) hd).inter
        (measurableSet_le hd measurable_const)
    · exact hd.pow_const 2 |>.inv
    · exact measurable_const
  · induction e using Sym2.ind with
    | h i j =>
      simp only [edgeProfile_mk]
      unfold spatialProfile MultipoleBKT.RouteLog.evenEdgeProfile
      have hd : Measurable fun c : V → ℂ × ℂ => dipoleDist (c i) (c j) :=
        measurable_dipoleDist.comp (show Measurable (fun c : V → ℂ × ℂ => (c i, c j)) by fun_prop)
      have hi : Measurable (fun c : V → ℂ × ℂ => rhoD lam (c i)) := (measurable_rhoD lam).comp (measurable_pi_apply i)
      have hj : Measurable (fun c : V → ℂ × ℂ => rhoD lam (c j)) := (measurable_rhoD lam).comp (measurable_pi_apply j)
      apply Measurable.ennreal_ofReal
      split_ifs <;> apply Measurable.div _ ((hi.min hj).pow_const 2) <;>
        exact Measurable.ite (measurableSet_le hd (measurable_const.mul (hi.min hj)))
          measurable_const (by fun_prop)

/-- The original odd weight is exactly supported on the cutoff annulus. -/
theorem keptWeight_le_oddProfile {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    {M lam eps R : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam)
    (c : W → ℂ × ℂ) (e : Sym2 W) :
    keptWeight (dipoleDistOn c) (absIndicator M lam eps R c) e ≤
      oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e) := by
  induction e using Sym2.ind with
  | h i j =>
    unfold keptWeight absIndicator oddProfile
    simp only [Sym2.lift_mk, dipoleDistOn_mk]
    by_cases hlink : MultipoleLinked M lam (c i) (c j)
    · simp only [hlink, ite_true, zero_mul, zero_div]
      exact indicator_nonneg (fun _ _ => inv_nonneg.mpr (sq_nonneg _)) _
    · have hd : minRad lam c < dipoleDist (c i) (c j) := by
        have hs := le_min (minRad_le lam c i) (minRad_le lam c j)
        have hs0 := (lt_min (rhoD_pos hlam (c i)) (rhoD_pos hlam (c j))).le
        exact lt_of_le_of_lt (hs.trans (le_mul_of_one_le_left hs0 hM)) (lt_of_not_ge hlink)
      by_cases hcut : dipoleDist (c i) (c j) ≤ 17 * eps * R
      · rw [ite_eq_right hlink, ite_eq_left hcut, one_mul, one_div,
          indicator_of_mem (show dipoleDist (c i) (c j) ∈ Set.Ioc (minRad lam c) (17 * (eps * R)) by
            exact ⟨hd, by simpa only [mul_assoc] using hcut⟩)]
      · rw [ite_eq_right hlink, ite_eq_right hcut, mul_zero, zero_div,
          indicator_of_notMem (show dipoleDist (c i) (c j) ∉ Set.Ioc (minRad lam c) (17 * (eps * R)) by
            intro h; exact hcut (by simpa only [mul_assoc] using h.2))]

/-- The core with the cutoff odd factors, before external gain and density. -/
noncomputable def core {X : Finset (Finset ℕ)} (M lam eps R : ℝ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (hat : Fin n → X) (c : X.biUnion id → ℂ × ℂ) : ℝ :=
  (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
    blockRadius hX (fun i => dipoleLength (c i)) S ^ 2) *
  (∏ e ∈ univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset,
    keptWeight (dipoleDistOn c) (absIndicator M lam eps R c) e) *
  (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset,
    (absWeight (fun i => dipoleLength (c i)) (dipoleDistOn c) (absIndicator M lam eps R c) e ^ 2 + linkE M lam c e)) *
  ∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) c) S) then 1 else 0

/-- The actual radius allocation followed by retained cutoff trees. -/
theorem core_le_retained_sum {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    [Nonempty (X.biUnion id)] {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (hXs : ∀ l, Xs l ⊆ X) (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf)
    (Tb : Finset (ℕ × ℕ))
    (hTb : Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf)
    (c : X.biUnion id → ℂ × ℂ) (hat : Fin n → X)
    (hhat : ∀ l, hat l ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
      blockRadius hX (fun i => dipoleLength (c i)) S ≤ blockRadius hX (fun i => dipoleLength (c i)) (hat l))
    {M lam eps R : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) :
    ENNReal.ofReal (core M lam eps R hX Xs Ta Tb hat c) ≤
      ∑ Q : NearTreeFamily (Limits.blockOf X), ENNReal.ofReal (radialFactor lam c) *
        cutTree M lam (eps * R)
          (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
          (graphOf (X.biUnion id) Tb).edgeFinset
          (nearForest (Limits.blockOf X) (fun b => (Q b).val)) c := by
  let A := univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
  let E := (graphOf (X.biUnion id) Tb).edgeFinset
  let drop := ∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
    blockRadius hX (fun i => dipoleLength (c i)) S ^ 2
  let B := ∏ e ∈ E, (aSqE M lam c e + linkE M lam c e)
  let P := ∏ e ∈ A, keptWeight (dipoleDistOn c) (absIndicator M lam eps R c) e
  have hdrop : 0 ≤ drop := prod_nonneg fun _ _ => prod_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ B := prod_nonneg fun _ _ => add_nonneg (aSqE_nonneg c _) (linkE_nonneg c _)
  have hP : 0 ≤ P := prod_nonneg fun e _ => keptWeight_nonneg' _ _ _ _ _ e
  by_cases hm : ∀ S ∈ X, ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) c) S)
  · have hconn : ∀ S : X, ((nearGraph M lam c).induce {i | Limits.blockOf X i = S}).Connected :=
      fun S => connected_induce_of_connOn hX c S.property (hm S S.property)
    obtain ⟨Q, hQ⟩ := exists_linked_nearTreeFamily (Limits.blockOf X) M lam c hconn
    let F := nearForest (Limits.blockOf X) (fun b => (Q b).val)
    have hp : (∏ e ∈ F, linkE M lam c e) = 1 := by
      apply prod_eq_one
      intro e he
      induction e using Sym2.ind with
      | h i j => exact ite_eq_left (hQ i j he)
    have hn := source_normalized_product hX Xs hXs hdisj Ta hTa Tb hTb c hat hhat Q hlam M
    rw [hp, mul_one] at hn
    have hcore : core M lam eps R hX Xs Ta Tb hat c ≤ P * (drop * B) := by
      unfold core
      rw [prod_eq_one (fun S hS => ite_eq_left (hm S hS)), mul_one]
      calc
        _ ≤ drop * P * B := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hdrop hP)
          exact prod_le_prod₀ (fun e _ => add_nonneg (sq_nonneg _) (linkE_nonneg c _))
            fun e _ => add_le_add (absWeight_sq_le_aSqE M lam eps R c e) le_rfl
        _ = _ := by ring
    obtain ⟨_, _, _, hinter, hconn', hcount⟩ := trees_structure hX hXs hdisj hTa hTb
    have hc : A.card + E.card + 1 ≤ Fintype.card X := by
      have ha : A.card ≤ ∑ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card := card_biUnion_le
      dsimp only [E]
      omega
    obtain ⟨_, _, hFAE, hAE, _⟩ := retained_tree (Limits.blockOf X) (fun b => (Q b).val)
      (fun b => (Q b).property) A E hinter hconn' hc
    change Disjoint F (A ∪ E) at hFAE
    have hprod : ENNReal.ofReal P *
        ((∏ e ∈ E, ENNReal.ofReal (normalizedEven M lam c e)) *
          ∏ e ∈ F, ENNReal.ofReal (nearE M lam c e)) ≤ cutTree M lam (eps * R) A E F c := by
      let f (e : Sym2 (X.biUnion id)) := ENNReal.ofReal (cutProfile A E M lam (eps * R) (vectors c) e (dipoleDistOn c e))
      have hsplit : cutTree M lam (eps * R) A E F c =
          (∏ e ∈ F, f e) * ((∏ e ∈ A, f e) * ∏ e ∈ E, f e) :=
        (Finset.prod_union (f := f) hFAE).trans
          (congrArg ((∏ e ∈ F, f e) * ·) (Finset.prod_union (f := f) hAE))
      rw [hsplit]
      dsimp only [f]
      simp_rw [cutProfile_of_config]
      have hodd : ENNReal.ofReal P ≤ ∏ e ∈ A, ENNReal.ofReal (oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e)) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => keptWeight_nonneg' _ _ _ _ _ e)]
        exact prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (keptWeight_le_oddProfile hM hlam c e)
      calc
        _ ≤ (∏ e ∈ A, ENNReal.ofReal (oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e))) *
            ((∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam c e)) *
              ∏ e ∈ F, ENNReal.ofReal (edgeProfile false M lam c e)) := by
          exact mul_le_mul' hodd (mul_le_mul'
            (prod_le_prod fun e _ => ENNReal.ofReal_le_ofReal (normalizedEven_le_edgeProfile hM hlam c e))
            (le_of_eq (prod_congr rfl fun e _ => congrArg ENNReal.ofReal (nearE_eq_edgeProfile M lam c e))))
        _ = _ := by
          have hE (e) (he : e ∈ E) : e ∉ A := fun ha => Finset.disjoint_left.mp hAE ha he
          have hF (e) (he : e ∈ F) : e ∉ A ∧ e ∉ E := by
            have hn : e ∉ A ∪ E := fun h => Finset.disjoint_left.mp hFAE he h
            simpa only [Finset.mem_union, not_or] using hn
          have pF : (∏ e ∈ F, ENNReal.ofReal
              (if e ∈ A then oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e)
                else edgeProfile (e ∈ E) M lam c e)) =
              ∏ e ∈ F, ENNReal.ofReal (edgeProfile false M lam c e) := by
            apply prod_congr rfl
            intro e he
            rw [ite_eq_right (hF e he).1, show decide (e ∈ E) = false from decide_eq_false (hF e he).2]
          have pA : (∏ e ∈ A, ENNReal.ofReal
              (if e ∈ A then oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e)
                else edgeProfile (e ∈ E) M lam c e)) =
              ∏ e ∈ A, ENNReal.ofReal (oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e)) :=
            prod_congr rfl fun e he => by rw [ite_eq_left he]
          have pE : (∏ e ∈ E, ENNReal.ofReal
              (if e ∈ A then oddProfile (minRad lam c) (eps * R) (dipoleDistOn c e)
                else edgeProfile (e ∈ E) M lam c e)) =
              ∏ e ∈ E, ENNReal.ofReal (edgeProfile true M lam c e) := by
            apply prod_congr rfl
            intro e he
            rw [ite_eq_right (hE e he), show decide (e ∈ E) = true from decide_eq_true he]
          rw [pF, pA, pE]
          ring
    have hrad : 0 ≤ radialFactor lam c := by
      unfold radialFactor
      exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _) (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam c)) _)
    have hnorm0 : 0 ≤ (∏ e ∈ E, normalizedEven M lam c e) := prod_nonneg fun e _ =>
      div_nonneg (add_nonneg (aSqE_nonneg c e) (linkE_nonneg c e)) (minSq_pos hlam c e).le
    have hbound : ENNReal.ofReal (core M lam eps R hX Xs Ta Tb hat c) ≤
        ENNReal.ofReal (radialFactor lam c) * cutTree M lam (eps * R) A E F c := by
      refine (ENNReal.ofReal_le_ofReal hcore).trans ?_
      rw [ENNReal.ofReal_mul hP]
      have hnorm := ENNReal.ofReal_le_ofReal hn
      change ENNReal.ofReal (drop * B) ≤ ENNReal.ofReal (radialFactor lam c *
        ((∏ e ∈ E, normalizedEven M lam c e) * ∏ e ∈ F, nearE M lam c e)) at hnorm
      rw [ENNReal.ofReal_mul hrad, ENNReal.ofReal_mul hnorm0] at hnorm
      have pE : ENNReal.ofReal (∏ e ∈ E, normalizedEven M lam c e) =
          ∏ e ∈ E, ENNReal.ofReal (normalizedEven M lam c e) :=
        ENNReal.ofReal_prod_of_nonneg (fun e _ => div_nonneg
          (add_nonneg (aSqE_nonneg c e) (linkE_nonneg c e)) (minSq_pos hlam c e).le)
      have pF : ENNReal.ofReal (∏ e ∈ F, nearE M lam c e) =
          ∏ e ∈ F, ENNReal.ofReal (nearE M lam c e) :=
        ENNReal.ofReal_prod_of_nonneg (fun e _ => nearE_nonneg M lam c e)
      rw [pE, pF] at hnorm
      calc
        _ ≤ ENNReal.ofReal P * (ENNReal.ofReal (radialFactor lam c) *
            ((∏ e ∈ E, ENNReal.ofReal (normalizedEven M lam c e)) *
              ∏ e ∈ F, ENNReal.ofReal (nearE M lam c e))) := mul_le_mul' le_rfl hnorm
        _ = ENNReal.ofReal (radialFactor lam c) * (ENNReal.ofReal P *
            ((∏ e ∈ E, ENNReal.ofReal (normalizedEven M lam c e)) *
              ∏ e ∈ F, ENNReal.ofReal (nearE M lam c e))) := by ring
        _ ≤ _ := mul_le_mul' le_rfl hprod
    exact hbound.trans (single_le_sum
      (f := fun Q : NearTreeFamily (Limits.blockOf X) => ENNReal.ofReal (radialFactor lam c) *
        cutTree M lam (eps * R) A E (nearForest (Limits.blockOf X) (fun b => (Q b).val)) c)
      (fun _ _ => bot_le) (mem_univ Q))
  · push Not at hm
    obtain ⟨S, hS, hn⟩ := hm
    unfold core
    rw [prod_eq_zero hS (ite_eq_right hn), mul_zero, ENNReal.ofReal_zero]
    exact bot_le

end MultipoleBKT.SmallIntegral.RouteJext

end
