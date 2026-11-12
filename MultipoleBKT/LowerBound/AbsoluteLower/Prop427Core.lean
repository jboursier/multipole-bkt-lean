/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.JCore
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.CoreMajorant

/-!
# Radius cancellation for fixed groups and trees

The proof of Lemma 4.58, equation (A.67). Select a near spanning tree inside each original block. `grouped_radius_allocation` from Lemma A.4 applies `ordering_tree` to the coarse even
tree and to the near trees. Their squared minima cancel all radii except
the largest, giving `radF`.

`core_le_fixed_nearTree` keeps the selected near trees fixed during radius
allocation. `core_le_sum_tree` derives the powerset bound by retaining one linked family. The paper's spatial argument uses
the fixed-family theorem.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SimpleGraph Limits SmallIntegral

variable {M lam : ℝ}

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype β'] [DecidableEq β']

/-- The radial factor `R^{-2} ∏_i ρ_i²` of a configuration (`R = max_i ρ_i`). -/
noncomputable def radF (lam : ℝ) (c : ι → ℂ × ℂ) : ℝ :=
  (∏ i, rhoD lam (c i) ^ (2 : ℝ)) * maxRad lam c ^ (-(2 : ℝ))

omit [DecidableEq ι] [Nonempty ι] in
theorem radF_nonneg (hlam : 0 < lam) (c : ι → ℂ × ℂ) : 0 ≤ radF lam c := by
  unfold radF
  have hR : 0 < maxRad lam c := hlam.trans_le (lam_le_maxRad lam c)
  exact mul_nonneg (prod_nonneg fun i _ => Real.rpow_nonneg (rhoD_pos hlam _).le _)
    (Real.rpow_nonneg hR.le _)

/-- The edges (non-loops) inside the blocks. -/
noncomputable def intraE (blk : ι → β') : Finset (Sym2 ι) :=
  (univ : Finset (Sym2 ι)).filter fun e => (Sym2.map blk e).IsDiag ∧ ¬ e.IsDiag

open scoped Classical in
/-- Radius allocation for a fixed linked near-tree family.
(A.67) in the proof of Lemma 4.58. -/
theorem core_le_fixed_nearTree (hlam : 0 < lam) (blk : ι → β') (c : ι → ℂ × ℂ)
    (R : SmallIntegral.RouteJ.NearTreeFamily blk)
    (hR : ∀ i j, s(i, j) ∈ SmallIntegral.RouteJ.nearForest blk (fun S => (R S).val) →
      MultipoleLinked M lam (c i) (c j))
    {κ : Type*} [Fintype κ] (Ea : κ → Finset (Sym2 ι)) (G : κ → Finset β')
    (hGdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (hEaG : ∀ l, ∀ e ∈ Ea l, ∀ i ∈ e, blk i ∈ G l)
    (hcardl : ∀ l, (Ea l).card + 1 = (G l).card)
    (Eb : Finset (Sym2 ι))
    (hinter : ∀ e ∈ univ.biUnion Ea ∪ Eb, ¬ (Sym2.map blk e).IsDiag)
    (hconn : ∀ i j : ι, (sameBlockGraph blk ⊔
      fromEdgeSet ((univ.biUnion Ea ∪ Eb : Finset (Sym2 ι)) : Set (Sym2 ι))).Reachable i j)
    (hcount : (∑ l, (Ea l).card) + Eb.card + 1 ≤ Fintype.card β')
    (rb : β' → ℝ) (hrb0 : ∀ S, 0 ≤ rb S)
    (hrb : ∀ S, ∃ i, blk i = S ∧ rb S ≤ rhoD lam (c i))
    (hat : κ → β') (hhat : ∀ l, hat l ∈ G l ∧ ∀ S ∈ G l, rb S ≤ rb (hat l))
    (ka kb kbN : Sym2 ι → ℝ) (hka : ∀ e, 0 ≤ ka e) (hkb : ∀ e, 0 ≤ kb e)
    (hkbN : ∀ e, 0 ≤ kbN e)
    (hkbb : ∀ i j, kb s(i, j) ≤ min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2 * kbN s(i, j)) :
    (∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) *
      ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Eb, kb e) ≤
      radF lam c * ((∏ e ∈ SmallIntegral.RouteJ.nearForest blk (fun S => (R S).val),
        nearE M lam c e) * ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Eb, kbN e)) := by
  let ρ : ι → ℝ := fun i => rhoD lam (c i)
  have hρ : ∀ i, 0 < ρ i := fun i => rhoD_pos hlam _
  have hroot : ∀ S : β', ∃ i, blk i = S ∧ ∀ j, blk j = S → ρ j ≤ ρ i := by
    intro S
    obtain ⟨i₀, hi₀, _⟩ := hrb S
    obtain ⟨i, hi, hmax⟩ := exists_max_image (univ.filter fun j => blk j = S) ρ
      ⟨i₀, mem_filter.mpr ⟨mem_univ _, hi₀⟩⟩
    exact ⟨i, (mem_filter.mp hi).2, fun j hj => hmax j (mem_filter.mpr ⟨mem_univ _, hj⟩)⟩
  choose root hroot hrootmax using hroot
  let s : β' → ℝ := fun S => ρ (root S)
  have hrbs (S : β') : rb S ≤ s S := by
    obtain ⟨i, hi, hb⟩ := hrb S
    exact hb.trans (hrootmax S i hi)
  have hhatρ : ∀ l, ∃ S ∈ G l, ∀ S' ∈ G l, s S' ≤ s S := by
    intro l
    exact exists_max_image _ _ ⟨hat l, (hhat l).1⟩
  choose hatρ hhatρ hhatρmax using hhatρ
  have hdrop : (∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) ≤
      ∏ l, ∏ S ∈ (G l).erase (hatρ l), s S ^ 2 := by
    apply prod_le_prod₀ (fun l _ => prod_nonneg fun S _ => sq_nonneg _)
    intro l _
    exact (prod_erase_le_prod_erase (fun S _ => sq_nonneg (rb S)) (hhat l).1 (hhatρ l)
      (pow_le_pow_left₀ (hrb0 _) ((hhat l).2 _ (hhatρ l)) 2)).trans
        (prod_le_prod₀ (fun S _ => sq_nonneg _) fun S _ =>
          pow_le_pow_left₀ (hrb0 S) (hrbs S) 2)
  let NT := SmallIntegral.RouteJ.nearForest blk (fun S => (R S).val)
  let A := univ.biUnion Ea
  have hAc : A.card ≤ ∑ l, (Ea l).card := card_biUnion_le
  obtain ⟨hTree, hTE, _, _, _⟩ := SmallIntegral.RouteJ.retained_tree blk
    (fun S => (R S).val) (fun S => (R S).property) A Eb hinter hconn (by omega)
  -- Apply the two radius orderings through radius-allocation API.
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have hcard' : (∑ l, (Ea (e l)).card) + Eb.card + 1 ≤ Fintype.card β' := by
    rw [e.sum_comp (fun l => (Ea l).card)]
    exact hcount
  have hUnion : (univ.biUnion fun l => Ea (e l)) = univ.biUnion Ea := by
    ext q
    simp only [mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨l, hl⟩ => ⟨e l, hl⟩, fun ⟨l, hl⟩ => by
      obtain ⟨l', rfl⟩ := e.surjective l
      exact ⟨l', hl⟩⟩
  obtain ⟨i₀, hmax, halloc⟩ := SmallIntegral.RouteJ.grouped_radius_allocation blk root hroot
    (fun l => G (e l)) (fun l l' h => hGdisj _ _ (fun heq => h (e.injective heq)))
    (fun l => Ea (e l)) Eb (fun l => hEaG (e l)) (fun l => hcardl (e l))
    (by simpa only [hUnion] using hconn) hcard' (fun l => hatρ (e l))
    (fun l => hhatρ (e l)) ρ (fun i => (hρ i).le) hrootmax
    (fun l S hS => hhatρmax (e l) S hS) (fun S => (R S).val)
    (fun S => (R S).property) lam hlam
  have hreg (i : ι) : max (ρ i) lam = ρ i := max_eq_left (le_max_right _ _)
  simp only [hreg] at halloc
  rw [e.prod_comp (fun l => ∏ b ∈ (G l).erase (hatρ l), ρ (root b) ^ 2)] at halloc
  have heqRad' : (∏ i ∈ univ.erase i₀, ρ i ^ 2) = radF lam c := by
    have hRmax : maxRad lam c = ρ i₀ := by
      apply le_antisymm
      · exact (fold_max_le _).mpr ⟨le_max_right _ _, fun i _ => hmax i⟩
      · exact rhoD_le_maxRad lam c i₀
    unfold radF
    simp only [Real.rpow_two]
    rw [hRmax, Real.rpow_neg (hρ i₀).le, Real.rpow_two,
      ← mul_prod_erase univ (fun i => ρ i ^ 2) (mem_univ i₀)]
    field_simp [(hρ i₀).ne']
  rw [heqRad'] at halloc
  let m : Sym2 ι → ℝ := edgeMin sqPos ρ
  have hm (i j : ι) : m s(i, j) = min (ρ i) (ρ j) ^ 2 :=
    sqPos_of_nonneg (le_min (hρ i).le (hρ j).le)
  have hmEq : edgeMin (fun x => max x lam ^ 2) ρ = m := by
    funext q
    induction q using Sym2.ind with
    | h i j =>
      rw [edgeMin_mk, hm, max_eq_left (show lam ≤ min (ρ i) (ρ j) from
        le_min (le_max_right _ _) (le_max_right _ _))]
  rw [hmEq] at halloc
  have hm0 (q : Sym2 ι) : 0 ≤ m q := by
    induction q using Sym2.ind with
    | h i j => rw [hm]; positivity
  have hn0 : 0 ≤ ∏ q ∈ NT, nearE M lam c q := prod_nonneg fun q _ => nearE_nonneg M lam c q
  have hnear : (∏ q ∈ NT, m q) * ∏ q ∈ NT, nearE M lam c q = 1 := by
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro q hq
    induction q using Sym2.ind with
    | h i j =>
      rw [hm]
      change min (ρ i) (ρ j) ^ 2 * nearW M lam (c i) (c j) = 1
      unfold nearW
      rw [ite_eq_left (show dipoleDist (c i) (c j) ≤
        M * min (rhoD lam (c i)) (rhoD lam (c j)) from hR i j hq)]
      change min (ρ i) (ρ j) ^ 2 * (1 / min (ρ i) (ρ j) ^ 2) = 1
      field_simp [(lt_min (hρ i) (hρ j)).ne']
  have hrad : (∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) * ∏ q ∈ Eb, m q ≤
      radF lam c * ∏ q ∈ NT, nearE M lam c q := by
    calc
      _ = ((∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) * ∏ q ∈ Eb, m q) *
          ((∏ q ∈ NT, m q) * ∏ q ∈ NT, nearE M lam c q) := by rw [hnear, mul_one]
      _ ≤ radF lam c * ∏ q ∈ NT, nearE M lam c q := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ hn0
        exact (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hdrop (prod_nonneg fun q _ => hm0 q))
          (prod_nonneg fun q _ => hm0 q)).trans halloc
  have hkbprod : (∏ q ∈ Eb, kb q) ≤ (∏ q ∈ Eb, m q) * ∏ q ∈ Eb, kbN q := by
    rw [← prod_mul_distrib]
    apply prod_le_prod₀ (fun q _ => hkb q)
    intro q _
    induction q using Sym2.ind with
    | h i j => rw [hm]; exact hkbb i j
  have hmain : (∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) *
      ((∏ q ∈ A, ka q) * ∏ q ∈ Eb, kb q) ≤
      radF lam c * ((∏ q ∈ NT, nearE M lam c q) *
        ((∏ q ∈ A, ka q) * ∏ q ∈ Eb, kbN q)) := by
    calc
      _ ≤ (∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) *
          ((∏ q ∈ A, ka q) * ((∏ q ∈ Eb, m q) * ∏ q ∈ Eb, kbN q)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hkbprod (prod_nonneg fun q _ => hka q))
          (prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _)
      _ = ((∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) * ∏ q ∈ Eb, m q) *
          ((∏ q ∈ A, ka q) * ∏ q ∈ Eb, kbN q) := by ring
      _ ≤ (radF lam c * ∏ q ∈ NT, nearE M lam c q) *
          ((∏ q ∈ A, ka q) * ∏ q ∈ Eb, kbN q) :=
        mul_le_mul_of_nonneg_right hrad (mul_nonneg (prod_nonneg fun q _ => hka q)
          (prod_nonneg fun q _ => hkbN q))
      _ = _ := by ring
  exact hmain

open scoped Classical in
/-- **The radii of the trees** (eq. (A.67), pointwise form. See the module docstring). -/
theorem core_le_sum_tree (hlam : 0 < lam) (blk : ι → β') (c : ι → ℂ × ℂ)
    (hB : ∀ S, ((nearGraph M lam c).induce {i | blk i = S}).Connected)
    {κ : Type*} [Fintype κ] (Ea : κ → Finset (Sym2 ι)) (G : κ → Finset β')
    (hGdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l'))
    (hEaG : ∀ l, ∀ e ∈ Ea l, ∀ i ∈ e, blk i ∈ G l)
    (hcardl : ∀ l, (Ea l).card + 1 = (G l).card)
    (Eb : Finset (Sym2 ι))
    (hinter : ∀ e ∈ univ.biUnion Ea ∪ Eb, ¬ (Sym2.map blk e).IsDiag)
    (hconn : ∀ i j : ι, (sameBlockGraph blk ⊔
      fromEdgeSet ((univ.biUnion Ea ∪ Eb : Finset (Sym2 ι)) : Set (Sym2 ι))).Reachable i j)
    (hcount : (∑ l, (Ea l).card) + Eb.card + 1 ≤ Fintype.card β')
    (rb : β' → ℝ) (hrb0 : ∀ S, 0 ≤ rb S)
    (hrb : ∀ S, ∃ i, blk i = S ∧ rb S ≤ rhoD lam (c i))
    (hat : κ → β') (hhat : ∀ l, hat l ∈ G l ∧ ∀ S ∈ G l, rb S ≤ rb (hat l))
    (ka kb kbN : Sym2 ι → ℝ) (hka : ∀ e, 0 ≤ ka e) (hkb : ∀ e, 0 ≤ kb e)
    (hkbN : ∀ e, 0 ≤ kbN e)
    (hkbb : ∀ i j, kb s(i, j) ≤ min (rhoD lam (c i)) (rhoD lam (c j)) ^ 2 * kbN s(i, j)) :
    (∏ l, ∏ S ∈ (G l).erase (hat l), rb S ^ 2) *
      ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Eb, kb e) ≤
      ∑ NT ∈ (intraE blk).powerset,
        if (fromEdgeSet ((NT ∪ (univ.biUnion Ea ∪ Eb) : Finset (Sym2 ι)) :
            Set (Sym2 ι))).IsTree then
          radF lam c * ((∏ e ∈ NT, nearE M lam c e) *
            ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Eb, kbN e))
        else 0 := by
  obtain ⟨R, hR⟩ := SmallIntegral.RouteJ.exists_linked_nearTreeFamily blk M lam c hB
  have hmain := core_le_fixed_nearTree hlam blk c R hR Ea G hGdisj hEaG hcardl Eb
    hinter hconn hcount rb hrb0 hrb hat hhat ka kb kbN hka hkb hkbN hkbb
  let NT := SmallIntegral.RouteJ.nearForest blk (fun S => (R S).val)
  have hAc : (univ.biUnion Ea).card ≤ ∑ l, (Ea l).card := card_biUnion_le
  obtain ⟨hTree, _⟩ := SmallIntegral.RouteJ.retained_tree blk
    (fun S => (R S).val) (fun S => (R S).property) (univ.biUnion Ea) Eb
    hinter hconn (by omega)
  have hNT : NT ∈ (intraE blk).powerset := by
    rw [mem_powerset]
    intro q hq
    obtain ⟨b, q', hq', rfl⟩ := (SmallIntegral.RouteJ.mem_nearForest blk
      (fun S => (R S).val) q).mp hq
    induction q' using Sym2.ind with
    | h i j =>
      rw [Sym2.map_mk]
      exact mem_filter.mpr ⟨mem_univ _, by
        rw [Sym2.map_mk, Sym2.mk_isDiag_iff, Sym2.mk_isDiag_iff]
        exact ⟨i.property.trans j.property.symm,
          fun h => (R b).val.ne_of_adj (mem_edgeFinset.mp hq') (Subtype.ext h)⟩⟩
  refine hmain.trans ?_
  refine le_trans (le_of_eq ?_) (single_le_sum (fun q _ => ?_) hNT)
  · exact (ite_eq_left hTree).symm
  · split_ifs
    · exact mul_nonneg (radF_nonneg hlam c) (mul_nonneg
        (prod_nonneg fun e _ => nearE_nonneg M lam c e)
        (mul_nonneg (prod_nonneg fun e _ => hka e) (prod_nonneg fun e _ => hkbN e)))
    · exact le_rfl

end AbsoluteLower

end MultipoleBKT

end
