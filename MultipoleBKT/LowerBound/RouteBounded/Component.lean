/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.RouteHalfSum.Graph
public import MultipoleBKT.LowerBound.BoundedLowerEps.Bonds
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Definitions

/-!
# Half-sum ears for one hatted odd component

The proof of Proposition 4.23, using the proof of (A.30) in the proof of Lemma A.5.
Enlarge the actual positive radii to block maxima, start at a maximal block,
and apply the endpoint half-sum on ordinary ears. The longest edge of the
whole ear family supplies the single exceptional deletion and tail.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open Finset SimpleGraph Hierarchical Multipole Parity Peeling Limits SmallIntegral
open UpperBound.BoundedUpper
open scoped Classical

/-- The hatted odd weight retains the unlinked indicator. -/
noncomputable def hatOdd (M lam : ℝ) (z : ℂ × ℂ) (w : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam z w then 0 else ahat z w

/-- Internal component estimate by the half-sum ear argument. The radii are
positive on the configuration under consideration. Cut parity supplies ears
through the maximal-radius block, and only the globally longest edge receives
an exceptional deletion.
proof of Proposition 4.23,
and (A.30) in the proof of Lemma A.5. -/
theorem component_bound_of_pair_bounds {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {M lam : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    {G : SimpleGraph (Y.biUnion id)} (hG : IsRelEulerianConnected Y G)
    (hcut : CutEven (Sym2.map (Limits.blockOf Y)) G.edgeFinset)
    (z : Y.biUnion id → ℂ × ℂ) (hz : ∀ i, 0 < dipoleLength (z i))
    {A : Sym2 (Y.biUnion id) → ℝ}
    (hA0 : ∀ e, 0 ≤ A e) {C : ℝ} (hC : 1 ≤ C)
    (hA : ∀ i j, G.Adj i j → A s(i, j) ≤ C * hatOdd M lam (z i) (z j))
    {Ŝ : Y} (hŜ : ∀ S, blockRadius hY (fun i => dipoleLength (z i)) S ≤
      blockRadius hY (fun i => dipoleLength (z i)) Ŝ) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧
      ∏ e ∈ G.edgeFinset, A e ≤ C ^ G.edgeFinset.card *
        (∏ S ∈ univ.erase Ŝ, blockRadius hY (fun i => dipoleLength (z i)) S ^ 2) *
        ((∏ e ∈ T.edgeFinset, keptE M lam z e) *
          treeTail (dipoleDistOn z) T (blockRadius hY (fun i => dipoleLength (z i)) Ŝ)) := by
  let s : Y → ℝ := blockRadius hY (fun i => dipoleLength (z i))
  let R := s Ŝ
  let ends := Sym2.map (Limits.blockOf Y)
  let d := dipoleDistOn z
  let a := fun e => A e / C
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hs : ∀ S, 0 < s S := by
    intro S
    obtain ⟨i, hi⟩ := hY.1 S S.2
    let v : Y.biUnion id := ⟨i, subset_biUnion_of_mem id S.2 hi⟩
    have hb : MultipoleBKT.blockOf hY v = S := (MultipoleBKT.blockOf_eq_iff hY).2 hi
    exact (hz v).trans_le (by simpa only [hb, s, dipoleLength] using le_blockRadius (fun i => dipoleLength (z i)) v)
  have hR : 0 < R := hs Ŝ
  have hrad0 : 0 ≤ ∏ S ∈ univ.erase Ŝ, s S ^ 2 := prod_nonneg fun S _ => sq_nonneg _
  by_cases hprod : 0 < ∏ e ∈ G.edgeFinset, A e
  swap
  · obtain ⟨T, -, hT⟩ := exists_isRelTree₀_le hY hG.1.1 hG.1.2.2
    have hT' : IsRelTree Y T := by
      rcases hT with hT | ⟨hcard, -⟩
      · exact hT
      · exact False.elim ((isRelConnected_iff.1 hG.1).2 hcard)
    refine ⟨T, hT', (le_of_not_gt hprod).trans ?_⟩
    exact mul_nonneg (mul_nonneg (pow_nonneg hCpos.le _) hrad0)
      (mul_nonneg (prod_nonneg fun e _ => keptE_nonneg _ e) (sq_nonneg _))
  have hapos : ∀ e ∈ G.edgeFinset, 0 < A e := by
    intro e he
    exact lt_of_le_of_ne (hA0 e) (Ne.symm (fun hz => hprod.ne' (prod_eq_zero he hz)))
  have hfar : ∀ i j, G.Adj i j → ¬ MultipoleLinked M lam (z i) (z j) := by
    intro i j hij hl
    have hb := hA i j hij
    rw [hatOdd, ite_eq_left hl, mul_zero] at hb
    exact (hapos s(i, j) (by simpa using hij)).not_ge hb
  obtain ⟨Cb, -, hbonds⟩ := exists_bond_bounds hχ (le_refl (0 : ℝ))
  have hd : ∀ e ∈ G.edgeFinset, 0 < d e := by
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      have hij : G.Adj i j := by simpa using he
      exact hlam.trans (hbonds lam hlam M hM (z i) (z j) (hfar i j hij)).1
  have ha0 : ∀ e ∈ G.edgeFinset, 0 ≤ a e := fun e _ => div_nonneg (hA0 e) hCpos.le
  have hale : ∀ i j, G.Adj i j → a s(i, j) ≤ ahat (z i) (z j) := by
    intro i j hij
    apply (div_le_iff₀ hCpos).2
    simpa only [hatOdd, ite_eq_right (hfar i j hij), mul_comm] using hA i j hij
  have ha1 : ∀ e ∈ G.edgeFinset, a e ≤ 1 := by
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      have hij : G.Adj i j := by simpa using he
      exact (hale i j hij).trans (BoundedLowerEps.ahat_le_one_of_not_linked hχ hlam hM (hfar i j hij))
  have hloop : ∀ e ∈ G.edgeFinset, ¬ (ends e).IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      have hij : G.Adj i j := by simpa using he
      have hb (i : Y.biUnion id) : Limits.blockOf Y i = MultipoleBKT.blockOf hY i :=
        Limits.blockOf_eq hY (MultipoleBKT.blockOf hY i).2 (MultipoleBKT.mem_blockOf hY i)
      apply Sym2.mk_isDiag_iff.not.2
      change Limits.blockOf Y i ≠ Limits.blockOf Y j
      rw [hb i, hb j]
      exact crossBlockGraph_adj.1 ((interEdges_eq hY ▸ hG.1.1) hij)
  have hreach : ∀ S, (nodeGraph ends G.edgeFinset).Reachable Ŝ S := by
    rw [show nodeGraph ends G.edgeFinset = quotientGraph Y G from RouteHalfSum.nodeGraph_eq_quotient hY G]
    exact ((connected_sup_intraEdges_iff hY).1 hG.1.2.2).preconnected Ŝ
  have hgeom : ∀ e ∈ G.edgeFinset, ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w))) := by
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      have hij : G.Adj i j := by simpa using he
      have hb (i : Y.biUnion id) : Limits.blockOf Y i = MultipoleBKT.blockOf hY i :=
        Limits.blockOf_eq hY (MultipoleBKT.blockOf hY i).2 (MultipoleBKT.mem_blockOf hY i)
      have hg : a s(i, j) ≤ s (Limits.blockOf Y i) * s (Limits.blockOf Y j) /
          (d s(i, j) * max (d s(i, j)) (max (s (Limits.blockOf Y i)) (s (Limits.blockOf Y j)))) := by
        apply (hale i j hij).trans
        change ahat (z i) (z j) ≤ _
        unfold ahat
        exact div_mul_max_le (norm_nonneg _) (norm_nonneg _)
          (by simpa only [hb, s, dipoleLength] using le_blockRadius (fun i => dipoleLength (z i)) i)
          (by simpa only [hb, s, dipoleLength] using le_blockRadius (fun i => dipoleLength (z i)) j)
          (hd s(i, j) he)
      intro v w hvw
      change s(Limits.blockOf Y i, Limits.blockOf Y j) = s(v, w) at hvw
      rcases Sym2.eq_iff.1 hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hg
      · simpa only [mul_comm (s (Limits.blockOf Y i)), max_comm (s (Limits.blockOf Y i))] using hg
  -- The forest lemma keeps the literal endpoint averages on ordinary ears.
  -- Its only exceptional deletion is the longest edge of the whole ear family.
  obtain ⟨F, hFG, hcard, hr, hbound⟩ := odd_forest_singleTail ends hloop hcut {Ŝ}
    (fun S => ⟨Ŝ, mem_singleton_self _, hreach S⟩) s hs
    (fun e _ v _ => hŜ v) d a hd ha0 ha1 hgeom
  have hcard' : F.card + 1 = Fintype.card Y := by
    rw [sdiff_singleton_eq_erase, card_erase_of_mem (mem_univ Ŝ), card_univ] at hcard
    have : Nonempty Y := ⟨Ŝ⟩
    have := Fintype.card_pos (α := Y)
    omega
  obtain ⟨T, hTF⟩ : ∃ T : SimpleGraph (Y.biUnion id),
      T = fromEdgeSet (F : Set (Sym2 (Y.biUnion id))) := ⟨_, rfl⟩
  have heq : T.edgeFinset = F := by
    subst T
    exact RouteHalfSum.edgeFinset_from_subset hFG
  have hT : IsRelTree Y T := by
    subst T
    exact RouteHalfSum.isRelTree_of_ear_edges hY hG.1 hFG Ŝ
      (fun S => by
        obtain ⟨v, hv, hr⟩ := hr S
        simpa only [mem_singleton.1 hv] using hr) hcard'
  have hkept : ∏ e ∈ F, (d e ^ 2)⁻¹ = ∏ e ∈ T.edgeFinset, keptE M lam z e := by
    rw [heq]
    apply prod_congr rfl
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      have hij : G.Adj i j := by simpa using hFG he
      simp only [keptE, symmLift_mk, ite_eq_right (hfar i j hij), d, dipoleDistOn_mk]
  have htail : globalTail R d F ≤ treeTail d T R := by
    have hb := RouteHalfSum.globalTail_le_treeTail d (dipoleDistOn_nonneg z) T hR
    simpa only [heq] using hb
  rw [sdiff_singleton_eq_erase] at hbound
  refine ⟨T, hT, ?_⟩
  have hscale : ∏ e ∈ G.edgeFinset, A e = C ^ G.edgeFinset.card * ∏ e ∈ G.edgeFinset, a e := by
    dsimp only [a]
    rw [prod_div_distrib, prod_const]
    exact (mul_div_cancel₀ _ (pow_ne_zero _ hCpos.ne')).symm
  rw [hscale]
  have hb := hbound.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail hrad0) (prod_nonneg fun e _ => inv_nonneg.2 (sq_nonneg _)))
  rw [hkept] at hb
  simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hb (pow_nonneg hCpos.le _)

end MultipoleBKT.LowerBound.RouteBounded

end
