/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.TreeIntegral

/-!
# The finite retained-tree majorant for a parity average

See Lemma A.5 of the paper. The odd and even trees are constructed separately. Their pointwise choices
are enlarged to a finite sum before any spatial integration.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph
open SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [LinearOrder I] [Nonempty I]
  [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- All retained near/odd/even decompositions of a tree on the labels. -/
noncomputable def mixedTrees (I : Type*) [Fintype I] [DecidableEq I] :
    Finset (SimpleGraph I × Finset (Sym2 I) × Finset (Sym2 I) × Finset (Sym2 I)) :=
  univ.filter fun t => t.1.IsTree ∧ t.2.2.1 ∪ (t.2.2.2 ∪ t.2.1) = t.1.edgeFinset ∧
    Disjoint t.2.2.1 (t.2.2.2 ∪ t.2.1) ∧ Disjoint t.2.2.2 t.2.1

/-- The finite sum that removes all configuration-dependent tree choices. -/
noncomputable def mixedTreeSum (χ : ℂ → ℝ) (β lam M : ℝ) (c : I → ℂ × ℂ) : ℝ≥0∞ :=
  ∑ t ∈ mixedTrees I, limitingTreeTerm χ β lam M t.2.1 t.2.2.1 t.2.2.2 c

/-- The finite retained-tree sum is integrable once the translation is fixed. -/
theorem lintegral_mixedTreeSum_lt_top (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (root : I) :
    ∫⁻ c, anchor root c * mixedTreeSum χ β lam M c < ∞ := by
  unfold mixedTreeSum
  simp_rw [Finset.mul_sum]
  have hm (t : SimpleGraph I × Finset (Sym2 I) × Finset (Sym2 I) × Finset (Sym2 I)) :
      Measurable (fun c => anchor root c * limitingTreeTerm χ β lam M t.2.1 t.2.2.1 t.2.2.2 c) :=
    (measurable_anchor root).mul (measurable_limitingTreeTerm hχ hlam t.2.1 t.2.2.1 t.2.2.2)
  rw [lintegral_finsetSum _ fun t _ => hm t]
  apply ENNReal.sum_lt_top.mpr
  intro t ht
  obtain ⟨hT, hpart, hA, hB⟩ := (mem_filter.mp ht).2
  exact lintegral_limitingTreeTerm_lt_top hχ hβ hlam hM hk t.1 hT t.2.1 t.2.2.1 t.2.2.2
    hpart hA hB root

/-- The single-tail majorant is dominated by the finite mixed-tree sum.
The coefficient precedes λ and M, so subsequent integration preserves uniformity. -/
theorem exists_parity_term_le_mixedTreeSum (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b') :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, 1 ≤ M →
      ∀ F : Finset (Sym2 I), F ⊆ E.edgeFinset → CutEven (Sym2.map blk) F →
      ∀ c : I → ℂ × ℂ,
      (∀ b, ((nearGraph M lam c).induce {i | blk i = b}).Connected) →
      ENNReal.ofReal ((∏ i, pairDensity χ β lam (c i)) *
        ((∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e|)) ≤
          ENNReal.ofReal C * mixedTreeSum χ β lam M c := by
  obtain ⟨C, hC, hb⟩ := exists_paper_majorant (ι := I) (κ := B) hχ hβ
  refine ⟨C ^ E.edgeFinset.card, pow_pos (zero_lt_one.trans_le hC) _,
    fun lam hlam M hM F hFE hcut c hnear => ?_⟩
  have hBne : Nonempty B := Nonempty.map blk inferInstance
  have hconn' : (nodeGraph (Sym2.map blk) E.edgeFinset).Connected :=
    (connected_iff _).mpr ⟨hconn, hBne⟩
  obtain ⟨rep, root, NT, A, Bf, hrep, hmax, hroot, hgroup, hNT, hAF, hBE, hdisj,
    htree, hAT, hBT, hAc, hBc, hNTc, hprod, hbound⟩ :=
      hb lam hlam M hM blk hblk E hinter hconn' F hFE hcut c hnear
  let Q := nodeGraph (Sym2.map blk) F
  let : Fintype Q.ConnectedComponent := Fintype.ofFinite _
  have hgroup' (b : B) : rhoD lam (c (rep b)) ≤
      rhoD lam (c (rep (root (Q.connectedComponentMk b)))) := hgroup _ b rfl
  have hnorm := paperTreeMajorant_le_profile hlam hM blk rep hrep Q.connectedComponentMk root hroot
    c hmax hgroup' NT A Bf hprod hBT (by simpa only [Nat.card_eq_fintype_card] using hBc)
  let U := NT ∪ (A ∪ Bf)
  let T := nodeGraph id U
  have hloop (e : Sym2 I) (he : e ∈ U) : ¬e.IsDiag := by
    induction e using Sym2.ind with
    | h i j =>
      apply Sym2.mk_isDiag_iff.not.mpr
      rcases mem_union.mp he with he | he
      · exact (hNT i j he).1
      · have heE : s(i, j) ∈ E.edgeFinset :=
          (Finset.union_subset (hAF.trans hFE) (hBE.trans Finset.sdiff_subset)) he
        exact (mem_edgeFinset.mp heE).ne
  have hTE : T.edgeFinset = U := by
    ext e
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeFinset]
      change (nodeGraph id U).Adj i j ↔ s(i, j) ∈ U
      rw [nodeGraph_adj]
      constructor
      · rintro ⟨_, e, he, rfl⟩
        exact he
      · intro he
        exact ⟨Sym2.mk_isDiag_iff.not.mp (hloop _ he), s(i, j), he, rfl⟩
  have hAB : Disjoint A Bf := disjoint_of_subset_left hAF
    (disjoint_of_subset_right hBE disjoint_sdiff_self_right)
  have hNTA : Disjoint NT A := (disjoint_union_right.mp hdisj).1
  have hNTB : Disjoint NT Bf := (disjoint_union_right.mp hdisj).2
  have hmem : (T, NT, A, Bf) ∈ mixedTrees I := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, htree, ?_, disjoint_union_right.mpr ⟨hAB, hNTA.symm⟩, hNTB.symm⟩
    rw [hTE]
    ext e
    simp only [U, Finset.mem_union]
    tauto
  have hsingle : limitingTreeTerm χ β lam M NT A Bf c ≤ mixedTreeSum χ β lam M c :=
    single_le_sum (f := fun t => limitingTreeTerm χ β lam M t.2.1 t.2.2.1 t.2.2.2 c)
      (fun _ _ => bot_le) hmem
  have hpd : 0 ≤ ∏ i, pairDensity χ β lam (c i) := prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
  calc
    _ ≤ ENNReal.ofReal ((∏ i, pairDensity χ β lam (c i)) *
        (C ^ E.edgeFinset.card * paperTreeMajorant M lam c (fun b => rhoD lam (c (rep b))) root NT A Bf)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hbound hpd)
    _ = ENNReal.ofReal (C ^ E.edgeFinset.card) * ENNReal.ofReal (∏ i, pairDensity χ β lam (c i)) *
        ENNReal.ofReal (paperTreeMajorant M lam c (fun b => rhoD lam (c (rep b))) root NT A Bf) := by
      rw [ENNReal.ofReal_mul hpd, ENNReal.ofReal_mul (pow_nonneg (zero_le_one.trans hC) _)]
      ring
    _ ≤ ENNReal.ofReal (C ^ E.edgeFinset.card) * limitingTreeTerm χ β lam M NT A Bf c := by
      unfold limitingTreeTerm
      rw [ENNReal.ofReal_mul hpd]
      exact (mul_le_mul_right hnorm _).trans_eq (by ring)
    _ ≤ _ := mul_le_mul_right hsingle _

end MultipoleBKT.Limits.RouteDirect

end
