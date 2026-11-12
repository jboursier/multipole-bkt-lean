/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.BlockBounds

/-!
# Integrability of the full block average after merging near parts

See Lemma 4.26 of the paper. Expand near and far bonds, merge parts along the near bonds,
apply parity on the merged quotient, and integrate the separate tree majorants.
The subgroup identity then recovers the specified original block average.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph SmallIntegral
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [LinearOrder I] [Nonempty I]
  [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- Each merged term is integrable by parity, the separate odd and even trees,
logarithmic spatial integration, and the final power absorption. -/
theorem integrable_anchor_blockAverage (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hconn : (E ⊔ sameBlockGraph blk).Connected)
    {F : Finset (Sym2 I)} (hF : F ⊆ E.edgeFinset) (root : I) :
    Integrable fun c => anchorR root c * blockAverage χ β lam M blk E F c := by
  obtain ⟨Cw, hCw, hw⟩ := exists_abs_blockTermWeight_le_uniform (β := β) hχ (by linarith) blk E
  apply integrable_anchor_of_parity_bound hχ hβ hlam hM hk (mergedOf blk E F)
    (fun C => C.exists_rep) (mergedInter blk E F) (fun _ _ h => h.2)
    (mergedInter_reachable blk E F hconn) root (measurable_blockAverage hχ hlam blk E F) hCw
  intro c
  refine (abs_blockAverage_le hχ hM blk hblk E hF c).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right (hw lam hlam M F hF c)
      (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le)
  · exact sum_nonneg fun A _ => mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _)
      (prod_nonneg fun _ _ => abs_nonneg _)

/-- The full specified average is integrable, with the original blocks kept
in the conclusion. The merger only occurs inside each near/far term. -/
theorem integrable_anchor_symBox_merged (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hconn : (E ⊔ sameBlockGraph blk).Connected) (root : I) :
    Integrable fun c => anchorR root c * symBox χ β lam M blk E c := by
  have hint : ∀ F ∈ E.edgeFinset.powerset,
      Integrable fun c => anchorR root c * reversalAverage blk (blockAverage χ β lam M blk E F) c := by
    intro F hF
    exact integrable_anchor_reversalAverage blk root (measurable_blockAverage hχ hlam blk E F)
      (blockAverage_translate blk E F)
      (integrable_anchor_blockAverage hχ hβ hlam hM hk blk hblk E hconn (mem_powerset.mp hF) root)
  have h := integrable_finsetSum _ hint
  convert h using 1
  ext c
  rw [symBox_eq_sum_blockAverage hχ hM blk hblk E, Finset.mul_sum]

omit [LinearOrder I] [Fintype B] [DecidableEq B] in
/-- Connectedness of the graph augmented by original blocks, expressed using
the edge-labelled quotient interface of the limiting-integral API. -/
theorem connected_augmented_of_nodeGraph (blk : I → B) (E : SimpleGraph I)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b') :
    (E ⊔ sameBlockGraph blk).Connected := by
  have hle : nodeGraph (Sym2.map blk) E.edgeFinset ≤ blockQuotient blk E := by
    intro b b' h
    obtain ⟨hne, e, he, hab⟩ := nodeGraph_adj.mp h
    induction e using Sym2.ind with
    | h i j =>
      rw [Sym2.map_mk, Sym2.eq_iff] at hab
      rcases hab with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · exact blockQuotient_adj.mpr ⟨hne, i, j, hi, hj, mem_edgeFinset.mp he⟩
      · exact blockQuotient_adj.mpr ⟨hne, j, i, hj, hi, (mem_edgeFinset.mp he).symm⟩
  exact ⟨fun i j => reachable_of_reachable_blockQuotient ((hconn (blk i) (blk j)).mono hle) rfl rfl⟩

omit [Nonempty I] in
/-- The written block average is integrable by the retained-tail logarithmic
route. This theorem keeps the original block average in its conclusion. -/
theorem integrable_anchor_symBox_log [decI : DecidableEq I] (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 1 ≤ M) [Nonempty I]
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (_hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b') (root : I) :
    Integrable fun c => anchorR root c * symBox χ β lam M blk E c := by
  cases Subsingleton.elim decI (inferInstance : LinearOrder I).toDecidableEq
  exact integrable_anchor_symBox_merged hχ hβ hlam hM hk blk hblk E
    (connected_augmented_of_nodeGraph blk E hconn) root

end MultipoleBKT.Limits.RouteDirect

end
