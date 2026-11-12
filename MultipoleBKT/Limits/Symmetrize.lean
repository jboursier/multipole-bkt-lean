/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.EdgeWeights

/-!
# The symmetrized multipole integrand

See equation (4.50) and the paragraph
 of the proof of Lemma 4.26.

Labels `ι` are grouped into blocks by `blk : ι → β`. For a set of blocks `A`, `flipCfg` reverses
the dipoles of the blocks in `A`. For an edge set `E` between distinct blocks, the product of the
bonds `∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)` at the reversed configuration is
`∏_{e ∈ E} (α_e + σ_e(A) γ_e)` (`prod_unlinkedBond_flip`), so that its average over the
`2^{|β|}` reversal sets is bounded by `∑_{F ⊆ E cut-even} ∏_{E \ F} |α_e| ∏_F |γ_e|`
(`abs_avg_prod_le`, in `MultipoleBKT.Limits.Reversal`).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset
open scoped ENNReal

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Pairs

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A symmetric function of pairs of labels, as a function of unordered pairs. -/
def symmLift (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) : Sym2 ι → ℝ :=
  Sym2.lift ⟨f, hf⟩

omit [Fintype ι] [LinearOrder ι] in
theorem symmLift_mk (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) (i j : ι) :
    symmLift f hf s(i, j) = f i j := rfl

/-- `∏_{i<j, ij ∈ E} f i j = ∏_{e ∈ E} f e` for symmetric `f`. -/
theorem prod_prod_ite_lt_adj (E : SimpleGraph ι) [DecidableRel E.Adj] (f : ι → ι → ℝ)
    (hf : ∀ i j, f i j = f j i) :
    ∏ i, ∏ j, (if i < j ∧ E.Adj i j then f i j else 1) =
      ∏ e ∈ E.edgeFinset, symmLift f hf e := by
  classical
  set P : Finset (ι × ι) :=
    (Finset.univ ×ˢ Finset.univ : Finset (ι × ι)).filter fun p => p.1 < p.2 ∧ E.Adj p.1 p.2
  have h1 : ∏ i, ∏ j, (if i < j ∧ E.Adj i j then f i j else 1) = ∏ p ∈ P, f p.1 p.2 := by
    rw [Finset.prod_filter, Finset.prod_product]
  have hinj : Set.InjOn (fun p : ι × ι => s(p.1, p.2)) P := by
    intro p hp q hq hpq
    simp only [P, coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      rw [h1, h2] at hp
      exact lt_asymm hp.1 hq.1
  have himg : P.image (fun p : ι × ι => s(p.1, p.2)) = E.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [P, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Prod.exists]
      constructor
      · rintro ⟨x, y, ⟨hxy, hadj⟩, he⟩
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
      · intro hab
        rcases lt_trichotomy a b with h | h | h
        · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
        · exact absurd h (E.ne_of_adj hab)
        · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
  rw [h1, ← himg, Finset.prod_image hinj]
  rfl

end Pairs

section Flip

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

/-- The labels of the blocks in `A`. -/
def blockLabels (blk : ι → β') (A : Finset β') : Finset ι := univ.filter fun i => blk i ∈ A

omit [DecidableEq ι] [LinearOrder ι] [Fintype β'] in
theorem mem_blockLabels {blk : ι → β'} {A : Finset β'} {i : ι} :
    i ∈ blockLabels blk A ↔ blk i ∈ A := by simp [blockLabels]

/-- The even part `α` as a function of unordered pairs of labels. -/
noncomputable def alphaE (hχ : IsMollifier χ) (β lam M : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => edgeAlpha χ β lam M (c i) (c j)) fun i j => by
    unfold edgeAlpha
    rw [dipoleInteraction_comm hχ]
    congr 1
    exact propext multipoleLinked_comm

/-- The odd part `γ` as a function of unordered pairs of labels. -/
noncomputable def gammaE (hχ : IsMollifier χ) (β lam M : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => edgeGamma χ β lam M (c i) (c j)) fun i j => by
    unfold edgeGamma
    rw [dipoleInteraction_comm hχ]
    congr 1
    exact propext multipoleLinked_comm

theorem unlinkedPairWeight_comm (hχ : IsMollifier χ) (d e : ℂ × ℂ) :
    unlinkedPairWeight χ β lam M d e = unlinkedPairWeight χ β lam M e d := by
  unfold unlinkedPairWeight
  rw [dipoleInteraction_comm hχ]
  congr 1
  exact propext multipoleLinked_comm

omit [Fintype β'] in
/-- **The bonds at a reversed configuration**: reversing the blocks in `A`,
`∏_{i<j ∈ E} (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1) = ∏_{e ∈ E} (α_e + σ_e(A) γ_e)`. -/
theorem prod_unlinkedBond_flip (hχ : IsMollifier χ) (blk : ι → β') (E : SimpleGraph ι)
    [DecidableRel E.Adj] (c : ι → ℂ × ℂ) (A : Finset β') :
    ∏ i, ∏ j, (if i < j ∧ E.Adj i j then
        unlinkedPairWeight χ β lam M (flipCfg (blockLabels blk A) c i)
          (flipCfg (blockLabels blk A) c j) - 1 else 1) =
      ∏ e ∈ E.edgeFinset, (alphaE hχ β lam M c e +
        signCross (Sym2.map blk) A e * gammaE hχ β lam M c e) := by
  rw [prod_prod_ite_lt_adj E _ fun i j => by rw [unlinkedPairWeight_comm hχ]]
  refine Finset.prod_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | h i j =>
    rw [symmLift_mk, flipCfg_apply, flipCfg_apply]
    simp only [mem_blockLabels]
    rw [unlinkedBond_flip hχ (c i) (c j) (blk i ∈ A) (blk j ∈ A)]
    simp only [alphaE, gammaE, symmLift_mk, signCross, Sym2.map_mk, crosses_mk]
    congr 2
    by_cases hi : blk i ∈ A <;> by_cases hj : blk j ∈ A <;> simp [hi, hj]

end Flip

end Limits

end MultipoleBKT

end
