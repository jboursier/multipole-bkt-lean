/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.LemmaA6Bridge

/-!
# Integrating the replacement-tree families through the hatted J bound

The paper: Proposition 5.18, and Lemma A.4.
The tree and tail integrand is bounded by the hatted integral. The
logarithmic integration supplies the bound without a small-power replacement.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset SimpleGraph Hierarchical Parity Quadratic Peeling Multipole SetPartition
open scoped Classical NNReal ENNReal

variable {χ : ℂ → ℝ}

/-- The bounded-cluster integration input from the hatted logarithmic estimate of Lemma A.4. -/
theorem lemmaA6J_source_holds (hχ : IsMollifier χ) {β : ℝ} (hβ : 2 < β) (p₀ : ℕ) {M ε₀ : ℝ}
    (hM : 1 ≤ M) (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) : LemmaA6J χ p₀ β M ε₀ := by
  intro k _
  obtain ⟨C, hC, hA6⟩ := SmallIntegral.lemma_A6_hat hχ hβ k hM hε₀ hε₁
  refine ⟨C, hC, Appendix.lamBound ε₀ k, Appendix.lamBound_pos hε₀ k, fun lam hlam hlt =>
    ⟨0, fun N _ X hX h2 hXk n Xs hXs hdisj Ta hTa Tb hTb => ?_⟩⟩
  -- a selection of the blocks of largest radius
  have hex : ∀ (l : Fin n) (z : X.biUnion id → ℂ × ℂ), ∃ S : X,
      S ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S' ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (z i)) S' ≤
          blockRadius hX (fun i => dipoleLength (z i)) S := by
    intro l z
    have hne : ((Xs l).subtype (· ∈ X)).Nonempty := by
      obtain ⟨e, -⟩ := (hTa l).1.2.1
      induction e using Sym2.ind with
      | h i j =>
        obtain ⟨B, hB, -⟩ := mem_biUnion_id.1 i.2
        exact ⟨⟨B, hXs l hB⟩, Finset.mem_subtype.2 hB⟩
    obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image _
      (fun S => blockRadius hX (fun i => dipoleLength (z i)) S) hne
    exact ⟨S, hS, hmax⟩
  choose hatS hhat using hex
  have hW : (coarsen X (Finset.univ.image Xs)).biUnion id = X.biUnion id :=
    biUnion_coarsen fun Y hY => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
      exact hXs l
  have hle : jIntegral M lam ε₀ (truncationScale p₀ β lam) χ N β X Xs Ta Tb ≤
      SmallIntegral.integralJ χ β lam M ε₀ p₀ N hX Xs (fun l => Multipole.edgesOf (Ta l))
        (Multipole.edgesOf Tb) hatS := by
    unfold jIntegral SmallIntegral.integralJ Limits.boxConfig
    exact lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (jFullIntegrand_le_integrandJ p₀ hX Xs hXs hdisj Ta Tb hW hatS (fun l z => hhat l z) y)
  have hhatle := SmallIntegral.integralJ_le_hatJ (χ := χ) (β := β) (lam := lam)
    (M := M) (ε₀ := ε₀) hX Xs (fun l => Multipole.edgesOf (Ta l))
    (Multipole.edgesOf Tb) hatS p₀ N
  refine (hle.trans hhatle).trans (hA6 X hX h2 hXk Xs hXs hdisj _
    (fun l => Finset.mem_image.2 ⟨Ta l, mem_relTrees.2 (hTa l), rfl⟩) _
    (Finset.mem_image.2 ⟨Tb, mem_relTrees₀.2 hTb, rfl⟩) hatS (fun l z => hhat l z) p₀ lam hlam
    hlt.le N)

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
