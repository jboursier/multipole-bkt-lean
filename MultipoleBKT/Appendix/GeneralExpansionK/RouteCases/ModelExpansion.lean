/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.ParityExpansion
public import MultipoleBKT.Appendix.GeneralExpansionK.WeightBounds

/-!
# The five-subset identity for the actual cluster integrands

See Step 1 of
the proof of Lemma A.7 and (A.51).
The intra-block baseline is factored with the exact exponential ratio.
The two vertex corrections are retained separately. Reversal cancellation then
expands the actual `clusterQ` integrands into the five-subset summands.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Hierarchical Multipole Parity SmallIntegral

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- The ordered intra-block pairs, with the smaller label first. -/
def intraPairs (blk : ι → κ) : Finset (ι × ι) :=
  univ.filter fun p => blk p.1 = blk p.2 ∧ p.1 < p.2

/-- The unordered intra-block edge family. -/
def intraEdges (blk : ι → κ) : Finset (Sym2 ι) :=
  (intraPairs blk).image fun p => s(p.1, p.2)

/-- The exact exponential correction to an intra-block interaction. -/
noncomputable def intraRatio (β : ℝ) (w₁ w₀ : ℂ × ℂ → ℂ × ℂ → ℝ)
    (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => Real.exp (β * (wOrd w₀ c i j - wOrd w₁ c i j)))
    (fun i j => by rw [wOrd_comm w₀ c, wOrd_comm w₁ c])

omit [Fintype κ] in
private theorem intra_prod (blk : ι → κ) (f : Sym2 ι → ℝ) :
    ∏ e ∈ intraEdges blk, f e =
      ∏ i, ∏ j, if blk i = blk j ∧ i < j then f s(i, j) else 1 := by
  have hinj : Set.InjOn (fun p : ι × ι => s(p.1, p.2)) (intraPairs blk) := by
    intro p hp q hq heq
    rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · have hp' := (mem_filter.1 hp).2.2
      have hq' := (mem_filter.1 hq).2.2
      rw [h1, h2] at hp'
      exact False.elim (lt_asymm hp' hq')
  rw [intraEdges, prod_image hinj, intraPairs, prod_filter]
  rw [show (univ : Finset (ι × ι)) = (univ : Finset ι) ×ˢ univ by ext p; simp, prod_product]

private theorem stableWeight_ratio (β : ℝ) (w₁ w₀ : ℂ × ℂ → ℂ × ℂ → ℝ)
    (a b : ℂ × ℂ) :
    stableWeight β w₁ a b = stableWeight β w₀ a b * Real.exp (β * (w₀ a b - w₁ a b)) := by
  classical
  unfold stableWeight
  split_ifs
  · rw [← Real.exp_add]
    congr 1
    ring
  · exact (zero_mul _).symm

open scoped Classical in
/-- Factor the actual invariant part into the baseline and its three correction
families. The stable-pair and near-support indicators remain in the baseline. -/
theorem clusterG_five_factor (β M lam : ℝ) (w₁ w₀ : ℂ × ℂ → ℂ × ℂ → ℝ)
    (u v : ℂ × ℂ → ℝ) (blk : ι → κ) (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    clusterG β w₁ (fun d => (1 + u d) * (1 + v d)) M lam blk Dn Dz c =
      clusterG β w₀ (fun _ => 1) M lam blk Dn Dz c *
        (∏ e ∈ intraEdges blk, intraRatio β w₁ w₀ c e) *
        (∏ i, (1 + u (c i))) * (∏ i, (1 + v (c i))) := by
  have hr := intra_prod blk (intraRatio β w₁ w₀ c)
  have hstable : (∏ i, ∏ j, if blk i = blk j ∧ i < j then stableWeight β w₁ (c i) (c j) else 1) =
      (∏ i, ∏ j, if blk i = blk j ∧ i < j then stableWeight β w₀ (c i) (c j) else 1) *
        ∏ e ∈ intraEdges blk, intraRatio β w₁ w₀ c e := by
    rw [hr, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    by_cases hij : blk i = blk j ∧ i < j
    · simp only [ite_eq_left hij, intraRatio, symmLift_mk, wOrd, ite_eq_left hij.2]
      exact stableWeight_ratio β w₁ w₀ (c i) (c j)
    · simp only [ite_eq_right hij, one_mul]
  unfold clusterG
  rw [prod_blockWW_eq, prod_blockWW_eq, hstable, prod_mul_distrib]
  simp only [prod_const_one, mul_one]
  ring

open scoped Classical in
/-- (A.51) for `clusterQ`, with each of the five error subsets explicit.
The support restriction and dipole density can be multiplied into both sides.
The odd/even factors include the far-edge indicators on their whole carrier. -/
theorem clusterQ_five_subset_error {β M lam : ℝ} (hM : 1 ≤ M)
    (w₁ w₀ : ℂ × ℂ → ℂ × ℂ → ℝ) (u v : ℂ × ℂ → ℝ)
    (hw₁l : ∀ d e, w₁ d.swap e = -w₁ d e) (hw₁r : ∀ d e, w₁ d e.swap = -w₁ d e)
    (hw₀l : ∀ d e, w₀ d.swap e = -w₀ d e) (hw₀r : ∀ d e, w₀ d e.swap = -w₀ d e)
    (hu : ∀ d, u d.swap = u d) (hv : ∀ d, v d.swap = v d)
    (blk : ι → κ) (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    (∑ A : Finset κ, (clusterQ β w₁ (fun d => (1 + u d) * (1 + v d)) M lam blk Dn Dz Df
        (flipCfg (blockLabels blk A) c) -
      clusterQ β w₀ (fun _ => 1) M lam blk Dn Dz Df (flipCfg (blockLabels blk A) c))) /
        2 ^ Fintype.card κ =
      ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        ∑ P ∈ (fiveSubsets O (Df \ O) (intraEdges blk) univ).erase (∅, ∅, ∅, ∅, ∅),
          clusterG β w₀ (fun _ => 1) M lam blk Dn Dz c *
            fiveTerm O (Df \ O) (intraEdges blk)
              (gammaW β w₁ M lam c) (gammaW β w₀ M lam c)
              (fun e => alphaW β w₁ M lam c e + linkIndE M lam c e)
              (fun e => alphaW β w₀ M lam c e + linkIndE M lam c e)
              (intraRatio β w₁ w₀ c) (u ∘ c) (v ∘ c) P := by
  have hψ : ∀ d, (1 + u d.swap) * (1 + v d.swap) = (1 + u d) * (1 + v d) := by
    intro d
    rw [hu, hv]
  simp_rw [clusterQ_flip (ψ := fun d => (1 + u d) * (1 + v d)) hM hw₁l hw₁r hψ,
    clusterQ_flip (ψ := fun _ => 1) hM hw₀l hw₀r (fun _ => rfl)]
  rw [clusterG_five_factor β M lam w₁ w₀ u v blk Dn Dz c]
  have hp := parity_five_subset_error (Sym2.map blk) Df (intraEdges blk) univ
    (fun e => alphaW β w₁ M lam c e + linkIndE M lam c e)
    (fun e => alphaW β w₀ M lam c e + linkIndE M lam c e)
    (gammaW β w₁ M lam c) (gammaW β w₀ M lam c)
    (intraRatio β w₁ w₀ c) (u ∘ c) (v ∘ c) (clusterG β w₀ (fun _ => 1) M lam blk Dn Dz c)
  refine hp.trans ?_
  apply sum_congr rfl
  intro O _
  apply sum_congr
  · ext P
    simp only [mem_erase]
  · intro P _
    rfl

end MultipoleBKT.ExpansionK.RouteCases

end
