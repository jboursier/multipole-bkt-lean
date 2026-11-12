/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.AnalyticControls

/-!
# The concrete five-subset expansion of the screened model

See (A.51). The Gaussian weight is rewritten as one plus its literal
correction. The summands are the actual integrands bounded at the spatial integration boundary.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits Hierarchical Parity SmallIntegral

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

open scoped Classical in
/-- Exact expansion of the original screened cluster integrand, including
its common cutoff, short-edge support and dipole density. -/
theorem clusterQ_screened_five_subset_error {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    (p₀ : ℕ) (β lam M ε₀ L : ℝ) (hM : 1 ≤ M) (blk : ι → κ)
    (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    ((∑ A : Finset κ,
      (clusterQ β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
        (gaussianWeight p₀ β lam ε₀ L) M lam blk Dn Dz Df (flipCfg (blockLabels blk A) c) -
        clusterQ β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz Df (flipCfg (blockLabels blk A) c))) /
      2 ^ Fintype.card κ) * mixedDensity χ β lam (ε₀ * truncationScale p₀ β lam) Df c =
      ∑ O ∈ Df.powerset.filter (CutEven (Sym2.map blk)),
        ∑ P ∈ (fiveSubsets O (Df \ O) (intraEdges blk) univ).erase (∅,∅,∅,∅,∅),
          mixedIntegrand χ β lam M (ε₀ * truncationScale p₀ β lam)
            (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
            (fun d => Real.exp (-L * (‖d.1-d.2‖ / (ε₀ * truncationScale p₀ β lam)) ^ 2) - 1)
            (fun _ => 0) blk Dn Dz Df O c P := by
  let u := fun d : ℂ × ℂ => Real.exp (-L * (‖d.1-d.2‖ / (ε₀ * truncationScale p₀ β lam)) ^ 2) - 1
  have hψ : gaussianWeight p₀ β lam ε₀ L = fun d => (1 + u d) * (1 + (0 : ℝ)) := by
    funext d
    dsimp only [gaussianWeight,u]
    rw [div_pow]
    ring
  have hu : ∀ d, u d.swap = u d := by
    intro d
    simp only [u,Prod.fst_swap,Prod.snd_swap,norm_sub_rev]
  have he := clusterQ_five_subset_error (β := β) (lam := lam) hM
    (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) (dipoleInteraction χ lam) u (fun _ => 0)
    (fun d e => Parity.upperBoundInteraction_swap_left d e χ lam ε₀ _)
    (fun d e => Parity.upperBoundInteraction_swap_right d e χ lam ε₀ _)
    (fun d e => Limits.dipoleInteraction_swap_left d e hχ lam)
    (fun d e => Limits.dipoleInteraction_swap_right d e hχ lam) hu (fun _ => rfl) blk Dn Dz Df c
  rw [← hψ] at he
  rw [he]
  simp_rw [sum_mul]
  rfl

end MultipoleBKT.ExpansionK.RouteCases

end
