/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.PointwiseAssembly

/-!
# Common factors and support in the complete pointwise bound

See (A.55)–(A.62). The original graph includes the actual near bonds. All
block, support, cutoff and density factors remain in the common coefficient.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Peeling Multipole Hierarchical SmallIntegral Parity UpperBound.BoundedUpper

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- A linked far edge annihilates every mixed term, with arbitrary choices of
all five subsets. This is the support used before the graph estimates. -/
theorem mixedIntegrand_eq_zero_of_linked (χ : ℂ → ℝ) (β lam M h : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (u v : ℂ × ℂ → ℝ) (blk : ι → κ)
    (Dn Dz Df O : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) (P : FiveSubsets (Sym2 ι) ι)
    (hP : P ∈ fiveSubsets O (Df \ O) (intraEdges blk) univ)
    {e : Sym2 ι} (he : e ∈ Df) (hl : ¬ FarE M lam c e) :
    mixedIntegrand χ β lam M h w u v blk Dn Dz Df O c P = 0 := by
  classical
  have hodd : mixedBond P.1 (gammaW β w M lam c) (gammaW β (dipoleInteraction χ lam) M lam c) e = 0 := by
    simp only [mixedBond, gammaW_of_linked c hl, sub_self, ite_self]
  have heven : mixedBond P.2.1
      (fun e => alphaW β w M lam c e + linkIndE M lam c e)
      (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e) e = 0 := by
    simp only [mixedBond, alphaW_add_linkIndE_of_linked c hl, sub_self, ite_self]
  have hp := abs_fiveTerm_mul O (Df \ O) (intraEdges blk)
    (gammaW β w M lam c) (gammaW β (dipoleInteraction χ lam) M lam c)
    (fun e => alphaW β w M lam c e + linkIndE M lam c e)
    (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
    (intraRatio β w (dipoleInteraction χ lam) c) (u ∘ c) (v ∘ c) P hP
    (clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c)
  by_cases heO : e ∈ O
  · rw [prod_eq_zero heO (by rw [hodd,abs_zero])] at hp
    have hz : clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
        fiveTerm O (Df \ O) (intraEdges blk) (gammaW β w M lam c)
          (gammaW β (dipoleInteraction χ lam) M lam c)
          (fun e => alphaW β w M lam c e + linkIndE M lam c e)
          (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
          (intraRatio β w (dipoleInteraction χ lam) c) (u ∘ c) (v ∘ c) P = 0 :=
      abs_eq_zero.1 (hp.trans (by ring))
    exact mul_eq_zero_of_left hz _
  · rw [prod_eq_zero (mem_sdiff.2 ⟨he,heO⟩) (by rw [heven,abs_zero])] at hp
    have hz : clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c *
        fiveTerm O (Df \ O) (intraEdges blk) (gammaW β w M lam c)
          (gammaW β (dipoleInteraction χ lam) M lam c)
          (fun e => alphaW β w M lam c e + linkIndE M lam c e)
          (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
          (intraRatio β w (dipoleInteraction χ lam) c) (u ∘ c) (v ∘ c) P = 0 :=
      abs_eq_zero.1 (hp.trans (by ring))
    exact mul_eq_zero_of_left hz _

/-- Missing near support annihilates the common factor itself. -/
theorem clusterG_eq_zero_of_not_linked (β lam M : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (blk : ι → κ)
    (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ)
    {e : Sym2 ι} (he : e ∈ Dn) (hl : FarE M lam c e) :
    clusterG β w ψ M lam blk Dn Dz c = 0 := by
  have hz : -linkIndE M lam c e = 0 := by rw [linkIndE_of_far c hl,neg_zero]
  unfold clusterG
  rw [prod_eq_zero he hz, mul_zero]

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ] in
/-- The even majorant is at most one, including its near branch. -/
theorem paperEven_le_one {lam M : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M)
    (c : ι → ℂ × ℂ) (e : Sym2 ι) : paperEvenE M lam c e ≤ 1 := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    change (if MultipoleLinked M lam (c i) (c j) then 1 else ahat (c i) (c j) ^ 2) ≤ 1
    split_ifs with hn
    · exact le_rfl
    · have ha := (far_facts hlam hM hn).2.2
      nlinarith [ahat_nonneg (c i) (c j)]

/-- The marked even kernel on an actual label edge. -/
noncomputable def markedEvenE (lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => markedEvenKernel (rhoD lam (c i)) (rhoD lam (c j)) (dipoleDist (c i) (c j)))
    (fun i j => by unfold markedEvenKernel; rw [dipoleDist_comm, max_comm (rhoD lam (c i)),mul_comm])

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ] in
/-- Every marked even kernel is nonnegative on its whole carrier. -/
theorem markedEvenE_nonneg (lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ markedEvenE lam c e := by
  induction e using Sym2.ind with
  | h i j =>
    unfold markedEvenE
    rw [symmLift_mk]
    unfold markedEvenKernel
    exact div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (dipoleDist_nonneg _ _) ((dipoleDist_nonneg _ _).trans (le_max_left _ _)))

/-- Reassociation places every common factor before the mixed product. -/
theorem mixedIntegrand_eq_reordered (χ : ℂ → ℝ) (β lam M h : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (u v : ℂ × ℂ → ℝ) (blk : ι → κ)
    (Dn Dz Df O : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) (P : FiveSubsets (Sym2 ι) ι) :
    mixedIntegrand χ β lam M h w u v blk Dn Dz Df O c P =
      (clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c * mixedDensity χ β lam h Df c) *
      fiveTerm O (Df \ O) (intraEdges blk)
        (gammaW β w M lam c) (gammaW β (dipoleInteraction χ lam) M lam c)
        (fun e => alphaW β w M lam c e + linkIndE M lam c e)
        (fun e => alphaW β (dipoleInteraction χ lam) M lam c e + linkIndE M lam c e)
        (intraRatio β w (dipoleInteraction χ lam) c) (u ∘ c) (v ∘ c) P := by
  unfold mixedIntegrand
  ring

/-- Internal common-factor comparison, independent of all correction subsets. -/
theorem internal_common_factor {χ : ℂ → ℝ} {β lam M K H : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hlam : 0 < lam) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (blk : ι → κ) (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) (n : ℕ) :
    |clusterG β (dipoleInteraction χ lam) (fun _ => 1) M lam blk Dn Dz c * H| * K ^ n ≤
      (Real.exp (β * cbK hχ) ^ (Fintype.card ι * Fintype.card ι) * K ^ n) *
        clusterSupport M lam blk Dn Dz c * H := by
  rw [abs_mul,abs_of_nonneg hH]
  have hh := mul_le_mul_of_nonneg_right (clusterG_baseline_common (M := M) hχ hβ hlam blk Dn Dz c) hH
  calc _ ≤ (Real.exp (β * cbK hχ) ^ (Fintype.card ι * Fintype.card ι) * clusterSupport M lam blk Dn Dz c * H) * K ^ n :=
          mul_le_mul_of_nonneg_right hh (pow_nonneg hK _)
       _ = _ := by ring


end MultipoleBKT.ExpansionK.RouteCases

end
