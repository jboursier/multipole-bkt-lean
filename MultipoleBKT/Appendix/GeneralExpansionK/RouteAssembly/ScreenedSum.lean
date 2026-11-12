/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.FrozenSum
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.ScreenedUniform

/-!
# Finite parity and five-subset assembly

See (A.51),
(A.63) and Step 5 of the proof of Lemma A.7.
Apply the written mixed-term estimates to the original subsets, then sum.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Limits Hierarchical Multipole Parity SmallIntegral
open UpperBound BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- Summing the actual A–E terms preserves the area bound of (A.63).
For each fixed epsilon the coefficient is independent of lambda and X. -/
theorem screened_mixed_sum_bound {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ) (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (X : Finset (Finset ℕ)), IsSubpartition X → X.Nonempty →
      (X.biUnion id).card = k → ∀ N : ℕ,
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ Dz : Finset (Sym2 (X.biUnion id)),
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ∑ O ∈ (symOf (X.biUnion id) Far).powerset.filter (CutEven (Sym2.map (Limits.blockOf X))),
          ∑ P ∈ (fiveSubsets O (symOf (X.biUnion id) Far \ O)
              (RouteCases.intraEdges (Limits.blockOf X)) (univ : Finset (X.biUnion id))).erase (∅,∅,∅,∅,∅),
            ENNReal.ofReal |mixedIntegrand χ β lam M (eps*truncationScale p₀ β lam)
              (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
              (fun d => Real.exp (-L * (‖d.1-d.2‖ / (eps*truncationScale p₀ β lam))^2)-1) (fun _ => 0) (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
              (symOf (X.biUnion id) Far) O c P|) ≤
        ENNReal.ofReal (C*eps^(-2 : ℝ)*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ)) := by
  obtain ⟨A,hA,hb⟩ := screened_mixed_integral_uniform (β := β) (L := L) (M := M) hχ hβ hM p₀ k hk eps heps
  let Q : ℝ := correctionCount k
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  refine ⟨(Q+1)*A,mul_pos (by linarith) hA,?_⟩
  intro lam hlam hle hl1 X hX hXne hcard N Near Far hFar hconn Dz
  let Df := symOf (X.biUnion id) Far
  let Js := Df.powerset.filter (CutEven (Sym2.map (Limits.blockOf X)))
  let Ps (O : Finset (Sym2 (X.biUnion id))) :=
    (fiveSubsets O (Df \ O) (RouteCases.intraEdges (Limits.blockOf X)) (univ : Finset (X.biUnion id))).erase (∅,∅,∅,∅,∅)
  let T : ℝ := A*eps^(-2 : ℝ)*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ)
  have hT : 0 ≤ T := by
    have hl := Real.rpow_nonneg hlam.le ((2-β)*k)
    have he := Real.rpow_nonneg (hlam.le.trans hle) (-2 : ℝ)
    have he' := Real.rpow_nonneg (hlam.le.trans hle) (alphaExponent β*k)
    have hr := Real.rpow_nonneg (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ)
    dsimp only [T]
    positivity
  have hm (O : Finset (Sym2 (X.biUnion id)))
      (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)) :
      Measurable (fun c : X.biUnion id → ℂ × ℂ => ENNReal.ofReal |mixedIntegrand χ β lam M
        (eps*truncationScale p₀ β lam) (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
        (fun d => Real.exp (-L*(‖d.1-d.2‖/(eps*truncationScale p₀ β lam))^2)-1) (fun _ => 0)
        (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz Df O c P|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (measurable_mixedIntegrand (I := X.biUnion id) (B := X) (β := β) (M := M) hχ hlam
        (measurable_screenedInteraction hχ hlam (8*eps*truncationScale p₀ β lam))
        (show Measurable (fun d : ℂ × ℂ => Real.exp (-L * (‖d.1-d.2‖ / (eps*truncationScale p₀ β lam))^2)-1) by fun_prop)
        (measurable_const (a :=  (0 : ℝ)))
        (eps*truncationScale p₀ β lam) (Limits.blockOf X)
        (symOf (X.biUnion id) Near) Dz Df O P))
  change (∫⁻ c in boxConfig (X.biUnion id) N,
    ∑ O ∈ Js, ∑ P ∈ Ps O,
      ENNReal.ofReal |mixedIntegrand χ β lam M (eps*truncationScale p₀ β lam)
        (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
          (fun d => Real.exp (-L * (‖d.1-d.2‖ / (eps*truncationScale p₀ β lam))^2)-1) (fun _ => 0) (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz Df O c P|) ≤ _
  rw [lintegral_finsetSum (μ := volume.restrict (boxConfig (X.biUnion id) N)) Js fun O _ => Finset.measurable_sum (Ps O) fun P _ => hm O P]
  simp_rw [lintegral_finsetSum (μ := volume.restrict (boxConfig (X.biUnion id) N)) _ fun P _ => hm _ P]
  have hterm O (hO : O ∈ Js) P (hP : P ∈ Ps O) :
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |mixedIntegrand χ β lam M (eps*truncationScale p₀ β lam)
          (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
          (fun d => Real.exp (-L * (‖d.1-d.2‖ / (eps*truncationScale p₀ β lam))^2)-1) (fun _ => 0) (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
          Df O c P|) ≤ ENNReal.ofReal T := by
    have hs := actual_source_odd hX hFar (mem_powerset.mp (mem_filter.mp hO).1) (mem_filter.mp hO).2
    have h := hb lam hlam hle hl1 X hX hXne hcard Near Far (sourcePairs O)
      hFar hconn hs.1 hs.2.2 Dz P (mem_erase.mp hP).1 (by simpa only [hs.2.1] using (mem_erase.mp hP).2) N
    simpa only [hs.2.1,hcard] using h
  calc
    _ ≤ ∑ O ∈ Js, ∑ _P ∈ Ps O, ENNReal.ofReal T := sum_le_sum fun O hO => sum_le_sum (hterm O hO)
    _ ≤ ∑ _O : Finset (Sym2 (X.biUnion id)), ∑ _P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id),
        ENNReal.ofReal T := by
      refine (sum_le_sum fun O _ => sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => bot_le)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => bot_le)
    _ = ENNReal.ofReal (Q*T) := by
      simp only [sum_const,card_univ,nsmul_eq_mul]
      rw [← mul_assoc,← Nat.cast_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      congr 1
      simp only [Fintype.card_prod,Fintype.card_finset,Sym2.card,Fintype.card_coe,hcard,Q,correctionCount]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have he := Real.rpow_nonneg (hlam.le.trans hle) (-2 : ℝ)
      have he' := Real.rpow_nonneg (hlam.le.trans hle) (alphaExponent β*k)
      have hr := Real.rpow_nonneg (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ)
      have hl := Real.rpow_nonneg hlam.le ((2-β)*k)
      have hqt := mul_le_mul_of_nonneg_right (by linarith : Q ≤ Q+1) hT
      exact hqt.trans_eq (by dsimp only [T]; ring))

end MultipoleBKT.ExpansionK.RouteAssembly

end
