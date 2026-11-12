/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.TailExpansion
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.SingletonCutoff
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.MinusInfrastructure

/-!
# Case F and the finite cutoff assembly

See (A.52),
(A.64) and Step 5 of the proof of Lemma A.7. Each original
closed-U₀ parity term is integrated through the strict-tail case-F bound.
Only then are the two finite subset families counted.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset Limits Hierarchical Multipole Parity SmallIntegral RouteCases RouteSpatial
open scoped Classical ENNReal

/-- The actual closed-U₀ integral is bounded by the strict case-F integral. -/
theorem lintegral_closed_tail_le {I B : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
    [Fintype B] [DecidableEq B] {χ : ℂ → ℝ} {β lam M h h' : ℝ} (hh : h' ≤ h)
    (blk : I → B) (Dn Dz Df O : Finset (Sym2 I)) (U : Finset I) (hU : U.Nonempty) (N : ℕ) :
    (∫⁻ c in boxConfig I N, ENNReal.ofReal |baselineParityIntegrand χ β lam M blk Dn Dz Df O c *
      tailProduct true h U c|) ≤
    ∫⁻ c in boxConfig I N ∩ {c : I → ℂ × ℂ | h' < maxRad lam c},
      ENNReal.ofReal |baselineParityIntegrand χ β lam M blk Dn Dz Df O c| := by
  let f := fun c : I → ℂ × ℂ => ENNReal.ofReal |baselineParityIntegrand χ β lam M blk Dn Dz Df O c|
  let D := {c : I → ℂ × ℂ | h' < maxRad lam c}
  have hD : MeasurableSet D := measurableSet_lt measurable_const (measurable_maxRad lam)
  calc
    _ = ∫⁻ c in boxConfig I N, ENNReal.ofReal |baselineParityIntegrand χ β lam M blk Dn Dz Df O c *
        tailProduct false h U c| := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (tailProduct_closed_ae (I := I) h U)] with c hc
      rw [hc]
    _ ≤ ∫⁻ c in boxConfig I N, D.indicator f c := by
      apply lintegral_mono
      intro c
      dsimp only []
      rw [abs_mul,ENNReal.ofReal_mul (abs_nonneg _)]
      have hb := tailProduct_strict_bound h lam U hU c
      by_cases ht : h' < maxRad lam c
      · rw [indicator_of_mem (show c ∈ D from ht)]
        have hp : |tailProduct false h U c| ≤ 1 := hb.trans (by split_ifs <;> norm_num)
        exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hp)).trans_eq (by rw [ENNReal.ofReal_one,mul_one])
      · rw [indicator_of_notMem (show c ∉ D from ht)]
        have hz : ¬ h < maxRad lam c := fun hc => ht (hh.trans_lt hc)
        rw [ite_eq_right hz] at hb
        rw [abs_nonpos_iff.mp hb,abs_zero,ENNReal.ofReal_zero,mul_zero]
    _ = _ := by
      rw [lintegral_indicator hD,Measure.restrict_restrict hD]
      rw [Set.inter_comm]

/-- Case F assembled on at least two labels, uniformly in their original values. -/
theorem cluster_cutoff_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ)
    (hk : ((k+2 : ℕ) : ℕ∞) ≤ pStar β) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ min eps 1 →
      ∀ (X : Finset (Finset ℕ)), IsSubpartition X → (X.biUnion id).card = k+2 →
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (N : ℕ),
      |∫ c in boxConfig (X.biUnion id) N,
        clusterBox χ β lam M (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c *
          (cutInd (eps*truncationScale p₀ β lam) c-1)| ≤
        C*N*lam^((2-β)*(k+2))*truncationScale p₀ β lam^(-2 : ℝ) := by
  let eps' := min eps 1
  have heps' : 0 < eps' := lt_min heps zero_lt_one
  obtain ⟨A,hA,hb⟩ := caseF_baseline_integral_uniform hχ hβ hM p₀ k hk eps' heps' (min_le_right _ _)
  let Q : ℝ := 2^(k+2)*2^((k+2+1).choose 2)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨(Q+1)*A,by positivity,?_⟩
  intro lam hlam hlε X hX hcard Near Far hFar hconn Dz N
  let I := X.biUnion id
  let blk := Limits.blockOf X
  let Dn := symOf I Near
  let Df := symOf I Far
  let h := eps*truncationScale p₀ β lam
  let Us := (univ : Finset I).powerset.erase ∅
  let Os := Df.powerset.filter (CutEven (Sym2.map blk))
  let base := baselineParityIntegrand χ β lam M blk Dn Dz Df
  let F := fun c : I → ℂ × ℂ => clusterBox χ β lam M blk Dn Dz Df c * (cutInd h c-1)
  let T := A*N*lam^((2-β)*(k+2))*truncationScale p₀ β lam^(-2 : ℝ)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hmeas : Measurable F := (measurable_clusterBox (β := β) (M := M) hχ hlam blk Dn Dz Df).mul ((measurable_cutInd h).sub_const 1)
  obtain ⟨B,hB⟩ := exists_abs_clusterBox_le (M := M) hχ (by linarith : 0 ≤ β) hlam blk Dn Dz Df
  have hFb (c : I → ℂ × ℂ) : |F c| ≤ B := by
    rw [abs_mul]
    have hc : |cutInd h c-1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [cutInd_nonneg h c,cutInd_le_one h c]
    exact (mul_le_mul (hB c) hc (abs_nonneg _) ((abs_nonneg _).trans (hB c))).trans_eq (mul_one B)
  rw [← integral_boxConfig_avg_flip blk hmeas hFb N,← Real.norm_eq_abs]
  refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal (show 0 ≤ (Q+1)*A*N*lam^((2-β)*(k+2))*truncationScale p₀ β lam^(-2 : ℝ) by positivity) ?_)
  have hav := ae_restrict_of_ae (μ := volume) (s := boxConfig I N)
    (avg_clusterBox_cutoff_expansion_ae (β := β) (lam := lam) hχ hM blk Dn Dz Df h)
  have hmaj : (∫⁻ c in boxConfig I N, ENNReal.ofReal ‖(∑ A : Finset X, F (flipCfg (blockLabels blk A) c))/2^Fintype.card X‖) ≤
      ∫⁻ c in boxConfig I N, ∑ U ∈ Us, ∑ O ∈ Os, ENNReal.ofReal |base O c * tailProduct true h U c| := by
    apply lintegral_mono_ae
    filter_upwards [hav] with c hc
    dsimp only [F]
    rw [Real.norm_eq_abs,hc]
    apply (ENNReal.ofReal_le_ofReal ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun U _ => abs_sum_le_sum_abs _ _))).trans_eq
    rw [ENNReal.ofReal_sum_of_nonneg (fun U _ => sum_nonneg fun O _ => abs_nonneg _)]
    exact sum_congr rfl fun U _ => ENNReal.ofReal_sum_of_nonneg (fun O _ => abs_nonneg _)
  refine hmaj.trans ?_
  have hm (U : Finset I) (O : Finset (Sym2 I)) : Measurable (fun c : I → ℂ × ℂ => ENNReal.ofReal |base O c * tailProduct true h U c|) := ENNReal.measurable_ofReal.comp
    (continuous_abs.measurable.comp (measurable_baseline_tail (β := β) (M := M) hχ hlam blk Dn Dz Df O h U))
  rw [lintegral_finsetSum (μ := volume.restrict (boxConfig I N)) Us (fun U _ => Finset.measurable_sum Os fun O _ => hm U O)]
  simp_rw [lintegral_finsetSum (μ := volume.restrict (boxConfig I N)) Os (fun O _ => hm _ O)]
  have hterm U (hU : U ∈ Us) O (hO : O ∈ Os) :
      (∫⁻ c in boxConfig I N, ENNReal.ofReal |base O c * tailProduct true h U c|) ≤ ENNReal.ofReal T := by
    have hs := actual_source_odd hX hFar (mem_powerset.mp (mem_filter.mp hO).1) (mem_filter.mp hO).2
    have hu : U.Nonempty := nonempty_iff_ne_empty.2 (mem_erase.mp hU).1
    have ht := lintegral_closed_tail_le (χ := χ) (β := β) (lam := lam) (M := M)
      (mul_le_mul_of_nonneg_right (min_le_left eps 1) (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le)
      blk Dn Dz Df O U hu N
    have hi := hb X hX hcard lam hlam hlε Near Far (sourcePairs O) hFar hconn hs.1 hs.2.2 Dz N
    rw [hs.2.1] at hi
    exact ht.trans hi
  calc
    _ ≤ ∑ U ∈ Us, ∑ O ∈ Os, ENNReal.ofReal T := sum_le_sum fun U hU => sum_le_sum (hterm U hU)
    _ ≤ ∑ _U : Finset I, ∑ _O : Finset (Sym2 I), ENNReal.ofReal T := by
      refine (sum_le_sum fun U _ => sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => bot_le)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => bot_le)
    _ = ENNReal.ofReal (Q*T) := by
      simp only [sum_const,card_univ,nsmul_eq_mul]
      rw [← mul_assoc,← Nat.cast_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      simp only [Fintype.card_finset,Sym2.card,Fintype.card_coe,I,hcard,Q,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right (by linarith : Q ≤ Q+1) hT).trans_eq (by dsimp [T]; ring))

/-- The positive-label range of the frozen statement, with the singleton isolated explicitly. -/
theorem cluster_cutoff_bound_all {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ) (hk1 : 1 ≤ k)
    (hk : (k : ℕ∞) ≤ pStar β) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ min eps 1 →
      ∀ (X : Finset (Finset ℕ)), IsSubpartition X → (X.biUnion id).card = k →
      ∀ (Near Far : Finset (ℕ × ℕ)), Far ⊆ interPairs X → Near ∪ Far ∈ relEdgeSets₀ X →
      ∀ (Dz : Finset (Sym2 (X.biUnion id))) (N : ℕ),
      |∫ c in boxConfig (X.biUnion id) N,
        clusterBox χ β lam M (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) c *
          (cutInd (eps*truncationScale p₀ β lam) c-1)| ≤
        C*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ) := by
  by_cases hkone : k = 1
  · -- Singleton compatibility, outside the paper's at-least-two range.
    subst k
    obtain ⟨C,hC,hb⟩ := singleton_cluster_cutoff_bound hχ hβ hM p₀ eps heps
    refine ⟨C,hC,?_⟩
    intro lam hlam hlε X hX hcard Near Far hFar _hconn Dz N
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcard
    have hpairs : pairsOn (X.biUnion id) = ∅ := by rw [ha,pairsOn_singleton]
    have hz := hFar.trans interPairs_subset_pairsOn
    rw [hpairs] at hz
    have hFar0 : Far = ∅ := subset_empty.mp hz
    have hXcard : X.card ≤ (X.biUnion id).card := by
      rw [Limits.card_biUnion_eq_sum hX]
      calc
        X.card = ∑ _S ∈ X, (1 : ℕ) := by simp
        _ ≤ ∑ S ∈ X, S.card := sum_le_sum fun S hS => Finset.card_pos.2 (hX.1 S hS)
    have hB : Fintype.card X ≤ 1 := by simpa only [Fintype.card_coe,hcard] using hXcard
    have hh := hb lam hlam hlε (X.biUnion id) hcard X hB (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz N
    simpa only [hFar0,symOf,Finset.notMem_empty, and_false,filter_false,Finset.image_empty,Nat.cast_one] using hh
  · obtain ⟨j,hj⟩ : ∃ j : ℕ, k = j+2 := ⟨k-2,by omega⟩
    subst k
    simpa only [Nat.cast_add,Nat.cast_ofNat] using cluster_cutoff_bound hχ hβ hM p₀ j hk eps heps

end MultipoleBKT.ExpansionK.RouteAssembly

end
