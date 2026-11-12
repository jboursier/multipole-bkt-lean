/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.FixedCutoff

/-!
# Screened bounds uniform in the original cluster labels

See (A.63). Restrict the model controls on natural labels before
selecting a subpartition. This puts the coefficient before the original cluster data, as required by the statement of Lemma A.7.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open TwoComponentCoulomb (box)
open scoped Classical ENNReal

/-- Internal restriction of the screened controls to the original finite labels. -/
theorem internal_screened_controls_uniform {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (S : Finset ℕ) {lam M eps R : ℝ},
      0 < lam → 1 ≤ M → lam ≤ eps * R → ∀ c : ℕ → ℂ × ℂ,
      (∀ i, ‖(c i).1 - (c i).2‖ ≤ eps * R) →
      InternalControls K (fun i : S => rhoD lam (c i)) (fun _ => eps * R)
        (mixedOddWeight M lam (fun i : S => c i)) (mixedEvenWeight M lam (fun i : S => c i))
        (gammaW β (upperBoundInteraction χ lam eps R) M lam (fun i : S => c i))
        (gammaW β (dipoleInteraction χ lam) M lam (fun i : S => c i))
        (fun e => alphaW β (upperBoundInteraction χ lam eps R) M lam (fun i : S => c i) e +
          linkIndE M lam (fun i : S => c i) e)
        (fun e => alphaW β (dipoleInteraction χ lam) M lam (fun i : S => c i) e +
          linkIndE M lam (fun i : S => c i) e)
        (intraRatio β (upperBoundInteraction χ lam eps R) (dipoleInteraction χ lam) (fun i : S => c i))
        (fun i : S => Real.exp (-L * (‖(c i).1-(c i).2‖ / (eps * R)) ^ 2) - 1)
        (fun _ => 0) := by
  obtain ⟨K,hK,hb⟩ := screened_controls (ι := ℕ) (L := L) hχ hβ
  refine ⟨K,hK,?_⟩
  intro S lam M eps R hlam hM hlh c hc
  have H := hb hlam hM hlh c hc
  refine ⟨H.coefficient,fun i => H.radius_nonneg i,fun i => H.screening_pos i,?_,?_,?_,
    fun i => H.quadratic i,fun i => H.bad i,?_,?_,?_,fun i => H.quadratic_error i⟩
  · intro e
    induction e using Sym2.ind with
    | h i j => simpa only [gammaW,mixedOddWeight,ahatE,farInd,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.odd s(i.val,j.val)
  · intro e
    induction e using Sym2.ind with
    | h i j => simpa only [alphaW,linkIndE,mixedEvenWeight,ahatE,farInd,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.even s(i.val,j.val)
  · intro e
    induction e using Sym2.ind with
    | h i j => simpa only [intraRatio,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.intra s(i.val,j.val)
  · intro i j
    simpa only [gammaW,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.odd_error i.val j.val
  · intro i j
    simpa only [alphaW,linkIndE,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.even_error i.val j.val
  · intro i j
    simpa only [intraRatio,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,Function.comp_apply] using H.intra_error i.val j.val

/-- Complete pointwise bounds for the screened mixed terms. The Gaussian
correction is literal, and the bad-label correction vanishes identically. -/
theorem internal_screened_boundary_cut_uniform {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      MixedBoundary hX (hOF.trans hFar) hpar χ β lam M (ε₀ * R) K (Real.exp (β * cbK hχ))
        (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
        (fun d => Real.exp (-L * (‖d.1 - d.2‖ / (ε₀ * R)) ^ 2) - 1)
        (fun _ => 0) Near Far Dz c := by
  obtain ⟨K₀,hK₀,hcontrols⟩ := internal_screened_controls_uniform (L := L) hχ hβ
  obtain ⟨Ke,hKe,href⟩ := internal_refined_even (ι := ℕ) (D := c310 hχ) hβ
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (cA_nonneg hχ))
  refine ⟨K₀ + Ke,by linarith,?_⟩
  intro X hX lam M ε₀ R hlam hM hlh Near Far O hFar hconn hOF hpar Dz c hcut
  let cfg := fun i : X.biUnion id => c i
  have hc : ∀ i, ‖(cfg i).1 - (cfg i).2‖ ≤ ε₀ * R := fun i => hcut i i.property
  let ext : ℕ → ℂ × ℂ := fun i => if i ∈ X.biUnion id then c i else (0,0)
  have he (i : X.biUnion id) : ext i = c i := by simp only [ext,ite_eq_left i.property]
  have hce : ∀ i, ‖(ext i).1-(ext i).2‖ ≤ ε₀ * R := by
    intro i
    by_cases hi : i ∈ X.biUnion id
    · simpa only [ext,ite_eq_left hi] using hcut i hi
    · simp only [ext,ite_eq_right hi,sub_self,norm_zero]
      exact (hlam.trans_le hlh).le
  have H := (hcontrols (X.biUnion id) hlam hM hlh ext hce).enlarge (le_add_of_nonneg_right hKe)
  simp only [he] at H
  have hh : 0 < ε₀ * R := hlam.trans_le hlh
  obtain ⟨hwe,hve,-,-⟩ := minus_far_facts hχ hlam hM hlh ext hce
  have herre : ∀ i j, |upperBoundInteraction χ lam ε₀ R (ext i) (ext j) - dipoleInteraction χ lam (ext i) (ext j)| ≤
      c310 hχ * (‖(ext i).1-(ext i).2‖ * ‖(ext j).1-(ext j).2‖) / max (ε₀*R) (ε₀*R)^2 := by
    intro i j
    have h8 (i) : 8 * max ‖(ext i).2-(ext i).1‖ lam ≤ 8*ε₀*R := by
      rw [norm_sub_rev,mul_assoc]
      exact mul_le_mul_of_nonneg_left (max_le (hce i) hlh) (by norm_num)
    have hp := ((Classical.choose_spec (lemma_3_10 hχ)).2 lam (8*ε₀*R) hlam (ext i) (ext j) (h8 i) (h8 j)).1
    change |upperBoundInteraction χ lam ε₀ R (ext i) (ext j)-dipoleInteraction χ lam (ext i) (ext j)| ≤
      c310 hχ * (‖(ext i).1-(ext i).2‖ * ‖(ext j).1-(ext j).2‖) / (8*ε₀*R)^2 at hp
    rw [max_self]
    exact hp.trans (div_le_div_of_nonneg_left (mul_nonneg (c310_pos hχ).le (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (pow_pos hh 2)
      (pow_le_pow_left₀ hh.le (by rw [mul_assoc]; linarith) 2))
  have hpoint := href hlam hM (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R) ext
    (fun _ => hh) (fun i j hf => by nlinarith [hwe i j hf,hve i j hf]) herre
  apply internal_model_boundary hχ hβ hlam hM hX Near Far hFar hconn hOF hpar Dz c
    (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
    (fun d => Real.exp (-L * (‖d.1 - d.2‖ / (ε₀ * R)) ^ 2) - 1) (fun _ => 0) H
  intro i j
  have hp := hpoint i.val j.val
  have heq : (fun i : X.biUnion id => ext i) = cfg := by funext i; exact he i
  simp only [alphaW,linkIndE,symmLift_mk,wOrd,Subtype.coe_lt_coe,linkInd,he] at hp ⊢
  exact hp.trans (mul_le_mul_of_nonneg_right (by linarith)
    (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) (markedEvenE_nonneg lam cfg s(i,j))))

/-- The screened bound on every configuration. Outside the actual radius
cutoff the complete summand vanishes, so the spatial integration needs no pointwise support proof. -/
theorem internal_screened_boundary_uniform {χ : ℂ → ℝ} {β L : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {lam M ε₀ R : ℝ}, 0 < lam → 1 ≤ M → lam ≤ ε₀ * R →
      ∀ (Near Far O : Finset (ℕ × ℕ)) (hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (hOF : O ⊆ Far) (hpar : IsParityPair X O ∅)
      (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ),
      MixedBoundary hX (hOF.trans hFar) hpar χ β lam M (ε₀ * R) K (Real.exp (β * cbK hχ))
        (upperBoundInteraction χ lam ε₀ R) (fun _ => ε₀ * R)
        (fun d => Real.exp (-L * (‖d.1 - d.2‖ / (ε₀ * R)) ^ 2) - 1)
        (fun _ => 0) Near Far Dz c := by
  obtain ⟨K,hK,hb⟩ := internal_screened_boundary_cut_uniform (L := L) hχ hβ
  refine ⟨K,hK,?_⟩
  intro X hX lam M ε₀ R hlam hM hlh Near Far O hFar hconn hOF hpar Dz c
  let cfg := fun i : X.biUnion id => c i
  rcases cutInd_eq_one_or (ε₀ * R) cfg with ⟨-,hc⟩ | hz
  · exact hb hX hlam hM hlh Near Far O hFar hconn hOF hpar Dz c (fun i hi => hc ⟨i,hi⟩)
  · obtain ⟨-,-,Tb,hTb,hTE⟩ := source_skeletons_and_even_tree hX hconn
      (hOF.trans subset_union_right) hpar
    refine ⟨Tb,hTb,hTE,?_⟩
    intro P _ _
    apply Or.inl
    unfold mixedIntegrand mixedDensity
    rw [hz,mul_zero,zero_mul,mul_zero]

/-- (A.63) for every actual screened mixed term on its original graph.
The statement assumes original graph data and parameter ranges only. -/
theorem screened_mixed_integral_uniform {χ : ℂ → ℝ} {β L M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ) (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → lam ≤ 1 →
      ∀ (X : Finset (Finset ℕ)) (_hX : IsSubpartition X) (_hXne : X.Nonempty),
      (X.biUnion id).card = k → ∀ (Near Far O : Finset (ℕ × ℕ)) (_hFar : Far ⊆ interPairs X),
      Near ∪ Far ∈ relEdgeSets₀ X → ∀ (_hOF : O ⊆ Far) (_hpar : IsParityPair X O ∅)
        (Dz : Finset (Sym2 (X.biUnion id))) (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)),
      P ≠ (∅,∅,∅,∅,∅) → P ∈ fiveSubsets (symOf (X.biUnion id) O)
        (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) (RouteCases.intraEdges (Limits.blockOf X)) univ →
      ∀ N : ℕ, (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal |mixedIntegrand χ β lam M (eps * truncationScale p₀ β lam)
          (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
          (fun d => Real.exp (-L * (‖d.1-d.2‖ / (eps * truncationScale p₀ β lam)) ^ 2) - 1)
          (fun _ => 0) (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
          (symOf (X.biUnion id) O) c P|) ≤
        ENNReal.ofReal (C * eps ^ (-2 : ℝ) * N * lam ^ ((2-β)*(X.biUnion id).card) *
          truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  obtain ⟨K,hK,hpoint⟩ := internal_screened_boundary_uniform (L := L) hχ (by linarith : 0 ≤ β)
  obtain ⟨A,hA,hint⟩ := screened_fixed_spatialEnvelope_bound hχ hβ hM p₀ hk eps heps
  let Q := mixedCoefficient (Real.exp (β * cbK hχ)) K k
  have hQ : 0 < Q := mul_pos (pow_pos (Real.exp_pos _) _) (pow_pos (lt_of_lt_of_le zero_lt_one hK) _)
  refine ⟨Q*A,mul_pos hQ hA,?_⟩
  intro lam hlam hle hl1 X hX _hXne hcard Near Far O hFar hconn hOF hpar Dz P hne hP N
  have hnX : Nonempty (X.biUnion id) := Fintype.card_pos_iff.mp (by rw [Fintype.card_coe,hcard]; omega)
  let h := eps * truncationScale p₀ β lam
  have heps0 : 0 < eps := hlam.trans_le hle
  have hlh : lam ≤ h := hle.trans (le_mul_of_one_le_right heps0.le
    (Appendix.one_le_truncationScale hβ hlam hl1))
  let F (c : X.biUnion id → ℂ × ℂ) (i : X.biUnion id) :=
    (box N).indicator (1 : ℂ → ℝ≥0∞) (c i).2 * ENNReal.ofReal ((h ^ 2)⁻¹)
  have hp (c : X.biUnion id → ℂ × ℂ) (hc : c ∈ boxConfig (X.biUnion id) N) :
      ENNReal.ofReal |mixedIntegrand χ β lam M h (upperBoundInteraction χ lam eps (truncationScale p₀ β lam))
        (fun d => Real.exp (-L * (‖d.1-d.2‖ / h) ^ 2) - 1) (fun _ => 0)
        (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far)
        (symOf (X.biUnion id) O) c P| ≤ ENNReal.ofReal Q * spatialEnvelope χ β M lam h F c := by
    let ext := extendConfig (X.biUnion id) c
    have he : (fun i : X.biUnion id => ext i) = c := by funext i; exact extendConfig_coe c i
    have H := hpoint hX hlam hM hlh Near Far O hFar hconn hOF hpar Dz ext
    have hb := internal_boundary_envelope hlam hM (zero_le_one.trans hK) (Real.exp_nonneg _)
      hOF H P hne hP F 1 (fun i => by
        rw [he]
        rw [abs_zero,zero_div,add_zero,one_mul]
        dsimp only [F]
        rw [indicator_of_mem (((Set.mem_univ_pi.mp hc) i).2),Pi.one_apply,one_mul])
    rw [he,mul_one] at hb
    exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by
      simpa only [Fintype.card_coe,hcard] using mixedCoefficient_le (Real.exp_nonneg _) hK
        (symOf (X.biUnion id) O) (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) P)) le_rfl)
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, ENNReal.ofReal Q * spatialEnvelope χ β M lam h F c :=
      setLIntegral_mono' (measurableSet_boxConfig N) hp
    _ ≤ ∫⁻ c, ENNReal.ofReal Q * spatialEnvelope χ β M lam h F c := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal Q * ∫⁻ c, spatialEnvelope χ β M lam h F c :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal Q * ENNReal.ofReal (A * eps ^ (-2 : ℝ) * N *
        lam ^ ((2-β)*k) * truncationScale p₀ β lam ^ (-2 : ℝ)) :=
      mul_le_mul' le_rfl (hint lam hlam hle hl1 (X.biUnion id) (by rw [Fintype.card_coe,hcard]) N)
    _ = _ := by rw [hcard,← ENNReal.ofReal_mul hQ.le]; congr 1; ring

end MultipoleBKT.ExpansionK.RouteAssembly

end
