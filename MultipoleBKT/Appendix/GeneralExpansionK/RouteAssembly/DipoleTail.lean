/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.DipoleBound
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailSectors
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RadialRelabel

/-!
# The direct dipole tail in Lemma A.8

See Lemma A.8. The radial tail is retained through the near/far expansion
and the merged reversal average. The parity expansion supplies the separate tree families.
The radial integration supplies the three radial regimes after spatial integration.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset SimpleGraph Limits SmallIntegral SmallIntegral.RouteJ
open Limits.RouteDirect
open scoped Classical ENNReal

/-- Relabelling leaves the largest regularized vector radius unchanged. -/
theorem maxRho_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (lam : ℝ) (u : J → ℂ) :
    SmallIntegral.maxRho lam (u ∘ e) = SmallIntegral.maxRho lam u := by
  apply le_antisymm
  · exact (fold_max_le _).2 ⟨SmallIntegral.lam_le_maxRho _ _,fun i _ => SmallIntegral.rho_le_maxRho _ _ (e i)⟩
  · apply (fold_max_le _).2
    refine ⟨SmallIntegral.lam_le_maxRho _ _,?_⟩
    intro j _
    obtain ⟨i,rfl⟩ := e.surjective j
    exact SmallIntegral.rho_le_maxRho lam (u ∘ e) i

/-- The unordered logarithmic tail integral is invariant under finite relabelling. -/
theorem lintegral_logRadial_tail_reindex {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (e : I ≃ J) (β lam h : ℝ) (q : ℕ) :
    (∫⁻ u in {u : I → ℂ | h < SmallIntegral.maxRho lam u}, ENNReal.ofReal (logRadialWeight β lam q u)) =
      ∫⁻ u in {u : J → ℂ | h < SmallIntegral.maxRho lam u}, ENNReal.ofReal (logRadialWeight β lam q u) := by
  let S : Set (J → ℂ) := {u | h < SmallIntegral.maxRho lam u}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (SmallIntegral.measurable_maxRho lam)
  let F : (J → ℂ) → ℝ≥0∞ := S.indicator (fun u => ENNReal.ofReal (logRadialWeight β lam q u))
  have hF : Measurable F := by
    apply Measurable.indicator
    · unfold logRadialWeight
      have hm := SmallIntegral.measurable_maxRho (ι := J) lam
      have hn := SmallIntegral.measurable_minRho (ι := J) lam
      unfold rho
      fun_prop
    · exact hS
  have hp := (volume_measurePreserving_piCongrLeft (fun _ : J => ℂ) e).lintegral_comp hF
  rw [← lintegral_indicator (measurableSet_lt measurable_const (SmallIntegral.measurable_maxRho lam)),
    ← lintegral_indicator hS]
  change _ = ∫⁻ u, F u
  rw [← hp]
  apply lintegral_congr
  intro u
  let v := MeasurableEquiv.piCongrLeft (fun _ : J => ℂ) e u
  have he : v ∘ e = u := by
    funext i
    simp [v,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have hm : SmallIntegral.maxRho lam v = SmallIntegral.maxRho lam u := by
    rw [← he,maxRho_reindex]
  have hr := logRadialWeight_reindex e β lam q v
  rw [he] at hr
  dsimp only [F,S,v] at *
  by_cases hu : h < SmallIntegral.maxRho lam u
  · rw [indicator_of_mem (show u ∈ {u : I → ℂ | h < SmallIntegral.maxRho lam u} from hu),
      indicator_of_mem (show v ∈ {u : J → ℂ | h < SmallIntegral.maxRho lam u} by change h < SmallIntegral.maxRho lam _; rw [hm]; exact hu),hr]
  · rw [indicator_of_notMem (show u ∉ {u : I → ℂ | h < SmallIntegral.maxRho lam u} from hu),
      indicator_of_notMem (show v ∉ {u : J → ℂ | h < SmallIntegral.maxRho lam u} by change ¬ h < SmallIntegral.maxRho lam _; rw [hm]; exact hu)]

/-- The three-regime vector bound on any original finite original label set. -/
theorem caseF_vector_bound_any {β : ℝ} (hβ : 2 < β) (p₀ k : ℕ)
    (hkp : ((k+2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ eps →
      ∀ (W : Type*) [Fintype W] [Nonempty W], Fintype.card W = k+2 →
      (∫⁻ u in {u : W → ℂ | eps * truncationScale p₀ β lam < SmallIntegral.maxRho lam u},
        ENNReal.ofReal (logRadialWeight β lam (k+2) u)) ≤
        ENNReal.ofReal (C * lam ^ ((2-β)*(k+2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  intro eps heps heps1
  obtain ⟨C,hC,hb⟩ := RouteSpatial.caseF_vector_bound hβ p₀ k hkp eps heps heps1
  refine ⟨C,hC,?_⟩
  intro lam hlam hle W _ _ hW
  let e : W ≃ Fin (k+2) := Fintype.equivOfCardEq (by simpa using hW)
  rw [lintegral_logRadial_tail_reindex e]
  exact hb lam hlam hle

variable {I : Type*} [Fintype I] [LinearOrder I] [Nonempty I]

/-- Spatial integration of one tree from the parity expansion with the original radial tail retained. -/
theorem limitingTreeTerm_tail_le {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam →
      ∀ (T : SimpleGraph I), T.IsTree → Fintype.card I = k + 2 →
      ∀ (NT A B : Finset (Sym2 I)), A ∪ (B ∪ NT) = T.edgeFinset →
      Disjoint A (B ∪ NT) → Disjoint B NT → ∀ n : ℕ,
      (∫⁻ c in boxConfig I n ∩ {c : I → ℂ × ℂ | h < maxRad lam c},
        limitingTreeTerm χ β lam M NT A B c) ≤
          ENNReal.ofReal (C * n) * ∫⁻ u in {u : I → ℂ | h < maxRho lam u},
            ENNReal.ofReal (logRadialWeight β lam (k+2) u) := by
  obtain ⟨Cs, hCs, hs⟩ := lintegral_treeProfile hM (k+1)
  obtain ⟨Cg, hCg, hg⟩ := exists_logDensityWeight_le hχ hβ
  refine ⟨Cs * Cg ^ Fintype.card I, by positivity, ?_⟩
  intro lam h hlam T hT hI NT A B hpart hA hB n
  let root : I := Classical.arbitrary I
  let G (c : I → ℂ × ℂ) := {c : I → ℂ × ℂ | h < maxRad lam c}.indicator
    (fun c => (TwoComponentCoulomb.box n).indicator (1 : ℂ → ℝ≥0∞) (c root).1 *
      limitingTreeTerm χ β lam M NT A B c) c
  have htail : MeasurableSet {c : I → ℂ × ℂ | h < maxRad lam c} :=
    measurableSet_lt measurable_const (measurable_maxRad lam)
  have hG : Measurable G := (((measurable_const.indicator
    (TwoComponentCoulomb.measurableSet_box n)).comp
      (measurable_fst.comp (measurable_pi_apply root))).mul
        (measurable_limitingTreeTerm hχ hlam NT A B)).indicator htail
  have hbox : (∫⁻ c in boxConfig I n ∩ {c : I → ℂ × ℂ | h < maxRad lam c},
      limitingTreeTerm χ β lam M NT A B c) ≤ ∫⁻ c, G c := by
    rw [← lintegral_indicator ((measurableSet_boxConfig n).inter htail)]
    apply lintegral_mono
    intro c
    by_cases hc : c ∈ boxConfig I n ∩ {c : I → ℂ × ℂ | h < maxRad lam c}
    · rw [indicator_of_mem hc]
      simp only [G, indicator_of_mem hc.2,
        indicator_of_mem (((Set.mem_univ_pi.mp hc.1) root).1), Pi.one_apply, one_mul, le_refl]
    · rw [indicator_of_notMem hc]
      exact bot_le
  refine hbox.trans ?_
  rw [lintegral_eq_lintegral_pos_vec G hG,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hU : MeasurableSet {u : I → ℂ | h < maxRho lam u} :=
    measurableSet_lt measurable_const (SmallIntegral.measurable_maxRho lam)
  rw [← lintegral_indicator hU]
  apply lintegral_mono
  intro u
  change (∫⁻ x : I → ℂ, G (ofPosVec x u)) ≤ _
  by_cases hu : h < maxRho lam u
  · rw [indicator_of_mem (show u ∈ {u : I → ℂ | h < maxRho lam u} from hu)]
    let P : ℝ := (∏ i, Real.exp (β * smearedKernel χ lam (u i))) *
      radialFactor lam (ofPosVec (fun _ : I => 0) u)
    have hP : 0 ≤ P := mul_nonneg (prod_nonneg fun _ _ => (Real.exp_pos _).le)
      (by unfold radialFactor
          exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
            (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam _)) _))
    have heq (x : I → ℂ) : G (ofPosVec x u) = ENNReal.ofReal P *
        ((TwoComponentCoulomb.box n).indicator (1 : ℂ → ℝ≥0∞) (x root) *
          treeProfile M lam A B NT (ofPosVec x u)) := by
      dsimp only [G]
      rw [indicator_of_mem (show ofPosVec x u ∈ {c | h < maxRad lam c} by
        simpa only [Set.mem_ofPred_eq, maxRad_ofPosVec_eq] using hu)]
      dsimp only [limitingTreeTerm, P, radialFactor]
      simp only [ofPosVec_apply, pairDensity_mk hχ, rhoD_mk, maxRad_ofPosVec_eq,
        ENNReal.ofReal_mul (prod_nonneg fun _ _ => (Real.exp_pos _).le)]
      ring
    simp_rw [heq]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsp := hs I (by omega) T hT A B NT hpart hA hB root u lam hlam n
    have hd : P * (1 + Real.log (maxRho lam u / minRho lam u)) ^ (k+1) = logDensityWeight χ β lam (k+1) u := by
      unfold P logDensityWeight radialFactor
      simp only [ofPosVec_apply, rhoD_mk, maxRad_ofPosVec_eq]
      ring
    have hden : logDensityWeight χ β lam (k+1) u ≤
        Cg ^ Fintype.card I * logRadialWeight β lam (k+2) u := by
      refine (hg I lam hlam (k+1) u).trans ?_
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hCg.le _)
      unfold logRadialWeight
      apply mul_le_mul_of_nonneg_right
      · apply pow_le_pow_right₀
        · exact le_add_of_nonneg_right (Real.log_nonneg
            ((one_le_div (minRho_pos hlam u)).2
              ((minRho_le_rho lam u root).trans (rho_le_maxRho lam u root))))
        · omega
      · exact mul_nonneg (Real.rpow_nonneg (maxRho_pos hlam u).le _)
          (prod_nonneg fun _ _ => Real.rpow_nonneg (rho_pos hlam _).le _)
    calc
      _ ≤ ENNReal.ofReal P * (ENNReal.ofReal (Cs * n) *
          ENNReal.ofReal ((1 + Real.log (maxRho lam u / minRho lam u)) ^ (k+1))) := mul_le_mul' le_rfl (hsp.trans_eq (ENNReal.ofReal_mul (mul_nonneg hCs.le (Nat.cast_nonneg _))))
      _ = ENNReal.ofReal (Cs * n) * ENNReal.ofReal (logDensityWeight χ β lam (k+1) u) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul hP, hd]
      _ ≤ ENNReal.ofReal (Cs * n) *
          ENNReal.ofReal (Cg ^ Fintype.card I * logRadialWeight β lam (k+2) u) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hden)
      _ = _ := by
        rw [ENNReal.ofReal_mul (pow_nonneg hCg.le _), ← mul_assoc,
          ← ENNReal.ofReal_mul (mul_nonneg hCs.le (Nat.cast_nonneg _))]
        congr 1
        congr 1
        ring
  · rw [indicator_of_notMem (show u ∉ {u : I → ℂ | h < maxRho lam u} from hu)]
    have hz (x : I → ℂ) : G (ofPosVec x u) = 0 := by
      unfold G
      exact indicator_of_notMem (by simpa only [Set.mem_ofPred_eq, maxRad_ofPosVec_eq] using hu) _
    simp only [hz, lintegral_zero, le_refl]

/-- The finite tree family satisfies case F, with no fractional edge powers. -/
theorem mixedTreeSum_tail_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ : ℕ)
    (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → ∀ n : ℕ,
      (∫⁻ c in boxConfig I n ∩
        {c : I → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        mixedTreeSum χ β lam M c) ≤
          ENNReal.ofReal (C * n * lam ^ ((2-β)*Fintype.card I) *
            truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  let k := Fintype.card I - 2
  have hcard : Fintype.card I = k+2 := (Nat.sub_add_cancel hI).symm
  obtain ⟨Cr,hCr,hr⟩ := caseF_vector_bound_any hβ p₀ k (by rwa [← hcard]) eps heps heps1
  obtain ⟨Cs,hCs,hs⟩ := limitingTreeTerm_tail_le (I := I) (β := β) (M := M) hχ (by linarith) hM k
  let C := ((mixedTrees I).card : ℝ) * (Cs*Cr)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCs.le hCr.le)
  refine ⟨C+1,by linarith,fun lam hlam hle n => ?_⟩
  have hterm (t : SimpleGraph I × Finset (Sym2 I) × Finset (Sym2 I) × Finset (Sym2 I))
      (ht : t ∈ mixedTrees I) :
      (∫⁻ c in boxConfig I n ∩
        {c : I → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        limitingTreeTerm χ β lam M t.2.1 t.2.2.1 t.2.2.2 c) ≤
        ENNReal.ofReal (Cs*Cr*n*lam^((2-β)*Fintype.card I)*truncationScale p₀ β lam^(-2 : ℝ)) := by
    obtain ⟨hT,hpart,hA,hB⟩ := (mem_filter.mp ht).2
    have h := (hs lam _ hlam t.1 hT hcard t.2.1 t.2.2.1 t.2.2.2 hpart hA hB n).trans
      (mul_le_mul' le_rfl (hr lam hlam hle I hcard))
    rw [← ENNReal.ofReal_mul (mul_nonneg hCs.le (Nat.cast_nonneg _))] at h
    have hcast : (k : ℝ)+2 = Fintype.card I := by exact_mod_cast hcard.symm
    rw [hcast] at h
    exact h.trans_eq (by congr 1; ring)
  unfold mixedTreeSum
  rw [lintegral_finsetSum _ fun t _ => measurable_limitingTreeTerm hχ hlam t.2.1 t.2.2.1 t.2.2.2]
  calc
    _ ≤ ∑ _t ∈ mixedTrees I,
        ENNReal.ofReal (Cs*Cr*n*lam^((2-β)*Fintype.card I)*truncationScale p₀ β lam^(-2 : ℝ)) :=
      sum_le_sum hterm
    _ = ENNReal.ofReal (C*n*lam^((2-β)*Fintype.card I)*truncationScale p₀ β lam^(-2 : ℝ)) := by
      rw [sum_const,nsmul_eq_mul,← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      dsimp only [C]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1)
        (Nat.cast_nonneg n)) (Real.rpow_nonneg hlam.le _))
      (Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _))

/-- Each direct merged reversal average has the written strict-tail bound. -/
theorem dipSym_tail_bound {χ : ℂ → ℝ} {β : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ)
    (hI : 2 ≤ Fintype.card I) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (E : SimpleGraph I) (hE : E.Connected) {E' : Finset (Sym2 I)}
    (hE' : E' ∈ E.edgeFinset.powerset) {eps : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ eps → ∀ n : ℕ,
      (∫⁻ c in boxConfig I n ∩
        {c : I → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        ENNReal.ofReal |dipSym χ β lam 30 E E' c|) ≤
        ENNReal.ofReal (A*n*lam^((2-β)*Fintype.card I)*truncationScale p₀ β lam^(-2 : ℝ)) := by
  obtain ⟨Cw,hCw,hw⟩ := exists_abs_dipWeight_le_uniform hχ (by linarith : 0 ≤ β) E
  obtain ⟨D,hD,hd⟩ := exists_parity_average_le_mixedTreeSum (β := β) hχ (by linarith)
    (blkOf E E') (blkOf_surjective E E') (interPart E E')
    (fun _ _ h => h.2) (reachable_interPart hE E') hCw
  obtain ⟨Ct,hCt,ht⟩ := mixedTreeSum_tail_bound (I := I) hχ hβ (by norm_num : (1 : ℝ) ≤ 30)
    p₀ hI hk heps heps1
  refine ⟨D*Ct,mul_nonneg hD hCt.le,fun lam hlam hle n => ?_⟩
  have hpt := hd lam hlam 30 (by norm_num) (dipSym χ β lam 30 E E') (fun c =>
    (abs_dipSym_le hχ (by norm_num : (1 : ℝ) ≤ 30) E (mem_powerset.mp hE') c).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hw lam hlam 30 E' (mem_powerset.mp hE') c)
          (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le))
        (sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => abs_nonneg _)
          (prod_nonneg fun _ _ => abs_nonneg _))))
  calc
    _ ≤ ∫⁻ c in boxConfig I n ∩
        {c : I → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        ENNReal.ofReal D * mixedTreeSum χ β lam 30 c := lintegral_mono hpt
    _ = ENNReal.ofReal D * ∫⁻ c in boxConfig I n ∩
        {c : I → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        mixedTreeSum χ β lam 30 c := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal
        (Ct*n*lam^((2-β)*Fintype.card I)*truncationScale p₀ β lam^(-2 : ℝ)) :=
      mul_le_mul' le_rfl (ht lam hlam hle n)
    _ = _ := by rw [← ENNReal.ofReal_mul hD]; congr 1; ring

end MultipoleBKT.ExpansionK.RouteAssembly

end
