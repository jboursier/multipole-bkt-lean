/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.JointTail
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.RadialRelabel

/-!
# Case-F vector tails on the original label carrier

See Step 4 of
the proof of Lemma A.7. Finite relabelling preserves the
maximum-radius tail set and every regularized radial factor.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset Limits SmallIntegral SmallIntegral.RouteJ
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
  obtain ⟨C,hC,hb⟩ := caseF_vector_bound hβ p₀ k hkp eps heps heps1
  refine ⟨C,hC,?_⟩
  intro lam hlam hle W _ _ hW
  let e : W ≃ Fin (k+2) := Fintype.equivOfCardEq (by simpa using hW)
  rw [lintegral_logRadial_tail_reindex e]
  exact hb lam hlam hle

end MultipoleBKT.ExpansionK.RouteSpatial

end
