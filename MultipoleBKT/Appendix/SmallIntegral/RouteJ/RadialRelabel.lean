/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.VectorRadial

/-!
# Relabelling the logarithmic vector majorant

See Lemma A.4. Transfer the ordered radial
calculation from `Fin k` to the paper's finite set of labels.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset Set Limits
open scoped ENNReal

theorem logRadialWeight_reindex {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (e : I ≃ J) (β lam : ℝ) (q : ℕ) (v : J → ℂ) :
    logRadialWeight β lam q (v ∘ e) = logRadialWeight β lam q v := by
  have hmax : maxRho lam (v ∘ e) = maxRho lam v := by
    apply le_antisymm
    · exact (fold_max_le _).mpr ⟨lam_le_maxRho lam v, fun i _ => rho_le_maxRho lam v (e i)⟩
    · apply (fold_max_le _).mpr
      refine ⟨lam_le_maxRho lam (v ∘ e), fun j _ => ?_⟩
      obtain ⟨i, rfl⟩ := e.surjective j
      exact rho_le_maxRho lam (v ∘ e) i
  have hmin : minRho lam (v ∘ e) = minRho lam v := by
    apply le_antisymm
    · apply (le_inf'_iff _ _).mpr
      intro j _
      obtain ⟨i, rfl⟩ := e.surjective j
      exact minRho_le_rho lam (v ∘ e) i
    · exact (le_inf'_iff _ _).mpr fun i _ => minRho_le_rho lam v (e i)
  unfold logRadialWeight
  rw [hmax, hmin]
  congr 2
  exact e.prod_comp (fun j => rho lam (v j) ^ (2 - β))

/-- Relabel the entire radial integral, including all radial cutoffs. -/
theorem lintegral_logRadialWeight_relabel {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (e : I ≃ J) (β lam : ℝ) (q : ℕ)
    (D : Set ℝ) (hD : MeasurableSet D) :
    (∫⁻ v in {v : I → ℂ | ∀ i, ‖v i‖ ∈ D}, ENNReal.ofReal (logRadialWeight β lam q v)) =
      ∫⁻ v in {v : J → ℂ | ∀ j, ‖v j‖ ∈ D}, ENNReal.ofReal (logRadialWeight β lam q v) := by
  classical
  let S : Set (J → ℂ) := {v | ∀ j, ‖v j‖ ∈ D}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => hD.preimage (by fun_prop)
  let F : (J → ℂ) → ℝ≥0∞ := S.indicator (fun v => ENNReal.ofReal (logRadialWeight β lam q v))
  have hF : Measurable F := by
    apply Measurable.indicator
    · unfold logRadialWeight
      have hmax := measurable_maxRho (ι := J) lam
      have hmin := measurable_minRho (ι := J) lam
      unfold rho
      fun_prop
    · exact hS
  have hp := (volume_measurePreserving_piCongrLeft (fun _ : J => ℂ) e).lintegral_comp hF
  have hI : MeasurableSet {v : I → ℂ | ∀ i, ‖v i‖ ∈ D} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => hD.preimage (by fun_prop)
  rw [← lintegral_indicator hI, ← lintegral_indicator hS]
  change _ = ∫⁻ v, F v
  rw [← hp]
  apply lintegral_congr
  intro v
  let w := (MeasurableEquiv.piCongrLeft (fun _ : J => ℂ) e) v
  have hcomp : w ∘ e = v := by
    funext i
    simp [w, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have heq := logRadialWeight_reindex e β lam q w
  rw [hcomp] at heq
  have hcut : (∀ i, ‖v i‖ ∈ D) ↔ ∀ j, ‖w j‖ ∈ D := by
    constructor
    · intro hv j
      obtain ⟨i, rfl⟩ := e.surjective j
      have hi := congrFun hcomp i
      change w (e i) = v i at hi
      rw [hi]
      exact hv i
    · intro hw i
      have hi := congrFun hcomp i
      change w (e i) = v i at hi
      rw [← hi]
      exact hw (e i)
  by_cases hv : ∀ i, ‖v i‖ ∈ D
  · have hw := hcut.mp hv
    dsimp only [w] at hw heq
    simp only [F, S, Set.indicator, Set.mem_ofPred_eq, ite_eq_left hv, ite_eq_left hw, heq]
  · have hw : ¬∀ j, ‖w j‖ ∈ D := fun h => hv (hcut.mpr h)
    dsimp only [w] at hw
    simp only [F, S, Set.indicator, Set.mem_ofPred_eq, ite_eq_right hv, ite_eq_right hw]

/-- The finite-cutoff vector bound for any finite carrier of the paper size. -/
theorem logRadialWeight_bound_any {β eps : ℝ} (hβ : 2 < β) (heps : 0 < eps) (heps1 : eps < 1)
    (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I] [Nonempty I], Fintype.card I = k + 2 →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam ≤ Appendix.lamBound eps (k + 2) →
      (∫⁻ v in {v : I → ℂ | ∀ i, ‖v i‖ ≤ eps * truncationScale p₀ β lam},
        ENNReal.ofReal (logRadialWeight β lam q v)) ≤
          ENNReal.ofReal (C * (lam ^ ((2 - β) * (k + 2)) * Appendix.gammaBeta p₀ β lam (k + 2))) := by
  obtain ⟨C, hC, hb⟩ := logRadialWeight_bound hβ heps heps1 k q
  refine ⟨C, hC, fun I _ _ hI p₀ lam hlam hlamB => ?_⟩
  let e : Fin (k + 2) ≃ I := Fintype.equivOfCardEq (by simpa using hI.symm)
  have he := lintegral_logRadialWeight_relabel e β lam q (Iic (eps * truncationScale p₀ β lam)) measurableSet_Iic
  simp only [Set.mem_Iic] at he
  rw [← he]
  exact hb p₀ lam hlam hlamB

/-- Infinite-cutoff vector convergence on the original carrier, with its size
restriction explicit. No finite-cutoff limiting argument is used. -/
theorem logRadialWeightInfinity_bound_any {β : ℝ} (hβ : 2 < β) (k q : ℕ)
    (hsize : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I] [Nonempty I], Fintype.card I = k + 2 →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam →
      (∫⁻ v : I → ℂ, ENNReal.ofReal (logRadialWeight β lam q v)) ≤
        ENNReal.ofReal (C * (lam ^ ((2 - β) * (k + 2)) * Appendix.gammaBeta p₀ β lam (k + 2))) := by
  obtain ⟨C, hC, hb⟩ := logRadialWeightInfinity_bound hβ k q hsize
  refine ⟨C, hC, fun I _ _ hI p₀ lam hlam => ?_⟩
  let e : Fin (k + 2) ≃ I := Fintype.equivOfCardEq (by simpa using hI.symm)
  have he := lintegral_logRadialWeight_relabel e β lam q univ MeasurableSet.univ
  simp only [mem_univ, implies_true, Set.ofPred_true, Measure.restrict_univ] at he
  rw [← he]
  exact hb p₀ lam hlam

end MultipoleBKT.SmallIntegral.RouteJ

end
