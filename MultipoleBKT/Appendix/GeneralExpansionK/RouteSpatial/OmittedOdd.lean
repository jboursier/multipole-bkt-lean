/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.OddEdges
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.LongEdge

/-!
# Integrating the quadratic omitted odd-tree gain

See Step 3 of
the proof of Lemma A.7. Keep the minimum of the quadratic
cutoff gain and one global maximum tail. Factoring out `R²/H²` changes
the scale of that single tail to `H`. Logarithmic integration evaluates it jointly.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- The omitted odd profile, including the empty odd family. In that case
only the surplus long-edge gain remains. -/
noncomputable def omittedOdd {I : Type*} [Fintype I] (a R H : ℝ) (z : I → ℂ) : ℝ≥0∞ :=
  if hn : Nonempty I then
    let := hn
    {z : I → ℂ | ∀ i, a < ‖z i‖}.indicator
      (fun z => ENNReal.ofReal
        (min (R ^ 2 / H ^ 2) (R ^ 2 / (univ.sup' univ_nonempty (fun i => ‖z i‖)) ^ 2)) *
          ∏ i, ENNReal.ofReal ((‖z i‖ ^ 2)⁻¹)) z
  else ENNReal.ofReal (R ^ 2 / H ^ 2)

/-- The quadratic gain is factored once for the whole odd forest. -/
theorem omittedOdd_eq {I : Type*} [Fintype I] {a H : ℝ} (ha : 0 < a) (hH : 0 < H)
    (R : ℝ) (z : I → ℂ) :
    omittedOdd a R H z = ENNReal.ofReal (R ^ 2 / H ^ 2) * jointOdd a H z := by
  unfold omittedOdd jointOdd
  split_ifs with hn
  · let := hn
    by_cases hz : ∀ i, a < ‖z i‖
    · rw [indicator_of_mem (show z ∈ {z : I → ℂ | ∀ i, a < ‖z i‖} from hz), indicator_of_mem (show z ∈ {z : I → ℂ | ∀ i, a < ‖z i‖} from hz)]
      have hm : 0 < univ.sup' univ_nonempty (fun i => ‖z i‖) := by
        obtain ⟨i⟩ := hn
        exact (ha.trans (hz i)).trans_le (le_sup' (fun i => ‖z i‖) (mem_univ i))
      have he : min (R ^ 2 / H ^ 2)
          (R ^ 2 / (univ.sup' univ_nonempty (fun i => ‖z i‖)) ^ 2) =
          (R ^ 2 / H ^ 2) * min 1
            ((H / univ.sup' univ_nonempty (fun i => ‖z i‖)) ^ 2) := by
        rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
        congr 1
        field_simp
      rw [he, ENNReal.ofReal_mul (by positivity)]
      ring
    · rw [indicator_of_notMem (show z ∉ {z : I → ℂ | ∀ i, a < ‖z i‖} from hz), indicator_of_notMem (show z ∉ {z : I → ℂ | ∀ i, a < ‖z i‖} from hz), mul_zero]
  · rw [mul_one]

/-- The omitted odd-tree integral has the exact quadratic gain and the
written logarithmic loss. There is no exponent loss in `R/H`. -/
theorem lintegral_omittedOdd (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Type*) [Fintype I], Fintype.card I = q →
      ∀ a R H : ℝ, 0 < a → a ≤ H →
      (∫⁻ z : I → ℂ, omittedOdd a R H z) ≤
        ENNReal.ofReal (C * (R ^ 2 / H ^ 2) * (1 + Real.log (H / a)) ^ q) := by
  obtain ⟨C,hC,hb⟩ := lintegral_jointOdd q
  refine ⟨C,hC, fun I _ hI a R H ha haH => ?_⟩
  simp_rw [omittedOdd_eq ha (ha.trans_le haH) R]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul' le_rfl (hb I hI a H ha haH)).trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
