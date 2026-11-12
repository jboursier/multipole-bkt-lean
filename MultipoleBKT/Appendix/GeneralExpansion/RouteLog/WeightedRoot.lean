/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansion.RouteLog.WeightedSpatial

/-!
# Tonelli after the weighted tree position integral

See (A.39). Integrate tree positions first, retaining the root weight,
then the independent dipole vectors. This includes a singleton tree.
-/

@[expose] public section

namespace MultipoleBKT.GeneralExpansion

open MeasureTheory Set Finset Function
open scoped ENNReal Classical
open MultipoleIntegral

variable {ι : Type*} [Fintype ι] {M lam : ℝ}

/-- Root-weighted tree integration through the endpoint coordinates. -/
theorem lintegral_rooted_weighted_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (i₀ : ι) (H : ℂ → ℝ≥0∞)
    (hH : Measurable H) (G : ℂ → ℂ → ℝ≥0∞) (hG : Measurable (uncurry G)) :
    ∫⁻ c : ι → ℂ × ℂ, connInd M lam c * ((∏ i, H ((c i).1 - (c i).2)) *
        G ((c i₀).1 - (c i₀).2) (c i₀).2) ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) *
        ((∏ _c ∈ univ.erase i₀, ∫⁻ w, H w * ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2)) *
          ∫⁻ w, H w * ∫⁻ y, G w y) := by
  set K : ℝ≥0∞ := ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞)
  set B : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2)
  have hB : Measurable B := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hGy : ∀ w, Measurable (G w) := fun w => hG.comp (measurable_const.prodMk measurable_id)
  have hGint : Measurable fun w => ∫⁻ y, G w y := hG.lintegral_prod_right'
  have hF : Measurable fun c : ι → ℂ × ℂ => connInd M lam c * ((∏ i, H ((c i).1 - (c i).2)) *
      G ((c i₀).1 - (c i₀).2) (c i₀).2) := by
    refine (measurable_connInd M lam).mul ((Finset.measurable_prod _ fun i _ =>
      hH.comp ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd)).mul ?_)
    exact hG.comp (((measurable_pi_apply i₀).fst.sub (measurable_pi_apply i₀).snd).prodMk
      (measurable_pi_apply i₀).snd)
  rw [lintegral_dipole_coords hF]
  -- the positions integral, for fixed dipole vectors
  have hinner : ∀ r : ι → ℂ, ∫⁻ y : ι → ℂ, connInd M lam (fun i => (y i + r i, y i)) *
      ((∏ i, H ((y i + r i, y i).1 - (y i + r i, y i).2)) *
        G ((y i₀ + r i₀, y i₀).1 - (y i₀ + r i₀, y i₀).2) (y i₀ + r i₀, y i₀).2) ≤
      ∏ i, (if i = i₀ then K * (H (r i) * ∫⁻ t, G (r i) t) else H (r i) * B (r i)) := by
    intro r
    simp only [add_sub_cancel_left]
    calc ∫⁻ y : ι → ℂ, connInd M lam (fun i => (y i + r i, y i)) *
          ((∏ i, H (r i)) * G (r i₀) (y i₀))
        = ∫⁻ y : ι → ℂ, (∏ i, H (r i)) * (G (r i₀) (y i₀) * connectedIndicator M lam y r) := by
          refine lintegral_congr fun y => ?_
          rw [connInd_dipole]
          ring
      _ = (∏ i, H (r i)) * ∫⁻ y : ι → ℂ, G (r i₀) (y i₀) * connectedIndicator M lam y r := by
          refine lintegral_const_mul _ ?_
          refine ((hGy (r i₀)).comp (measurable_pi_apply i₀)).mul ?_
          have hm : Measurable fun y : ι → ℂ => connInd M lam (fun i => (y i + r i, y i)) :=
            (measurable_connInd (ι := ι) M lam).comp
              (f := fun y : ι → ℂ => fun i => (y i + r i, y i))
              (measurable_pi_iff.2 fun i =>
                ((measurable_pi_apply i).add measurable_const).prodMk (measurable_pi_apply i))
          have heq : (fun y : ι → ℂ => connInd M lam (fun i => (y i + r i, y i))) =
              fun y => connectedIndicator M lam y r := funext fun y => connInd_dipole y r
          rw [heq] at hm
          exact hm
      _ ≤ (∏ i, H (r i)) * (K * (∫⁻ t, G (r i₀) t) * ∏ c ∈ univ.erase i₀, B (r c)) := by
          gcongr
          have hci : ∀ y : ι → ℂ, connectedIndicator M lam y r =
              (if (SimpleGraph.fromRel fun i j => MultipoleLinked M lam
                (y i + r i, y i) (y j + r j, y j)).Connected then (1 : ℝ≥0∞) else 0) := by
            intro y
            unfold connectedIndicator
            split_ifs <;> rfl
          simp_rw [hci]
          exact lintegral_connected_positions_root_le_weighted hM hlam (G (r i₀)) (hGy (r i₀)) r i₀
      _ = ∏ i, (if i = i₀ then K * (H (r i) * ∫⁻ t, G (r i) t) else H (r i) * B (r i)) := by
          rw [← mul_prod_erase univ (fun i => if i = i₀ then K * (H (r i) * ∫⁻ t, G (r i) t)
            else H (r i) * B (r i)) (mem_univ i₀), ← mul_prod_erase univ (fun i => H (r i))
            (mem_univ i₀)]
          simp only [↓reduceIte]
          have hprod : ∏ c ∈ univ.erase i₀, (if c = i₀ then K * (H (r c) * ∫⁻ t, G (r c) t)
              else H (r c) * B (r c)) = ∏ c ∈ univ.erase i₀, (H (r c) * B (r c)) :=
            prod_congr rfl fun c hc => by simp [ne_of_mem_erase hc]
          rw [hprod, prod_mul_distrib]
          ring
  have hfac : ∀ i, Measurable fun w : ℂ =>
      (if i = i₀ then K * (H w * ∫⁻ t, G w t) else H w * B w) := by
    intro i
    split_ifs
    · exact measurable_const.mul (hH.mul hGint)
    · exact hH.mul hB
  calc ∫⁻ r : ι → ℂ, ∫⁻ y : ι → ℂ, connInd M lam (fun i => (y i + r i, y i)) *
        ((∏ i, H ((y i + r i, y i).1 - (y i + r i, y i).2)) *
          G ((y i₀ + r i₀, y i₀).1 - (y i₀ + r i₀, y i₀).2) (y i₀ + r i₀, y i₀).2)
      ≤ ∫⁻ r : ι → ℂ, ∏ i, (if i = i₀ then K * (H (r i) * ∫⁻ t, G (r i) t)
          else H (r i) * B (r i)) := lintegral_mono hinner
    _ = ∏ i, ∫⁻ w, (if i = i₀ then K * (H w * ∫⁻ t, G w t) else H w * B w) :=
        lintegral_pi_prod_eq (fun i w => if i = i₀ then K * (H w * ∫⁻ t, G w t)
          else H w * B w) hfac
    _ = K * ((∏ _c ∈ univ.erase i₀, ∫⁻ w, H w * B w) * ∫⁻ w, H w * ∫⁻ y, G w y) := by
        rw [← mul_prod_erase univ _ (mem_univ i₀)]
        simp only [↓reduceIte]
        have hprod : ∏ c ∈ univ.erase i₀, ∫⁻ w, (if c = i₀ then K * (H w * ∫⁻ t, G w t)
            else H w * B w) = ∏ _c ∈ univ.erase i₀, ∫⁻ w, H w * B w :=
          prod_congr rfl fun c hc => by simp [ne_of_mem_erase hc]
        rw [hprod, lintegral_const_mul K (f := fun w => H w * ∫⁻ t, G w t) (hH.mul hGint)]
        ring

/-- The same rooted integral with the number of non-root radii explicit.
This form avoids any dependence on a chosen equality decision procedure. -/
theorem lintegral_rooted_weighted_power_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (i₀ : ι)
    (H : ℂ → ℝ≥0∞) (hH : Measurable H) (G : ℂ → ℂ → ℝ≥0∞)
    (hG : Measurable (uncurry G)) :
    ∫⁻ c : ι → ℂ × ℂ, connInd M lam c * ((∏ i, H ((c i).1 - (c i).2)) *
        G ((c i₀).1 - (c i₀).2) (c i₀).2) ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) *
        ((∫⁻ w, H w * ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2)) ^
          (Fintype.card ι - 1) * ∫⁻ w, H w * ∫⁻ y, G w y) := by
  have hb := lintegral_rooted_weighted_le hM hlam i₀ H hH G hG
  simpa only [prod_const, card_erase_of_mem (mem_univ i₀), card_univ] using hb

end MultipoleBKT.GeneralExpansion

end
