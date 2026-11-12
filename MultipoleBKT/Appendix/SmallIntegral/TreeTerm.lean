/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.Radial
public import MultipoleBKT.Limits.RouteBase.Integrand

/-!
# Configuration radii and cutoff densities

See Lemma A.4. These shared definitions relate
the extremal configuration radii to the dipole-vector radii and provide
the measurable cutoff density used by the logarithmic J integrals.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Set Finset Filter Metric SimpleGraph
open scoped ENNReal
open Limits TwoComponentCoulomb

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Defs

variable {ι : Type*} [Fintype ι]

/-- The smallest dipole radius `ρ_* = min_i max(|x_i - y_i|, λ)` of a configuration. -/
noncomputable def minRad [Nonempty ι] (lam : ℝ) (c : ι → ℂ × ℂ) : ℝ :=
  univ.inf' univ_nonempty fun i => rhoD lam (c i)

/-- The dipole weight with the length cutoff, `e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ h}`. -/
noncomputable def cutDens (χ : ℂ → ℝ) (β lam h : ℝ) (p : ℂ × ℂ) : ℝ :=
  pairDensity χ β lam p * (Iic h).indicator 1 ‖p.1 - p.2‖

theorem cutDens_nonneg (h : ℝ) (p : ℂ × ℂ) : 0 ≤ cutDens χ β lam h p :=
  mul_nonneg (pairDensity_pos _ _ _ _).le (indicator_nonneg (fun _ _ => zero_le_one) _)

end Defs

/-! ### Positions and dipole vectors -/

section PosVec

variable {ι : Type*} [Fintype ι]

theorem maxRad_ofPosVec_eq (lam : ℝ) (x u : ι → ℂ) : maxRad lam (ofPosVec x u) = maxRho lam u := by
  unfold maxRad maxRho
  congr 1
  funext i
  simp only [ofPosVec_apply, rhoD_mk]

theorem minRad_ofPosVec_eq [Nonempty ι] (lam : ℝ) (x u : ι → ℂ) :
    minRad lam (ofPosVec x u) = minRho lam u := by
  unfold minRad minRho
  congr 1
  funext i
  simp only [ofPosVec_apply, rhoD_mk]

end PosVec

/-! ### The pointwise majorant -/

section Majorant

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem rhoD_pos (hlam : 0 < lam) (d : ℂ × ℂ) : 0 < rhoD lam d := lt_max_of_lt_right hlam

theorem minRad_le (lam : ℝ) (c : ι → ℂ × ℂ) (i : ι) : minRad lam c ≤ rhoD lam (c i) :=
  inf'_le _ (mem_univ i)

theorem minRad_pos (hlam : 0 < lam) (c : ι → ℂ × ℂ) : 0 < minRad lam c :=
  (lt_inf'_iff _).2 fun _ _ => rhoD_pos hlam _

end Majorant

/-! ### Measurability -/

section Measurability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem measurable_minRad (lam : ℝ) : Measurable (minRad (ι := ι) lam) := by
  have : minRad (ι := ι) lam =
      univ.inf' univ_nonempty (fun i => fun c : ι → ℂ × ℂ => rhoD lam (c i)) := by
    funext c
    simp only [minRad, Finset.inf'_apply]
  rw [this]
  exact Finset.inf'_induction univ_nonempty _ (fun f hf g hg => hf.inf hg) fun i _ =>
    (measurable_rhoD lam).comp (measurable_pi_apply i)

theorem measurable_cutDens (hχ : IsMollifier χ) (hlam : 0 < lam) (β h : ℝ) :
    Measurable (cutDens χ β lam h) := by
  unfold cutDens
  exact (measurable_pairDensity hχ hlam β).mul ((measurable_const.indicator measurableSet_Iic).comp
    (continuous_norm.measurable.comp (measurable_fst.sub measurable_snd)))

end Measurability

theorem gammaBeta_nonneg {lam : ℝ} (hlam : 0 < lam) (p₀ : ℕ) (β : ℝ) (k : ℕ) :
    0 ≤ Appendix.gammaBeta p₀ β lam k := by
  have := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  unfold Appendix.gammaBeta
  split_ifs
  · positivity
  · positivity
  · positivity

end SmallIntegral

end MultipoleBKT

end
