/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.Defs
public import MultipoleBKT.Matching.Measurable
public import MultipoleBKT.Matching.Pair

/-!
# Removing the pairing (proof of Lemma 5.40, Step 1)

The paper: eq. (5.121): by Lemma 4.3,
`∏_{i ≠ j} 𝟙_{𝒜_ij} = 𝟙_{σ = Id}`, and "since there are `N₁!` permutations and particles are
indistinguishable",
`∫ 𝟙_{σ = Id} F(x, y) dx dy = (1/N₁!) ∫ F(x, y ∘ σ) dx dy`, the matching being recomputed.

Here `relabelNeg π c = (x_i, y_{π i})_i` relabels the negative charges and
`matched c = relabelNeg (σ c) c = (x_i, y_{σ(i)})_i` are the matched dipoles of an arbitrary
configuration. When the opposite-sign distances are distinct (almost everywhere,
`ae_injective_norm_sub`), the stable matching is equivariant:
`σ(relabelNeg π c) = ρ ↔ σ(c) = π ρ` (`stableMatching_relabelNeg_eq_iff`), so the change of
variables `c ↦ relabelNeg π c` (measure preserving, `measurePreserving_relabelNeg`) maps
`{σ = π}` onto `{σ = Id}` up to a null set. Summing over the `n!` permutations gives
`lintegral_stablePairs_eq`:
`n! ∫_{(Λ²)^n} 𝟙_{∏ 𝒜_ij} F = ∫_{(Λ²)^n} F ∘ matched` for every `F` (no measurability needed).
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset Function
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {n : ℕ}

/-- Relabelling the negative charges: `(x_i, y_{π(i)})_i`. -/
def relabelNeg (π : Equiv.Perm (Fin n)) (c : Fin n → ℂ × ℂ) : Fin n → ℂ × ℂ :=
  fun i => ((c i).1, (c (π i)).2)

theorem relabelNeg_relabelNeg (π ρ : Equiv.Perm (Fin n)) (c : Fin n → ℂ × ℂ) :
    relabelNeg π (relabelNeg ρ c) = relabelNeg (ρ * π) c := rfl

theorem relabelNeg_one (c : Fin n → ℂ × ℂ) : relabelNeg 1 c = c := rfl

/-- The matched dipoles `(x_i, y_{σ_n(i)})_i` of a configuration. -/
noncomputable abbrev matched (c : Fin n → ℂ × ℂ) : Fin n → ℂ × ℂ := relabelNeg (stableMatching c) c

theorem relabelNeg_mem_boxPi_iff (π : Equiv.Perm (Fin n)) (Nₐ : ℕ) (c : Fin n → ℂ × ℂ) :
    relabelNeg π c ∈ boxPi Nₐ n ↔ c ∈ boxPi Nₐ n := by
  simp only [boxPi, Set.mem_univ_pi, relabelNeg, Set.mem_prod]
  constructor
  · intro h i
    refine ⟨(h i).1, ?_⟩
    have := (h (π.symm i)).2
    rwa [Equiv.apply_symm_apply] at this
  · intro h i
    exact ⟨(h i).1, (h (π i)).2⟩

/-- Distinct opposite-sign distances are preserved by relabelling the negative charges. -/
theorem injective_norm_sub_relabelNeg {c : Fin n → ℂ × ℂ}
    (hc : Injective fun p : Fin n × Fin n => ‖(c p.1).1 - (c p.2).2‖) (π : Equiv.Perm (Fin n)) :
    Injective fun p : Fin n × Fin n => ‖(relabelNeg π c p.1).1 - (relabelNeg π c p.2).2‖ := by
  intro p q hpq
  have := @hc (p.1, π p.2) (q.1, π q.2) hpq
  simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at this
  exact Prod.ext this.1 this.2

/-- **Equivariance of the stable matching** (distinct opposite-sign distances):
`σ(relabelNeg π c) = ρ ↔ σ(c) = π ρ`. -/
theorem stableMatching_relabelNeg_eq_iff {c : Fin n → ℂ × ℂ}
    (hc : Injective fun p : Fin n × Fin n => ‖(c p.1).1 - (c p.2).2‖) (π ρ : Equiv.Perm (Fin n)) :
    stableMatching (relabelNeg π c) = ρ ↔ stableMatching c = π * ρ := by
  rw [stableMatching_eq_iff_of_injective (injective_norm_sub_relabelNeg hc π),
    stableMatching_eq_iff_of_injective hc]
  rfl

/-- `relabelNeg π` as a measurable equivalence. -/
def relabelNegEquiv (π : Equiv.Perm (Fin n)) : (Fin n → ℂ × ℂ) ≃ᵐ (Fin n → ℂ × ℂ) where
  toFun := relabelNeg π
  invFun := relabelNeg π⁻¹
  left_inv c := by
    rw [relabelNeg_relabelNeg, mul_inv_cancel, relabelNeg_one]
  right_inv c := by
    rw [relabelNeg_relabelNeg, inv_mul_cancel, relabelNeg_one]
  measurable_toFun := by
    refine measurable_pi_iff.2 fun i => ?_
    exact ((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply (π i)).snd)
  measurable_invFun := by
    refine measurable_pi_iff.2 fun i => ?_
    exact ((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply (π⁻¹ i)).snd)

theorem coe_relabelNegEquiv (π : Equiv.Perm (Fin n)) : ⇑(relabelNegEquiv π) = relabelNeg π := rfl

/-- `relabelNeg π` preserves Lebesgue measure. -/
theorem measurePreserving_relabelNeg (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (relabelNeg π) volume volume := by
  set e := MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ (Fin n)
  have he : MeasurePreserving e volume volume :=
    volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ (Fin n)
  have hp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ) π.symm)
      volume volume := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℂ) π.symm
  have hprod : MeasurePreserving (Prod.map id (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℂ)
      π.symm)) (volume : Measure ((Fin n → ℂ) × (Fin n → ℂ))) volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id _).prod hp
  have hcomp := he.symm.comp (hprod.comp he)
  convert hcomp using 1
  funext c
  funext i
  simp only [Function.comp_apply, e, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow, Prod.map,
    id, relabelNeg, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  congr 1
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simp

/-- The matched dipoles of `c` with `σ(c) = π` are `relabelNeg π c`, and the stable matching of a
relabelled configuration: almost everywhere, `σ(relabelNeg π⁻¹ c) = π ↔ σ(c) = Id`. -/
theorem ae_stableMatching_relabelNeg_inv_eq_iff (π : Equiv.Perm (Fin n)) :
    ∀ᵐ c ∂(volume : Measure (Fin n → ℂ × ℂ)),
      stableMatching (relabelNeg π⁻¹ c) = π ↔ stableMatching c = 1 := by
  filter_upwards [ae_injective_norm_sub (ι := Fin n)] with c hc
  rw [stableMatching_relabelNeg_eq_iff hc, inv_mul_cancel]

/-- **Removing the pairing** (eq. (5.121)): for every `F ≥ 0`,
`n! ∫_{(Λ²)^n} 𝟙_{∏_{i<j} 𝒜_ij} F = ∫_{(Λ²)^n} F((x_i, y_{σ_n(i)})_i)`. -/
theorem lintegral_stablePairs_eq (F : (Fin n → ℂ × ℂ) → ℝ≥0∞) (Nₐ : ℕ) :
    (n.factorial : ℝ≥0∞) * ∫⁻ c in boxPi Nₐ n,
        (by classical exact if StablePairs c then 1 else 0) * F c =
      ∫⁻ c in boxPi Nₐ n, F (matched c) := by
  classical
  have hbox := measurableSet_boxPi Nₐ n
  set A : Equiv.Perm (Fin n) → Set (Fin n → ℂ × ℂ) := fun π =>
    boxPi Nₐ n ∩ {c | stableMatching c = π} with hA
  have hAm : ∀ π, MeasurableSet (A π) := fun π => hbox.inter (measurableSet_stableMatching_eq π)
  have hAd : Pairwise (Disjoint on A) := by
    intro π ρ hπρ
    refine Set.disjoint_left.2 fun c hc hc' => hπρ ?_
    exact hc.2.symm.trans hc'.2
  have hU : ⋃ π, A π = boxPi Nₐ n := by
    ext c
    simp only [Set.mem_iUnion, hA, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨_, h, rfl⟩⟩
  -- each piece is the integral over `{σ = Id}`
  have hpiece : ∀ π, ∫⁻ c in A π, F (matched c) = ∫⁻ c in A 1, F c := by
    intro π
    have h1 : ∫⁻ c in A π, F (matched c) = ∫⁻ c in A π, F (relabelNeg π c) :=
      setLIntegral_congr_fun (hAm π) fun c hc => by
        simp only [matched]
        rw [hc.2]
    have hpre : A π = relabelNeg π ⁻¹' (relabelNeg π⁻¹ ⁻¹' A π) := by
      ext c
      simp only [Set.mem_preimage, relabelNeg_relabelNeg, mul_inv_cancel, relabelNeg_one]
    rw [h1, hpre, (measurePreserving_relabelNeg π).setLIntegral_comp_preimage_emb
      (relabelNegEquiv π).measurableEmbedding]
    refine setLIntegral_congr ?_
    filter_upwards [ae_stableMatching_relabelNeg_inv_eq_iff π] with c hc
    simp only [Set.mem_preimage, hA, Set.mem_inter_iff, Set.mem_ofPred_eq,
      relabelNeg_mem_boxPi_iff, hc]
  calc (n.factorial : ℝ≥0∞) * ∫⁻ c in boxPi Nₐ n, (if StablePairs c then 1 else 0) * F c
      = (n.factorial : ℝ≥0∞) * ∫⁻ c in A 1, F c := by
        congr 1
        rw [← lintegral_indicator hbox, ← lintegral_indicator (hAm 1)]
        refine lintegral_congr fun c => ?_
        by_cases hc : c ∈ boxPi Nₐ n
        · have hiff : StablePairs c ↔ stableMatching c = 1 :=
            (stableMatching_eq_refl_iff c).symm
          by_cases hs : StablePairs c
          · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (show c ∈ A 1 from ⟨hc, hiff.1 hs⟩),
              ite_eq_left hs, one_mul]
          · rw [Set.indicator_of_mem hc,
              Set.indicator_of_notMem (show c ∉ A 1 from fun h => hs (hiff.2 h.2)),
              ite_eq_right hs, zero_mul]
        · rw [Set.indicator_of_notMem hc,
            Set.indicator_of_notMem (show c ∉ A 1 from fun h => hc h.1)]
    _ = ∑ π : Equiv.Perm (Fin n), ∫⁻ c in A π, F (matched c) := by
        rw [Finset.sum_congr rfl fun π _ => hpiece π, Finset.sum_const, Finset.card_univ,
          Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ = ∫⁻ c in boxPi Nₐ n, F (matched c) := by
        rw [← hU, lintegral_iUnion hAm hAd, tsum_fintype]

end BadPointTypes

end MultipoleBKT

end
