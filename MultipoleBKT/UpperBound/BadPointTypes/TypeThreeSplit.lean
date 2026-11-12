/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Finset.Sort

/-!
# Splitting the coordinates along a partition of the labels

The proof of Lemma 5.39 integrates the
variables of `V^3_bad`, then those of `V^1_bad` and `V^2_bad` separately. For a partition
`[n] = V₁ ∪ V₂ ∪ V₃`, with `eₖ : Fin |Vₖ| ↪o Fin n` the increasing enumeration of `Vₖ`, the map
`d ↦ (d ∘ e₁, d ∘ e₂, d ∘ e₃)` is measure preserving (`lintegral_split3`), so that the integral
of any function of the three sub-configurations is the integral over the product; Tonelli's
inequality (`lintegral_prod_le`, which needs no measurability) then separates the variables.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset
open scoped ENNReal

variable {n : ℕ} {V₁ V₂ V₃ : Finset (Fin n)}

/-- The labels `Fin |V₁| ⊕ (Fin |V₂| ⊕ Fin |V₃|)` of a partition of `Fin n`. -/
noncomputable def partitionEquiv (h12 : Disjoint V₁ V₂) (h13 : Disjoint V₁ V₃)
    (h23 : Disjoint V₂ V₃) (hcov : V₁ ∪ V₂ ∪ V₃ = univ) :
    Fin V₁.card ⊕ (Fin V₂.card ⊕ Fin V₃.card) ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (V₁.orderEmbOfFin rfl) (Sum.elim (V₂.orderEmbOfFin rfl)
    (V₃.orderEmbOfFin rfl))) (by
    have hm1 := fun a => V₁.orderEmbOfFin_mem rfl a
    have hm2 := fun a => V₂.orderEmbOfFin_mem rfl a
    have hm3 := fun a => V₃.orderEmbOfFin_mem rfl a
    constructor
    · have hd : ∀ {V W : Finset (Fin n)}, Disjoint V W → ∀ {x y : Fin n}, x ∈ V → y ∈ W →
          x = y → False := fun hVW x y hx hy hxy =>
        Finset.disjoint_left.1 hVW hx (hxy ▸ hy)
      rintro (a | a | a) (b | b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
      · rw [(V₁.orderEmbOfFin rfl).injective hab]
      · exact (hd h12 (hm1 a) (hm2 b) hab).elim
      · exact (hd h13 (hm1 a) (hm3 b) hab).elim
      · exact (hd h12 (hm1 b) (hm2 a) hab.symm).elim
      · rw [(V₂.orderEmbOfFin rfl).injective hab]
      · exact (hd h23 (hm2 a) (hm3 b) hab).elim
      · exact (hd h13 (hm1 b) (hm3 a) hab.symm).elim
      · exact (hd h23 (hm2 b) (hm3 a) hab.symm).elim
      · rw [(V₃.orderEmbOfFin rfl).injective hab]
    · intro i
      have hi : i ∈ V₁ ∪ V₂ ∪ V₃ := hcov ▸ Finset.mem_univ i
      rcases Finset.mem_union.1 hi with hi | hi
      · rcases Finset.mem_union.1 hi with hi | hi
        · have : i ∈ Set.range (V₁.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]; exact hi
          obtain ⟨a, rfl⟩ := this
          exact ⟨Sum.inl a, rfl⟩
        · have : i ∈ Set.range (V₂.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]; exact hi
          obtain ⟨a, rfl⟩ := this
          exact ⟨Sum.inr (Sum.inl a), rfl⟩
      · have : i ∈ Set.range (V₃.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hi
        obtain ⟨a, rfl⟩ := this
        exact ⟨Sum.inr (Sum.inr a), rfl⟩)

/-- **Splitting the coordinates.** For a partition `[n] = V₁ ∪ V₂ ∪ V₃` and any `F`,
`∫ F(d ∘ e₁, d ∘ e₂, d ∘ e₃) dd = ∫ F`. -/
theorem lintegral_split3 {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (h12 : Disjoint V₁ V₂) (h13 : Disjoint V₁ V₃) (h23 : Disjoint V₂ V₃)
    (hcov : V₁ ∪ V₂ ∪ V₃ = univ)
    (F : (Fin V₁.card → α) × ((Fin V₂.card → α) × (Fin V₃.card → α)) → ℝ≥0∞) :
    ∫⁻ d : Fin n → α, F (d ∘ V₁.orderEmbOfFin rfl,
        (d ∘ V₂.orderEmbOfFin rfl, d ∘ V₃.orderEmbOfFin rfl)) = ∫⁻ p, F p := by
  set σ := partitionEquiv h12 h13 h23 hcov
  let Φ : (Fin n → α) ≃ᵐ (Fin V₁.card → α) × ((Fin V₂.card → α) × (Fin V₃.card → α)) :=
    ((MeasurableEquiv.piCongrLeft (fun _ => α) σ).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ => α)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
        (MeasurableEquiv.sumPiEquivProdPi fun _ => α))
  have hΦ : MeasurePreserving Φ volume volume := by
    refine (((volume_measurePreserving_piCongrLeft (fun _ => α) σ).symm _).trans
      (volume_measurePreserving_sumPiEquivProdPi fun _ => α)).trans ?_
    exact (MeasurePreserving.id volume).prod
      (volume_measurePreserving_sumPiEquivProdPi fun _ => α)
  have hΦd : ∀ d : Fin n → α, Φ d = (d ∘ V₁.orderEmbOfFin rfl,
      (d ∘ V₂.orderEmbOfFin rfl, d ∘ V₃.orderEmbOfFin rfl)) := by
    intro d
    rfl
  calc ∫⁻ d : Fin n → α, F (d ∘ V₁.orderEmbOfFin rfl,
        (d ∘ V₂.orderEmbOfFin rfl, d ∘ V₃.orderEmbOfFin rfl))
      = ∫⁻ d : Fin n → α, F (Φ d) := by simp_rw [hΦd]
    _ = ∫⁻ p, F p := hΦ.lintegral_comp_emb Φ.measurableEmbedding F

end BadPointTypes

end MultipoleBKT

end
