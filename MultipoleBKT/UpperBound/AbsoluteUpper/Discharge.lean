/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.AbsoluteUpper.Assembly
public import MultipoleBKT.UpperBound.BoundedUpper.Proposition

/-!
# Proposition 5.20 with the inputs of Proposition 5.18 discharged

The inputs `KPlusBoundInput` (eq. (5.67)) and `ExternalPositivityInput` (equation (5.101)) of `MultipoleBKT.UpperBound.AbsoluteUpper.prop_5_20_of_inputs` are proved by `MultipoleBKT.UpperBound.BoundedUpper.prop_5_18` (second conjunct) and
`MultipoleBKT.UpperBound.BoundedUpper.one_le_externalNormalization`.

* `kPlusBoundInput_holds`, `externalPositivityInput_holds`;
* `prop_5_20_of_simplified`: **Proposition 5.20** from the statement of Lemma 5.37
  (`SimplifiedBoundUpper`) and the transfer of Lemma 4.59 / Proposition 4.27 to an abstract activity
  (`AbsoluteConvergenceTransfer`) only.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace AbsoluteUpper

open Hierarchical

/-- **Eq. (5.67)** in the form `KPlusBoundInput`, from Proposition 5.18
(`MultipoleBKT.UpperBound.BoundedUpper.prop_5_18`). -/
theorem kPlusBoundInput_holds {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {β : ℝ}
    (hβ : 2 < β) (L : ℝ) : KPlusBoundInput χ p₀ β L := by
  intro M hM hMp ε₀ hε₀ hε₁ k hk
  obtain ⟨C, hC, lam₀, hlam₀, h⟩ :=
    (BoundedUpper.prop_5_18 hχ hβ hp₀ L hε₀ hε₁ hM hMp).2 k hk
  refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
  refine ⟨N₀, fun N hN V Z hVZ X hX hXne hXg hXp hXk => ?_⟩
  exact (hN₀ N hN V Z hVZ.1 X hX hXne (Finset.biUnion_subset.2 fun S hS => hXg S hS) hXp hXk).1

/-- **Eq. (5.101)** in the form `ExternalPositivityInput`
(`MultipoleBKT.UpperBound.BoundedUpper.one_le_externalNormalization`). -/
theorem externalPositivityInput_holds {χ : ℂ → ℝ} (hχ : IsMollifier χ) (p₀ : ℕ) (β L : ℝ) :
    ExternalPositivityInput χ p₀ β L :=
  fun _ _ _ _ _ hlam hε₀ hN hlamh hM hM3 hVZ _ hS hpos =>
    BoundedUpper.one_le_externalNormalization hχ hlam hε₀ hN hlamh hM hM3 hVZ hS hpos

/-- **Proposition 5.20**, internal form, from the statement
of Lemma 5.37 (`SimplifiedBoundUpper`) and the transfer of Lemma 4.59 and Proposition 4.27 to an
abstract activity (`AbsoluteConvergenceTransfer`); the conclusions are those of
`prop_5_20_of_inputs`. -/
theorem prop_5_20_of_simplified (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) (L : ℝ) (hsimp : SimplifiedBoundUpper χ p₀ β L)
    (htr : AbsoluteConvergenceTransfer χ p₀ β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
            IsFrozenConfig p₀ β lam M ε₀ V Z →
            ∀ π : Finset (Finset ℕ), IsSubpartition π →
              (∀ S ∈ π, S ⊆ (Finset.univ \ V).map Fin.valEmbedding) →
              (∀ S ∈ π, S.card ≤ pBeta p₀ β) → ProfileBound p₀ β lam ε₀ N π →
              AbsoluteUpperBounds (plusActivity χ N p₀ β lam M ε₀ L V Z) π (pBeta p₀ β)
                  (C * N * errorRate p₀ β lam) ∧
                AbsoluteUpperBounds (hatActivity χ N p₀ β lam M ε₀ L V Z) π (pBeta p₀ β)
                  (C * N * errorRate p₀ β lam) ∧
                0 < clusterSeriesW χ N p₀ β lam M ε₀ L V Z π ∧
                clusterSeriesW χ N p₀ β lam M ε₀ L V Z π =
                  Real.exp (connectedSeries (hatActivity χ N p₀ β lam M ε₀ L V Z) π) :=
  prop_5_20_of_inputs χ hχ p₀ hp₀ β hβ L hsimp (kPlusBoundInput_holds hχ hp₀ hβ L)
    (externalPositivityInput_holds hχ p₀ β L) htr

end AbsoluteUpper

end UpperBound

end MultipoleBKT

end
