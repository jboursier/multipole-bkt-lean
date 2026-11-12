/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.TreeIntegral

/-!
# Separating a coupled family of edge coordinates

See Lemma A.4. Tonelli separates the near and even
edges while leaving the odd coordinates together.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset
open scoped ENNReal

/-- Separate a coupled coordinate family from the product of the remaining
one-coordinate factors. No factorization of the coupled integrand is assumed. -/
theorem lintegral_separate_coordinates {V : Type*} [Fintype V] (p : V → Prop)
    [DecidablePred p] (F : ({i // p i} → ℂ) → ℝ≥0∞) (hF : Measurable F)
    (g : {i // ¬p i} → ℂ → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ z : V → ℂ, F (fun i => z i) * ∏ i : {i // ¬p i}, g i (z i)) =
      (∫⁻ z : {i // p i} → ℂ, F z) * ∏ i : {i // ¬p i}, ∫⁻ t : ℂ, g i t := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => ℂ) p
  let G : (({i // p i} → ℂ) × ({i // ¬p i} → ℂ)) → ℝ≥0∞ :=
    fun z => F z.1 * ∏ i, g i (z.2 i)
  have hm : Measurable G := by fun_prop
  change (∫⁻ z : V → ℂ, G (e z)) = _
  rw [(volume_preserving_piEquivPiSubtypeProd (fun _ : V => ℂ) p).lintegral_comp hm]
  change (∫⁻ z, G z ∂((volume : Measure ({i // p i} → ℂ)).prod volume)) = _
  dsimp only [G]
  have hgm : Measurable (fun z : {i // ¬p i} → ℂ => ∏ i, g i (z i)) :=
    Finset.measurable_prod univ fun i _ => (hg i).comp (measurable_pi_apply i)
  rw [lintegral_prod_mul (g := fun z : {i // ¬p i} → ℂ => ∏ i, g i (z i))
    hF.aemeasurable hgm.aemeasurable]
  congr 1
  rw [volume_pi]
  exact Limits.lintegral_pi_prod (fun _ => (volume : Measure ℂ)) g hg

/-- The retained translation coordinate integrates independently of all edges. -/
theorem lintegral_root_coordinates {V : Type*} [Fintype V] [DecidableEq V]
    (root : V) (h : ℂ → ℝ≥0∞) (hh : Measurable h)
    (F : ({i // i ≠ root} → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : V → ℂ, h (z root) * F (fun i => z i)) =
      (∫⁻ t : ℂ, h t) * ∫⁻ z : {i // i ≠ root} → ℂ, F z := by
  have hs := lintegral_separate_coordinates (fun i : V => i ≠ root) F hF
    (fun _ t => h t) (fun _ => hh)
  have hprod (z : V → ℂ) : (∏ i : {i : V // ¬i ≠ root}, h (z i)) = h (z root) := by
    let : Unique {i : V // ¬i ≠ root} :=
      { default := ⟨root, not_not.mpr rfl⟩
        uniq := fun i => Subtype.ext (not_not.mp i.property) }
    exact Fintype.prod_unique (fun i : {i : V // ¬i ≠ root} => h (z i))
  have heq : (∫⁻ z : V → ℂ, h (z root) * F (fun i => z i)) =
      ∫⁻ z : V → ℂ, F (fun i => z i) * ∏ i : {i : V // ¬i ≠ root}, h (z i) := by
    apply lintegral_congr
    intro z
    rw [hprod, mul_comm]
  rw [heq, hs]
  let : Unique {i : V // ¬i ≠ root} :=
    { default := ⟨root, not_not.mpr rfl⟩
      uniq := fun i => Subtype.ext (not_not.mp i.property) }
  rw [Fintype.prod_unique, mul_comm]

end MultipoleBKT.SmallIntegral.RouteJ

end
