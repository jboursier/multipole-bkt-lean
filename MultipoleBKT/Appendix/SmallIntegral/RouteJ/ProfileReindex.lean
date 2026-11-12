/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.EndpointIntegration

/-!
# Reindexing the odd family and the other tree edges

See Lemma A.4. The edge bijection carries the
whole odd family to child coordinates and separates its complement.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open Finset
open scoped Classical ENNReal

/-- Reindex a mixed distance profile by a bijection onto the tree edges.
The odd maximum is transported as one function on the entire odd subtype. -/
theorem mixedDistanceProfile_reindex {I E : Type*} [Fintype I] [DecidableEq E]
    (T A : Finset E) (hA : A ⊆ T) (f : I ≃ T) (even : E → Bool)
    (s t d : E → ℝ) (M a R : ℝ) :
    mixedDistanceProfile (fun i => (f i).val ∈ A)
      (fun i => even (f i.val)) (fun i => s (f i.val)) (fun i => t (f i.val))
      M a R (fun i => d (f i)) =
        jointOdd a R (fun e : A => (d e : ℂ)) *
          ∏ e ∈ T \ A, ENNReal.ofReal (spatialProfile (even e) M (s e) (t e) (d e) / s e ^ 2) := by
  let g : {i : I // (f i).val ∈ A} → A := fun i => ⟨f i.val, i.property⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply f.injective
      apply Subtype.ext
      exact congrArg (fun e : A => e.val) hij
    · intro e
      refine ⟨⟨f.symm ⟨e.val, hA e.property⟩, ?_⟩, ?_⟩
      · simp only [Equiv.apply_symm_apply]
        exact e.property
      · apply Subtype.ext
        simp [g]
  let eA := Equiv.ofBijective g hg
  have hodd := jointOdd_reindex eA a R (fun e : A => (d e : ℂ))
  unfold mixedDistanceProfile
  rw [show (fun i : {i : I // (f i).val ∈ A} => (d (f i.val) : ℂ)) =
      (fun e : A => (d e : ℂ)) ∘ eA by rfl, hodd]
  congr 1
  refine prod_bij (fun i _ => (f i.val).val) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    exact mem_sdiff.mpr ⟨(f i.val).property, i.property⟩
  · intro i _ j _ hij
    exact Subtype.ext (f.injective (Subtype.ext hij))
  · intro e he
    let i := f.symm ⟨e, (mem_sdiff.mp he).1⟩
    have hi : (f i).val = e := congrArg Subtype.val (f.apply_symm_apply _)
    exact ⟨⟨i, by change (f i).val ∉ A; rw [hi]; exact (mem_sdiff.mp he).2⟩, mem_univ _, hi⟩

end MultipoleBKT.SmallIntegral.RouteJ

end
