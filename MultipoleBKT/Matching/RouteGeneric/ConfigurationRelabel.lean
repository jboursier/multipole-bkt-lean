/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Matching.RouteGeneric.BadRelabel

/-!
# Independent arbitrary relabelings of positive and negative charges

Section 4.1 and
Definition 5.1. Strict distance preferences identify the
relabeled matching. Thus the matched dipoles are permuted by the positive-label
permutation, and their clustering and bad sets have the same symmetry.
-/

@[expose] public section

namespace MultipoleBKT.RouteGeneric

open MeasureTheory Finset BadPointTypes UpperBound

variable {N : ℕ}

/-- Independent permutations of the two charge species. -/
def relabelCharges (π ρ : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) : Fin N → ℂ × ℂ :=
  fun i => ((c (π i)).1, (c (ρ i)).2)

private theorem injective_relabelCharges {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (π ρ : Equiv.Perm (Fin N)) :
    Function.Injective fun p : Fin N × Fin N =>
      ‖(relabelCharges π ρ c p.1).1 - (relabelCharges π ρ c p.2).2‖ := by
  intro p q hpq
  have h := hc (show (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
      (π p.1, ρ p.2) = (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
      (π q.1, ρ q.2) from hpq)
  exact Prod.ext (π.injective (congrArg Prod.fst h)) (ρ.injective (congrArg Prod.snd h))

/-- The unique strict-preference matching is equivariant under independent arbitrary
permutations, as used in (4.1). -/
theorem stableMatching_permutation {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (π ρ : Equiv.Perm (Fin N)) :
    stableMatching (relabelCharges π ρ c) = ρ.symm * stableMatching c * π := by
  apply (stableMatching_eq_iff_of_injective (injective_relabelCharges hc π ρ) _).2
  intro i j hblock
  have h := (stableMatching_eq_iff_of_injective hc (stableMatching c)).1 rfl (π i) (π j)
  apply h
  simpa only [relabelCharges, Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using hblock

/-- Recomputing the matching after relabeling only permutes the matched dipoles. -/
theorem matched_permutation {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (π ρ : Equiv.Perm (Fin N)) :
    matched (relabelCharges π ρ c) = matched c ∘ π := by
  funext i
  simp only [matched, relabelNeg, stableMatching_permutation hc, relabelCharges,
    Equiv.Perm.mul_apply, Equiv.apply_symm_apply, Function.comp_apply]

private theorem injective_matched_lengths {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) :
    Function.Injective fun i => ‖(matched c i).1 - (matched c i).2‖ := by
  intro i j hij
  exact congrArg Prod.fst (hc (show
    (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) (i, stableMatching c i) =
    (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) (j, stableMatching c j) from hij))

/-- Both same-sign clusterings of a general configuration commute with independent
arbitrary relabelings off the full polynomial exceptional set. The function `s`
selects either coordinate of a dipole. Removal values are preserved as well. -/
theorem matched_clustering_permutation {c : Fin N → ℂ × ℂ} {h : ℝ}
    (hc : OutsideExceptional h c) (π ρ : Equiv.Perm (Fin N)) (q : ℕ)
    (s : ℂ × ℂ → ℂ) :
    sameSignClustering q h (s ∘ matched c)
        (fun i => ‖(matched c i).1 - (matched c i).2‖) univ =
      (sameSignClustering q h (s ∘ matched (relabelCharges π ρ c))
        (fun i => ‖(matched (relabelCharges π ρ c) i).1 -
          (matched (relabelCharges π ρ c) i).2‖) univ).image
        fun p => (p.1.map π.toEmbedding, p.2) := by
  rw [matched_permutation hc.1]
  have ht := clustering_embedding (q := q) (h := h) π.toEmbedding (s ∘ matched c)
    (fun i => ‖(matched c i).1 - (matched c i).2‖) (injective_matched_lengths hc.1) univ
  simpa only [Finset.map_univ_equiv, Equiv.coe_toEmbedding, Function.comp_def] using ht

/-- The bad and good labels of general configurations, computed on their matched dipoles,
commute with independent permutations of both species outside the paper's null set. -/
theorem matched_badPoints_permutation {c : Fin N → ℂ × ℂ} {h : ℝ}
    (hc : OutsideExceptional h c) (π ρ : Equiv.Perm (Fin N))
    (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    badPoints p₀ β lam M ε₀ (matched c) =
      (badPoints p₀ β lam M ε₀ (matched (relabelCharges π ρ c))).map π.toEmbedding ∧
    goodPoints p₀ β lam M ε₀ (matched c) =
      (goodPoints p₀ β lam M ε₀ (matched (relabelCharges π ρ c))).map π.toEmbedding := by
  rw [matched_permutation hc.1]
  exact ⟨Permutation.badPoints_permutation π p₀ β lam M ε₀ (matched c)
    (injective_matched_lengths hc.1),
    Permutation.goodPoints_permutation π p₀ β lam M ε₀ (matched c)
      (injective_matched_lengths hc.1)⟩

/-- The full arbitrary-relabeling assertion for matched configurations holds almost
 everywhere, with one exceptional set for both species and all permutations. -/
theorem ae_matched_badPoints_permutation (h : ℝ) :
    ∀ᵐ c ∂(volume : Measure (Fin N → ℂ × ℂ)), ∀ (π ρ : Equiv.Perm (Fin N))
      (p₀ : ℕ) (β lam M ε₀ : ℝ),
      badPoints p₀ β lam M ε₀ (matched c) =
        (badPoints p₀ β lam M ε₀ (matched (relabelCharges π ρ c))).map π.toEmbedding := by
  filter_upwards [ae_outsideExceptional (ι := Fin N) h] with c hc
  exact fun π ρ p₀ β lam M ε₀ => (matched_badPoints_permutation hc π ρ p₀ β lam M ε₀).1

end MultipoleBKT.RouteGeneric

end
