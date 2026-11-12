/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.ConfigurationIntegral

/-!
# Assembling the near-tree sum and the logarithmic radial majorant

See Lemma A.4, (A.22)–(A.27).
The finite near-tree count precedes the mixed spatial integration. The kernel
density comparison leaves precisely the logarithmic vector majorant.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps
open scoped Classical ENNReal

/-- A subpartition with at least two blocks has a nonempty label carrier. -/
theorem labels_nonempty {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card) :
    Nonempty (X.biUnion id) := by
  obtain ⟨S, hS⟩ := card_pos.mp (by omega : 0 < X.card)
  obtain ⟨i, _⟩ := Limits.blockOf_surjective hX ⟨S, hS⟩
  exact ⟨i⟩

/-- The assembled comparison for either hatted length cutoff. The remaining
vector integral is the one reduced to `orderedRadial` and its infinite variant. -/
theorem source_integral_le_logRadial {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 1 ≤ M) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X) (h2 : 2 ≤ X.card),
      (X.biUnion id).card = k → ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) → ∀ Ta : Fin n → Finset (ℕ × ℕ),
      (∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf) → ∀ Tb : Finset (ℕ × ℕ),
      Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf →
      ∀ hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X,
      (∀ l c, hatS l c ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (c i)) S ≤
          blockRadius hX (fun i => dipoleLength (c i)) (hatS l c)) →
      ∀ (lam : ℝ), 0 < lam → ∀ (D : Set ℝ), MeasurableSet D → ∀ N : ℕ,
      (∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal (hatJCore M lam hX Xs Ta Tb (fun l => hatS l c) c) *
          ∏ i, ENNReal.ofReal (restrictedPairDensity χ β lam D (c i))) ≤
        ENNReal.ofReal (C * N) * ∫⁻ u in {u : X.biUnion id → ℂ | ∀ i, ‖u i‖ ∈ D},
          ENNReal.ofReal (@logRadialWeight (X.biUnion id) _ (labels_nonempty hX h2) β lam (k - 1) u) := by
  obtain ⟨Cs, hCs, hs⟩ := lintegral_retainedTreeTerm_density hM (k - 1)
  obtain ⟨Cg, hCg, hg⟩ := exists_logDensityWeight_le hχ hβ
  let K : ℝ := ((k ^ k) ^ k : ℕ)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K * Cs * Cg ^ k, by positivity,
    fun X hX h2 hV n Xs hXs hdisj Ta hTa Tb hTb hatS hhat lam hlam D hD N => ?_⟩
  have := labels_nonempty hX h2
  have hV' : Fintype.card (X.biUnion id) = k := by rw [Fintype.card_coe, hV]
  have hBk : Fintype.card X ≤ k := by
    rw [← hV']
    exact Fintype.card_le_of_surjective _ (Limits.blockOf_surjective hX)
  let A := univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
  let E := (graphOf (X.biUnion id) Tb).edgeFinset
  obtain ⟨_, _, _, hinter, hconn, hcount⟩ := trees_structure hX hXs hdisj hTa hTb
  have hcount' : A.card + E.card + 1 ≤ Fintype.card X := by
    have hA : A.card ≤ ∑ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card := card_biUnion_le
    dsimp only [E]
    omega
  have hfamily : (Fintype.card (NearTreeFamily (Limits.blockOf X)) : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    have hc := card_nearTreeFamily_le (Limits.blockOf X) hk hV'.le hBk
    change (Fintype.card (NearTreeFamily (Limits.blockOf X)) : ℝ≥0∞) ≤ ENNReal.ofReal (((k ^ k) ^ k : ℕ) : ℝ)
    rw [ENNReal.ofReal_natCast]
    exact_mod_cast hc
  let W (R : NearTreeFamily (Limits.blockOf X)) (c : X.biUnion id → ℂ × ℂ) : ℝ≥0∞ :=
    retainedTreeTerm (Limits.blockOf X) M lam A E R c *
      ∏ i, ENNReal.ofReal (restrictedPairDensity χ β lam D (c i))
  have hm (R : NearTreeFamily (Limits.blockOf X)) : Measurable (W R) :=
    (measurable_retainedTreeTerm (Limits.blockOf X) M lam A E R).mul
      (Finset.measurable_prod _ fun i _ =>
        ((measurable_restrictedPairDensity hχ hlam β D hD).comp (measurable_pi_apply i)).ennreal_ofReal)
  have hpt (c : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal (hatJCore M lam hX Xs Ta Tb (fun l => hatS l c) c) *
        (∏ i, ENNReal.ofReal (restrictedPairDensity χ β lam D (c i))) ≤ ∑ R, W R c := by
    have h := hatJCore_le_retained_sum hX Xs hXs hdisj Ta hTa Tb hTb c
      (fun l => hatS l c) (fun l => hhat l c) hM hlam
    have hmul := mul_le_mul_left h (∏ i, ENNReal.ofReal (restrictedPairDensity χ β lam D (c i)))
    simpa only [sum_mul] using hmul
  have hDens : (∫⁻ u in {u : X.biUnion id → ℂ | ∀ i, ‖u i‖ ∈ D},
      ENNReal.ofReal (logDensityWeight χ β lam (k - 1) u)) ≤
      ENNReal.ofReal (Cg ^ k) * ∫⁻ u in {u : X.biUnion id → ℂ | ∀ i, ‖u i‖ ∈ D},
        ENNReal.ofReal (logRadialWeight β lam (k - 1) u) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro u
    have h := hg (X.biUnion id) lam hlam (k - 1) u
    rw [hV'] at h
    exact (ENNReal.ofReal_le_ofReal h).trans_eq (ENNReal.ofReal_mul (pow_nonneg hCg.le _))
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, ∑ R, W R c := lintegral_mono hpt
    _ = ∑ R, ∫⁻ c in boxConfig (X.biUnion id) N, W R c := lintegral_finsetSum _ fun R _ => hm R
    _ ≤ ∑ _R : NearTreeFamily (Limits.blockOf X), ENNReal.ofReal (Cs * N) *
        ∫⁻ u in {u : X.biUnion id → ℂ | ∀ i, ‖u i‖ ∈ D},
          ENNReal.ofReal (logDensityWeight χ β lam (k - 1) u) := by
      apply sum_le_sum
      intro R _
      exact hs (X.biUnion id) X (by omega) (Limits.blockOf X) R A E hinter hconn hcount' χ hχ β lam hlam D hD N
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (Cs * N) *
        (ENNReal.ofReal (Cg ^ k) * ∫⁻ u in {u : X.biUnion id → ℂ | ∀ i, ‖u i‖ ∈ D},
          ENNReal.ofReal (logRadialWeight β lam (k - 1) u))) := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      exact mul_le_mul' hfamily (mul_le_mul_right hDens _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul hK.le, ← ENNReal.ofReal_mul (mul_nonneg hK.le (mul_nonneg hCs.le (Nat.cast_nonneg _)))]
      congr 1
      congr 1
      ring

end MultipoleBKT.SmallIntegral.RouteJ

end
