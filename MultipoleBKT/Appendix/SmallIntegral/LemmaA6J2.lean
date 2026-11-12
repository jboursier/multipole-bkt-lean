/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJext.Integration

/-!
# Lemma A.4: logarithmic integration of the external gain

See (A.18),
(A.20) and its proof.
Retain the near, odd and even trees. In endpoint coordinates integrate the
common translation first and keep its logarithm. The remaining cutoff tree
integrals give logarithms. The radius allocation cancels the root
square, and the three radial regimes give a coefficient uniform in epsilon_0
for the bad-point term.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps UpperBound RouteJ RouteJext
open scoped Classical ENNReal

variable {χ : ℂ → ℝ} {β M : ℝ}

/-- The external-gain bound with its bad-point coefficient chosen before
 epsilon_0, as in (A.20), Lemma A.4. -/
theorem lemma_A6_J2 (hχ : IsMollifier χ) (hβ : 2 < β) (k : ℕ) (hM : 1 ≤ M) (p₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧
      ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X), 2 ≤ X.card →
      (X.biUnion id).card = k → ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) → ∀ Ta : Fin n → Finset (ℕ × ℕ),
      (∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf) → ∀ Tb : Finset (ℕ × ℕ),
      Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf →
      ∀ hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X,
      (∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (z i)) S ≤
          blockRadius hX (fun i => dipoleLength (z i)) (hatS l z)) →
      ∀ lam : ℝ, 0 < lam → lam ≤ ε₀ → ∀ (N : ℕ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
        integralJext χ β lam M ε₀ p₀ N V Z hX Xs Ta Tb hatS ≤
          ENNReal.ofReal (lam ^ ((2 - β) * (k : ℝ)) *
            (Cε * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
              C * ε₀ ^ (alphaExponent β * k) * V.card)) := by
  by_cases hk : 2 ≤ k
  swap
  · refine ⟨1, one_pos, fun eps _ _ => ⟨1, one_pos, fun X hX h2 hV => ?_⟩⟩
    have hcard : X.card ≤ (X.biUnion id).card := by
      have h := Fintype.card_le_of_surjective _ (Limits.blockOf_surjective hX)
      simpa only [Fintype.card_coe] using h
    omega
  obtain ⟨CT, hCT, hterm⟩ := term_bound hχ hβ hM p₀ (by omega : 1 ≤ k)
  let K : ℝ := ((k ^ k) ^ k : ℕ)
  let G : ℝ := k * K
  have hK : 0 < K := by dsimp only [K]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  refine ⟨G * CT, mul_pos hG hCT, fun eps heps heps1 =>
    ⟨G * CT * eps ^ (-2 : ℝ), by positivity, ?_⟩⟩
  intro X hX h2 hV n Xs hXs hdisj Ta hTa Tb hTb hatS hhat lam hlam hle N V Z
  have := labels_nonempty hX h2
  have hcard : Fintype.card (X.biUnion id) = k := by rw [Fintype.card_coe, hV]
  have hBcard : Fintype.card X ≤ k := by
    rw [← hcard]
    exact Fintype.card_le_of_surjective _ (Limits.blockOf_surjective hX)
  have hscale := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hh : 0 ≤ eps * truncationScale p₀ β lam := mul_nonneg heps.le hscale.le
  let A := univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
  let E := (graphOf (X.biUnion id) Tb).edgeFinset
  let F (Q : NearTreeFamily (Limits.blockOf X)) := nearForest (Limits.blockOf X) (fun b => (Q b).val)
  let W (j : X.biUnion id) (Q : NearTreeFamily (Limits.blockOf X)) :=
    term χ β lam M eps p₀ V Z A E (F Q) j
  have hW j Q : Measurable (W j Q) := measurable_term hχ hlam p₀ V Z A E (F Q) j
  let B : ℝ := lam ^ ((2 - β) * k) *
    (CT * eps ^ (-2 : ℝ) * N * truncationScale p₀ β lam ^ (-2 : ℝ) +
      CT * eps ^ (alphaExponent β * k) * V.card)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpt (c : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal (integrandJext χ β lam M eps p₀ V Z hX Xs Ta Tb hatS c) ≤
        ∑ j, ∑ Q : NearTreeFamily (Limits.blockOf X), W j Q c := by
    have hc := core_le_retained_sum hX Xs hXs hdisj Ta hTa Tb hTb c
      (fun l => hatS l c) (fun l => hhat l c) hM hlam (eps := eps) (R := truncationScale p₀ β lam)
    have hg := extGain_le_sum (V := V) (Z := Z) hh c (fun i => (le_max_left _ _).trans (rhoD_le_maxRad lam c i))
    have hg' := ENNReal.ofReal_le_ofReal hg
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => gainW_nonneg _ _)] at hg'
    have hi : integrandJext χ β lam M eps p₀ V Z hX Xs Ta Tb hatS c =
        extGain p₀ β lam eps V Z c * core M lam eps (truncationScale p₀ β lam)
          hX Xs Ta Tb (fun l => hatS l c) c *
            ∏ i, cutDens χ β lam (eps * truncationScale p₀ β lam) (c i) := by
      unfold integrandJext core
      ring
    rw [hi, ENNReal.ofReal_mul' (prod_nonneg fun i _ => cutDens_nonneg _ _),
      ENNReal.ofReal_mul (show 0 ≤ extGain p₀ β lam eps V Z c from sq_nonneg _),
      ENNReal.ofReal_prod_of_nonneg (fun i _ => cutDens_nonneg _ _)]
    refine (mul_le_mul' (mul_le_mul' hg' hc) le_rfl).trans_eq ?_
    simp only [sum_mul, mul_sum, W, term]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro Q _
    ring
  obtain ⟨_, _, _, hinter, hconn, hcount⟩ := trees_structure hX hXs hdisj hTa hTb
  have hcount' : A.card + E.card + 1 ≤ Fintype.card X := by
    have ha : A.card ≤ ∑ l, (graphOf (X.biUnion id) (Ta l)).edgeFinset.card := card_biUnion_le
    dsimp only [E]
    omega
  have hWB (j : X.biUnion id) (Q : NearTreeFamily (Limits.blockOf X)) :
      (∫⁻ c in boxConfig (X.biUnion id) N, W j Q c) ≤ ENNReal.ofReal B := by
    obtain ⟨hT, hTE, _⟩ := retained_tree (Limits.blockOf X) (fun b => (Q b).val)
      (fun b => (Q b).property) A E hinter hconn hcount'
    exact hterm eps lam hlam hle heps1.le (X.biUnion id) hcard V Z A E (F Q) hT hTE j
  have hfamily : (Fintype.card (NearTreeFamily (Limits.blockOf X)) : ℝ≥0∞) ≤ ENNReal.ofReal K := by
    rw [show ENNReal.ofReal K = (((k ^ k) ^ k : ℕ) : ℝ≥0∞) by rw [ENNReal.ofReal_natCast]]
    exact_mod_cast card_nearTreeFamily_le (Limits.blockOf X) hk hcard.le hBcard
  unfold integralJext
  calc
    _ ≤ ∫⁻ c in boxConfig (X.biUnion id) N, ∑ j, ∑ Q, W j Q c := lintegral_mono hpt
    _ = ∑ j, ∑ Q, ∫⁻ c in boxConfig (X.biUnion id) N, W j Q c := by
      rw [lintegral_finsetSum _ (fun j _ => Finset.measurable_sum _ fun Q _ => hW j Q)]
      exact sum_congr rfl fun j _ => lintegral_finsetSum _ fun Q _ => hW j Q
    _ ≤ ∑ _j : X.biUnion id, ∑ _Q : NearTreeFamily (Limits.blockOf X), ENNReal.ofReal B :=
      sum_le_sum fun j _ => sum_le_sum fun Q _ => hWB j Q
    _ ≤ ENNReal.ofReal G * ENNReal.ofReal B := by
      simp only [sum_const, card_univ, nsmul_eq_mul, hcard]
      have hb := mul_le_mul' (le_refl (k : ℝ≥0∞)) (mul_le_mul' hfamily (le_refl (ENNReal.ofReal B)))
      refine hb.trans_eq ?_
      rw [← mul_assoc, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ = _ := by
      rw [← ENNReal.ofReal_mul hG.le]
      congr 1
      dsimp only [B]
      ring

end MultipoleBKT.SmallIntegral

end
