/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.HatTrees
public import MultipoleBKT.UpperBound.BoundedUpper.LemmaA6Bridge

/-!
# The separate-tree expression and hatted integrand

The proof of Proposition 4.23, and Lemma A.4.
Remove the spatial cutoff in the finite-tree comparison. This retains
the actual radii, separate even tree and maximum-distance tail.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset SimpleGraph Hierarchical Multipole Parity Peeling Limits SmallIntegral
open UpperBound.BoundedUpper UpperBound.Quadratic
open scoped Classical NNReal

/-- The hatted tree expression is bounded by the integrand of Lemma A.4.
The comparison is pointwise, so an auxiliary finite spatial cutoff may
be chosen to contain the configuration before it is removed. -/
theorem hatTreeCore_density_le_infinity {χ : ℂ → ℝ} {β lam M : ℝ} (hlam : 0 < lam)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (hhat : ∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X), blockRadius hX (fun i => dipoleLength (z i)) S ≤
        blockRadius hX (fun i => dipoleLength (z i)) (hatS l z))
    (y : X.biUnion id → ℂ × ℂ) :
    hatTreeCore M lam X Xs Ta Tb (extendConfig (X.biUnion id) y) *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
        (∏ i, pairDensity χ β lam (y i)) ≤
      integrandHatJInfinity χ β lam M hX Xs (fun l => edgesOf (Ta l)) (edgesOf Tb) hatS y := by
  let W := X.biUnion id
  let c := extendConfig W y
  have hcy (i : W) : c i = y i := extendConfig_apply_coe W y i
  let R := truncationScale 0 β lam
  have hR : 0 < R := Appendix.truncationScale_pos hlam
  let H : ℝ := 1 + ((univ.sup fun i : W => ‖(y i).1 - (y i).2‖₊ : ℝ≥0) : ℝ) +
    ((univ.sup fun p : W × W => (dipoleDist (y p.1) (y p.2)).toNNReal : ℝ≥0) : ℝ)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hr (i : W) : ‖(y i).1 - (y i).2‖ ≤ H := by
    have hb : ‖(y i).1 - (y i).2‖₊ ≤ univ.sup fun i : W => ‖(y i).1 - (y i).2‖₊ :=
      le_sup (f := fun i : W => ‖(y i).1 - (y i).2‖₊) (mem_univ i)
    have hb' : ‖(y i).1 - (y i).2‖ ≤
        ((univ.sup fun i : W => ‖(y i).1 - (y i).2‖₊ : ℝ≥0) : ℝ) := hb
    dsimp only [H]
    linarith [NNReal.coe_nonneg (univ.sup fun p : W × W => (dipoleDist (y p.1) (y p.2)).toNNReal)]
  have hd (i j : W) : dipoleDist (y i) (y j) ≤ 17 * H := by
    have hb : (dipoleDist (y i) (y j)).toNNReal ≤
        univ.sup fun p : W × W => (dipoleDist (y p.1) (y p.2)).toNNReal := le_sup (f := fun p : W × W => (dipoleDist (y p.1) (y p.2)).toNNReal) (mem_univ (i, j))
    have hb' := Real.toNNReal_le_iff_le_coe.1 hb
    dsimp only [H]
    nlinarith [NNReal.coe_nonneg (univ.sup fun i : W => ‖(y i).1 - (y i).2‖₊)]
  let ε : ℝ := H / R
  have hεR : ε * R = H := div_mul_cancel₀ H hR.ne'
  have hW : (coarsen X (univ.image Xs)).biUnion id = W :=
    biUnion_coarsen fun Y hY => by obtain ⟨l, _, rfl⟩ := mem_image.1 hY; exact hXs l
  have hlarge : ∀ {U : Finset ℕ}, U ⊆ W → ∀ i j : U,
      dipoleDist (c i) (c j) ≤ 17 * ε * R := by
    intro U hU i j
    rw [mul_assoc, hεR]
    have heq (i : U) : c i = y ⟨i, hU i.2⟩ := hcy ⟨i, hU i.2⟩
    rw [heq, heq]
    exact hd _ _
  have hkept : ∀ l, ∀ e : Sym2 ((Xs l).biUnion id),
      keptLift M lam ε R c e = keptE M lam (fun i : (Xs l).biUnion id => c i) e := by
    intro l e
    induction e using Sym2.ind with
    | h i j =>
      have hb := hlarge (biUnion_subset_biUnion_of_subset_left id (hXs l)) i j
      simp only [keptLift, keptWeight, distOn, cutOn, Sym2.lift_mk, keptE, symmLift_mk,
        ite_eq_left hb, mul_one]
      split_ifs <;> simp [one_div]
  have heven : ∀ e : Sym2 ((coarsen X (univ.image Xs)).biUnion id),
      absEvenLift M lam ε R c e = symmLift
        (fun (i j : (coarsen X (univ.image Xs)).biUnion id) => hatEven M lam (c i) (c j))
        (fun i j => by unfold hatEven; rw [ahat_comm]; exact if_congr Limits.multipoleLinked_comm rfl rfl) e := by
    intro e
    induction e using Sym2.ind with
    | h i j =>
      have hb := hlarge (hW ▸ subset_rfl) i j
      simp only [absEvenLift, Sym2.lift_mk, symmLift_mk, absEvenWeight, absOddWeight, hatEven,
        ite_eq_left hb]
      split_ifs <;> simp [ahat]
  have hdens : ∀ i : W, Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
      (Metric.closedBall (0 : ℂ) (ε * R)).indicator 1 ((y i).1 - (y i).2) = pairDensity χ β lam (y i) := by
    intro i
    rw [Set.indicator_of_mem (show (y i).1 - (y i).2 ∈ Metric.closedBall (0 : ℂ) (ε * R) by
      simpa only [Metric.mem_closedBall, dist_zero_right, hεR] using hr i), Pi.one_apply, mul_one]
    rfl
  have heq : jFullIntegrand M lam ε R χ β X Xs Ta Tb y =
      hatTreeCore M lam X Xs Ta Tb c *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then 1 else 0) *
          ∏ i, pairDensity χ β lam (y i) := by
    change jIntegrand M lam ε R X Xs Ta Tb c *
      (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then 1 else 0) *
        (∏ i, Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
          (Metric.closedBall (0 : ℂ) (ε * R)).indicator 1 ((y i).1 - (y i).2)) = _
    unfold jIntegrand hatTreeCore
    simp_rw [hkept, heven, hdens]
  have hb := jFullIntegrand_le_integrandJ (χ := χ) (β := β) (lam := lam) (M := M) (ε₀ := ε)
    0 hX Xs hXs hdisj Ta Tb hW hatS hhat y
  rw [heq] at hb
  exact hb.trans ((integrandJ_le_hatJ (χ := χ) (β := β) (lam := lam) (M := M) (ε₀ := ε) hX Xs (fun l => edgesOf (Ta l)) (edgesOf Tb) hatS 0 y).trans
    (integrandHatJ_le_infinity (χ := χ) (β := β) (lam := lam) (M := M) (ε₀ := ε) hX Xs (fun l => edgesOf (Ta l)) (edgesOf Tb) hatS 0 y))

/-- The same spatial comparison with the finite radial cutoff retained. -/
theorem hatTreeCore_density_le_cut {χ : ℂ → ℝ} {β lam M ε₀ : ℝ} (hlam : 0 < lam)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l m, l ≠ m → Disjoint (Xs l) (Xs m))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (univ.image Xs)).biUnion id))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (hhat : ∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X), blockRadius hX (fun i => dipoleLength (z i)) S ≤
        blockRadius hX (fun i => dipoleLength (z i)) (hatS l z))
    (p₀ : ℕ) (y : X.biUnion id → ℂ × ℂ) :
    hatTreeCore M lam X Xs Ta Tb (extendConfig (X.biUnion id) y) *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
        (∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (y i)) ≤
      integrandHatJ χ β lam M ε₀ p₀ hX Xs (fun l => edgesOf (Ta l)) (edgesOf Tb) hatS y := by
  have hb := hatTreeCore_density_le_infinity (χ := χ) (β := β) (M := M) hlam hX Xs hXs hdisj Ta Tb hatS hhat y
  let Q : ℝ := ∏ i, (Set.Iic (ε₀ * truncationScale p₀ β lam)).indicator (1 : ℝ → ℝ) ‖(y i).1 - (y i).2‖
  have hQ : 0 ≤ Q := prod_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have h := mul_le_mul_of_nonneg_right hb hQ
  unfold integrandHatJInfinity at h
  unfold integrandHatJ cutDens
  simp only [prod_mul_distrib]
  dsimp only [Q] at h
  convert h using 1 <;> ring

end MultipoleBKT.LowerBound.RouteBounded

end
