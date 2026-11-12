/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.RouteBounded.Measurable
public import MultipoleBKT.LowerBound.RouteBounded.ScreenRaw
public import MultipoleBKT.LowerBound.RouteBounded.IntegralBound
public import MultipoleBKT.LowerBound.BoundedLowerEps.Pointwise

/-!
# Integrating a retained grouped parity term

The proof of Proposition 4.23. Enlarge the pointwise choice of odd trees to a finite
sum, keep its independent even tree, and integrate the screened J terms.
-/

@[expose] public section

namespace MultipoleBKT.LowerBound.RouteBounded

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition Limits SmallIntegral
open UpperBound.BoundedUpper UpperBound.NonEmptyMarks
open scoped Classical ENNReal

/-- Internal integration adapter for one grouped parity term. `D` is the
actual radial density and `hTree` is supplied by the appropriate bound of Lemma A.4. -/
theorem screen_grouped_integral_le {χ : ℂ → ℝ} (_hχ : IsMollifier χ)
    {ρ : Measure (ℂ × ℂ)} {β M lam ε₀ R : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K)
    (hlam : 0 < lam) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {k N : ℕ} (hk : (X.biUnion id).card = k)
    (D : ℂ × ℂ → ℝ) (hDm : Measurable D) (hD0 : ∀ d, 0 ≤ D d)
    (hDK : ∀ y ∈ boxConfig (X.biUnion id) N, (∏ i, D (y i)) ≠ 0 → ∀ i, y i ∈ K)
    {Wb Ψ Cab : ℝ} (hWb : 1 ≤ Wb) (hΨ : 1 ≤ Ψ) (hCab : 1 ≤ Cab)
    (hstab : ∀ d ∈ K, ∀ e ∈ K, stableWeight β w d e ≤ Wb)
    (hψb : ∀ d ∈ K, ψ d ≤ Ψ)
    (hb : ∀ d ∈ K, ∀ e ∈ K,
      |oddBondUnlinked β w M lam d e| ≤ Cab * absOddWeight M lam ε₀ R d e ∧
      |evenBondMult β w M lam d e| ≤ Cab * absEvenWeight M lam ε₀ R d e)
    {m : ℕ} {Xs : Fin m → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin m → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l))
    {F A : Finset (ℕ × ℕ)} (hF : F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)))
    (hAE : A ⊆ univ.biUnion Es) (hA : A ∈ relEulerianPairs X)
    {Ct : ℝ} (_hCt : 0 ≤ Ct)
    (hTree : ∀ {n : ℕ} (Ys : Fin n → Finset (Finset ℕ)),
      (∀ l, Ys l ⊆ X) → (∀ l j, l ≠ j → Disjoint (Ys l) (Ys j)) →
      ∀ Ta : ∀ l, SimpleGraph ((Ys l).biUnion id), (∀ l, IsRelTree (Ys l) (Ta l)) →
      ∀ Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id),
        IsRelTree₀ (coarsen X (univ.image Ys)) Tb →
      (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
        (jIntegrand M lam ε₀ R X Ys Ta Tb (extendConfig (X.biUnion id) y) *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
          ∏ i, D (y i))) ≤ ENNReal.ofReal Ct) :
    (∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal
      ((∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)) *
        |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F (extendConfig (X.biUnion id) y)| *
        ∏ i, D (y i))) ≤
      ENNReal.ofReal (Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k) * (2 ^ (k * k * k) * Ct)) := by
  let E := univ.biUnion Es ∪ F
  have hE : E ∈ relEdgeSets₀ X := union_mem_relEdgeSets₀ hX hXs hEs hF
  have hEp : E ⊆ pairsOn (X.biUnion id) := (mem_relEdgeSets₀.1 hE).1.trans interPairs_subset_pairsOn
  have hEk : E.card ≤ k * k := (card_le_card hEp).trans (by rw [← hk]; exact card_pairsOn_le _)
  obtain ⟨n, Ys, hn, hYs, hdisj, Tb, hTb, hpoint⟩ := majorants_le_screenTree hlam hM hX hE
    (hAE.trans subset_union_left) hA
  rw [hk] at hn
  let ts := (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
    (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l))
  let g := fun Ta (y : X.biUnion id → ℂ × ℂ) =>
    jIntegrand M lam ε₀ R X Ys Ta Tb (extendConfig (X.biUnion id) y) *
      (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
      ∏ i, D (y i)
  let B : ℝ := Wb ^ (k * k) * Ψ ^ k * Cab ^ (k * k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg0 : ∀ Ta y, 0 ≤ g Ta y := fun Ta y =>
    mul_nonneg (mul_nonneg (jIntegrand_nonneg _ _ _ _ _ _ _ _ _) (prod_nonneg fun S _ => by split_ifs <;> norm_num))
      (prod_nonneg fun i _ => hD0 _)
  have hgm : ∀ Ta, Measurable fun y => ENNReal.ofReal (g Ta y) := fun Ta =>
    ENNReal.measurable_ofReal.comp ((((measurable_jIntegrand M lam ε₀ R X Ys Ta Tb).comp
      (measurable_extendConfig _)).mul ((measurable_prod_connOn_indicator M lam X).comp
        (measurable_extendConfig _))).mul (Finset.measurable_prod _ fun i _ => hDm.comp (measurable_pi_apply i)))
  have hpt : ∀ᵐ y ∂volume.restrict (boxConfig (X.biUnion id) N),
      ENNReal.ofReal ((∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)) *
        |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F (extendConfig (X.biUnion id) y)| *
        ∏ i, D (y i)) ≤ ENNReal.ofReal B * ∑ Ta ∈ ts, ENNReal.ofReal (g Ta y) := by
    filter_upwards [ae_restrict_of_ae (ae_radii_pos (X.biUnion id)), ae_restrict_mem (measurableSet_boxConfig N)] with y hpos hy
    let c := extendConfig (X.biUnion id) y
    have hcy (i : X.biUnion id) : c i = y i := extendConfig_apply_coe _ y i
    have hR0 : 0 ≤ ENNReal.ofReal B * ∑ Ta ∈ ts, ENNReal.ofReal (g Ta y) := zero_le
    by_cases hden : ∏ i, D (y i) = 0
    · rw [hden, mul_zero, ENNReal.ofReal_zero]; exact hR0
    have hyK := hDK y hy hden
    have hcK : ∀ i ∈ X.biUnion id, c i ∈ K := fun i hi => by rw [hcy ⟨i, hi⟩]; exact hyK _
    have hcpos : ∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ := fun i hi => by
      rw [hcy ⟨i, hi⟩]; exact hpos _
    by_cases hconn : ∀ S ∈ X, ConnOn S (linkedPairs M lam c S)
    swap
    · push Not at hconn
      obtain ⟨S, hS, hnS⟩ := hconn
      have hzero : blockWeightOf β w ψ M lam S c = 0 := by unfold blockWeightOf; rw [ite_eq_right hnS, zero_mul, zero_mul]
      rw [prod_eq_zero hS hzero, zero_mul, zero_mul, ENNReal.ofReal_zero]
      exact hR0
    obtain ⟨Ta, hTa, hTaB⟩ := hpoint c hcpos
    have hraw := abs_eulerTerm_le_screenMajorants (fun l => (mem_relEdgeSets.1 (hEs l)).1)
      (mem_relEdgeSets₀.1 hF).1 hAE hCab hEk c (fun p hp =>
        hb _ (hcK _ (mem_pairsOn.1 (hEp hp)).1) _ (hcK _ (mem_pairsOn.1 (hEp hp)).2.1))
    have hbw := BoundedLowerEps.prod_blockWeightOf_le (M := M) (lam := lam) hX h.nonneg_ψ hWb hΨ hstab hψb c hcK
    rw [hk, sq] at hbw
    have hprod0 : 0 ≤ ∏ i, D (y i) := prod_nonneg fun i _ => hD0 _
    have hval : (∏ S ∈ X, blockWeightOf β w ψ M lam S c) *
        |eulerTerm β w M lam Xs A (univ.biUnion Es \ A) F c| * ∏ i, D (y i) ≤ B * g Ta y := by
      have hb0 : 0 ≤ ∏ S ∈ X, blockWeightOf β w ψ M lam S c :=
        prod_nonneg fun S _ => blockWeightOf_nonneg M lam h.nonneg_ψ S c
      have ht0 := jIntegrand_nonneg M lam ε₀ R X Ys Ta Tb c
      have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hTaB (pow_nonneg (zero_le_one.trans hCab) _))
      have h := mul_le_mul_of_nonneg_right (mul_le_mul hbw hraw' (abs_nonneg _)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hWb) _) (pow_nonneg (zero_le_one.trans hΨ) _))) hprod0
      have hind : ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) = 1 :=
        prod_eq_one fun S hS => ite_eq_left (hconn S hS)
      dsimp only [g, B]
      change _ ≤ _
      rw [hind]
      simpa only [mul_one, mul_assoc] using h
    apply (ENNReal.ofReal_le_ofReal hval).trans
    rw [ENNReal.ofReal_mul hB]
    have htmem : Ta ∈ ts := mem_filter.2 ⟨mem_univ Ta, hTa⟩
    have hsum : ENNReal.ofReal (g Ta y) ≤ ∑ Ta ∈ ts, ENNReal.ofReal (g Ta y) :=
      single_le_sum (f := fun Ta => ENNReal.ofReal (g Ta y)) (fun _ _ => zero_le) htmem
    exact mul_le_mul_right hsum _
  apply (lintegral_mono_ae hpt).trans
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun Ta _ => hgm Ta),
    lintegral_finsetSum _ fun Ta _ => hgm Ta]
  calc ENNReal.ofReal B * ∑ Ta ∈ ts, ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal (g Ta y)
      ≤ ENNReal.ofReal B * ∑ _Ta ∈ ts, ENNReal.ofReal Ct := by
        apply mul_le_mul_right
        apply sum_le_sum
        intro Ta hTa
        exact hTree Ys hYs hdisj Ta (mem_filter.1 hTa).2 Tb hTb
    _ = ENNReal.ofReal B * (ts.card * ENNReal.ofReal Ct) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal B * ((2 : ENNReal) ^ (k * k * k) * ENNReal.ofReal Ct) := by
        apply mul_le_mul_right
        apply mul_le_mul_left
        exact_mod_cast card_tree_tuples_le hk.le hn Ys hYs
    _ = _ := by
        rw [show (2 : ENNReal) ^ (k * k * k) = ENNReal.ofReal ((2 : ℝ) ^ (k * k * k)) by simp]
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (k * k * k)),
          ← ENNReal.ofReal_mul hB]

end MultipoleBKT.LowerBound.RouteBounded

end
