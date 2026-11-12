/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Position
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Flat
public import MultipoleBKT.LowerBound.AbsoluteLower.EulerGroup
public import MultipoleBKT.LowerBound.BoundedLowerEps.Transfer
public import MultipoleBKT.LowerBound.BoundedLowerEps.Pointwise
public import MultipoleBKT.UpperBound.AbsoluteUpper.Majorant

/-!
# The pointwise fixed-group spatial majorant

The proof of Lemma 4.58, equation (A.67). Keep the groups, odd trees and even tree fixed. Use the
connected-block events to select near spanning trees and apply the
radius allocation through `core_le_fixed_nearTree`.

The normalized even bond is bounded by a near indicator plus a truncated
inverse-square profile. Expanding this sum separates its disc and annular
contributions before endpoint integration. `flatIntegrand_le` gives the corresponding finite-sum bound. The logarithmic endpoint products at the
end of this file supply the comparison used when summing groups.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
open scoped ENNReal

variable {M lam ε₀ R : ℝ}

/-! ### The weights on pairs of dipoles -/

open scoped Classical in
/-- The kept weight `d^{-2} 𝟙_{d ≤ 17 ε₀ R} 𝟙_{𝓑^c}` of two dipoles (`keptPair` is this weight at a
pair of labels). -/
noncomputable def keptW (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) : ℝ :=
  (if MultipoleLinked M lam d e then 0 else 1) *
    (if dipoleDist d e ≤ 17 * ε₀ * R then 1 else 0) / dipoleDist d e ^ 2

theorem keptPair_eq (c : ℕ → ℂ × ℂ) (p : ℕ × ℕ) :
    keptPair M lam ε₀ R c p = keptW M lam ε₀ R (c p.1) (c p.2) := rfl

theorem keptW_comm (d e : ℂ × ℂ) : keptW M lam ε₀ R d e = keptW M lam ε₀ R e d := by
  classical
  unfold keptW
  rw [dipoleDist_comm e d, if_congr (Limits.multipoleLinked_comm (d := e) (e := d)) rfl rfl]

theorem keptW_nonneg (d e : ℂ × ℂ) : 0 ≤ keptW M lam ε₀ R d e := by
  classical
  unfold keptW
  split_ifs <;> positivity

/-- On `𝓑^c`, `d > M min(ρ_d, ρ_e) > 0`. -/
theorem lt_dipoleDist_of_not_linked (hlam : 0 < lam) (hM : 0 < M) {d e : ℂ × ℂ}
    (h : ¬ MultipoleLinked M lam d e) :
    M * min (rhoD lam d) (rhoD lam e) < dipoleDist d e ∧ 0 < dipoleDist d e := by
  rw [MultipoleLinked, not_le] at h
  have : 0 < M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) :=
    mul_pos hM (lt_min (lt_max_of_lt_right hlam) (lt_max_of_lt_right hlam))
  exact ⟨h, this.trans h⟩

/-- `d^{-2} 𝟙_{d ≤ 17 ε₀ R} 𝟙_{𝓑^c} ≤ farW`. -/
theorem keptW_le_farW (hlam : 0 < lam) (hM : 0 < M) (d e : ℂ × ℂ) :
    keptW M lam ε₀ R d e ≤ farW M lam (17 * ε₀ * R) d e := by
  classical
  unfold keptW farW
  by_cases hl : MultipoleLinked M lam d e
  · rw [ite_eq_left hl, zero_mul, zero_div]
    split_ifs <;> positivity
  · rw [ite_eq_right hl, one_mul]
    obtain ⟨h1, h2⟩ := lt_dipoleDist_of_not_linked hlam hM hl
    rw [max_eq_left h1.le, div_eq_mul_inv]

/-- `b^abs ≤ min(ρ_d, ρ_e)² (nearW + farW)`. -/
theorem absEvenWeight_le (hlam : 0 < lam) (hM : 0 < M) (d e : ℂ × ℂ) :
    absEvenWeight M lam ε₀ R d e ≤ min (rhoD lam d) (rhoD lam e) ^ 2 *
      (nearW M lam d e + farW M lam (17 * ε₀ * R) d e) := by
  classical
  have hρ : 0 < min (rhoD lam d) (rhoD lam e) := lt_min (rhoD_pos hlam d) (rhoD_pos hlam e)
  have hρ2 : 0 < min (rhoD lam d) (rhoD lam e) ^ 2 := by positivity
  unfold absEvenWeight
  by_cases hl : MultipoleLinked M lam d e
  · -- linked: `b^abs = 1 = min ρ² nearW`
    have ha : absOddWeight M lam ε₀ R d e = 0 := by
      unfold absOddWeight
      rw [ite_eq_left hl, mul_zero, zero_mul]
    rw [ha, ite_eq_left hl]
    have hn : min (rhoD lam d) (rhoD lam e) ^ 2 * nearW M lam d e = 1 := by
      unfold nearW
      rw [ite_eq_left (show dipoleDist d e ≤ M * min (rhoD lam d) (rhoD lam e) from hl)]
      field_simp
    have hf := farW_nonneg M lam (17 * ε₀ * R) d e
    nlinarith
  · rw [ite_eq_right hl, add_zero]
    obtain ⟨h1, h2⟩ := lt_dipoleDist_of_not_linked hlam hM hl
    have hfar : farW M lam (17 * ε₀ * R) d e =
        (if dipoleDist d e ≤ 17 * ε₀ * R then 1 else 0) * (dipoleDist d e ^ 2)⁻¹ := by
      unfold farW
      rw [max_eq_left h1.le]
    have hn0 := nearW_nonneg M lam d e
    -- `a ≤ min(r_d, r_e) / d`
    have ha : absOddWeight M lam ε₀ R d e ≤
        (if dipoleDist d e ≤ 17 * ε₀ * R then 1 else 0) *
          (min ‖d.1 - d.2‖ ‖e.1 - e.2‖ / dipoleDist d e) := by
      unfold absOddWeight
      rw [ite_eq_right hl, mul_one]
      have hcore : ‖d.1 - d.2‖ * ‖e.1 - e.2‖ /
          (dipoleDist d e * max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) ≤
          min ‖d.1 - d.2‖ ‖e.1 - e.2‖ / dipoleDist d e := by
        rw [div_le_div_iff₀ (mul_pos h2 (lt_max_of_lt_left h2)) h2]
        have hm := le_max_right (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)
        have hprod : ‖d.1 - d.2‖ * ‖e.1 - e.2‖ =
            min ‖d.1 - d.2‖ ‖e.1 - e.2‖ * max ‖d.1 - d.2‖ ‖e.1 - e.2‖ := by
          rcases le_total ‖d.1 - d.2‖ ‖e.1 - e.2‖ with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, mul_comm]
        rw [hprod]
        have hmin0 : 0 ≤ min ‖d.1 - d.2‖ ‖e.1 - e.2‖ := le_min (norm_nonneg _) (norm_nonneg _)
        calc min ‖d.1 - d.2‖ ‖e.1 - e.2‖ * max ‖d.1 - d.2‖ ‖e.1 - e.2‖ * dipoleDist d e
            ≤ min ‖d.1 - d.2‖ ‖e.1 - e.2‖ * max (dipoleDist d e)
                (max ‖d.1 - d.2‖ ‖e.1 - e.2‖) * dipoleDist d e := by gcongr
          _ = min ‖d.1 - d.2‖ ‖e.1 - e.2‖ * (dipoleDist d e *
                max (dipoleDist d e) (max ‖d.1 - d.2‖ ‖e.1 - e.2‖)) := by ring
      split_ifs
      · simpa using hcore
      · simp
    have ha0 : 0 ≤ absOddWeight M lam ε₀ R d e := absOddWeight_nonneg _ _ _ _ _ _
    have hmin : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ ≤ min (rhoD lam d) (rhoD lam e) :=
      min_le_min (le_max_left _ _) (le_max_left _ _)
    have hmin0 : 0 ≤ min ‖d.1 - d.2‖ ‖e.1 - e.2‖ := le_min (norm_nonneg _) (norm_nonneg _)
    calc absOddWeight M lam ε₀ R d e ^ 2
        ≤ ((if dipoleDist d e ≤ 17 * ε₀ * R then 1 else 0) *
            (min ‖d.1 - d.2‖ ‖e.1 - e.2‖ / dipoleDist d e)) ^ 2 :=
          pow_le_pow_left₀ ha0 ha 2
      _ ≤ min (rhoD lam d) (rhoD lam e) ^ 2 * farW M lam (17 * ε₀ * R) d e := by
          rw [hfar]
          split_ifs
          · rw [one_mul, one_mul, div_pow, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmin0 hmin 2) (by positivity)
          · simp
      _ ≤ min (rhoD lam d) (rhoD lam e) ^ 2 * (nearW M lam d e + farW M lam (17 * ε₀ * R) d e) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hn0) hρ2.le

/-! ### Products over edge sets -/

section Products

theorem prod_le_prod_of_subset_of_one_le_real' {α : Type*} {s t : Finset α} (hst : s ⊆ t)
    {g : α → ℝ} (hg : ∀ x, 1 ≤ g x) : ∏ x ∈ s, g x ≤ ∏ x ∈ t, g x := by
  classical
  rw [← prod_sdiff hst]
  have h1 : 1 ≤ ∏ x ∈ t \ s, g x := one_le_prod₀ fun x _ => hg x
  exact le_mul_of_one_le_left (prod_nonneg fun x _ => zero_le_one.trans (hg x)) h1

theorem prod_union_le_mul_of_one_le {α : Type*} [DecidableEq α] (s t : Finset α) {g : α → ℝ}
    (hg : ∀ x, 1 ≤ g x) : ∏ x ∈ s ∪ t, g x ≤ (∏ x ∈ s, g x) * ∏ x ∈ t, g x := by
  rw [← union_sdiff_self_eq_union, prod_union disjoint_sdiff]
  exact mul_le_mul_of_nonneg_left (prod_le_prod_of_subset_of_one_le_real' sdiff_subset hg)
    (prod_nonneg fun x _ => zero_le_one.trans (hg x))

theorem prod_biUnion_le_prod_of_one_le {κ α : Type*} [DecidableEq α] (s : Finset κ)
    (E : κ → Finset α) {g : α → ℝ} (hg : ∀ x, 1 ≤ g x) :
    ∏ x ∈ s.biUnion E, g x ≤ ∏ l ∈ s, ∏ x ∈ E l, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, prod_insert ha]
    exact (prod_union_le_mul_of_one_le _ _ hg).trans
      (mul_le_mul_of_nonneg_left ih (prod_nonneg fun x _ => zero_le_one.trans (hg x)))

end Products

/-! ### Edges and pairs -/

section Edges

variable {U : Finset ℕ}

/-- A product over the edges of `graphOf U E` is the product over the pairs of `E`. -/
theorem prod_edgeFinset_graphOf {E : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn U)
    [Fintype (graphOf U E).edgeSet] (g : Sym2 U → ℝ) (G : ℕ × ℕ → ℝ)
    (hG : ∀ p ∈ E, ∀ (h1 : p.1 ∈ U) (h2 : p.2 ∈ U), g s(⟨p.1, h1⟩, ⟨p.2, h2⟩) = G p) :
    ∏ e ∈ (graphOf U E).edgeFinset, g e = ∏ p ∈ E, G p := by
  symm
  refine Finset.prod_bij (fun p hp => s(⟨p.1, (mem_pairsOn.1 (hE hp)).1⟩,
    ⟨p.2, (mem_pairsOn.1 (hE hp)).2.1⟩)) ?_ ?_ ?_ ?_
  · intro p hp
    exact mem_edgeFinset_graphOf_mk.2 ⟨(mem_pairsOn.1 (hE hp)).2.2.ne, Or.inl hp⟩
  · intro p hp q hq h
    have hp' := (mem_pairsOn.1 (hE hp)).2.2
    have hq' := (mem_pairsOn.1 (hE hq)).2.2
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2)
    · have e1 : p.1 = q.2 := congrArg Subtype.val h1
      have e2 : p.2 = q.1 := congrArg Subtype.val h2
      omega
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      obtain ⟨-, h | h⟩ := mem_edgeFinset_graphOf_mk.1 he
      · exact ⟨((a : ℕ), (b : ℕ)), h, rfl⟩
      · exact ⟨((b : ℕ), (a : ℕ)), h, Sym2.eq_swap⟩
  · intro p hp
    exact (hG p hp _ _).symm

/-- Disjoint sets of pairs give disjoint edge sets. -/
theorem disjoint_edgeFinset_graphOf {E F : Finset (ℕ × ℕ)} (hE : E ⊆ pairsOn U)
    (hF : F ⊆ pairsOn U) (h : Disjoint E F) [Fintype (graphOf U E).edgeSet]
    [Fintype (graphOf U F).edgeSet] :
    Disjoint (graphOf U E).edgeFinset (graphOf U F).edgeFinset := by
  rw [Finset.disjoint_left]
  intro e he hf
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨-, h1 | h1⟩ := mem_edgeFinset_graphOf_mk.1 he <;>
      obtain ⟨-, h2 | h2⟩ := mem_edgeFinset_graphOf_mk.1 hf
    · exact disjoint_left.1 h h1 h2
    · have := (mem_pairsOn.1 (hE h1)).2.2
      have := (mem_pairsOn.1 (hF h2)).2.2
      simp only at *
      omega
    · have := (mem_pairsOn.1 (hE h1)).2.2
      have := (mem_pairsOn.1 (hF h2)).2.2
      simp only at *
      omega
    · exact disjoint_left.1 h h1 h2

end Edges

/-! ### The edges inside the blocks -/


/-! ### The dipole factor -/

/-- `(h/r)^b e^{β g_λ} 𝟙_{r ≤ h} ≤ Ψ(y - x)` for `0 < b ≤ a`. -/
theorem rpow_mul_cutDens_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam h a b : ℝ} (hb : 0 < b)
    (hba : b ≤ a) (hh : 0 ≤ h) (d : ℂ × ℂ) :
    (h / ‖d.1 - d.2‖) ^ b * cutDens χ β lam h d ≤ dipoleWeight χ β lam h a (d.2 - d.1) := by
  have ha : 0 ≤ a := hb.le.trans hba
  unfold cutDens dipoleWeight pairDensity
  rw [← neg_sub d.1 d.2, smearedKernel_neg hχ]
  by_cases hr : ‖d.1 - d.2‖ ≤ h
  · rw [Set.indicator_of_mem (Set.mem_Iic.2 hr), Set.indicator_of_mem
      (Metric.mem_closedBall.2 (by rwa [dist_zero_right, norm_neg])), Pi.one_apply, mul_one,
      norm_neg]
    by_cases h0 : ‖d.1 - d.2‖ = 0
    · rw [h0, div_zero, Real.zero_rpow hb.ne', zero_mul]
      positivity
    · have hr0 : 0 < ‖d.1 - d.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h1 : 1 ≤ h / ‖d.1 - d.2‖ := (one_le_div hr0).2 hr
      have h2 : (h / ‖d.1 - d.2‖) ^ b ≤ (17 * h / ‖d.1 - d.2‖) ^ a :=
        (Real.rpow_le_rpow_of_exponent_le h1 hba).trans (Real.rpow_le_rpow
          (zero_le_one.trans h1) (div_le_div_of_nonneg_right (by linarith) hr0.le) ha)
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem (fun h' => hr (Set.mem_Iic.1 h')), mul_zero, mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (Set.indicator_nonneg (fun _ _ => by positivity) _)

/-! ### The radii of the groups -/

theorem prodExceptMax_le_erase (c : ℕ → ℂ × ℂ) {Y : Finset (Finset ℕ)} {S : Finset ℕ}
    (hS : S ∈ Y) : prodExceptMax c Y ≤ ∏ S' ∈ Y.erase S, blockRad c S' ^ 2 := by
  unfold prodExceptMax
  split_ifs with h
  · exact inf'_le _ hS
  · exact absurd ⟨S, hS⟩ h

theorem prod_subtype_erase {X Y : Finset (Finset ℕ)} (hYX : Y ⊆ X) (f : Finset ℕ → ℝ)
    (S : X) :
    ∏ S' ∈ (Y.subtype (· ∈ X)).erase S, f S' = ∏ S' ∈ Y.erase S, f S' := by
  classical
  have hmap : ((Y.subtype (· ∈ X)).erase S).map (Function.Embedding.subtype _) = Y.erase S := by
    rw [map_erase, subtype_map, filter_true_of_mem fun T hT => hYX hT]
    rfl
  rw [← hmap, prod_map]
  rfl

/-! ### Expanding the even edges -/

/-- `ρ ∏_{NT} n (∏_{E^a} k^a ∏_{E^b} (n + f)) ≤ ∑_{A ⊆ E^b} ρ ∏_{NT ∪ A} n ∏_{(E^a ∪ E^b) ∖ A} f`
for `0 ≤ k^a ≤ f`, `n, f ≥ 0`, `NT`, `E^a`, `E^b` pairwise disjoint. -/
theorem term_expand {α : Type*} [DecidableEq α] {rad : ℝ} (hrad : 0 ≤ rad) (nE fE ka : α → ℝ)
    (hn : ∀ e, 0 ≤ nE e) (hf : ∀ e, 0 ≤ fE e) (hka0 : ∀ e, 0 ≤ ka e) (hka : ∀ e, ka e ≤ fE e)
    (NT EA EB : Finset α) (hNT : Disjoint NT EB) (hAB : Disjoint EA EB) :
    rad * ((∏ e ∈ NT, nE e) * ((∏ e ∈ EA, ka e) * ∏ e ∈ EB, (nE e + fE e))) ≤
      ∑ A ∈ EB.powerset, rad * ((∏ e ∈ NT ∪ A, nE e) * ∏ e ∈ (EA ∪ EB) \ A, fE e) := by
  have hNT0 : 0 ≤ ∏ e ∈ NT, nE e := prod_nonneg fun e _ => hn e
  have hEA : ∏ e ∈ EA, ka e ≤ ∏ e ∈ EA, fE e := prod_le_prod₀ (fun e _ => hka0 e) fun e _ => hka e
  calc rad * ((∏ e ∈ NT, nE e) * ((∏ e ∈ EA, ka e) * ∏ e ∈ EB, (nE e + fE e)))
      ≤ rad * ((∏ e ∈ NT, nE e) * ((∏ e ∈ EA, fE e) * ∏ e ∈ EB, (nE e + fE e))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hEA (prod_nonneg fun e _ => add_nonneg (hn e) (hf e))) hNT0)
          hrad
    _ = ∑ A ∈ EB.powerset, rad * ((∏ e ∈ NT, nE e) * ((∏ e ∈ EA, fE e) *
          ((∏ e ∈ A, nE e) * ∏ e ∈ EB \ A, fE e))) := by
        rw [prod_add, mul_sum, mul_sum, mul_sum]
    _ = ∑ A ∈ EB.powerset, rad * ((∏ e ∈ NT ∪ A, nE e) * ∏ e ∈ (EA ∪ EB) \ A, fE e) := by
        refine sum_congr rfl fun A hA => ?_
        have hAB' : A ⊆ EB := mem_powerset.1 hA
        have h1 : Disjoint NT A := disjoint_of_subset_right hAB' hNT
        have h2 : (EA ∪ EB) \ A = EA ∪ (EB \ A) := by
          ext e
          simp only [mem_sdiff, mem_union]
          constructor
          · rintro ⟨h | h, hA'⟩
            · exact Or.inl h
            · exact Or.inr ⟨h, hA'⟩
          · rintro (h | ⟨h, hA'⟩)
            · exact ⟨Or.inl h, fun h' => disjoint_left.1 hAB h (hAB' h')⟩
            · exact ⟨Or.inr h, hA'⟩
        have h3 : Disjoint EA (EB \ A) := disjoint_of_subset_right sdiff_subset hAB
        rw [prod_union h1, h2, prod_union h3]
        ring

/-! ### The tree terms -/

open scoped Classical in
/-- The tree term of one choice of `NT` (edges inside the blocks) and `A ⊆ E^b` (near even edges):
`𝟙_{NT ∪ E tree} R^{-2} ∏ ρ_i² ∏_{NT ∪ A} nearE ∏_{E ∖ A} farE ∏_i Ψ(y_i - x_i)`, for
`E = ⋃ E^a_l ∪ E^b`. -/
noncomputable def flatTerm (χ : ℂ → ℝ) (β lam M R' h a : ℝ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (E NT A : Finset (Sym2 ι)) (y : ι → ℂ × ℂ) : ℝ :=
  if (fromEdgeSet ((NT ∪ E : Finset (Sym2 ι)) : Set (Sym2 ι))).IsTree then
    radF lam y * ((∏ e ∈ NT ∪ A, nearE M lam y e) * ∏ e ∈ E \ A, farE M lam R' y e) *
      ∏ i, dipoleWeight χ β lam h a ((y i).2 - (y i).1)
  else 0

theorem flatTerm_nonneg {χ : ℂ → ℝ} {β lam M R' h a : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (E NT A : Finset (Sym2 ι)) (y : ι → ℂ × ℂ) :
    0 ≤ flatTerm χ β lam M R' h a E NT A y := by
  unfold flatTerm
  split_ifs
  · exact mul_nonneg (mul_nonneg (radF_nonneg hlam y) (mul_nonneg
      (prod_nonneg fun e _ => nearE_nonneg M lam y e)
      (prod_nonneg fun e _ => farE_nonneg M lam _ y e)))
      (prod_nonneg fun i _ => dipoleWeight_nonneg _ _ _ hh _)
  · exact le_rfl

theorem measurable_flatTerm {χ : ℂ → ℝ} (hχ : IsMollifier χ) {β lam M R' h a : ℝ}
    (hlam : 0 < lam) {ι : Type} [Fintype ι] [DecidableEq ι] (E NT A : Finset (Sym2 ι)) :
    Measurable (flatTerm χ β lam M R' h a E NT A) := by
  unfold flatTerm
  split_ifs
  · refine ((measurable_radF lam).mul ((Finset.measurable_prod _ fun e _ =>
      measurable_nearE M lam e).mul (Finset.measurable_prod _ fun e _ =>
        measurable_farE M lam R' e))).mul (Finset.measurable_prod _ fun i _ => ?_)
    exact (measurable_dipoleWeight hχ hlam β h a).comp (by fun_prop)
  · exact measurable_const

/-! ### The pointwise bound -/

section Pointwise

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β C₀ : ℝ} {X : Finset (Finset ℕ)}

/-- The kept weight on unordered pairs. -/
noncomputable def keptWE (M lam ε₀ R : ℝ) {ι : Type*} (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => keptW M lam ε₀ R (c i) (c j)) fun _ _ => keptW_comm _ _

/-- The even weight `b^abs` on unordered pairs. -/
noncomputable def absE (M lam ε₀ R : ℝ) {ι : Type*} (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => absEvenWeight M lam ε₀ R (c i) (c j)) fun _ _ => absEvenWeight_comm _ _

open scoped Classical in
/-- **The integrand of a flat structure** (the integrand of `J_{large,C₀}`, eq. (4.113), for
groups `G_k`, odd trees `T^a_k` and even edges `E^b`):
`∏_{E^b} b^abs ∏_k ∏_{S ∈ G_k, S ≠ Ŝ_k} r_S² ∏_k ∏_{T^a_k} d^{-2} 𝟙_{d ≤ 17 ε₀ R̄} 𝟙_{𝓑^c}
∏_{S ∈ X} 𝟙_{𝓑_S} ∏_{i ∈ V_X} (ε₀ R̄/r_i)^{C₀/M} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄}`. -/
noncomputable def flatIntegrand (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ C₀ : ℝ)
    (X : Finset (Finset ℕ)) {κ : Type*} [Fintype κ] (G : κ → Finset (Finset ℕ))
    (Ta : κ → Finset (ℕ × ℕ)) (Eb : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ Eb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam) (c p.1) (c p.2)) *
    (∏ l, prodExceptMax c (G l)) *
    (∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ (truncationScale p₀ β lam) c p) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
    ∏ i ∈ X.biUnion id,
      (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
        SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)

open scoped Classical in
/-- The integrand of the paper's `J₁`, with one actual near tree in each block.
proof of Lemma 4.58. -/
noncomputable def flatTreeIntegrand (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ C₀ : ℝ)
    (X : Finset (Finset ℕ)) {κ : Type*} [Fintype κ] (G : κ → Finset (Finset ℕ))
    (Ta : κ → Finset (ℕ × ℕ)) (Eb : Finset (ℕ × ℕ)) (R : RouteJ.NearTreeFamily (Limits.blockOf X))
    (y : X.biUnion id → ℂ × ℂ) : ℝ :=
  let c := extendConfig (X.biUnion id) y
  (∏ p ∈ Eb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam) (c p.1) (c p.2)) *
    (∏ l, prodExceptMax c (G l)) *
    (∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ (truncationScale p₀ β lam) c p) *
    (∏ e ∈ RouteJ.nearForest (Limits.blockOf X) (fun S => (R S).val),
      linkE M lam y e) *
    ∏ i ∈ X.biUnion id,
      (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
        SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)


open scoped Classical in
/-- Replace the connected-block indicators by the sum over actual near trees.
proof of Lemma 4.58. -/
theorem flatIntegrand_le_sum_nearTree (hX : IsSubpartition X)
    (hR : 0 ≤ ε₀ * truncationScale p₀ β lam)
    {κ : Type*} [Fintype κ] (G : κ → Finset (Finset ℕ))
    (Ta : κ → Finset (ℕ × ℕ)) (Eb : Finset (ℕ × ℕ))
    (y : X.biUnion id → ℂ × ℂ) :
    flatIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Eb (extendConfig (X.biUnion id) y) ≤
      ∑ Q : RouteJ.NearTreeFamily (Limits.blockOf X),
        flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Eb Q y := by
  let c := extendConfig (X.biUnion id) y
  have hc : (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) ≤
      if ∀ S : X, ((nearGraph M lam y).induce {i | Limits.blockOf X i = S}).Connected
      then 1 else 0 := by
    by_cases hmult : ∀ S ∈ X, ConnOn S (linkedPairs M lam c S)
    · have hconn := fun S : X =>
        BoundedLowerEps.connected_induce_of_connOn hX y S.2 (hmult S S.2)
      rw [ite_eq_left hconn, prod_eq_one (fun S hS => ite_eq_left (hmult S hS))]
    · push Not at hmult
      obtain ⟨S, hS, hn⟩ := hmult
      rw [prod_eq_zero hS (ite_eq_right hn)]
      split_ifs <;> norm_num
  have hs := hc.trans (RouteJ.connected_blocks_le_nearTreeFamily (Limits.blockOf X) M lam y)
  let P := (∏ p ∈ Eb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam) (c p.1) (c p.2)) *
    (∏ l, prodExceptMax c (G l)) *
    (∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ (truncationScale p₀ β lam) c p)
  let D := ∏ i ∈ X.biUnion id,
    (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) *
      cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg
    (prod_nonneg fun _ _ => absEvenWeight_nonneg _ _ _ _ _ _)
    (prod_nonneg fun _ _ => prodExceptMax_nonneg _))
    (prod_nonneg fun _ _ => prod_nonneg fun _ _ => keptPair_nonneg _)
  have hD : 0 ≤ D := prod_nonneg fun _ _ => mul_nonneg (Real.rpow_nonneg (div_nonneg hR (norm_nonneg _)) _)
    (cutDens_nonneg _ _)
  change P * _ * D ≤ ∑ Q : RouteJ.NearTreeFamily (Limits.blockOf X),
    P * (∏ e ∈ RouteJ.nearForest (Limits.blockOf X) (fun S => (Q S).val), linkE M lam y e) * D
  calc
    _ ≤ P * (∑ Q : RouteJ.NearTreeFamily (Limits.blockOf X),
        ∏ e ∈ RouteJ.nearForest (Limits.blockOf X) (fun S => (Q S).val), linkE M lam y e) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hP) hD
    _ = _ := by rw [mul_sum, sum_mul]

open scoped Classical in
/-- At fixed near trees, cancel the radii and expand the near and far even profiles.
proof of Lemma 4.58 and (A.67). -/
theorem flatTreeIntegrand_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) (hC₀ : 0 < C₀)
    (hR : 0 ≤ ε₀ * truncationScale p₀ β lam) {a : ℝ} (ha : C₀ / M ≤ a)
    (hX : IsSubpartition X) [Nonempty (X.biUnion id)] {κ : Type*} [Fintype κ]
    {G : κ → Finset (Finset ℕ)} {Ta : κ → Finset (ℕ × ℕ)} {Eb : Finset (ℕ × ℕ)}
    (hF : FlatHyp X G Ta Eb) (Q : RouteJ.NearTreeFamily (Limits.blockOf X)) (y : X.biUnion id → ℂ × ℂ) :
    flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Eb Q y ≤
      ∑ A ∈ (graphOf (X.biUnion id) Eb).edgeFinset.powerset,
          flatTerm χ β lam M (17 * ε₀ * truncationScale p₀ β lam) (ε₀ * truncationScale p₀ β lam) a
            (univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Eb).edgeFinset) (RouteJ.nearForest (Limits.blockOf X) (fun S => (Q S).val)) A y := by
  unfold flatTreeIntegrand
  dsimp only
  let NT := RouteJ.nearForest (Limits.blockOf X) (fun S => (Q S).val)
  set R := truncationScale p₀ β lam with hRdef
  set Ea : κ → Finset (Sym2 (X.biUnion id)) := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
    with hEa
  set Ebe := (graphOf (X.biUnion id) Eb).edgeFinset with hEbe
  set PD := ∏ i, dipoleWeight χ β lam (ε₀ * R) a ((y i).2 - (y i).1) with hPD
  have hMpos : 0 < M := by linarith
  have hPD0 : 0 ≤ PD := prod_nonneg fun i _ => dipoleWeight_nonneg _ _ _ hR _
  have hcy : ∀ i (hi : i ∈ X.biUnion id), extendConfig (X.biUnion id) y i = y ⟨i, hi⟩ :=
    fun i hi => by simp only [extendConfig, hi, dite_true]
  obtain ⟨hGdisj, hEaG, hcardl, hinter, hconn, hcount⟩ := flat_structure hX G hF.subset hF.disj
    Ta hF.inter hF.card Eb hF.inter_b hF.conn hF.count
  have hTaV : ∀ l, Ta l ⊆ pairsOn (X.biUnion id) := fun l =>
    (hF.inter l).trans ((interPairs_mono hX (hF.subset l)).trans interPairs_subset_pairsOn)
  have hTbV : Eb ⊆ pairsOn (X.biUnion id) := hF.inter_b.trans interPairs_subset_pairsOn
  have hRHS0 := sum_nonneg fun A (_ : A ∈ Ebe.powerset) =>
    flatTerm_nonneg (χ := χ) (β := β) (M := M) (R' := 17 * ε₀ * R) (a := a) hlam hR
      (univ.biUnion Ea ∪ Ebe) NT A y
  by_cases hlinked : ∀ i j, s(i, j) ∈ NT → MultipoleLinked M lam (y i) (y j)
  swap
  · push Not at hlinked
    obtain ⟨i, j, he, hn⟩ := hlinked
    have hz : (∏ e ∈ NT, linkE M lam y e) = 0 :=
      prod_eq_zero he (show linkE M lam y s(i, j) = 0 from ite_eq_right hn)
    change _ * (∏ e ∈ NT, linkE M lam y e) * _ ≤ _
    rw [hz, mul_zero, zero_mul]
    exact hRHS0
  have hP1 : (∏ e ∈ NT, linkE M lam y e) = 1 := by
    apply prod_eq_one
    intro e he
    induction e using Sym2.ind with
    | h i j => exact ite_eq_left (hlinked i j he)
  have hAc : (univ.biUnion Ea).card ≤ ∑ l, (Ea l).card := card_biUnion_le
  change (∑ l, (Ea l).card) + Ebe.card + 1 ≤ Fintype.card X at hcount
  obtain ⟨hTree, _⟩ := RouteJ.retained_tree (Limits.blockOf X)
    (fun S => (Q S).val) (fun S => (Q S).property) (univ.biUnion Ea) Ebe
    hinter hconn (by omega)
  have hNT : NT ∈ (intraE (Limits.blockOf X)).powerset := by
    apply mem_powerset.mpr
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      obtain ⟨hne, hb⟩ := RouteJ.nearForest_endpoints (Limits.blockOf X)
        (fun S => (Q S).val) he
      exact mem_filter.mpr ⟨mem_univ _, by
        simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using And.intro hb hne⟩
  -- the largest block of each group
  have hXne : ∀ l, (G l).Nonempty := fun l => by
    have := hF.card l
    exact card_pos.1 (by omega)
  have hhat : ∀ l, ∃ S ∈ G l, ∀ S' ∈ G l, blockRad (extendConfig (X.biUnion id) y) S' ≤
      blockRad (extendConfig (X.biUnion id) y) S := fun l =>
    exists_max_image _ _ (hXne l)
  choose hatS hhatS hhatmax using hhat
  set hat : κ → X := fun l => ⟨hatS l, hF.subset l (hhatS l)⟩ with hhatdef
  set rb : X → ℝ := fun S => blockRad (extendConfig (X.biUnion id) y) S with hrbdef
  have hrb0 : ∀ S, 0 ≤ rb S := fun S => blockRad_nonneg _
  have hrb : ∀ S : X, ∃ i, Limits.blockOf X i = S ∧ rb S ≤ rhoD lam (y i) := by
    intro S
    obtain ⟨i, hi, heq⟩ := exists_mem_eq_sup (S : Finset ℕ) (hX.1 S S.2)
      (fun i => ‖(extendConfig (X.biUnion id) y i).1 - (extendConfig (X.biUnion id) y i).2‖₊)
    have hiV : i ∈ X.biUnion id := mem_biUnion.2 ⟨S, S.2, hi⟩
    refine ⟨⟨i, hiV⟩, Limits.blockOf_eq hX S.2 hi, ?_⟩
    show (((S : Finset ℕ).sup fun i => ‖(extendConfig (X.biUnion id) y i).1 -
      (extendConfig (X.biUnion id) y i).2‖₊ : NNReal) : ℝ) ≤ _
    rw [heq, coe_nnnorm, hcy i hiV]
    exact le_max_left _ _
  have hhat' : ∀ l, hat l ∈ (G l).subtype (· ∈ X) ∧
      ∀ S ∈ (G l).subtype (· ∈ X), rb S ≤ rb (hat l) := fun l =>
    ⟨mem_subtype.2 (hhatS l), fun S hS => hhatmax l S (mem_subtype.1 hS)⟩
  -- the weights on unordered pairs
  set ka := keptWE M lam ε₀ R y with hkadef
  set kb := absE M lam ε₀ R y with hkbdef
  set fE := farE M lam (17 * ε₀ * R) y with hfEdef
  set nE := nearE M lam y with hnEdef
  have hka : ∀ e, 0 ≤ ka e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact keptW_nonneg (y i) (y j)
  have hkb : ∀ e, 0 ≤ kb e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact absEvenWeight_nonneg _ _ _ _ _ _
  have hkbN : ∀ e, 0 ≤ nE e + fE e := fun e =>
    add_nonneg (nearE_nonneg M lam y e) (farE_nonneg M lam _ y e)
  have hkbb : ∀ i j, kb s(i, j) ≤ min (rhoD lam (y i)) (rhoD lam (y j)) ^ 2 *
      (nE s(i, j) + fE s(i, j)) := fun i j => absEvenWeight_le hlam hMpos (y i) (y j)
  have hkaf : ∀ e, ka e ≤ fE e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact keptW_le_farW hlam hMpos (y i) (y j)
  have hcore := core_le_fixed_nearTree (M := M) hlam (Limits.blockOf X) y Q hlinked Ea
    (fun l => (G l).subtype (· ∈ X)) hGdisj hEaG hcardl Ebe hinter hconn hcount rb hrb0 hrb hat
    hhat' ka kb (fun e => nE e + fE e) hka hkb hkbN hkbb
  -- the factors of the integrand
  have hPB : (∏ p ∈ Eb, absEvenWeight M lam ε₀ R (extendConfig (X.biUnion id) y p.1)
      (extendConfig (X.biUnion id) y p.2)) = ∏ e ∈ Ebe, kb e := by
    refine (prod_edgeFinset_graphOf hTbV kb _ fun p _ h1 h2 => ?_).symm
    rw [hcy p.1 h1, hcy p.2 h2]
    rfl
  have hEadisj : ((univ : Finset κ) : Set κ).PairwiseDisjoint Ea := by
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h i j =>
      exact Finset.disjoint_left.1 (hGdisj l l' hll') (hEaG l _ he i (Sym2.mem_mk_left i j))
        (hEaG l' _ he' i (Sym2.mem_mk_left i j))
  have hPK : (∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ R (extendConfig (X.biUnion id) y) p) =
      ∏ e ∈ univ.biUnion Ea, ka e := by
    rw [prod_biUnion hEadisj]
    refine prod_congr rfl fun l _ => (prod_edgeFinset_graphOf (hTaV l) ka _
      fun p _ h1 h2 => ?_).symm
    rw [keptPair_eq, hcy p.1 h1, hcy p.2 h2]
    rfl
  have hPE : (∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l)) ≤
      ∏ l, ∏ S ∈ ((G l).subtype (· ∈ X)).erase (hat l), rb S ^ 2 := by
    refine prod_le_prod₀ (fun l _ => ?_) fun l _ => ?_
    · unfold prodExceptMax
      split_ifs with h
      · exact le_inf' _ _ fun S _ => prod_nonneg fun S' _ => sq_nonneg _
      · exact zero_le_one
    · rw [prod_subtype_erase (hF.subset l) (fun S => blockRad (extendConfig (X.biUnion id) y) S ^ 2)
        (hat l)]
      exact prodExceptMax_le_erase (extendConfig (X.biUnion id) y) (hhatS l)
  have hPD : (∏ i ∈ X.biUnion id, (ε₀ * R / ‖(extendConfig (X.biUnion id) y i).1 -
      (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
      cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i)) ≤ PD := by
    rw [← prod_coe_sort (X.biUnion id)]
    refine prod_le_prod₀ (fun i _ => mul_nonneg (Real.rpow_nonneg (div_nonneg hR
      (norm_nonneg _)) _) (cutDens_nonneg _ _)) fun i _ => ?_
    rw [hcy i i.2]
    exact rpow_mul_cutDens_le hχ (div_pos hC₀ hMpos) ha hR (y i)
  -- disjointness of the edge families
  have hAB : Disjoint (univ.biUnion Ea) Ebe := by
    refine (disjoint_biUnion_left _ _ _).2 fun l _ => ?_
    exact disjoint_edgeFinset_graphOf (hTaV l) hTbV
      (disjoint_of_subset_left (subset_biUnion_of_mem Ta (mem_univ l)) hF.disj_ab)
  have hNTB : ∀ NT ∈ (intraE (Limits.blockOf X)).powerset, Disjoint NT Ebe := by
    intro NT hNT
    rw [Finset.disjoint_left]
    intro e he he'
    have h1 := (mem_filter.1 (mem_powerset.1 hNT he)).2.1
    exact hinter e (mem_union_right _ he') h1
  -- assembling
  have hPB0 : 0 ≤ ∏ e ∈ Ebe, kb e := prod_nonneg fun e _ => hkb e
  have hPK0 : 0 ≤ ∏ e ∈ univ.biUnion Ea, ka e := prod_nonneg fun e _ => hka e
  have hPE0 : 0 ≤ ∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l) := by
    refine prod_nonneg fun l _ => ?_
    unfold prodExceptMax
    split_ifs with h
    · exact le_inf' _ _ fun S _ => prod_nonneg fun S' _ => sq_nonneg _
    · exact zero_le_one
  have hPDi0 : 0 ≤ ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(extendConfig (X.biUnion id) y i).1 -
      (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
        cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i) :=
    prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (div_nonneg hR (norm_nonneg _)) _)
      (cutDens_nonneg _ _)
  rw [hP1, hPB, hPK, mul_one]
  calc (∏ e ∈ Ebe, kb e) * (∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l)) *
        (∏ e ∈ univ.biUnion Ea, ka e) * ∏ i ∈ X.biUnion id, (ε₀ * R /
          ‖(extendConfig (X.biUnion id) y i).1 - (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
            cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i)
      = ((∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l)) *
          ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, kb e)) * ∏ i ∈ X.biUnion id, (ε₀ * R /
          ‖(extendConfig (X.biUnion id) y i).1 - (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
            cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i) := by ring
    _ ≤ ((∏ l, ∏ S ∈ ((G l).subtype (· ∈ X)).erase (hat l), rb S ^ 2) *
          ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, kb e)) * PD :=
        mul_le_mul (mul_le_mul_of_nonneg_right hPE (mul_nonneg hPK0 hPB0)) hPD hPDi0
          (mul_nonneg (prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _)
            (mul_nonneg hPK0 hPB0))
    _ ≤ (radF lam y * ((∏ e ∈ NT, nearE M lam y e) *
          ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, (nE e + fE e)))) * PD :=
        mul_le_mul_of_nonneg_right hcore hPD0
    _ ≤ _ := by
      unfold flatTerm
      simp only [hTree, ↓reduceIte]
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (term_expand (radF_nonneg hlam y) nE fE ka
        (nearE_nonneg M lam y) (farE_nonneg M lam _ y) hka hkaf NT (univ.biUnion Ea) Ebe
        (hNTB NT hNT) hAB) hPD0

open scoped Classical in
/-- **The integrand of a flat structure, bounded by tree terms** (proof of Lemma 4.59):
pointwise, with `NT` the edges inside the blocks, `A ⊆ E^b` the near even edges, and `T` the tree
`NT ∪ ⋃ E^a_k ∪ E^b`,
`integrand ≤ ∑_{NT, A} 𝟙_{T tree} R^{-2} ∏ ρ_i² ∏_{NT ∪ A} nearE ∏_{(⋃E^a ∪ E^b) ∖ A} farE ∏ Ψ`. -/
theorem flatIntegrand_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) (hC₀ : 0 < C₀)
    (hR : 0 ≤ ε₀ * truncationScale p₀ β lam) {a : ℝ} (ha : C₀ / M ≤ a)
    (hX : IsSubpartition X) [Nonempty (X.biUnion id)] {κ : Type*} [Fintype κ]
    {G : κ → Finset (Finset ℕ)} {Ta : κ → Finset (ℕ × ℕ)} {Eb : Finset (ℕ × ℕ)}
    (hF : FlatHyp X G Ta Eb) (y : X.biUnion id → ℂ × ℂ) :
    flatIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Eb (extendConfig (X.biUnion id) y) ≤
      ∑ NT ∈ (intraE (Limits.blockOf X)).powerset,
        ∑ A ∈ (graphOf (X.biUnion id) Eb).edgeFinset.powerset,
          flatTerm χ β lam M (17 * ε₀ * truncationScale p₀ β lam) (ε₀ * truncationScale p₀ β lam) a
            (univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Eb).edgeFinset) NT A y := by
  unfold flatIntegrand
  set R := truncationScale p₀ β lam with hRdef
  set Ea : κ → Finset (Sym2 (X.biUnion id)) := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
    with hEa
  set Ebe := (graphOf (X.biUnion id) Eb).edgeFinset with hEbe
  set PD := ∏ i, dipoleWeight χ β lam (ε₀ * R) a ((y i).2 - (y i).1) with hPD
  have hMpos : 0 < M := by linarith
  have hPD0 : 0 ≤ PD := prod_nonneg fun i _ => dipoleWeight_nonneg _ _ _ hR _
  have hcy : ∀ i (hi : i ∈ X.biUnion id), extendConfig (X.biUnion id) y i = y ⟨i, hi⟩ :=
    fun i hi => by simp only [extendConfig, hi, dite_true]
  obtain ⟨hGdisj, hEaG, hcardl, hinter, hconn, hcount⟩ := flat_structure hX G hF.subset hF.disj
    Ta hF.inter hF.card Eb hF.inter_b hF.conn hF.count
  have hTaV : ∀ l, Ta l ⊆ pairsOn (X.biUnion id) := fun l =>
    (hF.inter l).trans ((interPairs_mono hX (hF.subset l)).trans interPairs_subset_pairsOn)
  have hTbV : Eb ⊆ pairsOn (X.biUnion id) := hF.inter_b.trans interPairs_subset_pairsOn
  -- the right side is nonnegative
  have hRHS0 := sum_nonneg fun NT (_ : NT ∈ (intraE (Limits.blockOf X)).powerset) =>
    sum_nonneg fun A (_ : A ∈ Ebe.powerset) =>
      flatTerm_nonneg (χ := χ) (β := β) (M := M) (R' := 17 * ε₀ * R) (a := a) hlam hR
        (univ.biUnion Ea ∪ Ebe) NT A y
  -- the multipole events
  by_cases hmult : ∀ S ∈ X, ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
  swap
  · push Not at hmult
    obtain ⟨S, hS, hn⟩ := hmult
    have h0 : (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
        then (1 : ℝ) else 0) = 0 :=
      prod_eq_zero hS (ite_eq_right hn)
    rw [h0, mul_zero, zero_mul]
    exact hRHS0
  have hP1 : (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S)
      then (1 : ℝ) else 0) = 1 :=
    prod_eq_one fun S hS => ite_eq_left (hmult S hS)
  have hB : ∀ S : X, ((nearGraph M lam y).induce {i | Limits.blockOf X i = S}).Connected :=
    fun S => BoundedLowerEps.connected_induce_of_connOn hX y S.2 (hmult S.1 S.2)
  -- the largest block of each group
  have hXne : ∀ l, (G l).Nonempty := fun l => by
    have := hF.card l
    exact card_pos.1 (by omega)
  have hhat : ∀ l, ∃ S ∈ G l, ∀ S' ∈ G l, blockRad (extendConfig (X.biUnion id) y) S' ≤
      blockRad (extendConfig (X.biUnion id) y) S := fun l =>
    exists_max_image _ _ (hXne l)
  choose hatS hhatS hhatmax using hhat
  set hat : κ → X := fun l => ⟨hatS l, hF.subset l (hhatS l)⟩ with hhatdef
  set rb : X → ℝ := fun S => blockRad (extendConfig (X.biUnion id) y) S with hrbdef
  have hrb0 : ∀ S, 0 ≤ rb S := fun S => blockRad_nonneg _
  have hrb : ∀ S : X, ∃ i, Limits.blockOf X i = S ∧ rb S ≤ rhoD lam (y i) := by
    intro S
    obtain ⟨i, hi, heq⟩ := exists_mem_eq_sup (S : Finset ℕ) (hX.1 S S.2)
      (fun i => ‖(extendConfig (X.biUnion id) y i).1 - (extendConfig (X.biUnion id) y i).2‖₊)
    have hiV : i ∈ X.biUnion id := mem_biUnion.2 ⟨S, S.2, hi⟩
    refine ⟨⟨i, hiV⟩, Limits.blockOf_eq hX S.2 hi, ?_⟩
    show (((S : Finset ℕ).sup fun i => ‖(extendConfig (X.biUnion id) y i).1 -
      (extendConfig (X.biUnion id) y i).2‖₊ : NNReal) : ℝ) ≤ _
    rw [heq, coe_nnnorm, hcy i hiV]
    exact le_max_left _ _
  have hhat' : ∀ l, hat l ∈ (G l).subtype (· ∈ X) ∧
      ∀ S ∈ (G l).subtype (· ∈ X), rb S ≤ rb (hat l) := fun l =>
    ⟨mem_subtype.2 (hhatS l), fun S hS => hhatmax l S (mem_subtype.1 hS)⟩
  -- the weights on unordered pairs
  set ka := keptWE M lam ε₀ R y with hkadef
  set kb := absE M lam ε₀ R y with hkbdef
  set fE := farE M lam (17 * ε₀ * R) y with hfEdef
  set nE := nearE M lam y with hnEdef
  have hka : ∀ e, 0 ≤ ka e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact keptW_nonneg (y i) (y j)
  have hkb : ∀ e, 0 ≤ kb e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact absEvenWeight_nonneg _ _ _ _ _ _
  have hkbN : ∀ e, 0 ≤ nE e + fE e := fun e =>
    add_nonneg (nearE_nonneg M lam y e) (farE_nonneg M lam _ y e)
  have hkbb : ∀ i j, kb s(i, j) ≤ min (rhoD lam (y i)) (rhoD lam (y j)) ^ 2 *
      (nE s(i, j) + fE s(i, j)) := fun i j => absEvenWeight_le hlam hMpos (y i) (y j)
  have hkaf : ∀ e, ka e ≤ fE e := fun e => by
    induction e using Sym2.ind with
    | h i j => exact keptW_le_farW hlam hMpos (y i) (y j)
  have hcore := core_le_sum_tree (M := M) hlam (Limits.blockOf X) y hB Ea
    (fun l => (G l).subtype (· ∈ X)) hGdisj hEaG hcardl Ebe hinter hconn hcount rb hrb0 hrb hat
    hhat' ka kb (fun e => nE e + fE e) hka hkb hkbN hkbb
  -- the factors of the integrand
  have hPB : (∏ p ∈ Eb, absEvenWeight M lam ε₀ R (extendConfig (X.biUnion id) y p.1)
      (extendConfig (X.biUnion id) y p.2)) = ∏ e ∈ Ebe, kb e := by
    refine (prod_edgeFinset_graphOf hTbV kb _ fun p _ h1 h2 => ?_).symm
    rw [hcy p.1 h1, hcy p.2 h2]
    rfl
  have hEadisj : ((univ : Finset κ) : Set κ).PairwiseDisjoint Ea := by
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h i j =>
      exact Finset.disjoint_left.1 (hGdisj l l' hll') (hEaG l _ he i (Sym2.mem_mk_left i j))
        (hEaG l' _ he' i (Sym2.mem_mk_left i j))
  have hPK : (∏ l, ∏ p ∈ Ta l, keptPair M lam ε₀ R (extendConfig (X.biUnion id) y) p) =
      ∏ e ∈ univ.biUnion Ea, ka e := by
    rw [prod_biUnion hEadisj]
    refine prod_congr rfl fun l _ => (prod_edgeFinset_graphOf (hTaV l) ka _
      fun p _ h1 h2 => ?_).symm
    rw [keptPair_eq, hcy p.1 h1, hcy p.2 h2]
    rfl
  have hPE : (∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l)) ≤
      ∏ l, ∏ S ∈ ((G l).subtype (· ∈ X)).erase (hat l), rb S ^ 2 := by
    refine prod_le_prod₀ (fun l _ => ?_) fun l _ => ?_
    · unfold prodExceptMax
      split_ifs with h
      · exact le_inf' _ _ fun S _ => prod_nonneg fun S' _ => sq_nonneg _
      · exact zero_le_one
    · rw [prod_subtype_erase (hF.subset l) (fun S => blockRad (extendConfig (X.biUnion id) y) S ^ 2)
        (hat l)]
      exact prodExceptMax_le_erase (extendConfig (X.biUnion id) y) (hhatS l)
  have hPD : (∏ i ∈ X.biUnion id, (ε₀ * R / ‖(extendConfig (X.biUnion id) y i).1 -
      (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
      cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i)) ≤ PD := by
    rw [← prod_coe_sort (X.biUnion id)]
    refine prod_le_prod₀ (fun i _ => mul_nonneg (Real.rpow_nonneg (div_nonneg hR
      (norm_nonneg _)) _) (cutDens_nonneg _ _)) fun i _ => ?_
    rw [hcy i i.2]
    exact rpow_mul_cutDens_le hχ (div_pos hC₀ hMpos) ha hR (y i)
  -- disjointness of the edge families
  have hAB : Disjoint (univ.biUnion Ea) Ebe := by
    refine (disjoint_biUnion_left _ _ _).2 fun l _ => ?_
    exact disjoint_edgeFinset_graphOf (hTaV l) hTbV
      (disjoint_of_subset_left (subset_biUnion_of_mem Ta (mem_univ l)) hF.disj_ab)
  have hNTB : ∀ NT ∈ (intraE (Limits.blockOf X)).powerset, Disjoint NT Ebe := by
    intro NT hNT
    rw [Finset.disjoint_left]
    intro e he he'
    have h1 := (mem_filter.1 (mem_powerset.1 hNT he)).2.1
    exact hinter e (mem_union_right _ he') h1
  -- assembling
  have hPB0 : 0 ≤ ∏ e ∈ Ebe, kb e := prod_nonneg fun e _ => hkb e
  have hPK0 : 0 ≤ ∏ e ∈ univ.biUnion Ea, ka e := prod_nonneg fun e _ => hka e
  have hPE0 : 0 ≤ ∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l) := by
    refine prod_nonneg fun l _ => ?_
    unfold prodExceptMax
    split_ifs with h
    · exact le_inf' _ _ fun S _ => prod_nonneg fun S' _ => sq_nonneg _
    · exact zero_le_one
  have hPDi0 : 0 ≤ ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(extendConfig (X.biUnion id) y i).1 -
      (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
        cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i) :=
    prod_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (div_nonneg hR (norm_nonneg _)) _)
      (cutDens_nonneg _ _)
  rw [hP1, hPB, hPK, mul_one]
  calc (∏ e ∈ Ebe, kb e) * (∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l)) *
        (∏ e ∈ univ.biUnion Ea, ka e) * ∏ i ∈ X.biUnion id, (ε₀ * R /
          ‖(extendConfig (X.biUnion id) y i).1 - (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
            cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i)
      = ((∏ l, prodExceptMax (extendConfig (X.biUnion id) y) (G l)) *
          ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, kb e)) * ∏ i ∈ X.biUnion id, (ε₀ * R /
          ‖(extendConfig (X.biUnion id) y i).1 - (extendConfig (X.biUnion id) y i).2‖) ^ (C₀ / M) *
            cutDens χ β lam (ε₀ * R) (extendConfig (X.biUnion id) y i) := by ring
    _ ≤ ((∏ l, ∏ S ∈ ((G l).subtype (· ∈ X)).erase (hat l), rb S ^ 2) *
          ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, kb e)) * PD :=
        mul_le_mul (mul_le_mul_of_nonneg_right hPE (mul_nonneg hPK0 hPB0)) hPD hPDi0
          (mul_nonneg (prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _)
            (mul_nonneg hPK0 hPB0))
    _ ≤ (∑ NT ∈ (intraE (Limits.blockOf X)).powerset,
          if (fromEdgeSet ((NT ∪ (univ.biUnion Ea ∪ Ebe) : Finset (Sym2 (X.biUnion id))) :
              Set (Sym2 (X.biUnion id)))).IsTree then
            radF lam y * ((∏ e ∈ NT, nearE M lam y e) *
              ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, (nE e + fE e)))
          else 0) * PD := mul_le_mul_of_nonneg_right hcore hPD0
    _ = ∑ NT ∈ (intraE (Limits.blockOf X)).powerset,
          (if (fromEdgeSet ((NT ∪ (univ.biUnion Ea ∪ Ebe) : Finset (Sym2 (X.biUnion id))) :
              Set (Sym2 (X.biUnion id)))).IsTree then
            radF lam y * ((∏ e ∈ NT, nearE M lam y e) *
              ((∏ e ∈ univ.biUnion Ea, ka e) * ∏ e ∈ Ebe, (nE e + fE e)))
          else 0) * PD := sum_mul _ _ _
    _ ≤ _ := by
        refine sum_le_sum fun NT hNT => ?_
        unfold flatTerm
        split_ifs with ht
        · rw [← sum_mul]
          exact mul_le_mul_of_nonneg_right (term_expand (radF_nonneg hlam y) nE fE ka
            (nearE_nonneg M lam y) (farE_nonneg M lam _ y) hka hkaf NT (univ.biUnion Ea) Ebe
            (hNTB NT hNT) hAB) hPD0
        · simp

end Pointwise

/-! ### The logarithmic weights -/

section LogWeights

variable {U : Finset ℕ}

/-- The logarithmic factor `ell(ρ_i) = 1 + log⁺(R'/ρ_i)` of a label (`ρ_i = λ` off `U`). -/
noncomputable def logL (lam R' : ℝ) (u : U → ℂ) (i : ℕ) : ℝ :=
  ell R' (if h : i ∈ U then rho lam (u ⟨i, h⟩) else lam)

/-- The weight `8π ell(ρ_i) ell(ρ_j)` of a pair of labels. -/
noncomputable def logW (lam R' : ℝ) (u : U → ℂ) (p : ℕ × ℕ) : ℝ :=
  8 * Real.pi * (logL lam R' u p.1 * logL lam R' u p.2)

theorem one_le_logL (lam R' : ℝ) (u : U → ℂ) (i : ℕ) : 1 ≤ logL lam R' u i := one_le_ell _ _

theorem logL_nonneg (lam R' : ℝ) (u : U → ℂ) (i : ℕ) : 0 ≤ logL lam R' u i :=
  zero_le_one.trans (one_le_logL lam R' u i)

theorem logW_nonneg (lam R' : ℝ) (u : U → ℂ) (p : ℕ × ℕ) : 0 ≤ logW lam R' u p :=
  mul_nonneg (by positivity) (mul_nonneg (logL_nonneg _ _ _ _) (logL_nonneg _ _ _ _))

theorem one_le_eight_pi_mul_ell (R' x : ℝ) : 1 ≤ 8 * Real.pi * ell R' x := by
  have h1 := one_le_ell R' x
  have hπ : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.two_le_pi]
  nlinarith

theorem edge_le_logW (lam R' : ℝ) (u : U → ℂ) (p : ℕ × ℕ) (h1 : p.1 ∈ U) (h2 : p.2 ∈ U) :
    8 * Real.pi * ell R' (edgeMin id (fun i => rho lam (u i)) s(⟨p.1, h1⟩, ⟨p.2, h2⟩)) ≤
      logW lam R' u p := by
  unfold logW logL
  rw [dite_eq_left h1, dite_eq_left h2, edgeMin_mk, id]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hx := one_le_ell R' (rho lam (u ⟨p.1, h1⟩))
  have hy := one_le_ell R' (rho lam (u ⟨p.2, h2⟩))
  rcases min_choice (rho lam (u ⟨p.1, h1⟩)) (rho lam (u ⟨p.2, h2⟩)) with h | h <;> rw [h]
  · exact le_mul_of_one_le_right (by linarith) hy
  · exact le_mul_of_one_le_left (by linarith) hx

end LogWeights

/-! ### One flat structure, integrated -/

section Integrated

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β C₀ : ℝ} {X : Finset (Finset ℕ)}


end Integrated

end AbsoluteLower

end MultipoleBKT

end
