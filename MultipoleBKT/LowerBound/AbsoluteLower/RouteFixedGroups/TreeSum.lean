/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Logs

/-!
# Summing trees while keeping the groups fixed

(A.65),
(A.66) and (A.68) in the proof of Lemma 4.58. The disjoint odd groups
cost one logarithmic power per label. The even tree costs one more.
The initial power and these two powers total three, and the radial cutoff
allows the increase to four.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open MeasureTheory Finset SimpleGraph Set Limits SmallIntegral Multipole SetPartition
open RoutePosition
open scoped Classical ENNReal

/-- The cardinality factors in (4.115) and (A.68). -/
noncomputable def groupCardinality (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) : ℝ :=
  ((coarsen X (Finset.univ.image Xs)).card : ℝ) ^ (coarsen X (Finset.univ.image Xs)).card *
    ∏ l, ((Xs l).card : ℝ) ^ (Xs l).card

theorem groupCardinality_nonneg (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) : 0 ≤ groupCardinality X Xs := by
  unfold groupCardinality
  positivity

/-- The product of the two tree sums, with all written group factors retained. -/
theorem fixed_groups_endpoint_sum {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (hne : ∀ l, (Xs l).Nonempty)
    (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) {a : ℝ} (ha : 0 < a) :
    (∏ l, ∑ T ∈ relTreePairs (Xs l), ∏ p ∈ T, L p.1 * L p.2) *
      (∑ T ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), ∏ p ∈ T, L p.1 * L p.2) ≤
      (max (4 / a ^ 2) 1 ^ 2) ^ (X.biUnion id).card * groupCardinality X Xs *
        Real.exp (2 * a * ∑ i ∈ X.biUnion id, L i) := by
  let Y := coarsen X (Finset.univ.image Xs)
  have hGX : ∀ G ∈ Finset.univ.image Xs, G ⊆ X := by
    intro G hG
    obtain ⟨l, _, rfl⟩ := mem_image.mp hG
    exact hXs l
  have hGne : ∀ G ∈ Finset.univ.image Xs, G.Nonempty := by
    intro G hG
    obtain ⟨l, _, rfl⟩ := mem_image.mp hG
    exact hne l
  have hGd : ((Finset.univ.image Xs : Finset (Finset (Finset ℕ))) : Set (Finset (Finset ℕ))).PairwiseDisjoint id := by
    intro G hG H hH hGH
    obtain ⟨i, _, rfl⟩ := mem_image.mp hG
    obtain ⟨j, _, rfl⟩ := mem_image.mp hH
    exact hdisj i j (fun h => hGH (h ▸ rfl))
  have hY := isSubpartition_coarsen hX hGX hGne hGd
  have hVY : Y.biUnion id = X.biUnion id := biUnion_coarsen hGX
  have hsum : ∑ l, (Xs l).card ≤ X.card := by
    rw [← card_biUnion fun i _ j _ h => hdisj i j h]
    exact card_le_card (biUnion_subset.mpr fun l _ => hXs l)
  have hn : n ≤ ∑ l, (Xs l).card := by
    calc n = ∑ _l : Fin n, 1 := by simp
      _ ≤ _ := sum_le_sum fun l _ => card_pos.mpr (hne l)
  have hYc : Y.card ≤ X.card := by
    have := SmallIntegral.card_coarsen_add_le Xs hXs hdisj
    dsimp only [Y]
    omega
  have hXc : X.card ≤ (X.biUnion id).card := card_le_card_biUnion hX.2 hX.1
  have hsL : ∑ l, ∑ i ∈ (Xs l).biUnion id, L i ≤ ∑ i ∈ X.biUnion id, L i := by
    rw [← sum_biUnion (s := univ) (t := fun l => (Xs l).biUnion id)
      (fun i _ j _ h => Hierarchical.disjoint_biUnion_of_disjoint hX (hXs i) (hXs j) (hdisj i j h))]
    exact sum_le_sum_of_subset_of_nonneg (biUnion_subset.mpr fun l _ =>
      biUnion_subset_biUnion_of_subset_left id (hXs l)) (fun i _ _ => hL i)
  let D := max (4 / a ^ 2) 1
  have hD : 1 ≤ D := le_max_right _ _
  have hodd (l : Fin n) := sum_tree_weights_le (isSubpartition_of_subset hX (hXs l))
    (relTreePairs (Xs l)) (fun T hT => by
      obtain ⟨G, hG, rfl⟩ := mem_image.mp hT
      exact mem_image.mpr ⟨G, mem_relTrees₀.mpr (Or.inl (mem_relTrees.mp hG)), rfl⟩)
    L hL (fun p => L p.1 * L p.2) (fun p => mul_nonneg (hL _) (hL _))
    (fun _ _ => le_rfl) ha
  have heven := sum_tree_weights_le hY (relTreePairs₀ Y) (fun _ h => h)
    L hL (fun p => L p.1 * L p.2) (fun p => mul_nonneg (hL _) (hL _))
    (fun _ _ => le_rfl) ha
  have hexp : (∏ l, Real.exp (a * ∑ i ∈ (Xs l).biUnion id, L i)) *
      Real.exp (a * ∑ i ∈ Y.biUnion id, L i) ≤
        Real.exp (2 * a * ∑ i ∈ X.biUnion id, L i) := by
    rw [← Real.exp_sum, ← Real.exp_add, ← mul_sum, hVY]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hpow : D ^ (∑ l, (Xs l).card) * D ^ Y.card ≤ (D ^ 2) ^ (X.biUnion id).card := by
    rw [← pow_add, ← pow_mul]
    apply pow_le_pow_right₀ hD
    omega
  calc
    _ ≤ (∏ l, D ^ (Xs l).card * ((Xs l).card : ℝ) ^ (Xs l).card *
        Real.exp (a * ∑ i ∈ (Xs l).biUnion id, L i)) *
      (D ^ Y.card * (Y.card : ℝ) ^ Y.card * Real.exp (a * ∑ i ∈ Y.biUnion id, L i)) :=
      mul_le_mul (prod_le_prod₀ (fun l _ => sum_nonneg fun T _ =>
        prod_nonneg fun p _ => mul_nonneg (hL _) (hL _)) (fun l _ => hodd l)) heven
        (sum_nonneg fun T _ => prod_nonneg fun p _ => mul_nonneg (hL _) (hL _))
        (prod_nonneg fun l _ => mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hD) _)
          (pow_nonneg (Nat.cast_nonneg _) _)) (Real.exp_pos _).le)
    _ = (D ^ (∑ l, (Xs l).card) * D ^ Y.card) * groupCardinality X Xs *
        ((∏ l, Real.exp (a * ∑ i ∈ (Xs l).biUnion id, L i)) *
          Real.exp (a * ∑ i ∈ Y.biUnion id, L i)) := by
      simp_rw [prod_mul_distrib]
      rw [prod_pow_eq_pow_sum]
      unfold groupCardinality
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hpow (groupCardinality_nonneg X Xs))
      hexp (mul_nonneg (prod_nonneg fun l _ => (Real.exp_pos _).le) (Real.exp_pos _).le) (mul_nonneg (pow_nonneg (pow_nonneg (zero_le_one.trans hD) _) _)
        (groupCardinality_nonneg X Xs))

/-- The exponential from the two tree sums uses exactly two radial powers.
The cutoff then allows the paper's increase from three powers to four. -/
theorem radial_power_allocation {χ : ℂ → ℝ} {β lam h a : ℝ}
    (ha : 0 < a) (u : ℂ) (hu : 0 < ‖u‖ ∧ ‖u‖ ≤ h) :
    sourceWeight χ β lam h a u * Real.exp (2 * a * Real.log (17 * h / ‖u‖)) ≤
      ((17 : ℝ) ^ (2 * a)) * sourceWeight χ β lam h (4 * a) u := by
  have hh : 0 < h := hu.1.trans_le hu.2
  have hq : 1 ≤ h / ‖u‖ := (one_le_div hu.1).mpr hu.2
  unfold sourceWeight
  rw [indicator_of_mem (show u ∈ Metric.closedBall (0 : ℂ) h by simpa using hu.2),
    indicator_of_mem (show u ∈ Metric.closedBall (0 : ℂ) h by simpa using hu.2)]
  have he : Real.exp (2 * a * Real.log (17 * h / ‖u‖)) =
      (17 : ℝ) ^ (2 * a) * (h / ‖u‖) ^ (2 * a) := by
    rw [mul_comm (2 * a), ← Real.rpow_def_of_pos (by exact div_pos (mul_pos (by norm_num) hh) hu.1), mul_div_assoc,
      Real.mul_rpow (by norm_num) (by positivity)]
  rw [he]
  have hp : (h / ‖u‖) ^ a * (h / ‖u‖) ^ (2 * a) ≤ (h / ‖u‖) ^ (4 * a) := by
    rw [← Real.rpow_add (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  calc
    _ = (17 : ℝ) ^ (2 * a) * Real.exp (β * smearedKernel χ lam u) *
        ((h / ‖u‖) ^ a * (h / ‖u‖) ^ (2 * a)) := by ring
    _ ≤ (17 : ℝ) ^ (2 * a) * Real.exp (β * smearedKernel χ lam u) *
        (h / ‖u‖) ^ (4 * a) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- (A.68) at the level of its radial integrand, with fixed groups. -/
theorem fixed_groups_integrand_sum {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (hne : ∀ l, (Xs l).Nonempty)
    {χ : ℂ → ℝ} {β lam h a : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h) (ha : 0 < a)
    (u : X.biUnion id → ℂ) :
    (∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
      ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
        sourceSpatialWeight χ β lam h a
          (univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
            (graphOf (X.biUnion id) Tb).edgeFinset) u) ≤
      (max (4 / a ^ 2) 1 ^ 2 * (17 : ℝ) ^ (2 * a)) ^ (X.biUnion id).card *
        groupCardinality X Xs *
          ((∏ i, sourceWeight χ β lam h (4 * a) (u i)) * radiusFactor lam u) := by
  by_cases hu : ∀ i, 0 < ‖u i‖ ∧ ‖u i‖ ≤ h
  · let L := labelLog h u
    let F := radiusFactor lam u * ∏ i, sourceWeight χ β lam h a (u i)
    have hF : 0 ≤ F := mul_nonneg (radiusFactor_nonneg hlam u)
      (prod_nonneg fun _ _ => sourceWeight_nonneg χ β lam hh a _)
    have hpair : ∀ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
        ∀ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
        sourceSpatialWeight χ β lam h a
          (univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
            (graphOf (X.biUnion id) Tb).edgeFinset) u ≤
          F * ((∏ l, ∏ p ∈ Ta l, L p.1 * L p.2) * ∏ p ∈ Tb, L p.1 * L p.2) := by
      intro Ta hTa Tb hTb
      have hflat := flatHyp_of_relTree hX hXs hdisj
        (fun l => Fintype.mem_piFinset.mp hTa l) hTb
      have hTaV : ∀ l, Ta l ⊆ pairsOn (X.biUnion id) := fun l =>
        (hflat.inter l).trans ((interPairs_mono hX (hXs l)).trans interPairs_subset_pairsOn)
      have hTbV : Tb ⊆ pairsOn (X.biUnion id) := hflat.inter_b.trans interPairs_subset_pairsOn
      exact sourceSpatialWeight_le_endpoints hlam hh ha Ta hTaV Tb hTbV u
    have hs := fixed_groups_endpoint_sum hX Xs hXs hdisj hne L (labelLog_nonneg u hu) ha
    have hlog : ∑ i ∈ X.biUnion id, L i = ∑ i : X.biUnion id, Real.log (17 * h / ‖u i‖) := by
      rw [← sum_coe_sort]
      exact sum_congr rfl fun i _ => labelLog_coe h u i
    have hrad : F * Real.exp (2 * a * ∑ i ∈ X.biUnion id, L i) ≤
        ((17 : ℝ) ^ (2 * a)) ^ (X.biUnion id).card *
          ((∏ i, sourceWeight χ β lam h (4 * a) (u i)) * radiusFactor lam u) := by
      rw [hlog, mul_sum, Real.exp_sum]
      dsimp only [F]
      rw [mul_assoc, ← prod_mul_distrib]
      calc
        _ ≤ radiusFactor lam u * ∏ i : X.biUnion id,
            (17 : ℝ) ^ (2 * a) * sourceWeight χ β lam h (4 * a) (u i) :=
          mul_le_mul_of_nonneg_left (prod_le_prod₀
            (fun i _ => mul_nonneg (sourceWeight_nonneg χ β lam hh a _) (Real.exp_pos _).le)
            (fun i _ => radial_power_allocation ha (u i) (hu i))) (radiusFactor_nonneg hlam u)
        _ = _ := by rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_coe]; ring
    calc
      _ ≤ ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            F * ((∏ l, ∏ p ∈ Ta l, L p.1 * L p.2) * ∏ p ∈ Tb, L p.1 * L p.2) :=
        sum_le_sum fun Ta hTa => sum_le_sum fun Tb hTb => hpair Ta hTa Tb hTb
      _ = F * ((∏ l, ∑ T ∈ relTreePairs (Xs l), ∏ p ∈ T, L p.1 * L p.2) *
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), ∏ p ∈ Tb, L p.1 * L p.2) := by
        rw [prod_univ_sum, sum_mul_sum]
        simp only [mul_sum]
      _ ≤ F * ((max (4 / a ^ 2) 1 ^ 2) ^ (X.biUnion id).card * groupCardinality X Xs *
          Real.exp (2 * a * ∑ i ∈ X.biUnion id, L i)) := mul_le_mul_of_nonneg_left hs hF
      _ = ((max (4 / a ^ 2) 1 ^ 2) ^ (X.biUnion id).card * groupCardinality X Xs) *
          (F * Real.exp (2 * a * ∑ i ∈ X.biUnion id, L i)) := by ring
      _ ≤ ((max (4 / a ^ 2) 1 ^ 2) ^ (X.biUnion id).card * groupCardinality X Xs) *
          (((17 : ℝ) ^ (2 * a)) ^ (X.biUnion id).card *
            ((∏ i, sourceWeight χ β lam h (4 * a) (u i)) * radiusFactor lam u)) :=
        mul_le_mul_of_nonneg_left hrad (mul_nonneg (by positivity) (groupCardinality_nonneg X Xs))
      _ = _ := by rw [mul_pow]; ring
  · have hz := prod_sourceWeight_eq_zero (χ := χ) (β := β) (lam := lam) ha u hu
    have hz4 := prod_sourceWeight_eq_zero (χ := χ) (β := β) (lam := lam) (by linarith : 0 < 4 * a) u hu
    simp only [sourceSpatialWeight, hz, mul_zero, zero_mul, sum_const_zero, hz4, le_refl]

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
