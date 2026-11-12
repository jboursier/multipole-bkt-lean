/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.TreeSum
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.ProfileBounds
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.SourceSeries
public import MultipoleBKT.UpperBound.SimplifiedUpper.MergeBasic
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Sum

/-!
# Summing the displayed group cardinality factors

(4.124) and
(4.125) in the proof of Lemma 4.59. Enumerate by the selected size and the
ordered positive profile. Stirling absorbs the size powers, and stars
and bars bounds the number of profiles. Only then combine the estimate
with the fixed-group integral.
-/

@[expose] public section

namespace MultipoleBKT.AbsoluteLower.RouteFixedGroups

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits Hierarchical SmallIntegral
open UpperBound.AbsoluteUpper (jLarge)
open scoped Classical ENNReal

/-- The coarse partition has exactly `q - s + n` blocks, as in Step 2. -/
theorem coarse_cardinality {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : Xs ∈ nonemptyGroups X n) :
    (coarsen X (Finset.univ.image Xs)).card = X.card - ∑ l, (Xs l).card + n := by
  obtain ⟨hs, hd, hn⟩ := mem_nonemptyGroups.mp hXs
  have hinj : Function.Injective Xs := by
    intro i j he
    by_contra hij
    obtain ⟨S, hS⟩ := hn i
    exact (disjoint_left.mp (hd i j hij)) hS (he ▸ hS)
  have hGX : ∀ G ∈ Finset.univ.image Xs, G ⊆ X := by
    intro G hG
    obtain ⟨l, _, rfl⟩ := mem_image.mp hG
    exact hs l
  have hGn : ∀ G ∈ Finset.univ.image Xs, G.Nonempty := by
    intro G hG
    obtain ⟨l, _, rfl⟩ := mem_image.mp hG
    exact hn l
  have hGd : ((Finset.univ.image Xs : Finset (Finset (Finset ℕ))) : Set (Finset (Finset ℕ))).PairwiseDisjoint id := by
    intro G hG H hH hGH
    obtain ⟨i, _, rfl⟩ := mem_image.mp hG
    obtain ⟨j, _, rfl⟩ := mem_image.mp hH
    exact hd i j (fun h => hGH (h ▸ rfl))
  have hc := UpperBound.SimplifiedUpper.card_coarsen_add hX hGX hGn hGd
  rw [sum_image (fun i _ j _ he => hinj he), card_image_of_injective _ hinj,
    card_univ, Fintype.card_fin] at hc
  have hsum := sum_group_sizes_le hXs
  omega

/-- The literal binomial-multinomial enumeration of the displayed group factors. -/
theorem sum_groupCardinality_profiles {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (n : ℕ) :
    (∑ Xs ∈ nonemptyGroups X n, groupCardinality X Xs) =
      ∑ s ∈ range (X.card + 1), (X.card.choose s : ℝ) *
        ∑ m ∈ positiveProfiles n s, (Nat.multinomial univ m : ℝ) *
          (∏ i, (m i : ℝ) ^ m i) * ((X.card - s + n : ℕ) : ℝ) ^ (X.card - s + n) := by
  let F (m : Fin n → ℕ) : ℝ := (∏ i, (m i : ℝ) ^ m i) *
    ((X.card - ∑ i, m i + n : ℕ) : ℝ) ^ (X.card - ∑ i, m i + n)
  have he : (∑ Xs ∈ nonemptyGroups X n, groupCardinality X Xs) =
      ∑ Xs ∈ nonemptyGroups X n, F (fun i => (Xs i).card) := by
    apply sum_congr rfl
    intro Xs hXs
    rw [groupCardinality, coarse_cardinality hX hXs]
    dsimp only [F]
    ring
  rw [he, sum_nonemptyGroups X n F]
  apply sum_congr rfl
  intro s hs
  rw [mul_sum]
  apply sum_congr rfl
  intro m hm
  dsimp only [F]
  rw [(mem_positiveProfiles.mp hm).1, nsmul_eq_mul, Nat.cast_mul]
  ring

/-- (4.125) for the literal cardinality factors.
The proof retains the written `n^(-2n)` bound until the group-number sum. -/
theorem sum_groupCardinality_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ nonemptyGroups X n, groupCardinality X Xs) ≤
      (4 * Real.exp 6) ^ X.card * X.card.factorial := by
  have he : (∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ nonemptyGroups X n, groupCardinality X Xs) =
      ∑ s ∈ range (X.card + 1), (X.card.choose s : ℝ) *
        ∑ n ∈ range (s + 1), 1 / (n.factorial : ℝ) * ∑ m ∈ positiveProfiles n s,
          (Nat.multinomial univ m : ℝ) * (∏ i, (m i : ℝ) ^ m i) *
            ((X.card - s + n : ℕ) : ℝ) ^ (X.card - s + n) := by
    simp_rw [sum_groupCardinality_profiles hX, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro s hs
    have hsubset : range (s + 1) ⊆ range (X.card + 1) := range_mono (by have := mem_range.mp hs; omega)
    have hzero (n : ℕ) (_hn : n ∈ range (X.card + 1)) (hn : n ∉ range (s + 1)) :
        (positiveProfiles n s) = ∅ := positiveProfiles_eq_empty_of_lt (by
      have := not_lt.mp (fun h => hn (mem_range.mpr h))
      omega)
    calc
      _ = ∑ n ∈ range (X.card + 1), ∑ m ∈ positiveProfiles n s,
          (X.card.choose s : ℝ) * (1 / (n.factorial : ℝ) *
            ((Nat.multinomial univ m : ℝ) * (∏ i, (m i : ℝ) ^ m i) *
              ((X.card - s + n : ℕ) : ℝ) ^ (X.card - s + n))) := by
        apply sum_congr rfl
        intro n _
        apply sum_congr rfl
        intro m _
        ring
      _ = _ := by
        symm
        apply sum_subset hsubset
        intro n hn hn'
        simp only [hzero n hn hn', sum_empty]
  rw [he]
  refine (source_size_series_le X.card).trans ?_
  have hp := pow_self_le_factorial_mul_exp X.card
  calc
    _ ≤ (4 * Real.exp 5) ^ X.card * ((X.card.factorial : ℝ) * Real.exp X.card) := by gcongr
    _ = _ := by
      rw [mul_pow, mul_pow]
      have he : Real.exp 5 ^ X.card * Real.exp X.card = Real.exp 6 ^ X.card := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
        congr 1
        ring
      calc
        (4 : ℝ) ^ X.card * Real.exp 5 ^ X.card * (X.card.factorial * Real.exp X.card) =
          (4 : ℝ) ^ X.card * X.card.factorial * (Real.exp 5 ^ X.card * Real.exp X.card) := by ring
        _ = _ := by rw [he]; ring

/-- Compatibility after the fixed-group lemma has been proved.
The conditional premise belongs only to this internal summation helper. -/
theorem summed_integrals_le_of_fixed {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ C₀ A : ℝ}
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (hA : 0 ≤ A)
    (hfixed : ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      (∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
        ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) ≤ ENNReal.ofReal (A * groupCardinality X Xs)) :
    (∑' n : ℕ, ((n.factorial : ℝ≥0∞))⁻¹ *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) ≤
      ENNReal.ofReal (A * ((4 * Real.exp 6) ^ X.card * X.card.factorial)) := by
  let domain (n : ℕ) := (Fintype.piFinset fun _ : Fin n => X.powerset).filter
    (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))
  let J {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) :=
    ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
      ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb
  have hz {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hsub : ∀ l, Xs l ⊆ X)
      (hne : ¬ ∀ l, (Xs l).Nonempty) : J Xs = 0 := by
    apply sum_eq_zero
    intro Ta hTa
    exact (hne (fun l => nonempty_of_mem_relTreePairs (isSubpartition_of_subset hX (hsub l))
      (Fintype.mem_piFinset.mp hTa l))).elim
  have hsub {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : Xs ∈ domain n) :
      (∀ l, Xs l ⊆ X) ∧ (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) := by
    obtain ⟨hm, hd⟩ := mem_filter.mp hXs
    exact ⟨fun l => mem_powerset.mp (Fintype.mem_piFinset.mp hm l), hd⟩
  have heq (n : ℕ) : (∑ Xs ∈ domain n, J Xs) = ∑ Xs ∈ nonemptyGroups X n, J Xs := by
    symm
    apply sum_subset
    · intro Xs hXs
      obtain ⟨hs, hd, _⟩ := mem_nonemptyGroups.mp hXs
      exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun l => mem_powerset.mpr (hs l)), hd⟩
    · intro Xs hXs hnot
      apply hz Xs (hsub hXs).1
      intro hn
      exact hnot (mem_nonemptyGroups.mpr ⟨(hsub hXs).1, (hsub hXs).2, hn⟩)
  have hvan : ∀ n ∉ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
      ∑ Xs ∈ domain n, J Xs = 0 := by
    intro n hn
    rw [heq]
    have hempty : nonemptyGroups X n = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Xs hXs
      obtain ⟨hs, hd, hne⟩ := mem_nonemptyGroups.mp hXs
      have h := card_le_of_disjoint_nonempty hs hd hne
      have := not_lt.mp (fun hl => hn (mem_range.mpr hl))
      omega
    simp only [hempty, sum_empty, mul_zero]
  change (∑' n : ℕ, ((n.factorial : ℝ≥0∞))⁻¹ * ∑ Xs ∈ domain n, J Xs) ≤ _
  rw [tsum_eq_sum hvan]
  have hbound : ∀ n, ((n.factorial : ℝ≥0∞))⁻¹ * ∑ Xs ∈ domain n, J Xs ≤
      ENNReal.ofReal (A * (1 / (n.factorial : ℝ) * ∑ Xs ∈ nonemptyGroups X n, groupCardinality X Xs)) := by
    intro n
    rw [heq]
    have hJ : (∑ Xs ∈ nonemptyGroups X n, J Xs) ≤
        ENNReal.ofReal (A * ∑ Xs ∈ nonemptyGroups X n, groupCardinality X Xs) := by
      rw [mul_sum, ENNReal.ofReal_sum_of_nonneg (fun Xs _ => mul_nonneg hA (groupCardinality_nonneg X Xs))]
      apply sum_le_sum
      intro Xs hXs
      obtain ⟨hs, hd, _⟩ := mem_nonemptyGroups.mp hXs
      exact hfixed Xs hs hd
    refine (mul_le_mul' le_rfl hJ).trans_eq ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  refine (sum_le_sum fun n _ => hbound n).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg hA
    (mul_nonneg (by positivity) (sum_nonneg fun Xs _ => groupCardinality_nonneg X Xs))), ← mul_sum]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (sum_groupCardinality_le hX) hA

end MultipoleBKT.AbsoluteLower.RouteFixedGroups

end
