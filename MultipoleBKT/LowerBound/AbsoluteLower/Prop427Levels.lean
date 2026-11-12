/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Count
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.ProfileBounds
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteFixedGroups.Weighted
public import MultipoleBKT.LowerBound.AbsoluteLower.EulerGroup
public import MultipoleBKT.Appendix.SmallIntegral.JGraphs
public import MultipoleBKT.LowerBound.AbsoluteLower.Components

/-!
# Weighted tree sums and enumeration of groups

(A.65) and
(A.66) in the proof of Lemma 4.58, and (4.124) through (4.125) in the proof of Lemma 4.59.

`sum_prod_relTree_le` sums the endpoints of a fixed quotient tree,
applies the weighted Cayley formula, and uses arithmetic-geometric mean.
It expresses the resulting moment in the factorial normalization used by
the retained nested-series interface.

`groupSum_le` enumerates disjoint nonempty groups by their size profiles.
The binomial and multinomial factors are evaluated in `RouteFixedGroups`.
Stars and bars bounds the profile count, and factorial cancellation leaves
an exponential coefficient. The paper's exact cardinality powers are kept
in `RouteFixedGroups.sum_groupCardinality_le` until the final summation.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole SetPartition Hierarchical

/-! ### Elementary inequalities -/

/-- The maximum of a power times a decreasing exponential.
the display before (A.65) in the proof of Lemma 4.58.
The exponential tangent inequality gives the maximum at `x = p/a`. -/
theorem power_exponential_maximum {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x)
    {p : ℕ} (hp : 0 < p) :
    x ^ p * Real.exp (-(a * x)) ≤ ((p : ℝ) / a) ^ p * Real.exp (-(p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hbase : a * x / p ≤ Real.exp (a * x / p - 1) := by
    simpa only [sub_add_cancel] using Real.add_one_le_exp (a * x / p - 1)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ a * x / p) hbase p
  rw [← Real.exp_nat_mul] at hpow
  have he : (p : ℝ) * (a * x / p - 1) = a * x - p := by field_simp
  rw [he] at hpow
  have hscale : ((p : ℝ) / a) ^ p * (a * x / p) ^ p = x ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc
    _ = (((p : ℝ) / a) ^ p * (a * x / p) ^ p) * Real.exp (-(a * x)) := by rw [hscale]
    _ ≤ (((p : ℝ) / a) ^ p * Real.exp (a * x - p)) * Real.exp (-(a * x)) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 1; congr 1; ring

/-- The maximized logarithmic moment, in the retained factorial normalization.
the display before (A.65) in the proof of Lemma 4.58. -/
theorem pow_two_mul_le_exp {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (m : ℕ) :
    x ^ (2 * m) ≤ (4 / a ^ 2) ^ m * (m.factorial : ℝ) ^ 2 * Real.exp (a * x) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst m
    simpa only [Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one, one_mul] using
      Real.one_le_exp (mul_nonneg ha.le hx)
  have hs : (m : ℝ) ^ m * Real.exp (-(m : ℝ)) ≤ m.factorial := by
    have h := mul_le_mul_of_nonneg_right (pow_self_le_factorial_mul_exp m)
      (Real.exp_pos (-(m : ℝ))).le
    rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h
    exact h
  have hmax := power_exponential_maximum ha hx (show 0 < 2 * m by omega)
  have hE : Real.exp (-((2 * m : ℕ) : ℝ)) = Real.exp (-(m : ℝ)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hscale : (((2 * m : ℕ) : ℝ) / a) ^ (2 * m) * Real.exp (-((2 * m : ℕ) : ℝ)) =
      (4 / a ^ 2) ^ m * ((m : ℝ) ^ m * Real.exp (-(m : ℝ))) ^ 2 := by
    have hbase : ((2 * m : ℕ) : ℝ) / a = (2 / a) * (m : ℝ) := by push_cast; ring
    have hp : (((2 * m : ℕ) : ℝ) / a) ^ (2 * m) =
        (4 / a ^ 2) ^ m * ((m : ℝ) ^ m) ^ 2 := by
      rw [hbase, mul_pow, pow_mul (2 / a) 2 m, div_pow]
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
      rw [← pow_mul (m : ℝ) m 2, mul_comm m 2]
    rw [hp, hE, mul_pow]
    ring
  rw [hscale] at hmax
  have hbound : x ^ (2 * m) * Real.exp (-(a * x)) ≤ (4 / a ^ 2) ^ m * (m.factorial : ℝ) ^ 2 :=
    hmax.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hs 2) (by positivity))
  have h := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (a * x)).le
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  exact h

/-- Weighted Cayley and arithmetic-geometric mean, in the factorial normalization
retained by the nested-series interface. (A.65) and (A.66) in the proof of Lemma 4.58. -/
theorem sum_prod_relTree_le {Q : Finset (Finset ℕ)} (hQ : IsSubpartition Q)
    (𝒯 : Finset (Finset (ℕ × ℕ))) (h𝒯 : 𝒯 ⊆ relTreePairs₀ Q)
    (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) {C : ℝ} (hC : 0 ≤ C)
    (w : ℕ × ℕ → ℝ) (hw0 : ∀ p, 0 ≤ w p)
    (hw : ∀ p ∈ interPairs Q, w p ≤ C * (L p.1 * L p.2)) {a : ℝ} (ha : 0 < a) :
    ∑ T ∈ 𝒯, ∏ p ∈ T, w p ≤
      (4 * C / a ^ 2) ^ (Q.card - 1) * ((Q.card - 1).factorial : ℝ) *
        Real.exp (a * ∑ i ∈ Q.biUnion id, L i) := by
  let q := Q.card
  let m := q - 1
  let S := ∑ i ∈ Q.biUnion id, L i
  have hS : 0 ≤ S := sum_nonneg fun i _ => hL i
  by_cases hq : 2 ≤ q
  · have hqp : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    have hfac : (m.factorial : ℝ) ≤ (q : ℝ) ^ q := by
      calc
        _ ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
        _ ≤ (q : ℝ) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le q 1) _
        _ ≤ _ := pow_le_pow_right₀ hq1 (Nat.sub_le _ _)
    have hscalar : S ^ (2 * q - 2) / (q : ℝ) ^ q ≤
        (4 / a ^ 2) ^ m * (m.factorial : ℝ) * Real.exp (a * S) := by
      have hp := pow_two_mul_le_exp ha hS m
      rw [show 2 * m = 2 * q - 2 by dsimp only [m]; omega] at hp
      rw [div_le_iff₀ (pow_pos hqp _)]
      have hf : (m.factorial : ℝ) ^ 2 ≤ m.factorial * (q : ℝ) ^ q := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg m.factorial)
      calc
        _ ≤ (4 / a ^ 2) ^ m * (m.factorial : ℝ) ^ 2 * Real.exp (a * S) := hp
        _ ≤ (4 / a ^ 2) ^ m * ((m.factorial : ℝ) * (q : ℝ) ^ q) * Real.exp (a * S) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ ∑ T ∈ 𝒯, C ^ m * ∏ p ∈ T, L p.1 * L p.2 := by
        apply sum_le_sum
        intro T hT
        have hc : T.card = m := by
          have := card_add_one_of_mem_relTreePairs₀ hQ (h𝒯 hT)
          dsimp only [m, q]
          omega
        rw [← hc, ← prod_const, ← prod_mul_distrib]
        exact prod_le_prod₀ (fun p _ => hw0 p)
          (fun p hp => hw p (subset_interPairs_of_mem_relTreePairs₀ hQ (h𝒯 hT) hp))
      _ ≤ C ^ m * ∑ T ∈ relTreePairs₀ Q, ∏ p ∈ T, L p.1 * L p.2 := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg h𝒯
          (fun T _ _ => prod_nonneg fun p _ => mul_nonneg (hL _) (hL _))) (pow_nonneg hC _)
      _ ≤ C ^ m * (S ^ (2 * q - 2) / (q : ℝ) ^ q) :=
        mul_le_mul_of_nonneg_left (RouteFixedGroups.relative_weighted_amgm hQ hq L hL) (pow_nonneg hC _)
      _ ≤ C ^ m * ((4 / a ^ 2) ^ m * (m.factorial : ℝ) * Real.exp (a * S)) :=
        mul_le_mul_of_nonneg_left hscalar (pow_nonneg hC _)
      _ = _ := by
        rw [show 4 * C / a ^ 2 = C * (4 / a ^ 2) by ring, mul_pow C (4 / a ^ 2)]
        ring
  · have hT0 : ∀ T ∈ 𝒯, T = ∅ := by
      intro T hT
      have := card_add_one_of_mem_relTreePairs₀ hQ (h𝒯 hT)
      exact card_eq_zero.mp (by dsimp only [q] at hq; omega)
    have hle : (∑ T ∈ 𝒯, ∏ p ∈ T, w p) ≤ 1 := by
      calc
        _ ≤ ∑ T ∈ ({∅} : Finset (Finset (ℕ × ℕ))), ∏ p ∈ T, w p :=
          sum_le_sum_of_subset_of_nonneg (fun T hT => mem_singleton.mpr (hT0 T hT))
            (fun T _ _ => prod_nonneg fun p _ => hw0 p)
        _ = 1 := by simp
    rw [show Q.card - 1 = 0 by dsimp only [q] at hq; omega]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_mul]
    exact hle.trans (Real.one_le_exp (mul_nonneg ha.le hS))

section GroupSum

/-- `∏_s f ≤ ∏_t f` for `s ⊆ t` and real `f ≥ 1`. -/
theorem prod_le_prod_of_subset_of_one_le_real {s t : Finset ℕ} (hst : s ⊆ t) {f : ℕ → ℝ}
    (hf : ∀ i, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← prod_sdiff hst]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := by
    calc (1 : ℝ) = ∏ _i ∈ t \ s, (1 : ℝ) := prod_const_one.symm
      _ ≤ ∏ i ∈ t \ s, f i := prod_le_prod₀ (fun _ _ => zero_le_one) fun i _ => hf i
  exact le_mul_of_one_le_left (prod_nonneg fun i _ => zero_le_one.trans (hf i)) h1

open scoped Classical in
/-- **The group series** of Lemmas 4.54 and 4.55, as a finite sum:
`∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊆ X disjoint} ∏ₗ f(Xₗ)
∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} ∏_{T^b} kb`
(more than `|X|` disjoint groups include an empty one). -/
noncomputable def groupSum (kb : ℕ × ℕ → ℝ) (f : Finset (Finset ℕ) → ℝ) (X : Finset (Finset ℕ)) :
    ℝ :=
  ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      (∏ l, f (Xs l)) * ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), ∏ p ∈ Tb, kb p

variable {X : Finset (Finset ℕ)}

/-- One fixed tuple, with its factorial size weights retained for enumeration.
(4.124) in the proof of Lemma 4.59. -/
theorem groupTerm_factorials_le (hX : IsSubpartition X) (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) {C : ℝ}
    (hC : 0 ≤ C) (kb : ℕ × ℕ → ℝ) (hkb0 : ∀ p, 0 ≤ kb p)
    (hkb : ∀ p ∈ interPairs X, kb p ≤ C * (L p.1 * L p.2)) {a : ℝ} (ha : 0 < a)
    (f : Finset (Finset ℕ) → ℝ) (hf0 : ∀ G, 0 ≤ f G) {A : ℝ} (hA : 1 ≤ A) (E : ℕ → ℝ)
    (hE : ∀ i, 1 ≤ E i)
    (hf : ∀ G ⊆ X, f G ≤ A ^ G.card * (G.card.factorial : ℝ) * ∏ i ∈ G.biUnion id, E i)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (hne : ∀ l, (Xs l).Nonempty) :
    (∏ l, f (Xs l)) * ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), ∏ p ∈ Tb, kb p ≤
      (A * max (4 * C / a ^ 2) 1) ^ X.card *
        (∏ i ∈ X.biUnion id, E i * Real.exp (a * L i)) *
        ((∏ l, ((Xs l).card.factorial : ℝ)) *
          ((X.card - ∑ l, (Xs l).card + n).factorial : ℝ)) := by
  set q := X.card with hq
  set D := max (4 * C / a ^ 2) 1 with hD
  have hD1 : 1 ≤ D := le_max_right _ _
  set G := (Finset.univ : Finset (Fin n)).image Xs with hG
  have hGX : ∀ Y ∈ G, Y ⊆ X := fun Y hY => by
    obtain ⟨l, -, rfl⟩ := mem_image.1 hY
    exact hXs l
  have hGne : ∀ Y ∈ G, Y.Nonempty := fun Y hY => by
    obtain ⟨l, -, rfl⟩ := mem_image.1 hY
    exact hne l
  have hGd : ((G : Finset (Finset (Finset ℕ))) : Set (Finset (Finset ℕ))).PairwiseDisjoint id := by
    intro Y hY Y' hY' hYY'
    obtain ⟨l, -, rfl⟩ := mem_image.1 (mem_coe.1 hY)
    obtain ⟨l', -, rfl⟩ := mem_image.1 (mem_coe.1 hY')
    exact hdisj l l' fun h => hYY' (by rw [h])
  set Y := coarsen X G with hYdef
  have hY : IsSubpartition Y := isSubpartition_coarsen hX hGX hGne hGd
  have hVY : Y.biUnion id = X.biUnion id := biUnion_coarsen hGX
  -- the sizes
  set m : Fin n → ℕ := fun l => (Xs l).card with hm
  have hm1 : ∀ l, 1 ≤ m l := fun l => card_pos.2 (hne l)
  have hsum_m : ∑ l, m l ≤ q := by
    rw [hq, ← card_biUnion fun l _ l' _ h => hdisj l l' h]
    exact card_le_card (biUnion_subset.2 fun l _ => hXs l)
  have hnq : n ≤ ∑ l, m l := by
    calc n = ∑ _l : Fin n, 1 := by simp
      _ ≤ ∑ l, m l := sum_le_sum fun l _ => hm1 l
  have hYcard : Y.card + ∑ l, m l ≤ n + q := SmallIntegral.card_coarsen_add_le Xs hXs hdisj
  -- the tree sum
  have htree := sum_prod_relTree_le hY (relTreePairs₀ Y) (fun _ h => h)
    L hL hC kb hkb0 (fun p hp => hkb p (interPairs_coarsen_subset hGX hp)) ha
  rw [hVY] at htree
  -- the product of the `f`
  have hprodf : ∏ l, f (Xs l) ≤
      (∏ l, A ^ m l) * (∏ l, ((m l).factorial : ℝ)) * ∏ i ∈ X.biUnion id, E i := by
    have hE0 : ∀ i, 0 ≤ E i := fun i => zero_le_one.trans (hE i)
    calc ∏ l, f (Xs l) ≤ ∏ l, (A ^ m l * ((m l).factorial : ℝ) * ∏ i ∈ (Xs l).biUnion id, E i) :=
          prod_le_prod₀ (fun l _ => hf0 _) fun l _ => hf (Xs l) (hXs l)
      _ = (∏ l, A ^ m l) * (∏ l, ((m l).factorial : ℝ)) *
            ∏ l, ∏ i ∈ (Xs l).biUnion id, E i := by
          rw [prod_mul_distrib, prod_mul_distrib]
      _ ≤ (∏ l, A ^ m l) * (∏ l, ((m l).factorial : ℝ)) * ∏ i ∈ X.biUnion id, E i := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← prod_biUnion fun l _ l' _ h => disjoint_biUnion_of_disjoint hX (hXs l) (hXs l')
            (hdisj l l' h)]
          exact prod_le_prod_of_subset_of_one_le_real (biUnion_subset.2 fun l _ =>
            biUnion_subset_biUnion_of_subset_left id (hXs l)) (fun i => hE i)

  have hE0 : ∀ i, 0 ≤ E i := fun i => zero_le_one.trans (hE i)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hApow : ∏ l, A ^ m l ≤ A ^ q := by
    rw [prod_pow_eq_pow_sum]
    exact pow_le_pow_right₀ hA hsum_m
  have hDpow : (4 * C / a ^ 2) ^ (Y.card - 1) ≤ D ^ q :=
    (pow_le_pow_left₀ (by positivity) (le_max_left _ _) _).trans
      (pow_le_pow_right₀ hD1 (by omega))
  have hfac : ((Y.card - 1).factorial : ℝ) ≤ ((q - ∑ l, m l + n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : Y.card - 1 ≤ q - ∑ l, m l + n)
  have hfirst : ∏ l, f (Xs l) ≤
      A ^ q * (∏ l, ((m l).factorial : ℝ)) * ∏ i ∈ X.biUnion id, E i := by
    refine hprodf.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hApow (by positivity))
      (prod_nonneg fun i _ => hE0 i)
  have hsecond : (∑ Tb ∈ relTreePairs₀ Y, ∏ p ∈ Tb, kb p) ≤
      D ^ q * ((q - ∑ l, m l + n).factorial : ℝ) *
        Real.exp (a * ∑ i ∈ X.biUnion id, L i) := by
    refine htree.trans ?_
    gcongr
  calc
    _ ≤ (A ^ q * (∏ l, ((m l).factorial : ℝ)) * ∏ i ∈ X.biUnion id, E i) *
        (D ^ q * ((q - ∑ l, m l + n).factorial : ℝ) *
          Real.exp (a * ∑ i ∈ X.biUnion id, L i)) :=
      mul_le_mul hfirst hsecond (sum_nonneg fun T _ => prod_nonneg fun p _ => hkb0 p)
        (mul_nonneg (by positivity) (prod_nonneg fun i _ => hE0 i))
    _ = _ := by
      rw [prod_mul_distrib, ← Real.exp_sum, ← mul_sum, mul_pow A D]
      ring

open scoped Classical in
/-- **The sum over the groups** ((4.125) in the proof of Lemma 4.59): if `f(∅) = 0` and
`f(G) ≤ A^{|G|} |G|! ∏_{i ∈ V_G} E_i` (`A, E_i ≥ 1`) for `G ⊆ X`, and `0 ≤ kb_{ij} ≤ C L_i L_j` on
`ℰ^inter(X)`, then
`groupSum kb f X ≤ (A D e⁴)^{|X|} |X|! ∏_{i ∈ V_X} E_i e^{a L_i}` with `D = max(4C/a², 1)`. -/
theorem groupSum_le (hX : IsSubpartition X) (L : ℕ → ℝ) (hL : ∀ i, 0 ≤ L i) {C : ℝ}
    (hC : 0 ≤ C) (kb : ℕ × ℕ → ℝ) (hkb0 : ∀ p, 0 ≤ kb p)
    (hkb : ∀ p ∈ interPairs X, kb p ≤ C * (L p.1 * L p.2)) {a : ℝ} (ha : 0 < a)
    (f : Finset (Finset ℕ) → ℝ) (hf0 : ∀ G, 0 ≤ f G) (hfe : f ∅ = 0) {A : ℝ} (hA : 1 ≤ A)
    (E : ℕ → ℝ) (hE : ∀ i, 1 ≤ E i)
    (hf : ∀ G ⊆ X, f G ≤ A ^ G.card * (G.card.factorial : ℝ) * ∏ i ∈ G.biUnion id, E i) :
    groupSum kb f X ≤ (A * max (4 * C / a ^ 2) 1 * Real.exp 4) ^ X.card *
      (X.card.factorial : ℝ) * ∏ i ∈ X.biUnion id, (E i * Real.exp (a * L i)) := by
  let q := X.card
  let D := max (4 * C / a ^ 2) 1
  let P := ∏ i ∈ X.biUnion id, E i * Real.exp (a * L i)
  let K := (A * D) ^ q * P
  have hD : 1 ≤ D := le_max_right _ _
  have hP : 0 ≤ P := prod_nonneg fun i _ => mul_nonneg (zero_le_one.trans (hE i)) (Real.exp_pos _).le
  have hK : 0 ≤ K := mul_nonneg (pow_nonneg (mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hD)) _) hP
  let F {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) :=
    (∏ l, f (Xs l)) * ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), ∏ p ∈ Tb, kb p
  let domain (n : ℕ) := (Fintype.piFinset fun _ : Fin n => X.powerset).filter
    (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))
  have heq (n : ℕ) : (∑ Xs ∈ domain n, F Xs) =
      ∑ Xs ∈ RouteFixedGroups.nonemptyGroups X n, F Xs := by
    symm
    apply sum_subset
    · intro Xs hXs
      obtain ⟨hs, hd, _⟩ := RouteFixedGroups.mem_nonemptyGroups.mp hXs
      exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun l => mem_powerset.mpr (hs l)), hd⟩
    · intro Xs hXs hnot
      have hs : ∀ l, Xs l ⊆ X := fun l =>
        mem_powerset.mp (Fintype.mem_piFinset.mp (mem_filter.mp hXs).1 l)
      have hn : ¬ ∀ l, (Xs l).Nonempty := fun hn => hnot
        (RouteFixedGroups.mem_nonemptyGroups.mpr ⟨hs, (mem_filter.mp hXs).2, hn⟩)
      obtain ⟨l, hl⟩ := not_forall.mp hn
      have hzero : ∏ l', f (Xs l') = 0 := prod_eq_zero (mem_univ l) (by
        rw [not_nonempty_iff_eq_empty.mp hl, hfe])
      dsimp only [F]
      rw [hzero, zero_mul]
  have hn : ∀ n ∈ range (q + 1), 1 / (n.factorial : ℝ) * ∑ Xs ∈ domain n, F Xs ≤
      K * (1 / (n.factorial : ℝ) * ∑ Xs ∈ RouteFixedGroups.nonemptyGroups X n,
        (∏ l, ((Xs l).card.factorial : ℝ)) * ((q - ∑ l, (Xs l).card + n).factorial : ℝ)) := by
    intro n _
    rw [heq, mul_left_comm K]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_sum]
    apply sum_le_sum
    intro Xs hXs
    obtain ⟨hs, hd, hn⟩ := RouteFixedGroups.mem_nonemptyGroups.mp hXs
    exact groupTerm_factorials_le hX L hL hC kb hkb0 hkb ha f hf0 hA E hE hf Xs hs hd hn
  change (∑ n ∈ range (q + 1), 1 / (n.factorial : ℝ) * ∑ Xs ∈ domain n, F Xs) ≤ _
  refine (sum_le_sum hn).trans ?_
  rw [← mul_sum]
  have hcount := RouteFixedGroups.sum_groups_factorials_le X
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ ≤ K * ((16 : ℝ) ^ q * q.factorial) := mul_le_mul_of_nonneg_left hcount hK
    _ ≤ K * (Real.exp 4 ^ q * q.factorial) := by gcongr
    _ = _ := by
      change (A * D) ^ q * P * (Real.exp 4 ^ q * q.factorial) =
        (A * D * Real.exp 4) ^ q * (q.factorial : ℝ) * P
      rw [mul_pow (A * D) (Real.exp 4)]
      ring

end GroupSum

end AbsoluteLower

end MultipoleBKT

end
