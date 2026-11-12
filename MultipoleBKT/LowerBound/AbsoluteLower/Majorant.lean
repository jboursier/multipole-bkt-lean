/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Pairs

/-!
# The majorant `𝓛_{C₁}` (display (4.90)) and the block factor `𝒰` of Lemma 4.54

The majorant (4.90) and the factor `𝒰(X')` in Step 1 of the proof of Lemma 4.54.

Configurations are configurations `c : ℕ → ℂ × ℂ` of all labels (as in
`MultipoleBKT.Hierarchical.clusterTerm`), and edge sets are sets of pairs `(i, j)`, `i < j`.
The weights are `a^abs_ij = MultipoleBKT.Parity.absOddWeight M λ ε₀ R (c i) (c j)` and
`b^abs_ij = MultipoleBKT.Parity.absEvenWeight M λ ε₀ R (c i) (c j)` (Definition 4.29), with `R`
standing for the truncation scale `R̄_{β,λ}`.

* `eulerMajorant M λ ε₀ R C₁ X' c = 𝓛_{C₁}(X')`: `0` for `|X'| ≤ 1` and otherwise the series
  of (4.90) over the groups `X'₁, …, X'ₖ`, the connected Eulerian edge sets `Eₗ ∈ Eulc^{X'ₗ}` and
  the trees `T̃ ∈ 𝖳_0^{Coarse_{X'}(X'₁, …, X'ₖ)}`;
* `oddEvenSum β w M λ X' c = 𝒰(X')`: the sum over `E₁ ∈ Eul^{X'}` and `E₂` with
  `E₁ ∩ E₂ = ∅`, `E₁ ∪ E₂ ∈ 𝖤^{X'}` of `∏_{E₁} a^w ∏_{E₂} b^w ∏_{ℰ^inter(X')} 𝟙_{𝓑^c}`.

Results:

* `groupSeries_eq_sum`: the series over ordered disjoint groups is the finite sum over the sets
  `𝒱` of disjoint groups of at least two blocks (`disjointFamilies`);
* `eulerMajorant_eq_sum`, `eulerMajorant_nonneg`, and `eulerMajorant_eq_zero_of_linked`
  (`𝓛_{C₁}(X') = 0` off `⋂_{ij ∈ ℰ^inter(X')} 𝓑_ij^c`);
* `absOddWeight_le_one` (`a^abs ≤ 1` for `M ≥ 1`, `λ > 0`), `absEvenWeight_le_two`,
  measurability of the weights, and `measurable_eulerMajorant`, `boundedOn_eulerMajorant`;
* `exists_eq_empty_of_card_lt`: more than `|X|` disjoint subfamilies of `X` include an empty one
  (the series of Section 4 have finitely many nonzero terms), `summable_and_tsum_eq_of_vanish`, and
  `sum_card_biUnion_le` (`∑ₗ |V_{Xₗ}| ≤ |V_X|` for disjoint groups).
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity

/-! ### Disjoint tuples of groups -/

section Tuples

/-- More than `|X|` pairwise disjoint subfamilies of `X` include an empty one. -/
theorem exists_eq_empty_of_card_lt {X : Finset (Finset ℕ)} {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (hn : X.card < n) : ∃ l, Xs l = ∅ := by
  by_contra h
  have hne : ∀ l, (Xs l).Nonempty := fun l => nonempty_iff_ne_empty.2 fun h' => h ⟨l, h'⟩
  choose f hf using hne
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne'
    exact disjoint_left.1 (hdisj i j hne') (hf i) (hij ▸ hf j)
  have : n ≤ X.card := by
    have := card_le_card_of_injOn f (s := (univ : Finset (Fin n))) (t := X)
      (fun l _ => hXs l (hf l)) (hinj.injOn)
    simpa using this
  omega

/-- The block sizes of disjoint groups of `X` add up to at most `|V_X|`. -/
theorem sum_card_biUnion_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :
    ∑ l, ((Xs l).biUnion id).card ≤ (X.biUnion id).card := by
  rw [← card_biUnion fun i _ j _ hij =>
    disjoint_biUnion_of_disjoint hX (hXs i) (hXs j) (hdisj i j hij)]
  exact card_le_card (biUnion_subset.2 fun l _ => biUnion_subset_biUnion_of_subset_left id (hXs l))

/-- A sequence vanishing beyond `K` is summable, with sum its partial sum up to `K`. -/
theorem summable_and_tsum_eq_of_vanish {f : ℕ → ℝ} {K : ℕ} (hf : ∀ n, K < n → f n = 0) :
    Summable f ∧ ∑' n, f n = ∑ n ∈ range (K + 1), f n := by
  have h : ∀ n ∉ range (K + 1), f n = 0 := fun n hn => hf n (by
    rw [mem_range] at hn
    omega)
  exact ⟨summable_of_ne_finset_zero h, tsum_eq_sum h⟩

end Tuples

/-! ### The series over groups -/

section Series

open scoped Classical

variable (C₁ : ℝ) (a b : ℕ × ℕ → ℝ)

/-- The weight `∑_{E ∈ Eulc^Y} ∏_{ij ∈ E} C₁ a_ij` of one group. -/
noncomputable def eulerGroupSum (Y : Finset (Finset ℕ)) : ℝ :=
  ∑ E ∈ relEulerianConnectedPairs Y, ∏ p ∈ E, C₁ * a p

/-- The series of display (4.90) without the common factor
`∏_{ij ∈ ℰ^inter(X')} e^{C₁ a^abs_ij} 𝟙_{𝓑_ij^c}`, for abstract weights `a`, `b`. -/
noncomputable def groupSeries (X' : Finset (Finset ℕ)) : ℝ :=
  ∑' k : ℕ, 1 / (k.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => X'.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
        ∑ T ∈ relTreePairs₀ (coarsen X' (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, C₁ * a p) * ∏ p ∈ T, b p

variable {C₁ a b}

theorem relEulerianConnectedPairs_eq_empty_of_card_le_one {Y : Finset (Finset ℕ)}
    (h : Y.card ≤ 1) : relEulerianConnectedPairs Y = ∅ := by
  rw [relEulerianConnectedPairs, relEdgeSets_eq_empty_of_card_le_one h, empty_inter]

theorem subset_interPairs_of_mem_relEulerianConnectedPairs {Y : Finset (Finset ℕ)}
    {E : Finset (ℕ × ℕ)} (hE : E ∈ relEulerianConnectedPairs Y) : E ⊆ interPairs Y :=
  (mem_relEdgeSets.1 (mem_relEulerianConnectedPairs.1 hE).1).1

/-- One term of the series: for disjoint groups, the sum over the `Eₗ` factorizes. -/
theorem sum_groupTerm_eq {X' : Finset (Finset ℕ)} (hX' : IsSubpartition X') {k : ℕ}
    {Xs : Fin k → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X')
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :
    ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
        ∑ T ∈ relTreePairs₀ (coarsen X' (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, C₁ * a p) * ∏ p ∈ T, b p =
      (∏ l, eulerGroupSum C₁ a (Xs l)) *
        ∑ T ∈ relTreePairs₀ (coarsen X' (Finset.univ.image Xs)), ∏ p ∈ T, b p := by
  have hE : ∀ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
      ∏ p ∈ Finset.univ.biUnion Es, C₁ * a p = ∏ l, ∏ p ∈ Es l, C₁ * a p := by
    intro Es hEs
    refine prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX' hXs hdisj fun l => ?_)
    exact subset_interPairs_of_mem_relEulerianConnectedPairs (Fintype.mem_piFinset.1 hEs l)
  rw [sum_congr rfl fun Es hEs => by rw [← mul_sum, hE Es hEs], ← sum_mul]
  congr 1
  exact (prod_univ_sum (fun l => relEulerianConnectedPairs (Xs l))
    (fun _ E => ∏ p ∈ E, C₁ * a p)).symm

/-- **The series over ordered groups is a finite sum over sets of groups**: for a subpartition
`X'`, `groupSeries C₁ a b X' = ∑_{𝒱} (∏_{Y ∈ 𝒱} ∑_{E ∈ Eulc^Y} ∏_E C₁ a)
∑_{T ∈ 𝖳_0^{Coarse_{X'}(𝒱)}} ∏_T b`, the sum over the sets `𝒱` of pairwise disjoint groups
`Y ⊆ X'` with `|Y| ≥ 2`. -/
theorem groupSeries_eq_sum {X' : Finset (Finset ℕ)} (hX' : IsSubpartition X') :
    groupSeries C₁ a b X' =
      ∑ 𝒱 ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱, eulerGroupSum C₁ a Y) *
          ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱), ∏ p ∈ T, b p := by
  set P : Finset (Finset ℕ) → Prop := fun Y => 2 ≤ Y.card with hPdef
  have hPne : ∀ Y, P Y → Y.Nonempty := fun Y h => card_pos.1 (by simp only [hPdef] at h; omega)
  set H : Finset (Finset (Finset ℕ)) → ℝ := fun 𝒱 =>
    (∏ Y ∈ 𝒱, eulerGroupSum C₁ a Y) * ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱), ∏ p ∈ T, b p with hH
  have hterm : ∀ k : ℕ,
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => X'.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
          ∑ T ∈ relTreePairs₀ (coarsen X' (Finset.univ.image Xs)),
            (∏ p ∈ Finset.univ.biUnion Es, C₁ * a p) * ∏ p ∈ T, b p =
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => X'.powerset).filter
          (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, P (Xs i)),
          H (Finset.univ.image Xs) := by
    intro k
    have hsub : ∀ Xs ∈ (Fintype.piFinset fun _ : Fin k => X'.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)), ∀ l, Xs l ⊆ X' := fun Xs hXs l =>
      mem_powerset.1 (Fintype.mem_piFinset.1 (mem_filter.1 hXs).1 l)
    rw [sum_congr rfl fun Xs hXs => sum_groupTerm_eq hX' (hsub Xs hXs) (mem_filter.1 hXs).2]
    rw [← filter_filter]
    refine (sum_filter_of_ne fun Xs _ hne => fun i => ?_).symm.trans
      (sum_congr rfl fun Xs hXs => ?_)
    · by_contra hlt
      refine hne ?_
      rw [prod_eq_zero (mem_univ i), zero_mul]
      rw [eulerGroupSum, relEulerianConnectedPairs_eq_empty_of_card_le_one
        (by simp only [hPdef] at hlt; omega), sum_empty]
    · rw [mem_filter, mem_filter] at hXs
      have hinj := injective_of_disjoint hXs.1.2 fun i => hPne _ (hXs.2 i)
      rw [hH]
      simp only
      rw [prod_image fun i _ j _ h => hinj h]
  have key := tsum_tuples_image_eq_sum X'.powerset P hPne H
  rw [biUnion_powerset_id] at key
  rw [groupSeries]
  simp_rw [hterm]
  calc _ = ∑ 𝒱 ∈ (disjointFamilies X' P).filter (· ⊆ X'.powerset), H 𝒱 := by
        convert key using 7
    _ = _ := by
        refine sum_congr ?_ fun _ _ => rfl
        exact filter_true_of_mem fun 𝒱 h𝒱 Y hY =>
          mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)

theorem eulerGroupSum_nonneg (hC₁ : 0 ≤ C₁) (ha : ∀ p, 0 ≤ a p) (Y : Finset (Finset ℕ)) :
    0 ≤ eulerGroupSum C₁ a Y :=
  sum_nonneg fun _ _ => prod_nonneg fun p _ => mul_nonneg hC₁ (ha p)

theorem groupSeries_nonneg (hC₁ : 0 ≤ C₁) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (X' : Finset (Finset ℕ)) : 0 ≤ groupSeries C₁ a b X' :=
  tsum_nonneg fun _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
    sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun p _ => mul_nonneg hC₁ (ha p))
      (prod_nonneg fun p _ => hb p))

end Series

/-! ### The majorant `𝓛_{C₁}` -/

section Majorant

open scoped Classical

variable (M lam ε₀ R C₁ : ℝ)

/-- **The majorant `𝓛_{C₁}(X')`** (display (4.90), (4.89)): `0` for
`|X'| ≤ 1` and, for `|X'| ≥ 2`,
`∑_{k ≥ 0} (1/k!) ∑_{X'₁, …, X'ₖ ⊂ X' disjoint} ∑_{E₁ ∈ Eulc^{X'₁}} ⋯ ∑_{Eₖ ∈ Eulc^{X'ₖ}}
∑_{T̃ ∈ 𝖳_0^{Coarse_{X'}(X'₁, …, X'ₖ)}} ∏_{ij ∈ E₁ ∪ ⋯ ∪ Eₖ} (C₁ a^abs_ij) ∏_{ij ∈ T̃} b^abs_ij
∏_{ij ∈ ℰ^inter(X')} e^{C₁ a^abs_ij} 𝟙_{𝓑_ij^c}`, at the configuration `c` of all labels, with
`R` in the role of `R̄_{β,λ}`. -/
noncomputable def eulerMajorant (X' : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  if X'.card ≤ 1 then 0 else
    ∑' k : ℕ, 1 / (k.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => X'.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
          ∑ T ∈ relTreePairs₀ (coarsen X' (Finset.univ.image Xs)),
            (∏ p ∈ Finset.univ.biUnion Es, C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
              (∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) *
              ∏ p ∈ interPairs X', Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
                (if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1)

/-- The common factor `∏_{ij ∈ ℰ^inter(X')} e^{C₁ a^abs_ij} 𝟙_{𝓑_ij^c}` of (4.90). -/
noncomputable def expUnlinked (X' : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∏ p ∈ interPairs X', Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
    (if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1)

variable {M lam ε₀ R C₁}

theorem expUnlinked_nonneg (X' : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ expUnlinked M lam ε₀ R C₁ X' c :=
  prod_nonneg fun _ _ => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num)

/-- `𝓛_{C₁}(X') = groupSeries · ∏_{ℰ^inter(X')} e^{C₁ a^abs} 𝟙_{𝓑^c}` for `|X'| ≥ 2`. -/
theorem eulerMajorant_eq_groupSeries {X' : Finset (Finset ℕ)} (h2 : 2 ≤ X'.card)
    (c : ℕ → ℂ × ℂ) :
    eulerMajorant M lam ε₀ R C₁ X' c =
      groupSeries C₁ (fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2))
          (fun p => absEvenWeight M lam ε₀ R (c p.1) (c p.2)) X' *
        expUnlinked M lam ε₀ R C₁ X' c := by
  rw [eulerMajorant, ite_eq_right (by omega), groupSeries, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [mul_assoc, sum_mul]
  congr 1
  refine sum_congr rfl fun Xs _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun Es _ => ?_
  rw [sum_mul]
  rfl

theorem eulerMajorant_eq_zero_of_card_le_one {X' : Finset (Finset ℕ)} (h : X'.card ≤ 1)
    (c : ℕ → ℂ × ℂ) : eulerMajorant M lam ε₀ R C₁ X' c = 0 := by
  rw [eulerMajorant, ite_eq_left h]

/-- **The finite form of `𝓛_{C₁}(X')`**: for a subpartition `X'` with `|X'| ≥ 2`,
`𝓛_{C₁}(X') = ∑_{𝒱} (∏_{Y ∈ 𝒱} ∑_{E ∈ Eulc^Y} ∏_E C₁ a^abs) ∑_{T ∈ 𝖳_0^{Coarse_{X'}(𝒱)}} ∏_T b^abs
· ∏_{ℰ^inter(X')} e^{C₁ a^abs} 𝟙_{𝓑^c}` over the sets `𝒱` of disjoint groups of at least two
blocks. -/
theorem eulerMajorant_eq_sum {X' : Finset (Finset ℕ)} (hX' : IsSubpartition X')
    (h2 : 2 ≤ X'.card) (c : ℕ → ℂ × ℂ) :
    eulerMajorant M lam ε₀ R C₁ X' c =
      (∑ 𝒱 ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱, eulerGroupSum C₁ (fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2)) Y) *
          ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱), ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) *
        expUnlinked M lam ε₀ R C₁ X' c := by
  rw [eulerMajorant_eq_groupSeries h2, groupSeries_eq_sum hX']

/-- `𝓛_{C₁}(X') = 0` off the event `⋂_{ij ∈ ℰ^inter(X')} 𝓑_ij^c` (the first line of the proof of
proof of Lemma 4.55). -/
theorem eulerMajorant_eq_zero_of_linked {X' : Finset (Finset ℕ)} {c : ℕ → ℂ × ℂ}
    (h : ∃ p ∈ interPairs X', MultipoleLinked M lam (c p.1) (c p.2)) :
    eulerMajorant M lam ε₀ R C₁ X' c = 0 := by
  by_cases h1 : X'.card ≤ 1
  · exact eulerMajorant_eq_zero_of_card_le_one h1 c
  obtain ⟨p, hp, hl⟩ := h
  rw [eulerMajorant_eq_groupSeries (by omega), expUnlinked,
    prod_eq_zero (f := fun p => Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
      (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)) hp
      (by rw [ite_eq_left hl, mul_zero]), mul_zero]

theorem eulerMajorant_nonneg (hC₁ : 0 ≤ C₁) (X' : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ eulerMajorant M lam ε₀ R C₁ X' c := by
  by_cases h : X'.card ≤ 1
  · rw [eulerMajorant_eq_zero_of_card_le_one h]
  · rw [eulerMajorant_eq_groupSeries (by omega)]
    exact mul_nonneg (groupSeries_nonneg hC₁ (fun _ => absOddWeight_nonneg _ _ _ _ _ _)
      (fun _ => absEvenWeight_nonneg _ _ _ _ _ _) X') (expUnlinked_nonneg X' c)

end Majorant

/-! ### The factor `𝒰` -/

section Factor

open scoped Classical

/-- **The factor `𝒰(X')`** (Step 1 of the proof of Lemma 4.54):
`∑_{E₁ ∈ Eul^{X'}} ∑_{E₂ : E₁ ∪ E₂ ∈ 𝖤^{X'}, E₁ ∩ E₂ = ∅} ∏_{ij ∈ E₁} a^w_ij ∏_{ij ∈ E₂} b^w_ij
∏_{ij ∈ ℰ^inter(X')} 𝟙_{𝓑_ij^c}`, at the configuration `c` of all labels. It is `0` for
`|X'| ≤ 1` (`oddEvenSum_eq_zero_of_card_le_one`). -/
noncomputable def oddEvenSum (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ)
    (X' : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ E₁ ∈ relEulerianPairs X', ∑ E₂ ∈ (interPairs X').powerset.filter
      (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X'),
    (∏ p ∈ E₁, oddBond β w (c p.1) (c p.2)) * (∏ p ∈ E₂, evenBond β w (c p.1) (c p.2)) *
      ∏ p ∈ interPairs X', (if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1)

theorem oddEvenSum_eq_zero_of_card_le_one {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ}
    {X' : Finset (Finset ℕ)} (h : X'.card ≤ 1) (c : ℕ → ℂ × ℂ) :
    oddEvenSum β w M lam X' c = 0 := by
  refine sum_eq_zero fun E₁ _ => ?_
  rw [filter_false_of_mem fun E₂ _ hE => by
    rw [relEdgeSets_eq_empty_of_card_le_one h] at hE
    exact absurd hE.2 (notMem_empty _), sum_empty]

end Factor

/-! ### Bounds and measurability of the weights -/

section Weights

variable {M lam ε₀ R : ℝ}

theorem absOddWeight_comm (d e : ℂ × ℂ) :
    absOddWeight M lam ε₀ R d e = absOddWeight M lam ε₀ R e d := by
  classical
  unfold absOddWeight
  rw [dipoleDist_comm e d, max_comm ‖e.1 - e.2‖, mul_comm ‖e.1 - e.2‖,
    if_congr (multipoleLinked_comm (d := e) (e := d)) rfl rfl]

theorem absEvenWeight_comm (d e : ℂ × ℂ) :
    absEvenWeight M lam ε₀ R d e = absEvenWeight M lam ε₀ R e d := by
  classical
  unfold absEvenWeight
  rw [absOddWeight_comm, if_congr (multipoleLinked_comm (d := e) (e := d)) rfl rfl]

/-- `a^abs_ij ≤ 1` (for `M ≥ 1`, `λ > 0`): on `𝓑_ij^c`, `d_ij ≥ min(r_i, r_j)` and `d_ij > 0`. -/
theorem absOddWeight_le_one (hM : 1 ≤ M) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    absOddWeight M lam ε₀ R d e ≤ 1 := by
  classical
  by_cases h : MultipoleLinked M lam d e
  · unfold absOddWeight
    rw [ite_eq_left h]
    simp
  set r₁ := ‖d.1 - d.2‖
  set r₂ := ‖e.1 - e.2‖
  set D := dipoleDist d e
  have hDlt : M * min (max r₁ lam) (max r₂ lam) < D := not_le.1 h
  have hmin0 : lam ≤ min (max r₁ lam) (max r₂ lam) := le_min (le_max_right _ _) (le_max_right _ _)
  have hMmin : min (max r₁ lam) (max r₂ lam) ≤ M * min (max r₁ lam) (max r₂ lam) :=
    le_mul_of_one_le_left (hlam.le.trans hmin0) hM
  have hDpos : 0 < D := (lt_of_lt_of_le hlam (hmin0.trans hMmin)).trans hDlt
  have hminD : min r₁ r₂ ≤ D :=
    ((min_le_min (le_max_left _ _) (le_max_left _ _)).trans hMmin).trans hDlt.le
  set m := max D (max r₁ r₂)
  have hmpos : 0 < m := lt_of_lt_of_le hDpos (le_max_left _ _)
  have hrr : r₁ * r₂ ≤ D * m := by
    rw [← min_mul_max]
    exact mul_le_mul hminD (le_max_right _ _) (by positivity) hDpos.le
  have hA1 : r₁ * r₂ / (D * m) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hrr
  unfold absOddWeight
  rw [ite_eq_right h, mul_one]
  split_ifs
  · rw [mul_one]; exact hA1
  · rw [mul_zero]; exact zero_le_one

theorem absEvenWeight_le_two (hM : 1 ≤ M) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    absEvenWeight M lam ε₀ R d e ≤ 2 := by
  classical
  unfold absEvenWeight
  have h1 := absOddWeight_le_one (ε₀ := ε₀) (R := R) hM hlam d e
  have h0 := absOddWeight_nonneg M lam ε₀ R d e
  have : (if MultipoleLinked M lam d e then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  nlinarith

/-- On `𝓑_ij^c`, `b^abs_ij = (a^abs_ij)² ≤ a^abs_ij`. -/
theorem absEvenWeight_le_absOddWeight (hM : 1 ≤ M) (hlam : 0 < lam) {d e : ℂ × ℂ}
    (h : ¬ MultipoleLinked M lam d e) :
    absEvenWeight M lam ε₀ R d e ≤ absOddWeight M lam ε₀ R d e := by
  classical
  unfold absEvenWeight
  rw [ite_eq_right h, add_zero]
  have h1 := absOddWeight_le_one (ε₀ := ε₀) (R := R) hM hlam d e
  have h0 := absOddWeight_nonneg M lam ε₀ R d e
  nlinarith

open scoped Classical in
/-- `𝟙_{𝓑_ij} ≤ b^abs_ij`. -/
theorem linkedIndicator_le_absEvenWeight (d e : ℂ × ℂ) :
    (if MultipoleLinked M lam d e then (1 : ℝ) else 0) ≤ absEvenWeight M lam ε₀ R d e := by
  classical
  unfold absEvenWeight
  have := sq_nonneg (absOddWeight M lam ε₀ R d e)
  linarith

theorem measurable_dipoleDist : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => dipoleDist q.1 q.2 := by
  unfold dipoleDist
  fun_prop

theorem measurable_absOddWeight (M lam ε₀ R : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => absOddWeight M lam ε₀ R q.1 q.2 := by
  classical
  unfold absOddWeight
  refine ((Measurable.div (by fun_prop) (measurable_dipoleDist.mul
    (measurable_dipoleDist.max (by fun_prop)))).mul ?_).mul ?_
  · exact Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const
  · exact Measurable.ite (measurableSet_le measurable_dipoleDist measurable_const)
      measurable_const measurable_const

theorem measurable_absEvenWeight (M lam ε₀ R : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => absEvenWeight M lam ε₀ R q.1 q.2 := by
  classical
  unfold absEvenWeight
  exact ((measurable_absOddWeight M lam ε₀ R).pow_const 2).add
    (Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const)

end Weights

/-! ### Measurability and boundedness of `𝓛_{C₁}` -/

section Measurability

open scoped Classical

variable {M lam ε₀ R C₁ : ℝ}

theorem measurable_prod_pairWeight {s : Finset (ℕ × ℕ)} {g : ℂ × ℂ → ℂ × ℂ → ℝ}
    (hg : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => g q.1 q.2) (C : ℝ) :
    Measurable fun c : ℕ → ℂ × ℂ => ∏ p ∈ s, C * g (c p.1) (c p.2) :=
  Finset.measurable_prod _ fun p _ => (measurable_pairWeight hg p).const_mul C

theorem measurable_expUnlinked (X' : Finset (Finset ℕ)) :
    Measurable (expUnlinked M lam ε₀ R C₁ X') := by
  unfold expUnlinked
  refine Finset.measurable_prod _ fun p _ => ?_
  exact (((measurable_pairWeight (measurable_absOddWeight M lam ε₀ R) p).const_mul C₁).exp).mul
    (measurable_pairWeight (φ := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
      (measurable_unlinkedIndicator M lam) p)

/-- `𝓛_{C₁}(X')` is a measurable function of the configuration. -/
theorem measurable_eulerMajorant {X' : Finset (Finset ℕ)} (hX' : IsSubpartition X') :
    Measurable (eulerMajorant M lam ε₀ R C₁ X') := by
  by_cases h : X'.card ≤ 1
  · have : eulerMajorant M lam ε₀ R C₁ X' = fun _ => 0 :=
      funext fun c => eulerMajorant_eq_zero_of_card_le_one h c
    rw [this]
    exact measurable_const
  · have : eulerMajorant M lam ε₀ R C₁ X' = fun c =>
        (∑ 𝒱 ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
          (∏ Y ∈ 𝒱, eulerGroupSum C₁ (fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2)) Y) *
            ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱),
              ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) *
          expUnlinked M lam ε₀ R C₁ X' c :=
      funext fun c => eulerMajorant_eq_sum hX' (by omega) c
    rw [this]
    refine (Finset.measurable_sum _ fun 𝒱 _ => ?_).mul (measurable_expUnlinked X')
    refine (Finset.measurable_prod _ fun Y _ => ?_).mul
      (Finset.measurable_sum _ fun T _ => ?_)
    · exact Finset.measurable_sum _ fun E _ =>
        measurable_prod_pairWeight (measurable_absOddWeight M lam ε₀ R) C₁
    · exact Finset.measurable_prod _ fun p _ =>
        measurable_pairWeight (measurable_absEvenWeight M lam ε₀ R) p

/-- `𝓛_{C₁}(X')` is bounded (for `M ≥ 1`, `λ > 0`). -/
theorem boundedOn_eulerMajorant (hM : 1 ≤ M) (hlam : 0 < lam) {X' : Finset (Finset ℕ)}
    (hX' : IsSubpartition X') (K : Set (ℂ × ℂ)) :
    BoundedOn K (eulerMajorant M lam ε₀ R C₁ X') := by
  have ha : ∃ B, ∀ d ∈ K, ∀ e ∈ K, |absOddWeight M lam ε₀ R d e| ≤ B :=
    ⟨1, fun d _ e _ => by
      rw [abs_of_nonneg (absOddWeight_nonneg _ _ _ _ _ _)]
      exact absOddWeight_le_one hM hlam d e⟩
  have hb : ∃ B, ∀ d ∈ K, ∀ e ∈ K, |absEvenWeight M lam ε₀ R d e| ≤ B :=
    ⟨2, fun d _ e _ => by
      rw [abs_of_nonneg (absEvenWeight_nonneg _ _ _ _ _ _)]
      exact absEvenWeight_le_two hM hlam d e⟩
  by_cases h : X'.card ≤ 1
  · have : eulerMajorant M lam ε₀ R C₁ X' = fun _ => 0 :=
      funext fun c => eulerMajorant_eq_zero_of_card_le_one h c
    rw [this]
    exact BoundedOn.const K 0
  · have : eulerMajorant M lam ε₀ R C₁ X' = fun c =>
        (∑ 𝒱 ∈ disjointFamilies X' (fun Y => 2 ≤ Y.card),
          (∏ Y ∈ 𝒱, eulerGroupSum C₁ (fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2)) Y) *
            ∑ T ∈ relTreePairs₀ (coarsen X' 𝒱),
              ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) *
          expUnlinked M lam ε₀ R C₁ X' c :=
      funext fun c => eulerMajorant_eq_sum hX' (by omega) c
    rw [this]
    refine (BoundedOn.sum _ fun 𝒱 _ => ?_).mul ?_
    · refine (BoundedOn.prod _ fun Y _ => ?_).mul (BoundedOn.sum _ fun T _ => ?_)
      · exact BoundedOn.sum _ fun E _ => BoundedOn.prod _ fun p _ =>
          (BoundedOn.const K C₁).mul (BoundedOn.pair ha p.1 p.2)
      · exact BoundedOn.prod _ fun p _ => BoundedOn.pair hb p.1 p.2
    · refine BoundedOn.prod _ fun p _ => ?_
      refine ⟨Real.exp |C₁|, fun c _ => ?_⟩
      have h0 := absOddWeight_nonneg M lam ε₀ R (c p.1) (c p.2)
      have h1 := absOddWeight_le_one (ε₀ := ε₀) (R := R) hM hlam (c p.1) (c p.2)
      rw [abs_mul, Real.abs_exp]
      have hi : |(if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)| ≤ 1 := by
        split_ifs <;> norm_num
      calc Real.exp (C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
            |(if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)|
          ≤ Real.exp |C₁| * 1 := by
            refine mul_le_mul (Real.exp_le_exp.2 ?_) hi (abs_nonneg _) (Real.exp_pos _).le
            calc C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)
                ≤ |C₁ * absOddWeight M lam ε₀ R (c p.1) (c p.2)| := le_abs_self _
              _ = |C₁| * absOddWeight M lam ε₀ R (c p.1) (c p.2) := by
                  rw [abs_mul, abs_of_nonneg h0]
              _ ≤ |C₁| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
              _ = |C₁| := mul_one _
        _ = Real.exp |C₁| := mul_one _

end Measurability

end AbsoluteLower

end MultipoleBKT

end
