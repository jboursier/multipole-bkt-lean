/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.EulerGroup
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Lemma 4.55: summing over Eulerian graphs

Lemma 4.55, equations (4.96)–(4.97).

`eulerTreeMajorant` is the majorant `H_X` in (4.97).
`lemma_4_55_route` follows the written proof: each group is bounded using
`eulerGroupSum_route_le`, including its reattachment multiplicity, then the
logarithmic factors already present in the groups are multiplied over `V_X`.
`prod_prod_log_le` supplies this last comparison for disjoint groups.


-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity Peeling

section Def

open scoped Classical

variable (M lam ε₀ R C₁ : ℝ) (X : Finset (Finset ℕ))

/-- **The majorant `H_X(X₁, …, Xₙ)`** ((4.97), Lemma 4.55), at the
configuration `c`, with `R` in the role of `R̄_{β,λ}`:
`∏ₗ (∏_{S ∈ Xₗ, S ≠ Ŝₗ} r_S² ∑_{Tₗ^a ∈ 𝖳^{Xₗ}} ∏_{ij ∈ Tₗ^a} d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c})
(∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} ∏_{ij ∈ T^b} b^abs_ij) ∏_{i ∈ V_X} (1 + log_M(17 ε₀ R̄/r_i))²
exp(2 C₁ ∑_{ij ∈ ℰ^inter(X)} a^abs_ij) ∏_{i ∈ V_X} (1 + ∑_{j ∈ V_X, j ≠ i} ḡ_ij)`. -/
noncomputable def eulerTreeMajorant {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ l, prodExceptMax c (Xs l) * ∑ T ∈ relTreePairs (Xs l), ∏ p ∈ T, keptPair M lam ε₀ R c p) *
    (∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
      ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) *
    (∏ i ∈ X.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2) *
    Real.exp (2 * C₁ * ∑ p ∈ interPairs X, absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
    ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j)

variable {M lam ε₀ R C₁ X}

theorem eulerTreeMajorant_nonneg {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ eulerTreeMajorant M lam ε₀ R C₁ X Xs c := by
  unfold eulerTreeMajorant
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) (Real.exp_pos _).le) ?_
  · exact prod_nonneg fun l _ => mul_nonneg (prodExceptMax_nonneg _)
      (sum_nonneg fun T _ => prod_nonneg fun p _ => keptPair_nonneg p)
  · exact sum_nonneg fun T _ => prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _
  · exact prod_nonneg fun i _ => sq_nonneg _
  · exact prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)

end Def

/-! ### Products over the groups -/

section Products

open scoped Classical

variable {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}

/-- `∏ₗ ∏_{i ∈ V_{Xₗ}} (1 + ∑_{j ∈ V_{Xₗ}, j ≠ i} ḡ_ij) ≤ ∏_{i ∈ V_X} (1 + ∑_{j ∈ V_X, j ≠ i} ḡ_ij)`
for disjoint groups `Xₗ ⊆ X`. -/
theorem prod_prod_one_add_gbar_le (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) :
    ∏ l, ∏ i ∈ (Xs l).biUnion id, (1 + ∑ j ∈ ((Xs l).biUnion id).erase i, gbar M lam ε₀ R c i j) ≤
      ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
  have hpd : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint fun l => (Xs l).biUnion id :=
    fun i _ j _ hij => disjoint_biUnion_of_disjoint hX (hXs i) (hXs j) (hdisj i j hij)
  have hsub : ∀ l, (Xs l).biUnion id ⊆ X.biUnion id := fun l =>
    biUnion_subset_biUnion_of_subset_left id (hXs l)
  have hone : ∀ i, 1 ≤ 1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j := fun i => by
    have := sum_nonneg fun j (_ : j ∈ (X.biUnion id).erase i) => gbar_nonneg (M := M) (lam := lam)
      (ε₀ := ε₀) (R := R) (c := c) i j
    linarith
  calc ∏ l, ∏ i ∈ (Xs l).biUnion id, (1 + ∑ j ∈ ((Xs l).biUnion id).erase i,
        gbar M lam ε₀ R c i j)
      ≤ ∏ l, ∏ i ∈ (Xs l).biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i,
          gbar M lam ε₀ R c i j) := by
        refine prod_le_prod₀ (fun l _ => prod_nonneg fun i _ => add_nonneg zero_le_one
          (sum_nonneg fun j _ => gbar_nonneg _ _)) fun l _ => prod_le_prod₀
          (fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _))
          fun i _ => ?_
        refine add_le_add_right (sum_le_sum_of_subset_of_nonneg
          (erase_subset_erase _ (hsub l)) fun j _ _ => gbar_nonneg _ _) 1
    _ = ∏ i ∈ univ.biUnion fun l => (Xs l).biUnion id,
          (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) := (prod_biUnion hpd).symm
    _ ≤ ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) :=
        prod_le_prod_of_subset_of_one_le₀ (biUnion_subset.2 fun l _ => hsub l)
          (fun i _ => zero_le_one.trans (hone i)) fun i _ _ => hone i

/-- `∏ₗ ∏_{ij ∈ ℰ^inter(Xₗ)} e^{C₁ a_ij} ≤ ∏_{ij ∈ ℰ^inter(X)} e^{C₁ a_ij}` for `C₁ a ≥ 0` and
disjoint groups `Xₗ ⊆ X`. -/
theorem prod_prod_exp_le (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (f : ℕ × ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    ∏ l, ∏ p ∈ interPairs (Xs l), Real.exp (f p) ≤ ∏ p ∈ interPairs X, Real.exp (f p) := by
  rw [← prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX hXs hdisj fun _ => le_rfl)]
  exact prod_le_prod_of_subset_of_one_le₀
    (biUnion_subset.2 fun l _ => interPairs_subset_of_subset hX (hXs l))
    (fun p _ => (Real.exp_pos _).le) fun p _ _ => Real.one_le_exp (hf p)

/-- The logarithmic factors already obtained for the groups combine into the
product over `V_X`, equation (4.103) and the following sentence, (4.103). -/
theorem prod_prod_log_le (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) {M ε₀ R : ℝ}
    (hM : 1 < M) (c : ℕ → ℂ × ℂ)
    (hr : ∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    (∏ l, ∏ i ∈ (Xs l).biUnion id,
      (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2) ≤
      ∏ i ∈ X.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2 := by
  have hpd : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun l => (Xs l).biUnion id) :=
    fun i _ j _ hij => disjoint_biUnion_of_disjoint hX (hXs i) (hXs j) (hdisj i j hij)
  rw [← prod_biUnion hpd]
  refine prod_le_prod_of_subset_of_one_le₀
    (biUnion_subset.2 fun l _ => biUnion_subset_biUnion_of_subset_left id (hXs l))
    (fun i _ => sq_nonneg _) fun i hi _ => ?_
  have hlog : 0 ≤ Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) := by
    apply Real.logb_nonneg hM
    rw [le_div_iff₀ (hr i hi).1]
    nlinarith [(hr i hi).1, (hr i hi).2]
  nlinarith

end Products

/-! ### Lemma 4.55 -/

section Main

open scoped Classical

/-- Lemma 4.55, equation (4.96), with the paper's hypotheses and proof.
The logarithmic factors are obtained within each group from reattachment multiplicities,
then multiplied over the disjoint groups. The constant depends on `p` and `C₁`. -/
theorem lemma_4_55_route (p : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M lam ε₀ R : ℝ), 9 ≤ M → 0 < lam →
      ∀ {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ p) →
      ∀ c : ℕ → ℂ × ℂ,
        (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
        eulerMajorant M lam ε₀ R C₁ X c ≤ Real.exp (C * (X.biUnion id).card) *
          ∑' n : ℕ, 1 / (n.factorial : ℝ) *
            ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
                (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
              eulerTreeMajorant M lam ε₀ R C₁ X Xs c := by
  have hC0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  obtain ⟨K₀, hK₀, hgroupRoute⟩ := eulerGroupSum_route_le p hC₁
  set K : ℝ := max K₀ 2 with hK
  have hK2 : 2 ≤ K := le_max_right _ _
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := zero_lt_one.trans_le hK1
  refine ⟨Real.log K, Real.log_pos (by linarith), fun M lam ε₀ R hM hlam X hX hp c hc => ?_⟩
  by_cases hlinked : ∃ q ∈ interPairs X, MultipoleLinked M lam (c q.1) (c q.2)
  · rw [eulerMajorant_eq_zero_of_linked hlinked]
    exact mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun n =>
      mul_nonneg (by positivity) (sum_nonneg fun Xs _ => eulerTreeMajorant_nonneg Xs c))
  have hnot : ∀ q ∈ interPairs X, ¬ MultipoleLinked M lam (c q.1) (c q.2) :=
    fun q hq h => hlinked ⟨q, hq, h⟩
  set V := X.biUnion id with hV
  have hexpK : Real.exp (Real.log K * V.card) = K ^ V.card := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log hK0]
  rw [hexpK]
  set a : ℕ × ℕ → ℝ := fun p => absOddWeight M lam ε₀ R (c p.1) (c p.2) with ha
  set b : ℕ × ℕ → ℝ := fun p => absEvenWeight M lam ε₀ R (c p.1) (c p.2) with hb
  have ha0 : ∀ p, 0 ≤ a p := fun p => absOddWeight_nonneg _ _ _ _ _ _
  have hb0 : ∀ p, 0 ≤ b p := fun p => absEvenWeight_nonneg _ _ _ _ _ _
  -- the right-hand side
  set B : ℕ → ℝ := fun n => 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      eulerTreeMajorant M lam ε₀ R C₁ X Xs c with hB
  have hB0 : ∀ n, 0 ≤ B n := fun n => mul_nonneg (by positivity)
    (sum_nonneg fun Xs _ => eulerTreeMajorant_nonneg Xs c)
  have hBvan : ∀ n, X.card < n → B n = 0 := by
    intro n hn
    refine mul_eq_zero_of_right _ (sum_eq_zero fun Xs hXs => ?_)
    rw [mem_filter] at hXs
    obtain ⟨l, hl⟩ := exists_eq_empty_of_card_lt
      (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)) hXs.2 hn
    have hT : relTreePairs (Xs l) = ∅ := by
      rw [hl]
      exact relTreePairs_eq_empty_of_card_le_one isSubpartition_empty (by simp)
    unfold eulerTreeMajorant
    rw [prod_eq_zero (mem_univ l) (by rw [hT, sum_empty, mul_zero])]
    ring
  obtain ⟨hBsum, -⟩ := summable_and_tsum_eq_of_vanish hBvan
  by_cases h1 : X.card ≤ 1
  · rw [eulerMajorant_eq_zero_of_card_le_one h1]
    exact mul_nonneg (pow_nonneg hK0.le _) (tsum_nonneg hB0)
  rw [eulerMajorant, ite_eq_right h1]
  -- the left-hand side, term by term
  set Q := ∏ p ∈ interPairs X, Real.exp (C₁ * a p) *
    (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) with hQ
  have hQ0 : 0 ≤ Q :=
    prod_nonneg fun p _ => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num)
  have hQle : Q ≤ ∏ p ∈ interPairs X, Real.exp (C₁ * a p) :=
    prod_le_prod₀ (fun p _ => mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num))
      fun p _ => mul_le_of_le_one_right (Real.exp_pos _).le (by split_ifs <;> norm_num)
  have hterm : ∀ {k : ℕ} (Xs : Fin k → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
        ∑ T ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, C₁ * a p) * (∏ p ∈ T, b p) * Q ≤
        K ^ V.card * eulerTreeMajorant M lam ε₀ R C₁ X Xs c := by
    intro k Xs hXs hdisj
    have hXsub : ∀ l, IsSubpartition (Xs l) := fun l => isSubpartition_mono hX (hXs l)
    set ST := ∑ T ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)), ∏ p ∈ T, b p with hST
    have hST0 : 0 ≤ ST := sum_nonneg fun T _ => prod_nonneg fun p _ => hb0 p
    set PS : Fin k → ℝ := fun l =>
      prodExceptMax c (Xs l) * ∑ T ∈ relTreePairs (Xs l), ∏ p ∈ T, keptPair M lam ε₀ R c p
      with hPS
    have hPS0 : ∀ l, 0 ≤ PS l := fun l => mul_nonneg (prodExceptMax_nonneg _)
      (sum_nonneg fun T _ => prod_nonneg fun p _ => keptPair_nonneg p)
    set Eₗ : Fin k → ℝ := fun l => ∏ p ∈ interPairs (Xs l), Real.exp (C₁ * a p) with hEₗ
    set Gₗ : Fin k → ℝ := fun l => ∏ i ∈ (Xs l).biUnion id,
      (1 + ∑ j ∈ ((Xs l).biUnion id).erase i, gbar M lam ε₀ R c i j) with hGₗ
    have hEₗ0 : ∀ l, 0 ≤ Eₗ l := fun l => prod_nonneg fun _ _ => (Real.exp_pos _).le
    have hGₗ0 : ∀ l, 0 ≤ Gₗ l := fun l => prod_nonneg fun i _ =>
      add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)
    set GX := ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) with hGX
    set EX := ∏ p ∈ interPairs X, Real.exp (C₁ * a p) with hEX
    set Λ := ∏ i ∈ V, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2 with hΛ
    have hEX0 : 0 ≤ EX := prod_nonneg fun _ _ => (Real.exp_pos _).le
    have hGX0 : 0 ≤ GX := prod_nonneg fun i _ =>
      add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)
    -- the sum over the `Eₗ` factorizes
    have hfac : ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
        ∑ T ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, C₁ * a p) * (∏ p ∈ T, b p) * Q =
        (∏ l, eulerGroupSum C₁ a (Xs l)) * ST * Q := by
      rw [← sum_groupTerm_eq hX hXs hdisj, sum_mul]
      refine sum_congr rfl fun Es _ => ?_
      rw [sum_mul]
    set Λₗ : Fin k → ℝ := fun l => ∏ i ∈ (Xs l).biUnion id,
      (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2 with hΛₗ
    have hΛₗ0 : ∀ l, 0 ≤ Λₗ l := fun l => prod_nonneg fun i _ => sq_nonneg _
    -- Apply the group estimate after the reattachment exchange.
    have hgroup : ∏ l, eulerGroupSum C₁ a (Xs l) ≤
        ∏ l, (K ^ ((Xs l).biUnion id).card * PS l * Eₗ l * Gₗ l * Λₗ l) := by
      refine prod_le_prod₀ (fun l _ => eulerGroupSum_nonneg hC0 ha0 _) fun l _ => ?_
      have hsubV : (Xs l).biUnion id ⊆ X.biUnion id :=
        biUnion_subset_biUnion_of_subset_left id (hXs l)
      have hnotl : ∀ i j : (Xs l).biUnion id, (interEdges (Xs l)).Adj i j →
          ¬ MultipoleLinked M lam (c i) (c j) := by
        intro i j hij
        have hpair : ∀ a b : (Xs l).biUnion id, (interEdges (Xs l)).Adj a b →
            (a : ℕ) < b → ¬ MultipoleLinked M lam (c a) (c b) := by
          intro a b hab hlt
          have hab' : ((a : ℕ), (b : ℕ)) ∈ edgesOf (interEdges (Xs l)) :=
            mem_edgesOf.2 ⟨a.2, b.2, hlt, hab⟩
          rw [edgesOf_interEdges (hXsub l)] at hab'
          exact hnot _ (interPairs_subset_of_subset hX (hXs l) hab')
        rcases lt_or_gt_of_ne (show (i : ℕ) ≠ j from fun h => hij.ne (Subtype.ext h)) with h | h
        · exact hpair i j hij h
        · exact fun hl => hpair j i hij.symm h ((multipoleLinked_comm).1 hl)
      have hg := hgroupRoute M lam ε₀ R hM hlam (hXsub l)
        (fun S hS => hp S (hXs l hS)) c (fun i hi => hc i (hsubV hi)) hnotl
      calc eulerGroupSum C₁ a (Xs l) ≤
          K₀ ^ ((Xs l).biUnion id).card * PS l * Eₗ l * Gₗ l * Λₗ l := by
            simpa only [hPS, hEₗ, hGₗ, hΛₗ, ha, mul_assoc] using hg
        _ ≤ K ^ ((Xs l).biUnion id).card * PS l * Eₗ l * Gₗ l * Λₗ l := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hK₀.le (le_max_left _ _) _) (hPS0 l)) (hEₗ0 l))
                (hGₗ0 l)) (hΛₗ0 l)
    have hprod : ∏ l, (K ^ ((Xs l).biUnion id).card * PS l * Eₗ l * Gₗ l * Λₗ l) =
        K ^ (∑ l, ((Xs l).biUnion id).card) * (∏ l, PS l) * (∏ l, Eₗ l) *
          (∏ l, Gₗ l) * ∏ l, Λₗ l := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib,
        prod_pow_eq_pow_sum]
    have hΛle : ∏ l, Λₗ l ≤ Λ := prod_prod_log_le hX hXs hdisj (by linarith) c hc
    have hKpow : K ^ (∑ l, ((Xs l).biUnion id).card) ≤ K ^ V.card :=
      pow_le_pow_right₀ hK1 (sum_card_biUnion_le hX hXs hdisj)
    have hEle : ∏ l, Eₗ l ≤ EX := prod_prod_exp_le hX hXs hdisj (fun p => C₁ * a p)
      fun p => mul_nonneg hC0 (ha0 p)
    have hGle : ∏ l, Gₗ l ≤ GX := prod_prod_one_add_gbar_le hX hXs hdisj M lam ε₀ R c
    have hEXEX : EX * EX = Real.exp (2 * C₁ * ∑ p ∈ interPairs X, a p) := by
      rw [hEX, ← Real.exp_sum, ← Real.exp_add, ← mul_sum]
      ring_nf
    have hPS0' : 0 ≤ ∏ l, PS l := prod_nonneg fun l _ => hPS0 l
    rw [hfac]
    calc (∏ l, eulerGroupSum C₁ a (Xs l)) * ST * Q
        ≤ (K ^ V.card * (∏ l, PS l) * EX * GX * Λ) * ST * EX := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ hST0) hQle hQ0
            (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
              (pow_nonneg hK0.le _) hPS0') hEX0) hGX0)
                (prod_nonneg fun i _ => sq_nonneg _)) hST0)
          rw [hprod] at hgroup
          refine hgroup.trans ?_
          refine mul_le_mul ?_ hΛle (prod_nonneg fun l _ => hΛₗ0 l)
            (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hK0.le _) hPS0') hEX0) hGX0)
          exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hKpow hPS0') hEle
            (prod_nonneg fun l _ => hEₗ0 l) (mul_nonneg (pow_nonneg hK0.le _) hPS0')) hGle
              (prod_nonneg fun l _ => hGₗ0 l)
              (mul_nonneg (mul_nonneg (pow_nonneg hK0.le _) hPS0') hEX0)
      _ = K ^ V.card * ((∏ l, PS l) * ST * Λ * (EX * EX) * GX) := by ring
      _ = K ^ V.card * eulerTreeMajorant M lam ε₀ R C₁ X Xs c := by
          rw [hEXEX]
          simp only [eulerTreeMajorant, hPS, hST, hΛ, hGX, ha, hb, hV]
  -- the series
  set A : ℕ → ℝ := fun k => 1 / (k.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset (fun l => relEulerianConnectedPairs (Xs l)),
        ∑ T ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          (∏ p ∈ Finset.univ.biUnion Es, C₁ * a p) * (∏ p ∈ T, b p) * Q with hA
  have hA0 : ∀ k, 0 ≤ A k := fun k => mul_nonneg (by positivity)
    (sum_nonneg fun Xs _ => sum_nonneg fun Es _ => sum_nonneg fun T _ => mul_nonneg
      (mul_nonneg (prod_nonneg fun p _ => mul_nonneg hC0 (ha0 p)) (prod_nonneg fun p _ => hb0 p))
      hQ0)
  have hAB : ∀ k, A k ≤ K ^ V.card * B k := by
    intro k
    rw [hA, hB, mul_left_comm, mul_sum]
    refine mul_le_mul_of_nonneg_left (sum_le_sum fun Xs hXs => ?_) (by positivity)
    rw [mem_filter] at hXs
    exact hterm Xs (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)) hXs.2
  have hAsum : Summable A :=
    Summable.of_nonneg_of_le hA0 hAB (hBsum.mul_left _)
  calc ∑' k, A k ≤ ∑' k, K ^ V.card * B k := hAsum.tsum_le_tsum hAB (hBsum.mul_left _)
    _ = K ^ V.card * ∑' n, B n := tsum_mul_left

end Main

end AbsoluteLower

end MultipoleBKT

end
