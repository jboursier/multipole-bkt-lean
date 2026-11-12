/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.RouteLog.Inner
public import MultipoleBKT.LowerBound.AbsoluteLower.ClaimInt2

/-!
# Logarithmic Euler group bounds and interaction control

The paper: Lemma 5.36, (4.97), and the paragraph preceding
Lemma 5.37.

`groups_route_le` multiplies the marked and unmarked logarithmic inner estimates
over disjoint groups. `upperH` is the literal tree, logarithmic, exponential and
pseudoforest weight `H_X`. `outerGroup_H_le` bounds the odd/even decomposition by
its sum. `outerGroup_le` then applies Lemma 4.56, retaining the logarithmic product.
The separation hypothesis is used throughout interaction control. Activity absorbs
the logarithms before using the log-free tree-series and integration interfaces.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset SimpleGraph Multipole Hierarchical SetPartition AbsoluteLower Parity

/-! ### Products over disjoint families of groups -/

section Families

open scoped Classical

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {𝒱 : Finset (Finset (Finset ℕ))}
  (h𝒱 : 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card))
include hX h𝒱

theorem pairwiseDisjoint_biUnion_of_mem_disjointFamilies :
    (𝒱 : Set (Finset (Finset ℕ))).PairwiseDisjoint fun Y => Y.biUnion id := by
  obtain ⟨hsub, hdisj, -⟩ := mem_disjointFamilies.1 h𝒱
  intro Y hY Y' hY' hne
  exact disjoint_biUnion_of_disjoint hX (hsub Y hY) (hsub Y' hY') (hdisj hY hY' hne)

/-- `∑_{Y ∈ 𝒱} |V_Y| ≤ |V_X|`. -/
theorem sum_card_le_of_mem_disjointFamilies :
    ∑ Y ∈ 𝒱, (Y.biUnion id).card ≤ (X.biUnion id).card := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒱
  rw [← card_biUnion (pairwiseDisjoint_biUnion_of_mem_disjointFamilies hX h𝒱)]
  exact card_le_card (biUnion_subset.2 fun Y hY => biUnion_subset_biUnion_of_subset_left id
    (hsub Y hY))

/-- `∏_{Y ∈ 𝒱} ∏_{ℰ^inter(Y)} f ≤ ∏_{ℰ^inter(X)} f` for `f ≥ 1`. -/
theorem prod_interPairs_le_of_mem_disjointFamilies (f : ℕ × ℕ → ℝ) (hf : ∀ q, 1 ≤ f q) :
    ∏ Y ∈ 𝒱, ∏ q ∈ interPairs Y, f q ≤ ∏ q ∈ interPairs X, f q := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒱
  have hd : (𝒱 : Set (Finset (Finset ℕ))).PairwiseDisjoint interPairs := by
    intro Y hY Y' hY' hne
    have h := pairwiseDisjoint_biUnion_of_mem_disjointFamilies hX h𝒱 hY hY' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro q hq hq'
    exact Finset.disjoint_left.1 h (interPairs_subset_pairsOn_biUnion _ hq).1
      (interPairs_subset_pairsOn_biUnion _ hq').1
  rw [← prod_biUnion hd]
  exact prod_le_prod_of_subset_of_one_le₀
    (biUnion_subset.2 fun Y hY => interPairs_subset_of_subset hX (hsub Y hY))
    (fun q _ => zero_le_one.trans (hf q)) fun q _ _ => hf q

/-- `∏_{Y ∈ 𝒱} ∏_{i ∈ V_Y} (1 + ∑_{j ∈ V_Y} ḡ_ij) ≤ ∏_{i ∈ V_X} (1 + ∑_{j ∈ V_X} ḡ_ij)`. -/
theorem prod_gbar_le_of_mem_disjointFamilies (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) :
    ∏ Y ∈ 𝒱, ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j) ≤
      ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒱
  have hsubV : ∀ Y ∈ 𝒱, Y.biUnion id ⊆ X.biUnion id := fun Y hY =>
    biUnion_subset_biUnion_of_subset_left id (hsub Y hY)
  have hone : ∀ i, 1 ≤ 1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j := fun i => by
    have := sum_nonneg fun j (_ : j ∈ (X.biUnion id).erase i) =>
      gbar_nonneg (M := M) (lam := lam) (ε₀ := ε₀) (R := R) (c := c) i j
    linarith
  calc ∏ Y ∈ 𝒱, ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j)
      ≤ ∏ Y ∈ 𝒱, ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i,
          gbar M lam ε₀ R c i j) := by
        refine prod_le_prod₀ (fun Y _ => prod_nonneg fun i _ => add_nonneg zero_le_one
          (sum_nonneg fun j _ => gbar_nonneg _ _)) fun Y hY => prod_le_prod₀
          (fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _))
          fun i _ => ?_
        exact add_le_add_right (sum_le_sum_of_subset_of_nonneg
          (erase_subset_erase _ (hsubV Y hY)) fun j _ _ => gbar_nonneg _ _) 1
    _ = ∏ i ∈ 𝒱.biUnion fun Y => Y.biUnion id,
          (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) :=
        (prod_biUnion (pairwiseDisjoint_biUnion_of_mem_disjointFamilies hX h𝒱)).symm
    _ ≤ ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) :=
        prod_le_prod_of_subset_of_one_le₀ (biUnion_subset.2 hsubV)
          (fun i _ => zero_le_one.trans (hone i)) fun i _ _ => hone i

/-- The logarithmic factors multiply over disjoint groups, with unused vertices
contributing factors at least one (4.97). -/
theorem prod_logProduct_le_of_mem_disjointFamilies {M ε₀ R : ℝ} (hM : 1 < M)
    (c : ℕ → ℂ × ℂ)
    (hr : ∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    ∏ Y ∈ 𝒱, logProduct M ε₀ R c Y ≤ logProduct M ε₀ R c X := by
  obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒱
  unfold logProduct
  rw [← prod_biUnion (pairwiseDisjoint_biUnion_of_mem_disjointFamilies hX h𝒱)]
  refine prod_le_prod_of_subset_of_one_le₀
    (biUnion_subset.2 fun Y hY => biUnion_subset_biUnion_of_subset_left id (hsub Y hY))
    (fun i _ => sq_nonneg _) ?_
  intro i hi _
  exact one_le_logFactor hM (hr i hi).1 (hr i hi).2

/-- Pseudoforest and predecessor factors for disjoint groups. -/
theorem prod_gbar_log_le_of_mem_disjointFamilies {M lam ε₀ R : ℝ} (hM : 1 < M)
    (c : ℕ → ℂ × ℂ)
    (hr : ∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) :
    ∏ Y ∈ 𝒱, ((∏ i ∈ Y.biUnion id,
      (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j)) * logProduct M ε₀ R c Y) ≤
      (∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j)) *
        logProduct M ε₀ R c X := by
  rw [prod_mul_distrib]
  exact mul_le_mul (prod_gbar_le_of_mem_disjointFamilies hX h𝒱 M lam ε₀ R c)
    (prod_logProduct_le_of_mem_disjointFamilies hX h𝒱 hM c hr)
    (prod_nonneg fun Y _ => logProduct_nonneg _ _ _ _ _)
    (prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _))

end Families

/-! ### Lemma 4.56 for one outer group -/

section Rad

/-- `e^{t (log(17 x) + 1)} ≤ e^{t₀} 17^{t₀} x^t` for `t ≤ t₀` and `x ≥ 1`. -/
theorem exp_log_le {t t₀ x : ℝ} (htt : t ≤ t₀) (hx : 1 ≤ x) :
    Real.exp (t * (Real.log (17 * x) + 1)) ≤ Real.exp t₀ * 17 ^ t₀ * x ^ t := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have h17 : Real.exp (t * Real.log (17 * x)) = 17 ^ t * x ^ t := by
    rw [← Real.mul_rpow (by norm_num) hx0.le, Real.rpow_def_of_pos (by positivity), mul_comm]
  rw [mul_add, Real.exp_add, h17, mul_one]
  have h1 : Real.exp t ≤ Real.exp t₀ := Real.exp_le_exp.2 htt
  have h2 : (17 : ℝ) ^ t ≤ 17 ^ t₀ := Real.rpow_le_rpow_of_exponent_le (by norm_num) htt
  have hxt : 0 ≤ x ^ t := Real.rpow_nonneg hx0.le _
  calc 17 ^ t * x ^ t * Real.exp t = (Real.exp t * 17 ^ t) * x ^ t := by ring
    _ ≤ (Real.exp t₀ * 17 ^ t₀) * x ^ t :=
        mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le) hxt

open scoped Classical in
/-- **Lemma 4.56 for one outer group** (eqs. (4.103)–(4.104), as used in the proofs of Lemmas
4.57 and 5.37): see the module docstring. -/
theorem exp_gbar_le_rad (p : ℕ) : ∃ Cp : ℝ, 0 < Cp ∧ ∀ {M : ℝ}, 20 < M → ∀ (C₁ : ℝ),
    0 ≤ C₁ → ∀ (lam ε₀ R : ℝ) {X : Finset (Finset ℕ)}, IsSubpartition X →
      (∀ S ∈ X, S.card ≤ p) → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
      (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
        ¬ MultipoleLinked M lam (c i) (c j)) →
      (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2 *
          ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) ≤
        (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * (Cp * M)) ^ (X.biUnion id).card *
          ∏ i ∈ X.biUnion id,
            (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((2 * C₁ * Cp + 1) / M) := by
  obtain ⟨Cp, hCp, h56⟩ := lemma_4_56 p
  refine ⟨Cp, hCp, fun {M} hM C₁ hC₁ lam ε₀ R X hX hp c hr hD => ?_⟩
  obtain ⟨h1, h2⟩ := h56 hM lam ε₀ R hX hp c hr hD
  set V := X.biUnion id with hVdef
  have hM0 : 0 < M := by linarith
  set t := 2 * C₁ * Cp / M with ht
  have ht0 : 0 ≤ t := by positivity
  have htt : t ≤ C₁ * Cp / 10 := by
    rw [ht, div_le_div_iff₀ hM0 (by norm_num)]
    nlinarith [mul_nonneg hC₁ hCp.le]
  set x : ℕ → ℝ := fun i => ε₀ * R / ‖(c i).1 - (c i).2‖ with hx
  have hx1 : ∀ i ∈ V, 1 ≤ x i := fun i hi => by
    rw [hx, le_div_iff₀ (hr i hi).1, one_mul]
    exact (hr i hi).2
  -- the interaction term
  have hint : (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2
      ≤ ∏ i ∈ V, (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * x i ^ t) := by
    have hs := sum_interPairs_absOddWeight_le X M lam ε₀ R c
    have hsum : 2 * (C₁ * ∑ q ∈ interPairs X, absOddWeight M lam ε₀ R (c q.1) (c q.2)) ≤
        ∑ i ∈ V, t * (Real.log (17 * x i) + 1) := by
      calc 2 * (C₁ * ∑ q ∈ interPairs X, absOddWeight M lam ε₀ R (c q.1) (c q.2))
          ≤ 2 * C₁ * ∑ i ∈ V, ∑ j ∈ V.filter (fun j => ¬ SameBlock X i j),
              absOddWeight M lam ε₀ R (c i) (c j) *
                (if ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ then 1 else 0) := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_left hs (by positivity)
        _ ≤ 2 * C₁ * ∑ i ∈ V, Cp / M * (Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1) :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun i hi => h1 i hi) (by positivity)
        _ = ∑ i ∈ V, t * (Real.log (17 * x i) + 1) := by
            rw [mul_sum]
            refine sum_congr rfl fun i _ => ?_
            rw [hx, ht, mul_div_assoc]
            ring_nf
    calc (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2
        = Real.exp (2 * (C₁ * ∑ q ∈ interPairs X, absOddWeight M lam ε₀ R (c q.1) (c q.2))) := by
          rw [← Real.exp_sum, ← mul_sum, sq, ← Real.exp_add]
          ring_nf
      _ ≤ Real.exp (∑ i ∈ V, t * (Real.log (17 * x i) + 1)) := Real.exp_le_exp.2 hsum
      _ = ∏ i ∈ V, Real.exp (t * (Real.log (17 * x i) + 1)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ V, (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * x i ^ t) :=
          prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i hi => exp_log_le htt (hx1 i hi)
  have hhint0 : 0 ≤ (∏ q ∈ interPairs X,
      Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2 := sq_nonneg _
  have hx0 : ∀ i ∈ V, 0 ≤ x i := fun i hi => zero_le_one.trans (hx1 i hi)
  calc (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2 *
        ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)
      ≤ (∏ i ∈ V, (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * x i ^ t)) *
          ((Cp * M) ^ V.card * ∏ i ∈ V, x i ^ (1 / M)) :=
        mul_le_mul hint h2 (prod_nonneg fun i _ => add_nonneg zero_le_one
          (sum_nonneg fun j _ => gbar_nonneg _ _))
          (prod_nonneg fun i hi => mul_nonneg (by positivity) (Real.rpow_nonneg (hx0 i hi) _))
    _ = (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * (Cp * M)) ^ V.card *
          ∏ i ∈ V, (x i ^ t * x i ^ (1 / M)) := by
        rw [prod_mul_distrib, prod_const, mul_pow, prod_mul_distrib]
        ring
    _ = (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * (Cp * M)) ^ V.card *
          ∏ i ∈ V, x i ^ ((2 * C₁ * Cp + 1) / M) := by
        congr 1
        refine prod_congr rfl fun i hi => ?_
        rw [← Real.rpow_add (zero_lt_one.trans_le (hx1 i hi)), ht]
        congr 1
        field_simp

end Rad

/-! ### The bound of one outer group -/

section Outer

open scoped Classical

/-- The weight
`∏_{S ∈ Y, S ≠ Ŝ} r_S² ∑_{T ∈ 𝖳^Y} ∏_{ij ∈ T} d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c}` of an
inner group `Y` (the group factor of `H_X` in (4.97) and of `J_{large,C₀}` in (4.113)). -/
noncomputable def treeWeightA (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) : ℝ :=
  prodExceptMax c Y * ∑ T ∈ relTreePairs Y, ∏ p ∈ T, keptPair M lam ε₀ R c p

/-- The weight `∑_{T ∈ 𝖳_0^{Coarse_X(𝒱)}} ∏_{ij ∈ T} b^abs_ij` of the trees between the groups. -/
noncomputable def treeWeightB (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ))
    (𝒱 : Finset (Finset (Finset ℕ))) : ℝ :=
  ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2)

/-- The inner series of an outer group `X`:
`∑_{𝒱} ∏_{Y ∈ 𝒱} (∏_{S ∈ Y, S ≠ Ŝ} r_S² ∑_{T ∈ 𝖳^Y} ∏_T d^{-2} 𝟙 𝟙_{𝓑^c})
∑_{T ∈ 𝖳_0^{Coarse_X(𝒱)}} ∏_T b^abs`,
over the disjoint families `𝒱` of groups of at least two blocks of `X`. -/
noncomputable def innerSeries (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ)) : ℝ :=
  ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
    (∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) * treeWeightB M lam ε₀ R c X 𝒱

theorem treeWeightA_nonneg (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) :
    0 ≤ treeWeightA M lam ε₀ R c Y :=
  mul_nonneg (prodExceptMax_nonneg Y) (sum_nonneg fun _ _ => prod_nonneg fun p _ =>
    keptPair_nonneg p)

theorem treeWeightB_nonneg (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ))
    (𝒱 : Finset (Finset (Finset ℕ))) : 0 ≤ treeWeightB M lam ε₀ R c X 𝒱 :=
  sum_nonneg fun _ _ => prod_nonneg fun _ _ => absEvenWeight_nonneg _ _ _ _ _ _

theorem innerSeries_nonneg (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ)) :
    0 ≤ innerSeries M lam ε₀ R c X :=
  sum_nonneg fun _ _ => mul_nonneg (prod_nonneg fun _ _ => treeWeightA_nonneg _ _ _ _ _ _)
    (treeWeightB_nonneg _ _ _ _ _ _ _)

/-- The literal `H_X` of (4.97), indexed by a disjoint
family instead of its ordered tuples. Its exponential coefficient is `2 C₁`. -/
noncomputable def upperH (M lam ε₀ R C₁ : ℝ) (c : ℕ → ℂ × ℂ)
    (X : Finset (Finset ℕ)) (𝒱 : Finset (Finset (Finset ℕ))) : ℝ :=
  (∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) * treeWeightB M lam ε₀ R c X 𝒱 *
    logProduct M ε₀ R c X *
    Real.exp (2 * C₁ * ∑ q ∈ interPairs X, absOddWeight M lam ε₀ R (c q.1) (c q.2)) *
    ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j)

/-- Factor the group-independent terms out of the sum of `H_X`. -/
theorem sum_upperH_eq (M lam ε₀ R C₁ : ℝ) (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ)) :
    (∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card), upperH M lam ε₀ R C₁ c X 𝒱) =
      innerSeries M lam ε₀ R c X * logProduct M ε₀ R c X *
        (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2 *
        ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j) := by
  have hexp : Real.exp (2 * C₁ * ∑ q ∈ interPairs X,
      absOddWeight M lam ε₀ R (c q.1) (c q.2)) =
      (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2 := by
    rw [← Real.exp_sum, ← mul_sum, sq, ← Real.exp_add]
    congr 1
    ring
  simp only [upperH, hexp, innerSeries, sum_mul]

/-- The constant of `outerGroup_le`. -/
noncomputable def outerConst (Cp Q M C₁ C₂ K : ℝ) : ℝ :=
  C₂ * C₁ * (Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1)) *
    (Real.exp (C₁ * Cp / 10) * 17 ^ (C₁ * Cp / 10) * (Cp * M))

/-- The product of the marked and unmarked inner estimates over disjoint
groups, including the predecessor logarithms (Lemma 5.36). -/
theorem groups_route_le (p : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ {M : ℝ}, 20 < M → ∀ {C₂ K : ℝ},
    1 ≤ C₂ → 1 ≤ K → ∀ (lam ε₀ R : ℝ), 0 < lam → ∀ {X : Finset (Finset ℕ)},
    IsSubpartition X → (∀ S ∈ X, S.card ≤ p) → ∀ (U : Finset ℕ) (c : ℕ → ℂ × ℂ),
    (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
      ¬ MultipoleLinked M lam (c i) (c j)) →
    ∀ (a : ℕ → ℕ → ℝ), (∀ i j, 0 ≤ a i j) → (∀ i j, a i j = a j i) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, a i j ≤ C₁ * absOddWeight M lam ε₀ R (c i) (c j)) →
    ∀ (m δ : ℕ → ℝ), (∀ i, 0 ≤ m i) →
    (∀ i ∈ U ∩ X.biUnion id, m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i)) →
    (∀ i ∈ X.biUnion id, 0 < δ i) → (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ δ i) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i) →
    (∀ S ∈ X, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i) →
    ∀ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
      (∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
        ∏ i ∈ U ∩ Y.biUnion id, m i) ≤
      (Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1)) ^ (X.biUnion id).card *
        (∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) *
        (∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) *
        ((∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j)) *
          logProduct M ε₀ R c X) := by
  obtain ⟨Q, hQ, hinner⟩ := groupSum_route_le p hC₁
  refine ⟨Q, hQ, fun {M} hM {C₂ K} hC₂ hK lam ε₀ R hlam X hX hp U c hr hD a ha0 hasymm ha
    m δ hm0 hm hδ hrδ hKE hKS => ?_⟩
  set V := X.biUnion id with hVdef
  set n := V.card with hn
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  set aA : ℕ × ℕ → ℝ := fun q => absOddWeight M lam ε₀ R (c q.1) (c q.2) with haA
  set Ex := ∏ q ∈ interPairs X, Real.exp (C₁ * aA q) with hEx
  set G := (∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)) *
    logProduct M ε₀ R c X with hG
  set Kh := Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1) with hKh
  have hKh0 : 0 ≤ Kh := by positivity
  have hKh1 : 1 ≤ Kh := by
    have h0 : 0 ≤ 8 * (C₁ ^ 3 * C₂ * K ^ 6) := by positivity
    dsimp [Kh]
    nlinarith
  have hEx0 : 0 ≤ Ex := prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hgroups : ∀ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
      ∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
        ∏ i ∈ U ∩ Y.biUnion id, m i ≤
      Kh ^ n * (∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) * Ex * G := by
    intro 𝒱 h𝒱
    obtain ⟨hsub, -, -⟩ := mem_disjointFamilies.1 h𝒱
    have hY : ∀ Y ∈ 𝒱, Y.biUnion id ⊆ V := fun Y hY =>
      biUnion_subset_biUnion_of_subset_left id (hsub Y hY)
    have hone : ∀ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
        ∏ i ∈ U ∩ Y.biUnion id, m i ≤
        Kh ^ (Y.biUnion id).card * treeWeightA M lam ε₀ R c Y *
          (∏ q ∈ interPairs Y, Real.exp (C₁ * aA q)) *
          ((∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j)) *
            logProduct M ε₀ R c Y) := by
      intro Y hYm
      have hYs : IsSubpartition Y := isSubpartition_mono hX (hsub Y hYm)
      have h := hinner hYs U c (by linarith) hlam hC₂ hK a ha0 hasymm
        (fun i hi j hj => ha i (hY Y hYm hi) j (hY Y hYm hj)) m δ hm0
        (fun i hi => hm i (mem_inter.2 ⟨(mem_inter.1 hi).1, hY Y hYm (mem_inter.1 hi).2⟩))
        (fun i hi => hδ i (hY Y hYm hi)) (fun i hi => hrδ i (hY Y hYm hi))
        (fun i hi j hj => hKE i (hY Y hYm hi) j (hY Y hYm hj))
        (fun S hS => hKS S (hsub Y hYm hS))
        (fun S hS => hp S (hsub Y hYm hS)) (fun i hi => hr i (hY Y hYm hi))
        (by
          intro i j hij
          have hpair : ∀ a b : Y.biUnion id, (interEdges Y).Adj a b → (a : ℕ) < b →
              ¬ MultipoleLinked M lam (c a) (c b) := by
            intro a b hab hlt
            have hab' : ((a : ℕ), (b : ℕ)) ∈ edgesOf (interEdges Y) :=
              mem_edgesOf.2 ⟨a.2, b.2, hlt, hab⟩
            rw [edgesOf_interEdges hYs] at hab'
            have hq := interPairs_subset_of_subset hX (hsub Y hYm) hab'
            exact hD a (hY Y hYm a.2) b (hY Y hYm b.2) (by
              rintro ⟨S, hS, haS, hbS⟩
              exact (mem_interPairs.1 hq).2 ⟨S, hS, mem_pairsOn.2 ⟨haS, hbS, hlt⟩⟩)
          rcases lt_or_gt_of_ne (show (i : ℕ) ≠ j from fun h => hij.ne (Subtype.ext h)) with h | h
          · exact hpair i j hij h
          · exact fun hl => hpair j i hij.symm h (multipoleLinked_comm.1 hl))
      refine h.trans (le_of_eq ?_)
      rw [treeWeightA]
      ring
    have hnn : ∀ Y ∈ 𝒱, 0 ≤ ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
        ∏ i ∈ U ∩ Y.biUnion id, m i := fun Y _ => sum_nonneg fun E _ =>
      mul_nonneg (prod_nonneg fun q _ => ha0 _ _) (prod_nonneg fun i _ => hm0 i)
    refine (prod_le_prod₀ hnn hone).trans ?_
    rw [prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum]
    have hcard := sum_card_le_of_mem_disjointFamilies hX h𝒱
    have hexp := prod_interPairs_le_of_mem_disjointFamilies hX h𝒱 (fun q => Real.exp (C₁ * aA q))
      fun q => Real.one_le_exp (mul_nonneg hC₁0 (absOddWeight_nonneg _ _ _ _ _ _))
    have hgb := prod_gbar_log_le_of_mem_disjointFamilies hX h𝒱 (M := M) (lam := lam) (by linarith) c hr
    have hA0 : 0 ≤ ∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y :=
      prod_nonneg fun Y _ => treeWeightA_nonneg _ _ _ _ _ _
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hKh1 hcard) hA0) hexp
      (prod_nonneg fun Y _ => prod_nonneg fun _ _ => (Real.exp_pos _).le)
      (mul_nonneg (pow_nonneg hKh0 _) hA0)) hgb
      (prod_nonneg fun Y _ => mul_nonneg (prod_nonneg fun i _ => add_nonneg zero_le_one
        (sum_nonneg fun j _ => gbar_nonneg _ _)) (logProduct_nonneg _ _ _ _ _))
      (mul_nonneg (mul_nonneg (pow_nonneg hKh0 _) hA0) hEx0)
  exact hgroups

/-- The literal `H_X` bound after the odd/even decomposition. -/
theorem outerGroup_H_le (p : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ {M : ℝ}, 20 < M → ∀ {C₂ K : ℝ},
    1 ≤ C₂ → 1 ≤ K → ∀ (lam ε₀ R : ℝ), 0 < lam → ∀ {X : Finset (Finset ℕ)},
    IsSubpartition X → (∀ S ∈ X, S.card ≤ p) → ∀ (U : Finset ℕ) (c : ℕ → ℂ × ℂ),
    (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
      ¬ MultipoleLinked M lam (c i) (c j)) →
    ∀ (a : ℕ → ℕ → ℝ), (∀ i j, 0 ≤ a i j) → (∀ i j, a i j = a j i) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, a i j ≤ C₁ * absOddWeight M lam ε₀ R (c i) (c j)) →
    ∀ (B : ℕ × ℕ → ℝ), (∀ q ∈ interPairs X, 0 ≤ B q) →
    (∀ q ∈ interPairs X, B q ≤ C₁ * absEvenWeight M lam ε₀ R (c q.1) (c q.2)) →
    ∀ (m δ : ℕ → ℝ), (∀ i, 0 ≤ m i) →
    (∀ i ∈ U ∩ X.biUnion id, m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i)) →
    (∀ i ∈ X.biUnion id, 0 < δ i) → (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ δ i) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i) →
    (∀ S ∈ X, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i) →
    ∑ E₁ ∈ markEulerPairs X U, (∏ q ∈ E₁, a q.1 q.2) * (∏ i ∈ U ∩ X.biUnion id, m i) *
        ∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ q ∈ E₂, B q ≤
      (C₂ * C₁ * (Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1))) ^ (X.biUnion id).card *
        ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card), upperH M lam ε₀ R C₁ c X 𝒱 := by
  obtain ⟨Q, hQ, hfamily⟩ := groups_route_le p hC₁
  refine ⟨Q, hQ, fun {M} hM {C₂ K} hC₂ hK lam ε₀ R hlam X hX hp U c hr hD a ha0 hasymm ha
    B hB0 hB m δ hm0 hm hδ hrδ hKE hKS => ?_⟩
  set V := X.biUnion id with hVdef
  set n := V.card with hn
  have hM1 : 1 ≤ M := by linarith
  have hC₁0 : 0 ≤ C₁ := zero_le_one.trans hC₁
  have hC₂0 : 0 ≤ C₂ := zero_le_one.trans hC₂
  set aA : ℕ × ℕ → ℝ := fun q => absOddWeight M lam ε₀ R (c q.1) (c q.2) with haA
  set bA : ℕ × ℕ → ℝ := fun q => absEvenWeight M lam ε₀ R (c q.1) (c q.2) with hbA
  set Ex := ∏ q ∈ interPairs X, Real.exp (C₁ * aA q) with hEx
  set G := (∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)) *
    logProduct M ε₀ R c X with hG
  set Kh := Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1) with hKh
  have hKh0 : 0 ≤ Kh := by positivity
  have hKh1 : 1 ≤ Kh := by
    have h0 : 0 ≤ 8 * (C₁ ^ 3 * C₂ * K ^ 6) := by positivity
    dsimp [Kh]
    nlinarith
  have hEx0 : 0 ≤ Ex := prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hG0 : 0 ≤ G := mul_nonneg
    (prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _))
    (logProduct_nonneg _ _ _ _ _)
  -- the marks are bounded by `C₂`
  have hmC : ∀ i ∈ U ∩ V, m i ≤ C₂ := by
    intro i hi
    have hiV := (mem_inter.1 hi).2
    have hq : ‖(c i).1 - (c i).2‖ / δ i ≤ 1 := by
      rw [div_le_one (hδ i hiV)]
      exact hrδ i hiV
    calc m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i) := hm i hi
      _ ≤ C₂ * 1 := mul_le_mul_of_nonneg_left hq hC₂0
      _ = C₂ := mul_one C₂
  -- Step 1
  have h1 := stepOne_le hX U hC₂ hC₁ (fun q => a q.1 q.2) B bA m (fun q => ha0 _ _) hB0
    (fun q => absEvenWeight_nonneg _ _ _ _ _ _) hB hm0 hmC
  -- the inner groups (Lemma 5.36)
  have hgroups := hfamily hM hC₂ hK lam ε₀ R hlam hX hp U c hr hD a ha0 hasymm ha
    m δ hm0 hm hδ hrδ hKE hKS
  -- the even bonds: `1 + B ≤ e^{C₁ a^abs}`
  have hBexp : ∏ q ∈ interPairs X, (1 + B q) ≤ Ex := by
    refine prod_le_prod₀ (fun q hq => by have := hB0 q hq; linarith) fun q hq => ?_
    have hq2 := interPairs_subset_pairsOn_biUnion X hq
    have hns : ¬ SameBlock X q.1 q.2 := by
      rintro ⟨S, hS, h1, h2⟩
      exact (mem_interPairs.1 hq).2 ⟨S, hS, mem_pairsOn.2 ⟨h1, h2,
        (mem_pairsOn.1 (interPairs_subset_pairsOn hq)).2.2⟩⟩
    have hbA : bA q ≤ aA q := absEvenWeight_le_absOddWeight hM1 hlam (hD _ hq2.1 _ hq2.2 hns)
    calc 1 + B q ≤ 1 + C₁ * aA q := by
          have := hB q hq
          nlinarith
      _ ≤ Real.exp (C₁ * aA q) := by linarith [Real.add_one_le_exp (C₁ * aA q)]
  -- the inner series
  have hser : ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
      (∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
        ∏ i ∈ U ∩ Y.biUnion id, m i) * ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, bA q ≤
      Kh ^ n * Ex * G * innerSeries M lam ε₀ R c X := by
    rw [innerSeries, mul_sum]
    refine sum_le_sum fun 𝒱 h𝒱 => ?_
    have hT0 : 0 ≤ ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, bA q :=
      sum_nonneg fun T _ => prod_nonneg fun q _ => absEvenWeight_nonneg _ _ _ _ _ _
    calc (∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
          ∏ i ∈ U ∩ Y.biUnion id, m i) * ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, bA q
        ≤ (Kh ^ n * (∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) * Ex * G) *
            ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, bA q :=
          mul_le_mul_of_nonneg_right (hgroups 𝒱 h𝒱) hT0
      _ = Kh ^ n * Ex * G * ((∏ Y ∈ 𝒱, treeWeightA M lam ε₀ R c Y) *
            treeWeightB M lam ε₀ R c X 𝒱) := by
          rw [treeWeightB]
          ring
  calc _ ≤ (C₂ * C₁) ^ n * (∏ q ∈ interPairs X, (1 + B q)) *
        ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
          (∏ Y ∈ 𝒱, ∑ E ∈ markEulerConnPairs Y U, (∏ q ∈ E, a q.1 q.2) *
            ∏ i ∈ U ∩ Y.biUnion id, m i) * ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ q ∈ T, bA q := h1
    _ ≤ (C₂ * C₁) ^ n * Ex * (Kh ^ n * Ex * G * innerSeries M lam ε₀ R c X) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hBexp (by positivity)) hser
          (sum_nonneg fun 𝒱 _ => mul_nonneg (prod_nonneg fun Y _ => sum_nonneg fun E _ =>
            mul_nonneg (prod_nonneg fun q _ => ha0 _ _) (prod_nonneg fun i _ => hm0 i))
            (sum_nonneg fun T _ => prod_nonneg fun q _ => absEvenWeight_nonneg _ _ _ _ _ _))
          (mul_nonneg (by positivity) hEx0)
    _ = (C₂ * C₁ * Kh) ^ n * (Ex ^ 2 * G) * innerSeries M lam ε₀ R c X := by ring_nf
    _ = _ := by
        rw [sum_upperH_eq]
        dsimp [G, Kh, Ex, aA, n, V]
        ring

/-- Apply Lemma 4.56 to the separated `H_X` bound, retaining its logarithms. -/
theorem outerGroup_le (p : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∃ Cp : ℝ, 0 < Cp ∧ ∀ {M : ℝ}, 20 < M → ∀ {C₂ K : ℝ},
    1 ≤ C₂ → 1 ≤ K → ∀ (lam ε₀ R : ℝ), 0 < lam → ∀ {X : Finset (Finset ℕ)},
    IsSubpartition X → (∀ S ∈ X, S.card ≤ p) → ∀ (U : Finset ℕ) (c : ℕ → ℂ × ℂ),
    (∀ i ∈ X.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, ¬ SameBlock X i j →
      ¬ MultipoleLinked M lam (c i) (c j)) →
    ∀ (a : ℕ → ℕ → ℝ), (∀ i j, 0 ≤ a i j) → (∀ i j, a i j = a j i) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, a i j ≤ C₁ * absOddWeight M lam ε₀ R (c i) (c j)) →
    ∀ (B : ℕ × ℕ → ℝ), (∀ q ∈ interPairs X, 0 ≤ B q) →
    (∀ q ∈ interPairs X, B q ≤ C₁ * absEvenWeight M lam ε₀ R (c q.1) (c q.2)) →
    ∀ (m δ : ℕ → ℝ), (∀ i, 0 ≤ m i) →
    (∀ i ∈ U ∩ X.biUnion id, m i ≤ C₂ * (‖(c i).1 - (c i).2‖ / δ i)) →
    (∀ i ∈ X.biUnion id, 0 < δ i) → (∀ i ∈ X.biUnion id, ‖(c i).1 - (c i).2‖ ≤ δ i) →
    (∀ i ∈ X.biUnion id, ∀ j ∈ X.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i) →
    (∀ S ∈ X, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i) →
    ∑ E₁ ∈ markEulerPairs X U, (∏ q ∈ E₁, a q.1 q.2) * (∏ i ∈ U ∩ X.biUnion id, m i) *
        ∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ q ∈ E₂, B q ≤
      outerConst Cp Q M C₁ C₂ K ^ (X.biUnion id).card *
        (∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((2 * C₁ * Cp + 1) / M)) *
        innerSeries M lam ε₀ R c X * logProduct M ε₀ R c X := by
  obtain ⟨Q, hQ, hH⟩ := outerGroup_H_le p hC₁
  obtain ⟨Cp, hCp, hrad⟩ := exp_gbar_le_rad p
  refine ⟨Q, hQ, Cp, hCp, fun {M} hM {C₂ K} hC₂ hK lam ε₀ R hlam X hX hp U c hr hD a ha0 hasymm ha
    B hB0 hB m δ hm0 hm hδ hrδ hKE hKS => ?_⟩
  have hmain := hH hM hC₂ hK lam ε₀ R hlam hX hp U c hr hD a ha0 hasymm ha
    B hB0 hB m δ hm0 hm hδ hrδ hKE hKS
  rw [sum_upperH_eq] at hmain
  have hrad' := hrad hM C₁ (by linarith) lam ε₀ R hX hp c hr hD
  have h0 : 0 ≤ (C₂ * C₁ * (Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1))) ^ (X.biUnion id).card *
      innerSeries M lam ε₀ R c X * logProduct M ε₀ R c X :=
    mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (innerSeries_nonneg _ _ _ _ _ _))
      (logProduct_nonneg _ _ _ _ _)
  refine hmain.trans ?_
  calc _ = ((C₂ * C₁ * (Q * (8 * (C₁ ^ 3 * C₂ * K ^ 6) + 1))) ^ (X.biUnion id).card *
      innerSeries M lam ε₀ R c X * logProduct M ε₀ R c X) *
      ((∏ q ∈ interPairs X, Real.exp (C₁ * absOddWeight M lam ε₀ R (c q.1) (c q.2))) ^ 2 *
        ∏ i ∈ X.biUnion id, (1 + ∑ j ∈ (X.biUnion id).erase i, gbar M lam ε₀ R c i j)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrad' h0
    _ = _ := by simp only [outerConst, mul_pow]; ring

end Outer

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
