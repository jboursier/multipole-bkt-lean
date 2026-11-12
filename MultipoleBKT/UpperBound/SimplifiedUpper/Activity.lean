/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.Series
public import MultipoleBKT.UpperBound.SimplifiedUpper.RouteLog.Absorption

/-!
# `|𝖪^{+,Z}_{ε₀}(X)|` as an expectation, and its pointwise bound (Lemmas 5.35–5.37)

The paper: Definition 5.15 and
the proofs of Lemmas 5.35–5.37.

* `abs_plusActivity_le_integral`: for `|X| ≥ 2`, the series of Definition 5.15 has finitely many
  nonzero terms (the groups `Xₗ` have at least two blocks, so there are at most `|X|` of them), and
  `|𝖪^{+,Z}_{ε₀}(X)| ≤ 𝔼_{𝖯^{+,ε₀,Z}_X}[actSum]`, with
  `actSum = ∑_{V^∞ ⊆ V_X} ∑_{n ≤ |X|} (1/n!) ∑_{X₁, …, Xₙ} parAbsSum` (Corollary 5.24).
* `pointwise_le`: on the support of `μ_{β,λ,ε₀}^{⊗ V_X}`,
  `(∏_{S ∈ X} 𝖬-weight of S) · actSum ≤ K^{|V_X|} · majSum`, where `majSum` is the series of the
  integrands of `J_{large,C₀}` without the densities `e^{β g_λ} 𝟙_{r ≤ ε₀ R̄}` (Lemmas 5.35–5.37:
  `parAbsSum_le`, `sum_tuples_inner_le`, `innerSeries_le_tuples`), `C₀ = 2 C₁ C_p + 2` depending
  only on `χ`, `β`, `p(β)`, and `K` on `χ`, `p₀`, `β`, `M`, `L`.
  The extra `1/M` is the absorption of `Λ(X)` in the proof of Lemma 4.57 before the log-free
  series is merged and before integration.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Hierarchical Multipole SetPartition AbsoluteLower Parity BoundedUpper

/-! ### The reduced series -/

section Defs

open scoped Classical

/-- `∑_{U ⊆ V_X} ∑_{n ≤ |X|} (1/n!) ∑_{(Xₗ) ∈ tuplesT X n} parAbsSum X (Xₗ) U`. -/
noncomputable def actSum (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (s : ℂ × ℂ → ℝ)
    (X : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ U ∈ (X.biUnion id).powerset, ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ tuplesT X n, parAbsSum β w M lam s X Xs U c

/-- The series of the integrands of `J_{large,C₀}` without the dipole densities:
`∑_{n ≤ |X|} (1/n!) ∑_{(Xₗ)} ∑_{(Tₗ^a)} ∑_{T^b} treeProd ∏_{S ∈ X} 𝟙_{𝓑_S}
∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{C₀/M}`. -/
noncomputable def majSum (M lam ε₀ R C₀ : ℝ) (X : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
      ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
        treeProd M lam ε₀ R Xs Ta Tb c *
          (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
          ∏ i ∈ X.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)

theorem majSum_nonneg {M lam ε₀ R C₀ : ℝ} (X : Finset (Finset ℕ)) {c : ℕ → ℂ × ℂ}
    (hc : ∀ i ∈ X.biUnion id, 0 ≤ ε₀ * R / ‖(c i).1 - (c i).2‖) :
    0 ≤ majSum M lam ε₀ R C₀ X c := by
  unfold majSum
  refine sum_nonneg fun n _ => mul_nonneg (by positivity) (sum_nonneg fun Xs _ =>
    sum_nonneg fun Ta _ => sum_nonneg fun Tb _ => mul_nonneg (mul_nonneg
      (treeProd_nonneg _ _ _ _ _ _ _ _) (prod_nonneg fun S _ => by split_ifs <;> norm_num))
      (prod_nonneg fun i hi => Real.rpow_nonneg (hc i hi) _))

end Defs

/-! ### The activity as an expectation -/

section Activity

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}
variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

open scoped Classical in
/-- **`|𝖪^{+,Z}_{ε₀}(X)|` is at most the expectation of the reduced series** (Definition 5.15 with
Corollary 5.24). -/
theorem abs_plusActivity_le_integral (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) :
    |plusActivity χ N p₀ β lam M ε₀ L V Z X| ≤
      ∫ y, actSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X
        (extendConfig (X.biUnion id) y) ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  set W := X.biUnion id with hW
  set A : Finset ℕ → ∀ {n : ℕ}, (Fin n → Finset (Finset ℕ)) → ℝ := fun U {n} Xs =>
    ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
        ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F (extendConfig W y) *
          ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig W y i)
          ∂plusModel χ N p₀ β lam M ε₀ L V Z X with hA
  -- the groups have at least two blocks
  have hT : ∀ U n, ∑ Xs ∈ tuplesD X n, A U Xs = ∑ Xs ∈ tuplesT X n, A U Xs := by
    intro U n
    refine (sum_subset (tuplesT_subset_tuplesD X n) fun Xs hD hT => ?_).symm
    have hne : ∃ l, (Xs l).card ≤ 1 := by
      by_contra h
      push Not at h
      exact hT (mem_tuplesT.2 ⟨fun l => mem_powerset.1 (Fintype.mem_piFinset.1
        (mem_filter.1 hD).1 l), (mem_filter.1 hD).2, fun l => h l⟩)
    obtain ⟨l, hl⟩ := hne
    have hemp : Fintype.piFinset (fun l => relEdgeSets (Xs l)) = ∅ :=
      Fintype.piFinset_eq_empty.2 ⟨l, relEdgeSets_eq_empty_of_card_le_one hl⟩
    simp only [hA, hemp, sum_empty]
  have hseries : ∀ U, ∑' n : ℕ, 1 / (n.factorial : ℝ) * ∑ Xs ∈ tuplesD X n, A U Xs =
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) * ∑ Xs ∈ tuplesT X n, A U Xs := by
    intro U
    simp_rw [hT U]
    exact (summable_and_tsum_eq_of_vanish (K := X.card) fun n hn => by
      simp only [tuplesT_eq_empty hn, sum_empty, mul_zero]).2
  have hact : plusActivity χ N p₀ β lam M ε₀ L V Z X =
      ∑ U ∈ W.powerset, ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ tuplesT X n, A U Xs := by
    rw [plusActivity, ite_eq_right (by omega)]
    exact sum_congr rfl fun U _ => hseries U
  rw [hact]
  -- the integral of the reduced series
  unfold actSum
  rw [integral_finsetSum _ fun U hU => integrable_finsetSum _ fun n _ =>
    (integrable_finsetSum _ fun Xs hXs => integrable_parAbsSum hχ hlam hε₀ hN
      (mem_tuplesT.1 hXs).1 (mem_powerset.1 hU)).const_mul _]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun U hU => ?_)
  rw [integral_finsetSum _ fun n _ => (integrable_finsetSum _ fun Xs hXs =>
    integrable_parAbsSum hχ hlam hε₀ hN (mem_tuplesT.1 hXs).1 (mem_powerset.1 hU)).const_mul _]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
  rw [integral_const_mul, abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [integral_finsetSum _ fun Xs hXs => integrable_parAbsSum hχ hlam hε₀ hN
    (mem_tuplesT.1 hXs).1 (mem_powerset.1 hU)]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Xs hXs => ?_)
  obtain ⟨hXs', hdisj, -⟩ := mem_tuplesT.1 hXs
  exact abs_sum_integral_le hχ hlam hε₀ hN hM hX hXs' hdisj (mem_powerset.1 hU)

end Activity

/-! ### The pointwise bound -/

section Pointwise

open scoped Classical

/-- The reduced series from the bound of its terms (internal): if every `parAbsSum` is at most
`K^{|V_X|} Rad ∑_{T^b} ∏ b^abs ∏ₗ 𝒰(Xₗ)`, then
`actSum ≤ (4K)^{|V_X|} Rad ∑_{n ≤ |X|} (1/n!) ∑ ∑ ∑ treeProd`. -/
theorem actSum_le_of {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (c : ℕ → ℂ × ℂ) {K Rad ε₀ R : ℝ}
    (hK : 0 ≤ K) (hRad : 0 ≤ Rad)
    (hpar : ∀ U ⊆ X.biUnion id, ∀ n, ∀ Xs ∈ tuplesT X n, parAbsSum β w M lam s X Xs U c ≤
      K ^ (X.biUnion id).card * Rad * treeWeightB M lam ε₀ R c X (univ.image Xs) *
        ∏ l, innerSeries M lam ε₀ R c (Xs l)) :
    actSum β w M lam s X c ≤ (4 * K) ^ (X.biUnion id).card * Rad *
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)), treeProd M lam ε₀ R Xs Ta Tb c := by
  set k := (X.biUnion id).card with hk
  set S1 := ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ tuplesT X n, treeWeightB M lam ε₀ R c X (univ.image Xs) *
      ∏ l, innerSeries M lam ε₀ R c (Xs l) with hS1
  set S2 := ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
      ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)), treeProd M lam ε₀ R Xs Ta Tb c with hS2
  have hXk : X.card ≤ k := Finset.card_le_card_biUnion hX.2 hX.1
  have hS1le : S1 ≤ 2 ^ k * S2 := by
    have hI := innerSeries_nonneg M lam ε₀ R c X
    refine (sum_tuples_inner_le hX c).trans ?_
    calc (2 : ℝ) ^ X.card * innerSeries M lam ε₀ R c X ≤ 2 ^ k * innerSeries M lam ε₀ R c X :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hXk) hI
      _ ≤ 2 ^ k * S2 := mul_le_mul_of_nonneg_left (innerSeries_le_tuples c) (by positivity)
  have hU : ∀ U ∈ (X.biUnion id).powerset, ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ tuplesT X n, parAbsSum β w M lam s X Xs U c ≤ K ^ k * Rad * S1 := by
    intro U hU
    calc ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ tuplesT X n, parAbsSum β w M lam s X Xs U c
        ≤ ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ tuplesT X n, K ^ k * Rad * (treeWeightB M lam ε₀ R c X (univ.image Xs) *
            ∏ l, innerSeries M lam ε₀ R c (Xs l)) :=
          sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (sum_le_sum fun Xs hXs =>
            (hpar U (mem_powerset.1 hU) n Xs hXs).trans_eq (by ring)) (by positivity)
      _ = K ^ k * Rad * S1 := by
          rw [hS1, mul_sum]
          refine sum_congr rfl fun n _ => ?_
          rw [← mul_sum]
          ring
  unfold actSum
  refine (sum_le_sum hU).trans ?_
  rw [sum_const, card_powerset, nsmul_eq_mul]
  have hKR : 0 ≤ K ^ k * Rad := mul_nonneg (pow_nonneg hK _) hRad
  calc ((2 ^ k : ℕ) : ℝ) * (K ^ k * Rad * S1) ≤ 2 ^ k * (K ^ k * Rad * (2 ^ k * S2)) := by
        push_cast
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS1le hKR) (by positivity)
    _ = (4 * K) ^ k * Rad * S2 := by
        rw [mul_pow, show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
        ring

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}

/-- **The weights of the blocks on the support**: `∏_{S ∈ X} (𝖬-weight of S) ≤ B^{|V_X|}
∏_{S ∈ X} 𝟙_{𝓑_S}` (`e^{-β v^Z} 𝟙_𝒜 ≤ C` and `e^{L r²/τ²} ≤ e^{16|L|}`). -/
theorem prod_blockWeight_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (p₀ : ℕ) (L : ℝ) :
    ∃ Bw : ℝ, 1 ≤ Bw ∧ ∀ {M : ℝ}, (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ {N : ℕ} (lam ε₀ : ℝ)
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ {X : Finset (Finset ℕ)}, IsSubpartition X →
      (∀ S ∈ X, S.card ≤ pBeta p₀ β) → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i)) →
      ∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c ≤
        Bw ^ (X.biUnion id).card *
          ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
  obtain ⟨Cs, -, hstab⟩ := stableWeightZ_le hχ β hβ0
  set Cs' := max Cs 1 with hCs'
  have hCs'1 : 1 ≤ Cs' := le_max_right _ _
  set Ew := Real.exp (16 * |L|) with hEw
  have hEw1 : 1 ≤ Ew := Real.one_le_exp (by positivity)
  refine ⟨Cs' ^ pBeta p₀ β * Ew, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCs'1) hEw1,
    fun {M} hMp {N} lam ε₀ V Z hlam hlamh hVZ {X} hX hXp c hc => ?_⟩
  have hblock : ∀ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c ≤
      (Cs' ^ pBeta p₀ β * Ew) ^ B.card *
        (if ConnOn B (linkedPairs M lam c B) then (1 : ℝ) else 0) := by
    intro B hB
    have hBX : B ⊆ X.biUnion id := subset_biUnion_of_mem id hB
    unfold blockWeightOf
    by_cases hconn : ConnOn B (linkedPairs M lam c B)
    · rw [ite_eq_left hconn, one_mul, mul_one, mul_pow]
      refine mul_le_mul ?_ ?_ (prod_nonneg fun i _ => dipoleWeightZ_nonneg _)
        (pow_nonneg (pow_nonneg (by linarith) _) _)
      · have hcard : (pairsOn B).card ≤ pBeta p₀ β * B.card := by
          unfold pairsOn
          refine (card_filter_le _ _).trans ?_
          rw [card_product]
          exact Nat.mul_le_mul_right _ (hXp B hB)
        calc ∏ p ∈ pairsOn B, stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V Z) (c p.1) (c p.2)
            ≤ ∏ _p ∈ pairsOn B, Cs' :=
              prod_le_prod₀ (fun p _ => stableWeight_nonneg _ _ _ _) fun p hp => by
                obtain ⟨h1, h2, -⟩ := mem_pairsOn.1 hp
                exact (hstab p₀ lam M ε₀ V Z hlam hlamh hMp hVZ _ _ (hc _ (hBX h1))
                  (hc _ (hBX h2))).trans (le_max_left _ _)
          _ = Cs' ^ (pairsOn B).card := prod_const _
          _ ≤ Cs' ^ (pBeta p₀ β * B.card) := pow_le_pow_right₀ hCs'1 hcard
          _ = (Cs' ^ pBeta p₀ β) ^ B.card := pow_mul _ _ _
      · calc ∏ i ∈ B, dipoleWeightZ p₀ β lam M ε₀ L V Z (c i) ≤ ∏ _i ∈ B, Ew :=
              prod_le_prod₀ (fun i _ => dipoleWeightZ_nonneg _) fun i hi =>
                BoundedUpper.dipoleWeightZ_le hlam hlamh hMp hVZ L (hc i (hBX hi)).norm_le
          _ = Ew ^ B.card := prod_const _
    · rw [ite_eq_right hconn, zero_mul, zero_mul, mul_zero]
  refine (prod_le_prod₀ (fun B _ =>
    blockWeightOf_nonneg M lam (fun _ => dipoleWeightZ_nonneg _) B c)
    hblock).trans (le_of_eq ?_)
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, card_biUnion hX.2]
  rfl

open scoped Classical in
/-- **The pointwise bound** (Lemmas 5.35–5.37): see the module docstring. -/
theorem pointwise_le (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) (L : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {M : ℝ}, 20 < M → (3 : ℝ) ^ pBeta p₀ β ≤ M → ∃ Kf : ℝ, 1 ≤ Kf ∧
      ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ pBeta p₀ β) →
      ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, c i ∈ supportSet N p₀ β lam ε₀ ∧
        0 < ‖(c i).1 - (c i).2‖) →
      (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
          actSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X c ≤
        Kf ^ (X.biUnion id).card * majSum M lam ε₀ (truncationScale p₀ β lam) C₀ X c := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨C₁, hC₁, C₂, hC₂, Q, hQ, Cp, hCp, C₃, hC₃, hpt⟩ := parAbsSum_le hχ p₀ β
  obtain ⟨Bw, hBw, hbw⟩ := prod_blockWeight_le hχ hβ0 p₀ L
  have hC₀ : 0 < 2 * C₁ * Cp + 2 := by
    have : 0 ≤ C₁ * Cp := mul_nonneg (by linarith) hCp.le
    linarith
  refine ⟨2 * C₁ * Cp + 2, hC₀, fun {M} hM hMp => ?_⟩
  obtain ⟨CL, hCL, hlog⟩ := exists_radLogProduct_le (M := M) (by linarith)
  obtain ⟨Kp, hKp⟩ : ∃ Kp : ℝ,
      Kp = (2 * C₃ ^ 2 * outerConst' Cp Q M C₁ C₂ (compConst M (pBeta p₀ β))) * CL :=
    ⟨_, rfl⟩
  have hKp1 : 1 ≤ Kp := by
    have h1 : 1 ≤ outerConst' Cp Q M C₁ C₂ (compConst M (pBeta p₀ β)) := le_max_right _ _
    have h2 : 1 ≤ C₃ ^ 2 := one_le_pow₀ hC₃
    rw [hKp]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by nlinarith) h1) hCL
  refine ⟨4 * Bw * Kp, by nlinarith, fun {N} lam ε₀ V Z hlam hlamh hVZ {X} hX hXp c hc => ?_⟩
  set W := X.biUnion id with hW
  set R := truncationScale p₀ β lam with hR
  have hrad0 : ∀ i ∈ W, 0 ≤ ε₀ * R / ‖(c i).1 - (c i).2‖ := fun i hi =>
    div_nonneg ((hc i hi).2.le.trans (hc i hi).1.2) (norm_nonneg _)
  have hRHS0 : 0 ≤ (4 * Bw * Kp) ^ W.card * majSum M lam ε₀ R (2 * C₁ * Cp + 2) X c :=
    mul_nonneg (pow_nonneg (by nlinarith) _) (majSum_nonneg X hrad0)
  have hact0 : 0 ≤ actSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (extSumZ χ p₀ β lam ε₀ V Z) X c := by
    unfold actSum
    exact sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (by positivity)
      (sum_nonneg fun _ _ => parAbsSum_nonneg _ _ _ _ _ _ _ _ _)
  -- the dipoles that are not good
  by_cases hgood : ∀ i ∈ W, IsGoodZ p₀ β lam M ε₀ V Z (c i)
  swap
  · push Not at hgood
    obtain ⟨i, hi, hng⟩ := hgood
    obtain ⟨B, hB, hiB⟩ := mem_biUnion_id.1 hi
    have h0 : blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
        (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c = 0 := by
      unfold blockWeightOf
      rw [prod_eq_zero hiB (by unfold dipoleWeightZ; rw [ite_eq_right hng, mul_zero]), mul_zero]
    rw [prod_eq_zero hB h0, zero_mul]
    exact hRHS0
  have hsupp : ∀ i ∈ W, OnSupportZ p₀ β lam M ε₀ V Z (c i) := fun i hi =>
    ⟨(hc i hi).1, hgood i hi⟩
  have hbw' := hbw hMp lam ε₀ V Z hlam hlamh hVZ hX hXp c hsupp
  have hbw0 : 0 ≤ ∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c :=
    prod_nonneg fun B _ => blockWeightOf_nonneg M lam (fun _ => dipoleWeightZ_nonneg _) B c
  -- the blocks that are not linked
  by_cases hconn : ∀ S ∈ X, ConnOn S (linkedPairs M lam c S)
  swap
  · push Not at hconn
    obtain ⟨S, hS, hnc⟩ := hconn
    have h0 : ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) = 0 :=
      prod_eq_zero hS (ite_eq_right hnc)
    rw [h0, mul_zero] at hbw'
    rw [le_antisymm hbw' hbw0, zero_mul]
    exact hRHS0
  have hConn1 : ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) = 1 :=
    prod_eq_one fun S hS => ite_eq_left (hconn S hS)
  rw [hConn1, mul_one] at hbw'
  -- the reduced series
  set Rad := ∏ i ∈ W, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((2 * C₁ * Cp + 2) / M) with hRad
  have hRad0 : 0 ≤ Rad := prod_nonneg fun i hi => Real.rpow_nonneg (hrad0 i hi) _
  have hA := actSum_le_of (β := β) (w := interactionGoodZ χ p₀ β lam ε₀ V Z) (M := M)
    (lam := lam) (s := extSumZ χ p₀ β lam ε₀ V Z) (ε₀ := ε₀) (R := R) hX c (K := Kp)
    (by linarith) hRad0 fun U hU n Xs hXs => by
      obtain ⟨hXs', hdisj, h2⟩ := mem_tuplesT.1 hXs
      rw [hKp]
      have hraw := hpt hM hMp lam ε₀ V Z hlam hlamh hVZ hX hXp hXs' hdisj h2 hU c
        (fun i hi => ⟨hsupp i hi, (hc i hi).2⟩) hconn
      have hl := hlog W c ε₀ R (2 * C₁ * Cp + 1)
        (fun i hi => ⟨(hc i hi).2, (hc i hi).1.2⟩)
      have hbase0 : 0 ≤ 2 * C₃ ^ 2 * outerConst' Cp Q M C₁ C₂ (compConst M (pBeta p₀ β)) := by
        have : 0 ≤ outerConst' Cp Q M C₁ C₂ (compConst M (pBeta p₀ β)) :=
          zero_le_one.trans (le_max_right _ _)
        positivity
      have hI0 : 0 ≤ ∏ l, innerSeries M lam ε₀ R c (Xs l) :=
        prod_nonneg fun l _ => innerSeries_nonneg _ _ _ _ _ _
      refine hraw.trans (le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (pow_nonneg hbase0 _))
          (treeWeightB_nonneg M lam ε₀ R c X (univ.image Xs))) hI0) (le_of_eq ?_))
      dsimp [Rad, W, R]
      rw [mul_pow]
      ring_nf

  have hmaj : majSum M lam ε₀ R (2 * C₁ * Cp + 2) X c = Rad *
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)), treeProd M lam ε₀ R Xs Ta Tb c := by
    unfold majSum
    rw [mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_left_comm]
    congr 1
    rw [mul_sum]
    refine sum_congr rfl fun Xs _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun Ta _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun Tb _ => ?_
    rw [hConn1, hRad]
    ring
  rw [hmaj]
  calc (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
        actSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X c
      ≤ Bw ^ W.card * ((4 * Kp) ^ W.card * Rad *
        ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
          ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
            ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
              treeProd M lam ε₀ R Xs Ta Tb c) :=
        mul_le_mul hbw' hA hact0 (pow_nonneg (by linarith) _)
    _ = _ := by
        rw [mul_pow, mul_pow]
        ring

end Pointwise

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
