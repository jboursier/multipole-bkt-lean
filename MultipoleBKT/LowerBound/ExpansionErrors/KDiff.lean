/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.ActivityDiff

/-!
# Fixed normalization and expectation errors, then activity errors

The proof of Proposition 4.24, especially (4.80), (4.79) and (4.81).

`fixed_minus_errors_of_lemma_A8` and `fixed_zero_errors_of_lemma_A8`
prove the fixed normalization and expectation-difference estimates for
`M > 20`. The block products are telescoped with the maximum block size.
The total-size power in (4.80) is retained through multiplication by the
reciprocal error, then its quotient with the maximum-block power is
bounded by one. The two fixed errors are added. The activity theorems
then sum these expectation estimates using only finite counting.
Their existential bounds take `M₀ = 21`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open TwoComponentCoulomb (box)
open Hierarchical Limits Multipole SetPartition MultipoleIntegral

variable {χ : ℂ → ℝ} {β : ℝ}

/-- The blocks of a subpartition `X` with `|V_X| = k` have `1 ≤ |S| ≤ k`. -/
theorem card_block_mem {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {S : Finset ℕ}
    (hS : S ∈ X) : 1 ≤ S.card ∧ S.card ≤ (X.biUnion id).card :=
  ⟨card_pos.2 (hX.1 S hS), card_le_card (subset_biUnion_of_mem id hS)⟩

open scoped Classical in
/-- Internal fixed-term version of (4.81) and the expectation-difference
display in Proposition 4.24. See the proof of Proposition 4.24. For every `M > 20`, the two inputs from Lemma A.7 and the block
comparisons give both estimates for every valid fixed datum. The coefficient
is uniform in that datum and in the label values. -/
theorem fixed_minus_errors_of_lemma_A8 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (L : ℝ) (p₀ : ℕ) (M : ℝ) (hM20 : 20 < M) :
      LemmaA8MinusStatement χ β M L p₀ k → LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            ∀ n (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
              (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
              ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
              ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
                |zeroClusterIntegralInf χ N β lam M X Xs Es F| *
                    |(∏ S ∈ X, multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S)⁻¹ -
                      (∏ S ∈ X, multipoleIntegral χ N β lam M S)⁻¹| ≤
                  C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                    ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) ∧
                |clusterExpectation (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
                      (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) (gaussianWeight p₀ β lam ε₀ L) M lam X Xs Es F -
                    clusterExpectation (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam)
                      (fun _ => 1) M lam X Xs Es F| ≤
                  C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                    ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  intro hA8 hA8b ε₀ hε₀ hε₁
  obtain ⟨CK, hCK, hborn⟩ := bornI2 hχ hβ (by linarith : 1 ≤ M) k hkp
  obtain ⟨A₁, hA₁, l₁, hl₁, hA⟩ := hA8 ε₀ hε₀ hε₁
  obtain ⟨A₂, hA₂, l₂, hl₂, hB⟩ := hA8b ε₀ hε₀ hε₁
  obtain ⟨CB, hCB, lB, hlB, -, hblk⟩ := minus_blocks hχ hβ hkp hM20 L p₀ ε₀ hε₀ hε₁
  obtain ⟨Cn, -, ln, hln, hln1, hnorm⟩ := normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨((A₁ + A₂) * (2 / Z) ^ k * CB ^ k + CK * (2 / Z) ^ k * (CB ^ k * (k * CB))),
    by positivity, min (min (min (1 : ℝ) l₁) (min l₂ lB)) ln,
    lt_min (lt_min (lt_min one_pos hl₁) (lt_min hl₂ hlB)) hln, (min_le_right _ _).trans hln1,
    fun lam hlam hlt => ?_⟩
  have hlt₁ : lam < l₁ := hlt.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hlt₂ : lam < l₂ := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hltB : lam < lB := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hltn : lam < ln := hlt.trans_le (min_le_right _ _)
  have hlam1 : lam ≤ 1 := (hltn.trans_le hln1).le
  obtain ⟨N₁, hN₁⟩ := hA lam hlam hlt₁
  obtain ⟨N₂, hN₂⟩ := hB lam hlam hlt₂
  obtain ⟨NB, hNB⟩ := hblk lam hlam hltB
  obtain ⟨Nn, hNn⟩ := hnorm lam hlam hltn
  refine ⟨max (max (max 1 N₁) (max N₂ NB)) Nn, fun N hN X hX hXN hX1 hXk => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hN
  have hNB' : NB ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hN
  have hNn' : Nn ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, h2l, hCe, -, hC, -, -⟩ := hNn N hNn'
  have h2 : 2 ≤ X.card := hX1
  have hlamR : lam ≤ ε₀ * truncationScale p₀ β lam := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ0 : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hCe0 : 0 < cutoffDipoleNormalization χ N p₀ β lam ε₀ := lt_of_lt_of_le (by positivity) hCe
  have hC' : Z / 2 * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam := by linarith
  intro n Xs hXs hdisj Es hEs F hF
  have h := internal_fixed_errors_of_blocks (M := M) hχ hlam hN1 (by linarith) hX h2 hXk
    (modelHyp_minus hχ hlam β hε₀ hN1 hlamR L)
    (a := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹)
    (inv_pos.2 (mul_pos hNpos hCe0)) (dens := cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam))
    (I₁ := fun S => multipoleIntegralMinus χ N β lam M L ε₀ (truncationScale p₀ β lam) S)
    (fun S _ => by
      have := BoundedLowerEps.minusPartitionFunction_singleton_eq (p₀ := p₀) (β := β) (M := M)
        (L := L) hχ hlam hε₀ hN1 S
      rwa [minusPartitionFunction, Finset.prod_singleton] at this)
    (fun Φ hΦ hdep => integral_labelField_cutoff hχ hlam β hε₀ hN1 hΦ hdep) hCB
    (pow_pos hlam _)
    (fun S hS => blockComparison_max hS hlam hlam1
      (hNB N hNB' S (card_block_mem hX hS).1 (hXk ▸ (card_block_mem hX hS).2)))
    hXs hEs hF (D := A₁ + A₂) (by positivity) hCK.le hZ hC'
    (by
      have e₁ := hN₁ N hN₁' X hX hXN h2 hXk n Xs hXs hdisj Es hEs F hF
      have e₂ := hN₂ N hN₂' X hX hXN h2 hXk n Xs hXs hdisj Es hEs F hF
      calc |clusterIntegral N β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
              (gaussianWeight p₀ β lam ε₀ L) (cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam))
              M lam X Xs Es F - zeroClusterIntegralInf χ N β lam M X Xs Es F|
          ≤ |minusClusterIntegral χ N p₀ β lam M ε₀ L X Xs Es F -
                zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F| +
              |zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F -
                zeroClusterIntegralInf χ N β lam M X Xs Es F| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add e₁ e₂
        _ = _ := by ring)
    (by positivity)
    (total_power_le_max_block_power hXk hlam hlam1)
    (hborn lam hlam N hN1 X hX h2 hXk Xs hXs hdisj Es hEs F hF)
  have hP : 0 < ∏ S ∈ X, multipolePartitionFunction χ N β lam M S :=
    prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β (by linarith) hN1 (hX.1 S hS)
  refine ⟨?_, h.2.2⟩
  apply h.2.1.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha : 0 ≤ (A₁ + A₂) * (2 / Z) ^ k * CB ^ k := by positivity
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha)
    (Real.rpow_nonneg (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ))

open scoped Classical in
/-- The activity error obtained by summing the fixed expectation differences.
proof of Proposition 4.24. -/
theorem internal_K_diff_at_M_of_lemma_A8 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (L : ℝ) (p₀ : ℕ) (M : ℝ) (hM20 : 20 < M) :
      LemmaA8MinusStatement χ β M L p₀ k → LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  intro hA8 hA8b ε₀ hε₀ hε₁
  obtain ⟨C, hC, lam₀, hlam₀, hlam₁, hf⟩ :=
    fixed_minus_errors_of_lemma_A8 hχ hβ hk hkp L p₀ M (by linarith) hA8 hA8b ε₀ hε₀ hε₁
  have hcount : (0 : ℝ) < countBound k := by unfold countBound; positivity
  refine ⟨countBound k * C, by positivity, lam₀, hlam₀, hlam₁, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hf lam hlam hlt
  refine ⟨N₀, fun N hN X hX hXN h2 hXk => ?_⟩
  have hx := hN₀ N hN X hX hXN h2 hXk
  have hP : 0 < ∏ S ∈ X, multipolePartitionFunction χ N β lam M S :=
    prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β
      (by linarith : 0 < M) (by
        obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (X.biUnion id).card)
        have := mem_range.1 (hXN hi)
        omega) (hX.1 S hS)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hbound := internal_activity_diff_of_fixed_expectations hX h2 hXk
    (D := C * truncationScale p₀ β lam ^ (-2 : ℝ) /
      ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)))
    (by positivity)
    (fun n Xs hXs hdisj Es hEs F hF => (hx n Xs hXs hdisj Es hEs F hF).2)
  exact hbound.trans_eq (by ring)

open scoped Classical in
/-- The existential activity-error bound, with `M₀ = 21`.
proof of Proposition 4.24. -/
theorem eq_K_diff_of_lemma_A8 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (L : ℝ) (p₀ : ℕ) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      LemmaA8MinusStatement χ β M L p₀ k → LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |minusActivity χ N p₀ β lam M ε₀ L X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  refine ⟨21, by norm_num, fun M hM => ?_⟩
  exact internal_K_diff_at_M_of_lemma_A8 hχ hβ hk hkp L p₀ M (by linarith)

open scoped Classical in
/-- Internal fixed-term normalization and expectation errors for the zero
model. See the proof of Proposition 4.24.
Use (A.47) in the block comparison and (A.50) in the numerator.
The range is every `M > 20`, with coefficients uniform in the fixed datum. -/
theorem fixed_zero_errors_of_lemma_A8 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (p₀ : ℕ) (M : ℝ) (hM20 : 20 < M) : LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            ∀ n (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
              (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
              ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
              ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
                |zeroClusterIntegralInf χ N β lam M X Xs Es F| *
                    |(∏ S ∈ X, multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S)⁻¹ -
                      (∏ S ∈ X, multipoleIntegral χ N β lam M S)⁻¹| ≤
                  C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                    ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) ∧
                |clusterExpectation (cutoffDipoleMeasure χ N p₀ β lam ε₀) β
                      (dipoleInteraction χ lam) (fun _ => 1) M lam X Xs Es F -
                    clusterExpectation (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam)
                      (fun _ => 1) M lam X Xs Es F| ≤
                  C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                    ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  intro hA8b ε₀ hε₀ hε₁
  obtain ⟨CK, hCK, hborn⟩ := bornI2 hχ hβ (by linarith : 1 ≤ M) k hkp
  obtain ⟨A₂, hA₂, l₂, hl₂, hB⟩ := hA8b ε₀ hε₀ hε₁
  obtain ⟨CB, hCB, lB, hlB, -, hblk⟩ := zero_blocks hχ hβ hkp hM20 p₀ ε₀ hε₀ hε₁
  obtain ⟨Cn, -, ln, hln, hln1, hnorm⟩ := normalization_bounds hχ hβ p₀ ε₀ hε₀ hε₁
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨(A₂ * (2 / Z) ^ k * CB ^ k + CK * (2 / Z) ^ k * (CB ^ k * (k * CB))),
    by positivity, min (min (1 : ℝ) (min l₂ lB)) ln,
    lt_min (lt_min one_pos (lt_min hl₂ hlB)) hln, (min_le_right _ _).trans hln1,
    fun lam hlam hlt => ?_⟩
  have hlt₂ : lam < l₂ := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hltB : lam < lB := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hltn : lam < ln := hlt.trans_le (min_le_right _ _)
  have hlam1 : lam ≤ 1 := (hltn.trans_le hln1).le
  obtain ⟨N₂, hN₂⟩ := hB lam hlam hlt₂
  obtain ⟨NB, hNB⟩ := hblk lam hlam hltB
  obtain ⟨Nn, hNn⟩ := hnorm lam hlam hltn
  refine ⟨max (max 1 (max N₂ NB)) Nn, fun N hN X hX hXN hX1 hXk => ?_⟩
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hN
  have hNB' : NB ≤ N := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hN
  have hNn' : Nn ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, h2l, hCe, -, hC, -, -⟩ := hNn N hNn'
  have h2 : 2 ≤ X.card := hX1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ0 : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hCe0 : 0 < cutoffDipoleNormalization χ N p₀ β lam ε₀ := lt_of_lt_of_le (by positivity) hCe
  have hC' : Z / 2 * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam := by linarith
  intro n Xs hXs hdisj Es hEs F hF
  have h := internal_fixed_errors_of_blocks (M := M) hχ hlam hN1 (by linarith) hX h2 hXk
    (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN1)
    (a := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹)
    (inv_pos.2 (mul_pos hNpos hCe0)) (dens := cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam))
    (I₁ := fun S => multipoleIntegralCut χ N β lam M (ε₀ * truncationScale p₀ β lam) S)
    (fun S _ => by
      have := zeroPartitionFunction_singleton_eq (p₀ := p₀) (β := β) (M := M) hχ hlam hε₀ hN1 S
      rwa [zeroPartitionFunction, Finset.prod_singleton] at this)
    (fun Φ hΦ hdep => integral_labelField_cutoff hχ hlam β hε₀ hN1 hΦ hdep) hCB
    (pow_pos hlam _)
    (fun S hS => blockComparison_max hS hlam hlam1
      (hNB N hNB' S (card_block_mem hX hS).1 (hXk ▸ (card_block_mem hX hS).2)))
    hXs hEs hF (D := A₂) (by positivity) hCK.le hZ hC'
    (by
      have e₂ := hN₂ N hN₂' X hX hXN h2 hXk n Xs hXs hdisj Es hEs F hF
      exact e₂.trans_eq (by ring))
    (by positivity)
    (total_power_le_max_block_power hXk hlam hlam1)
    (hborn lam hlam N hN1 X hX h2 hXk Xs hXs hdisj Es hEs F hF)
  have hP : 0 < ∏ S ∈ X, multipolePartitionFunction χ N β lam M S :=
    prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β (by linarith) hN1 (hX.1 S hS)
  refine ⟨?_, h.2.2⟩
  apply h.2.1.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha : 0 ≤ A₂ * (2 / Z) ^ k * CB ^ k := by positivity
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha)
    (Real.rpow_nonneg (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam).le (-2 : ℝ))

open scoped Classical in
/-- The activity error obtained by summing the fixed expectation differences.
proof of Proposition 4.24. -/
theorem internal_K_diff0_at_M_of_lemma_A8 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (p₀ : ℕ) (M : ℝ) (hM20 : 20 < M) : LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  intro hA8b ε₀ hε₀ hε₁
  obtain ⟨C, hC, lam₀, hlam₀, hlam₁, hf⟩ :=
    fixed_zero_errors_of_lemma_A8 hχ hβ hk hkp p₀ M (by linarith) hA8b ε₀ hε₀ hε₁
  have hcount : (0 : ℝ) < countBound k := by unfold countBound; positivity
  refine ⟨countBound k * C, by positivity, lam₀, hlam₀, hlam₁, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hf lam hlam hlt
  refine ⟨N₀, fun N hN X hX hXN h2 hXk => ?_⟩
  have hx := hN₀ N hN X hX hXN h2 hXk
  have hP : 0 < ∏ S ∈ X, multipolePartitionFunction χ N β lam M S :=
    prod_pos fun S hS => multipolePartitionFunction_pos hχ hlam β
      (by linarith : 0 < M) (by
        obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (X.biUnion id).card)
        have := mem_range.1 (hXN hi)
        omega) (hX.1 S hS)
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have hbound := internal_activity_diff_of_fixed_expectations hX h2 hXk
    (D := C * truncationScale p₀ β lam ^ (-2 : ℝ) /
      ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)))
    (by positivity)
    (fun n Xs hXs hdisj Es hEs F hF => (hx n Xs hXs hdisj Es hEs F hF).2)
  exact hbound.trans_eq (by ring)

open scoped Classical in
/-- The existential activity-error bound, with `M₀ = 21`.
proof of Proposition 4.24. -/
theorem eq_K_diff0_of_lemma_A8 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 2 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (p₀ : ℕ) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  refine ⟨21, by norm_num, fun M hM => ?_⟩
  exact internal_K_diff0_at_M_of_lemma_A8 hχ hβ hk hkp p₀ M (by linarith)

end ExpansionErrors

end MultipoleBKT

end
