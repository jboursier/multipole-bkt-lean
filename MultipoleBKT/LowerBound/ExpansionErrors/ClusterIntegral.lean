/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.Normalization
public import MultipoleBKT.LowerBound.BoundedLowerEps.Activity

/-!
# Fixed cluster integrals and their hierarchical expectations

The proof of Proposition 4.24, and (A.48), Section A.4.

The three cluster integrals are the literal box integrals of the minus,
truncated zero and infinite-cutoff zero models. The fixed density identity
`prod_mul_clusterExpectation_eq` cancels their dipole normalizations before
comparison. `clusterSum` is the finite sum over the data of Definition 4.15.
`abs_clusterSum_le` counts these data only after a bound on each fixed
expectation difference has been proved.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open TwoComponentCoulomb (box)
open Hierarchical Limits Multipole SetPartition

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-! ### The cluster integrals -/

open scoped Classical in
/-- The cluster integral of the model `(w, ψ)` with the dipole weight `dens`, for the data
`(X; X₁, …, Xₙ, E₁, …, Eₙ, F)`: `∫_{(Λ²)^{V_X}} (∏_{S ∈ X} bw_S) term(𝐗, 𝐄, F) ∏_i dens`. -/
noncomputable def clusterIntegral (N : ℕ) (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ)
    (dens : ℂ × ℂ → ℝ) (M lam : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) : ℝ :=
  ∫ y in boxConfig (X.biUnion id) N,
    (∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)) *
      clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) * ∏ i, dens (y i)

/-- **`I^-_{cl,ε₀}(X; 𝐗, 𝐄, F)`** (proof of Proposition 4.24): the cluster integral of the lower-bound
model, `w = ṽ` (screening radius `8 ε₀ R̄`), `ψ = e^{-L r²/(ε₀ R̄)²}`, with the dipole weight
`e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄}`. This is `I_{cl,ε₀}(X; 𝐗, 𝐄, F; ṽ, τ̃, -64L, ∅)` of
(A.48) (Section A.4). -/
noncomputable def minusClusterIntegral (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ L : ℝ)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) : ℝ :=
  clusterIntegral N β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam))
    (gaussianWeight p₀ β lam ε₀ L) (cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam)) M lam X
    Xs Es F

/-- **`I^0_{cl,ε₀}(X; 𝐗, 𝐄, F)`** (eq. (A.48), Section A.4, with
`(w, τ, L, Z) = (v, ∞, 0, ∅)`): the true interaction `v`, `ψ = 1`, with the dipole weight
`e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄}`. -/
noncomputable def zeroClusterIntegral (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ : ℝ)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) : ℝ :=
  clusterIntegral N β (dipoleInteraction χ lam) (fun _ => 1)
    (cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam)) M lam X Xs Es F

/-- **`I^0_{cl,∞}(X; 𝐗, 𝐄, F)`** (proof of Proposition 4.24): the true interaction `v`, `ψ = 1`, with
the dipole weight `e^{β g_λ(x - y)}` (no length cutoff). -/
noncomputable def zeroClusterIntegralInf (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) : ℝ :=
  clusterIntegral N β (dipoleInteraction χ lam) (fun _ => 1) (pairDensity χ β lam) M lam X Xs Es F

/-! ### The finite sum of Definition 4.15 -/

open scoped Classical in
/-- The finite sum of Definition 4.15 over the data
`(n; X₁, …, Xₙ; E₁, …, Eₙ; F)`, `n ≤ |X|`. -/
noncomputable def clusterSum (X : Finset (Finset ℕ))
    (f : ∀ n : ℕ, (Fin n → Finset (Finset ℕ)) → (Fin n → Finset (ℕ × ℕ)) → Finset (ℕ × ℕ) → ℝ) :
    ℝ :=
  ∑ n ∈ Finset.range (X.card + 1), 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F

theorem clusterSum_sub (X : Finset (Finset ℕ))
    (f g : ∀ n : ℕ, (Fin n → Finset (Finset ℕ)) → (Fin n → Finset (ℕ × ℕ)) → Finset (ℕ × ℕ) →
      ℝ) :
    clusterSum X f - clusterSum X g = clusterSum X fun n Xs Es F => f n Xs Es F - g n Xs Es F := by
  unfold clusterSum
  rw [← Finset.sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun Xs _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine sum_congr rfl fun Es _ => ?_
  rw [← Finset.sum_sub_distrib]

/-! ### From `ρ^{⊗ ℕ}` to box integrals -/

open scoped Classical in
/-- The integrand `(∏_{B ∈ X} bw_B) term` depends only on the labels of `V_X` and is
measurable. -/
theorem dependsOn_blockTerm {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} {X : Finset (Finset ℕ)}
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) {F : Finset (ℕ × ℕ)}
    (hF : F ⊆ interPairs (coarsen X (Finset.univ.image Xs))) :
    DependsOn (fun c => (∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
      clusterTerm β w M lam Xs Es F c) ((X.biUnion id : Finset ℕ) : Set ℕ) := by
  intro c c' hcc'
  simp only
  rw [dependsOn_clusterTerm β w M lam hXs hEs hF hcc']
  congr 1
  refine prod_congr rfl fun B hB => ?_
  exact (dependsOn_blockWeightOf (β := β) (w := w) (ψ := ψ) M lam B).mono
    (fun i hi => mem_coe.2 (mem_biUnion.2 ⟨B, hB, mem_coe.1 hi⟩)) hcc'

/-- **From `μ_{β,λ,ε₀}^{⊗ ℕ}` to box integrals**: for `Φ` measurable and depending only on the
labels of `U`, `∫ Φ dμ_{β,λ,ε₀}^{⊗ ℕ} = (N C_{β,λ,ε₀})^{-|U|} ∫_{(Λ²)^U} Φ(y) ∏_i e^{β g_λ}
𝟙_{r_i ≤ ε₀ R̄}`. -/
theorem integral_labelField_cutoff (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hε₀ : 0 < ε₀) (hN : 1 ≤ N) {U : Finset ℕ} {Φ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : Measurable Φ)
    (hdep : DependsOn Φ (U : Set ℕ)) :
    ∫ c, Φ c ∂labelField (cutoffDipoleMeasure χ N p₀ β lam ε₀) =
      ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^ U.card *
        ∫ y in boxConfig U N, Φ (extendConfig U y) *
          ∏ i, cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam) (y i) := by
  have := isProbabilityMeasure_cutoffDipoleMeasure (p₀ := p₀) hχ hlam β hε₀ hN
  rw [integral_labelField_eq_pi hΦ hdep, integral_pi_cutoffDipoleMeasure hχ hlam β hε₀ hN,
    Fintype.card_coe]

/-- **From `μ_{β,λ}^{⊗ ℕ}` to box integrals**: for `Φ` measurable and depending only on the
labels of `U`, `∫ Φ dμ_{β,λ}^{⊗ ℕ} = (N C_{β,λ})^{-|U|} ∫_{(Λ²)^U} Φ(y) ∏_i e^{β g_λ}`. -/
theorem integral_labelField_dipoleMeasure (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) {U : Finset ℕ} {Φ : (ℕ → ℂ × ℂ) → ℝ} (hΦ : Measurable Φ)
    (hdep : DependsOn Φ (U : Set ℕ)) :
    ∫ c, Φ c ∂labelField (dipoleMeasure χ N β lam) =
      ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ U.card *
        ∫ y in boxConfig U N, Φ (extendConfig U y) * ∏ i, pairDensity χ β lam (y i) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [integral_labelField_eq_pi hΦ hdep, integral_pi_dipoleMeasure hχ hlam β hN,
    Fintype.card_coe]

/-- The expectation of one fixed term under its hierarchical model.
proof of Proposition 4.24. -/
noncomputable def clusterExpectation (ρ : Measure (ℂ × ℂ)) (β : ℝ)
    (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)
    (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) : ℝ :=
  ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
    ∂modelHierarchical ρ β w ψ M lam X

/-! ### A fixed expectation in density form -/

/-- `∏_{S ∈ X} a^{|S|} f(S) = a^{|V_X|} ∏_{S ∈ X} f(S)` for a subpartition. -/
theorem prod_pow_card_mul {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (a : ℝ)
    (f : Finset ℕ → ℝ) :
    ∏ S ∈ X, (a ^ S.card * f S) = a ^ (X.biUnion id).card * ∏ S ∈ X, f S := by
  rw [prod_mul_distrib, prod_pow_eq_pow_sum, BoundedLowerEps.sum_card_eq hX]

open scoped Classical in
/-- The fixed expectation is its cluster numerator divided by the product
of the block integrals. See the proof of Proposition 4.24. -/
theorem prod_mul_clusterExpectation_eq {ρ : Measure (ℂ × ℂ)}
    {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)}
    (h : ModelHyp ρ β w ψ K) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {a : ℝ} (ha : a ≠ 0) {dens : ℂ × ℂ → ℝ} {I : Finset ℕ → ℝ}
    (hM : ∀ S ∈ X, modelPartitionFunction ρ β w ψ M lam S = a ^ S.card * I S)
    (hconv : ∀ Φ : (ℕ → ℂ × ℂ) → ℝ, Measurable Φ →
      DependsOn Φ ((X.biUnion id : Finset ℕ) : Set ℕ) →
      ∫ c, Φ c ∂labelField ρ = a ^ (X.biUnion id).card *
        ∫ y in boxConfig (X.biUnion id) N, Φ (extendConfig (X.biUnion id) y) * ∏ i, dens (y i))
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l))
    {F : Finset (ℕ × ℕ)} (hF : F ⊆ interPairs (coarsen X (univ.image Xs))) :
    (∏ S ∈ X, I S) *
        (∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
          ∂modelHierarchical ρ β w ψ M lam X) =
      clusterIntegral N β w ψ dens M lam X Xs Es F := by
  have key := h.prod_mul_integral_modelHierarchical (M := M) (lam := lam) (X := X)
    (f := fun y => clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y))
    ((measurable_clusterTerm β w M lam h Xs Es F).comp (measurable_extendConfig _))
  have hdep := dependsOn_clusterTerm β w M lam hXs hEs hF
  have key' : (∏ S ∈ X, modelPartitionFunction ρ β w ψ M lam S) *
      (∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X) =
      ∫ c, (∏ B ∈ X, blockWeightOf β w ψ M lam B c) * clusterTerm β w M lam Xs Es F c
        ∂labelField ρ := by
    rw [key]
    exact integral_congr_ae (Filter.Eventually.of_forall fun c => by
      simp only
      rw [apply_extendConfig_restrict hdep c])
  rw [prod_congr rfl hM, prod_pow_card_mul hX] at key'
  rw [hconv (fun c => (∏ B ∈ X, blockWeightOf β w ψ M lam B c) *
    clusterTerm β w M lam Xs Es F c) ((Finset.measurable_prod _ fun B _ => h.measurable_blockWeightOf M lam B).mul
    (measurable_clusterTerm β w M lam h Xs Es F)) (dependsOn_blockTerm hXs hEs hF)] at key'
  exact mul_left_cancel₀ (pow_ne_zero (X.biUnion id).card ha)
    (by simpa only [clusterIntegral, mul_assoc] using key')

/-! ### Counting the terms -/

/-- A bound on the number of terms of Definition 4.15 for `|V_X| = k`. -/
def countBound (k : ℕ) : ℕ := (k + 1) * (2 ^ k) ^ k * (2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2)

theorem pairsOn_mono {U U' : Finset ℕ} (h : U ⊆ U') : pairsOn U ⊆ pairsOn U' := by
  intro p hp
  rw [mem_pairsOn] at hp ⊢
  exact ⟨h hp.1, h hp.2.1, hp.2.2⟩

open scoped Classical in
theorem card_relEdgeSets_le {Y X : Finset (Finset ℕ)} (hY : Y ⊆ X) :
    (relEdgeSets Y).card ≤ 2 ^ ((X.biUnion id).card ^ 2) := by
  calc (relEdgeSets Y).card ≤ (interPairs Y).powerset.card := by
        unfold relEdgeSets; exact card_filter_le _ _
    _ = 2 ^ (interPairs Y).card := card_powerset _
    _ ≤ 2 ^ ((X.biUnion id).card ^ 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (interPairs Y).card ≤ (pairsOn (X.biUnion id)).card :=
              card_le_card (interPairs_subset_pairsOn.trans
                (pairsOn_mono (biUnion_subset_biUnion_of_subset_left id hY)))
          _ ≤ _ := BoundedLowerEps.card_pairsOn_le _

open scoped Classical in
theorem card_relEdgeSets₀_coarsen_le {X : Finset (Finset ℕ)} {G : Finset (Finset (Finset ℕ))}
    (hG : ∀ Y ∈ G, Y ⊆ X) :
    (relEdgeSets₀ (coarsen X G)).card ≤ 2 ^ ((X.biUnion id).card ^ 2) := by
  calc (relEdgeSets₀ (coarsen X G)).card ≤ (interPairs (coarsen X G)).powerset.card := by
        unfold relEdgeSets₀; exact card_filter_le _ _
    _ = 2 ^ (interPairs (coarsen X G)).card := card_powerset _
    _ ≤ 2 ^ ((X.biUnion id).card ^ 2) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        calc (interPairs (coarsen X G)).card ≤ (pairsOn ((coarsen X G).biUnion id)).card :=
              card_le_card interPairs_subset_pairsOn
          _ = (pairsOn (X.biUnion id)).card := by rw [biUnion_coarsen hG]
          _ ≤ _ := BoundedLowerEps.card_pairsOn_le _

/-- A subpartition has at most `|V_X|` blocks. -/
theorem card_le_card_biUnion {X : Finset (Finset ℕ)} (hX : IsSubpartition X) :
    X.card ≤ (X.biUnion id).card := by
  rw [← BoundedLowerEps.sum_card_eq hX]
  calc X.card = ∑ _S ∈ X, 1 := by rw [sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ S ∈ X, S.card := sum_le_sum fun S hS => card_pos.2 (hX.1 S hS)

open scoped Classical in
/-- **The number of terms is bounded in terms of `k = |V_X|`**: if `|f| ≤ D` on every term of
Definition 4.15, then `|clusterSum X f| ≤ countBound k · D`. -/
theorem abs_clusterSum_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {D : ℝ} (hD : 0 ≤ D)
    {f : ∀ n : ℕ, (Fin n → Finset (Finset ℕ)) → (Fin n → Finset (ℕ × ℕ)) → Finset (ℕ × ℕ) → ℝ}
    (hf : ∀ n (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), |f n Xs Es F| ≤ D) :
    |clusterSum X f| ≤ countBound (X.biUnion id).card * D := by
  set k := (X.biUnion id).card
  have hXk : X.card ≤ k := card_le_card_biUnion hX
  unfold clusterSum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.range (X.card + 1),
      |1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F| ≤
        ((2 ^ k) ^ k * (2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D := by
    intro n hn
    have hnk : n ≤ k := by rw [Finset.mem_range] at hn; omega
    have hfac : |1 / (n.factorial : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by exact_mod_cast n.factorial_pos)]
      exact_mod_cast n.factorial_pos
    rw [abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hfac).trans ?_
    refine (abs_sum_le_sum_abs _ _).trans ?_
    -- each `Xs`
    have hXs_card : ((Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))).card ≤ (2 ^ k) ^ k := by
      refine (card_filter_le _ _).trans ?_
      rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_powerset]
      calc (2 ^ X.card) ^ n ≤ (2 ^ k) ^ n :=
            Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hXk) n
        _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_right (pow_pos (by norm_num) _) hnk
    have hEs : ∀ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        |∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F| ≤
        ((2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D := by
      intro Xs hXs
      rw [Finset.mem_filter] at hXs
      have hXsX : ∀ l, Xs l ⊆ X := fun l =>
        Finset.mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)
      have hG : ∀ Y ∈ Finset.univ.image Xs, Y ⊆ X := fun Y hY => by
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
        exact hXsX l
      have hEs_card :
          (Fintype.piFinset (fun l => relEdgeSets (Xs l))).card ≤ (2 ^ (k ^ 2)) ^ k := by
        rw [Fintype.card_piFinset]
        calc ∏ l, (relEdgeSets (Xs l)).card ≤ ∏ _l : Fin n, 2 ^ (k ^ 2) :=
              Finset.prod_le_prod fun l _ => card_relEdgeSets_le (hXsX l)
          _ = (2 ^ (k ^ 2)) ^ n := by rw [prod_const, card_univ, Fintype.card_fin]
          _ ≤ (2 ^ (k ^ 2)) ^ k :=
              Nat.pow_le_pow_right (pow_pos (by norm_num) _) hnk
      refine (abs_sum_le_sum_abs _ _).trans ?_
      have hF : ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          |∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F| ≤
            (2 ^ (k ^ 2) : ℕ) * D := by
        intro Es hEs
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), |f n Xs Es F|
            ≤ ∑ _F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), D :=
              sum_le_sum fun F hF => hf n Xs hXsX hXs.2 Es hEs F hF
          _ = (relEdgeSets₀ (coarsen X (Finset.univ.image Xs))).card * D := by
              rw [sum_const, nsmul_eq_mul]
          _ ≤ (2 ^ (k ^ 2) : ℕ) * D := by
              gcongr
              exact_mod_cast card_relEdgeSets₀_coarsen_le hG
      calc ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            |∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F|
          ≤ ∑ _Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)), (2 ^ (k ^ 2) : ℕ) * D :=
            sum_le_sum hF
        _ = (Fintype.piFinset (fun l => relEdgeSets (Xs l))).card * ((2 ^ (k ^ 2) : ℕ) * D) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ ((2 ^ (k ^ 2)) ^ k : ℕ) * ((2 ^ (k ^ 2) : ℕ) * D) := by
            gcongr
        _ = ((2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D := by push_cast; ring
    calc ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          |∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F|
        ≤ ∑ _Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
            ((2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D := sum_le_sum hEs
      _ = ((Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))).card *
            (((2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ((2 ^ k) ^ k : ℕ) * (((2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D) := by
          gcongr
      _ = ((2 ^ k) ^ k * (2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D := by push_cast; ring
  calc ∑ n ∈ Finset.range (X.card + 1), |1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F|
      ≤ ∑ _n ∈ Finset.range (X.card + 1), ((2 ^ k) ^ k * (2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D :=
        sum_le_sum hterm
    _ = (X.card + 1) * (((2 ^ k) ^ k * (2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (k + 1) * (((2 ^ k) ^ k * (2 ^ (k ^ 2)) ^ k * 2 ^ (k ^ 2) : ℕ) * D) := by
        gcongr
    _ = countBound k * D := by
        unfold countBound
        push_cast
        ring

end ExpansionErrors

end MultipoleBKT

end
