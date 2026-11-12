/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.ExpansionErrors.RouteTermwise.Numerator
public import MultipoleBKT.LowerBound.ExpansionErrors.RouteTermwise.Normalization
public import MultipoleBKT.LowerBound.ExpansionErrors.RouteTermwise.ExpectationSum

/-!
# Termwise errors for the lower and upper activities

The proofs of Propositions 4.24 and 5.19.
For each fixed expansion datum, bound its numerator difference, multiply
(4.80) by the reciprocal-product error, and add these two errors.
Only then sum the expectation differences over the expansion data.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionErrors

open MeasureTheory Set Finset Metric Filter
open TwoComponentCoulomb (box)
open Hierarchical Limits Multipole SetPartition MultipoleIntegral LowerBound.RouteBounded

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ}

/-! ### Lemma A.7 as hypotheses -/

open scoped Classical in
/-- **Lemma A.7, eq. (A.49)**, for
`(w, τ) = (ṽ, τ̃)`, `V_bad = ∅` (`Z = ∅`) and the damping of `𝖬^-_{ε₀}` (the parameter `-64L`):
for `ε₀ ∈ (0, 1)` there is `C > 0` such that for `λ` small, `N` large, every subpartition `X` of
`[N]` with `|X| ≥ 2` and `|V_X| = k`, and all `X₁, …, Xₙ ⊂ X` disjoint, `Eₗ ∈ 𝖤^{Xₗ}`,
`F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}`,
`|I^-_{cl,ε₀}(X; 𝐗, 𝐄, F) - I^0_{cl,ε₀}(X; 𝐗, 𝐄, F)| ≤ C N λ^{(2-β)k} R̄^{-2}`.
The paper has `λ` small and every `N`. Asking it only for `N` large makes the statement weaker.
`C` may depend on `χ, β, M, L, k, p₀, ε₀`. -/
def LemmaA8MinusStatement (χ : ℂ → ℝ) (β M L : ℝ) (p₀ k : ℕ) : Prop :=
  ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
        2 ≤ X.card → (X.biUnion id).card = k →
        ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
          (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
          ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            |minusClusterIntegral χ N p₀ β lam M ε₀ L X Xs Es F -
                zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F| ≤
              C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))

open scoped Classical in
/-- **Lemma A.7, eq. (A.50)**: for
`ε₀ ∈ (0, 1)` there is `C > 0` such that for `λ` small, `N` large, every subpartition `X` of
`[N]` with `|X| ≥ 2` and `|V_X| = k`, and all data `(𝐗, 𝐄, F)` as in Definition 4.15,
`|I^0_{cl,ε₀}(X; 𝐗, 𝐄, F) - I^0_{cl,∞}(X; 𝐗, 𝐄, F)| ≤ C N λ^{(2-β)k} R̄^{-2}`. As for
`LemmaA8MinusStatement`, `N` large is weaker than the paper's every `N`. -/
def LemmaA8BisStatement (χ : ℂ → ℝ) (β M : ℝ) (p₀ k : ℕ) : Prop :=
  ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
    ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
        2 ≤ X.card → (X.biUnion id).card = k →
        ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
          (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
          ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
          ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            |zeroClusterIntegral χ N p₀ β lam M ε₀ X Xs Es F -
                zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤
              C * N * (lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-2 : ℝ))

/-- The scale: from `C ≥ (Z/2) ℓ`, `N ℓ^k (N C)^{-k} N^{k-1} ≤ (2/Z)^k`. -/
theorem scale_le {N C Z ℓ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) (hZ : 0 < Z) (hℓ : 0 < ℓ)
    (hC : Z / 2 * ℓ ≤ C) : N * ℓ ^ k * ((N * C)⁻¹) ^ k * N ^ (k - 1) ≤ (2 / Z) ^ k := by
  have hC0 : 0 < C := lt_of_lt_of_le (by positivity) hC
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have heq : N * ℓ ^ (m + 1) * ((N * C)⁻¹) ^ (m + 1) * N ^ (m + 1 - 1) = (ℓ / C) ^ (m + 1) := by
    rw [Nat.add_sub_cancel, mul_inv, mul_pow, div_pow]
    have h1 : N * N ^ m * (N⁻¹) ^ (m + 1) = 1 := by
      rw [← pow_succ', inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hN.ne')]
    calc N * ℓ ^ (m + 1) * ((N⁻¹) ^ (m + 1) * (C⁻¹) ^ (m + 1)) * N ^ m
        = (N * N ^ m * (N⁻¹) ^ (m + 1)) * (ℓ ^ (m + 1) * (C⁻¹) ^ (m + 1)) := by ring
      _ = ℓ ^ (m + 1) / C ^ (m + 1) := by rw [h1, one_mul, inv_pow, div_eq_mul_inv]
  rw [heq]
  refine pow_le_pow_left₀ (div_nonneg hℓ.le hC0.le) ?_ _
  rw [div_le_div_iff₀ hC0 hZ]
  linarith

open scoped Classical in
/-- Internal fixed-datum adapter for (4.79), (4.81) and the
expectation difference, in that order. The fixed numerator bound is
supplied by (4.80) in each of the three model consumers.
proof of Proposition 4.24.
The block scale `ℓ` and numerator scale `r` remain separate through the
reciprocal error. Their quotient is bounded only after multiplication. -/
theorem internal_fixed_errors_of_blocks (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card) {k : ℕ}
    (hXk : (X.biUnion id).card = k) {ρ : Measure (ℂ × ℂ)} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K) {a : ℝ} (ha : 0 < a)
    {dens : ℂ × ℂ → ℝ} {I₁ : Finset ℕ → ℝ}
    (hM₁ : ∀ S ∈ X, modelPartitionFunction ρ β w ψ M lam S = a ^ S.card * I₁ S)
    (hconv₁ : ∀ Φ : (ℕ → ℂ × ℂ) → ℝ, Measurable Φ →
      DependsOn Φ ((X.biUnion id : Finset ℕ) : Set ℕ) →
      ∫ c, Φ c ∂labelField ρ = a ^ (X.biUnion id).card *
        ∫ y in boxConfig (X.biUnion id) N, Φ (extendConfig (X.biUnion id) y) * ∏ i, dens (y i))
    {CB ℓ η : ℝ} (hCB : 1 ≤ CB) (hℓ : 0 < ℓ)
    (hblocks : ∀ S ∈ X, BlockComparison CB ℓ η (I₁ S) (multipoleIntegral χ N β lam M S))
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)))
    {F : Finset (ℕ × ℕ)} (hF : F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)))
    {D CK Z : ℝ} (hD : 0 ≤ D) (hCK : 0 ≤ CK) (hZ : 0 < Z)
    (hC : Z / 2 * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam)
    (hterm : |clusterIntegral N β w ψ dens M lam X Xs Es F -
        zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤ D * N * (lam ^ ((2 - β) * k) * η))
    {r : ℝ} (hr : 0 ≤ r) (hrℓ : r ≤ ℓ)
    (hnum : |zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤
      CK * N * (lam ^ ((2 - β) * k) * r)) :
    |clusterIntegral N β w ψ dens M lam X Xs Es F -
        zeroClusterIntegralInf χ N β lam M X Xs Es F| / (∏ S ∈ X, I₁ S) ≤
        (D * (2 / Z) ^ k * CB ^ k) * η /
          ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) ∧
    |zeroClusterIntegralInf χ N β lam M X Xs Es F| *
        |(∏ S ∈ X, I₁ S)⁻¹ - (∏ S ∈ X, multipoleIntegral χ N β lam M S)⁻¹| ≤
        (CK * (2 / Z) ^ k * (CB ^ k * (k * CB))) * η /
          ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) ∧
    |(∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X) -
      (∫ y, clusterTerm β (dipoleInteraction χ lam) M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1) M lam X)| ≤
      (D * (2 / Z) ^ k * CB ^ k + CK * (2 / Z) ^ k * (CB ^ k * (k * CB))) * η /
        ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  have hXk' : X.card ≤ k := hXk ▸ card_le_card_biUnion hX
  have hk1 : 1 ≤ k := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓ0 : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hη : 0 ≤ η := by
    obtain ⟨S, hS⟩ := card_pos.1 (by omega : 0 < X.card)
    exact (hblocks S hS).1
  -- the model `∞`
  have hinf := modelHyp_infinity hχ hlam β hN
  have hCpos : 0 < dipoleNormalization χ N β lam := lt_of_lt_of_le (by positivity) hC
  set b : ℝ := ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ with hb_def
  have hb : 0 < b := inv_pos.2 (mul_pos hNpos hCpos)
  have hM₀ : ∀ S ∈ X, modelPartitionFunction (dipoleMeasure χ N β lam) β
      (dipoleInteraction χ lam) (fun _ => 1) M lam S =
        b ^ S.card * multipoleIntegral χ N β lam M S :=
    fun S _ => by
      rw [modelPartitionFunction_dipoleMeasure,
        multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN S]
  have hEsX := fun l => (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1
  have hFX := (mem_relEdgeSets₀.1 hF).1
  have hid₀ := prod_mul_clusterExpectation_eq (M := M) (lam := lam) hinf hX hb.ne' hM₀
    (fun Φ hΦ hdep => integral_labelField_dipoleMeasure hχ hlam β hN hΦ hdep) hXs hEsX hFX
  have hid₁ := prod_mul_clusterExpectation_eq (M := M) (lam := lam) h hX ha.ne' hM₁ hconv₁ hXs hEsX hFX
  -- the block products
  obtain ⟨hQ₁, hQ, hd⟩ := prod_blockComparison hCB hℓ hblocks
  have hCBk : CB ^ X.card ≤ CB ^ k := pow_le_pow_right₀ hCB hXk'
  have hQ₁0 := hQ₁.le
  have hQ' : ∏ S ∈ X, multipoleIntegral χ N β lam M S ≤
      CB ^ k * ∏ S ∈ X, I₁ S := hQ.trans (mul_le_mul_of_nonneg_right hCBk hQ₁0)
  have hd' : |∏ S ∈ X, multipoleIntegral χ N β lam M S - ∏ S ∈ X, I₁ S| * ℓ ≤
      CB ^ k * (k * CB) * η * ∏ S ∈ X, I₁ S := by
    refine hd.trans ?_
    have hXc : (X.card : ℝ) * CB ≤ k * CB :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hXk') (zero_le_one.trans hCB)
    gcongr
  -- `𝖬^0_∞(X) = b^k ∏ I^0_∞(S)`
  set P₀ := ∏ S ∈ X, multipolePartitionFunction χ N β lam M S with hP₀_def
  have hP₀eq : P₀ = b ^ k * ∏ S ∈ X, multipoleIntegral χ N β lam M S := by
    rw [← hXk, ← prod_pow_card_mul hX]
    exact prod_congr rfl fun S _ =>
      multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN S
  have hP₀ : 0 < P₀ := prod_pos fun S hS =>
    multipolePartitionFunction_pos hχ hlam β (by linarith) hN (hX.1 S hS)
  have hT : (0 : ℝ) < (N : ℝ) ^ (k - 1) := by positivity
  have hPT : 0 < P₀ * (N : ℝ) ^ (k - 1) := mul_pos hP₀ hT
  have hQ₀ : 0 < ∏ S ∈ X, multipoleIntegral χ N β lam M S := by
    have hp : 0 < b ^ k * ∏ S ∈ X, multipoleIntegral χ N β lam M S := hP₀eq ▸ hP₀
    exact pos_of_mul_pos_right hp (pow_nonneg hb.le _)
  have hscale : (N : ℝ) * lam ^ ((2 - β) * k) * b ^ k * (N : ℝ) ^ (k - 1) ≤ (2 / Z) ^ k := by
    rw [rpow_mul_natCast_eq hlam k]
    exact scale_le hk1 hNpos hZ hℓ0 hC
  -- Normalize the fixed numerator difference, (4.79).
  have hS : |clusterIntegral N β w ψ dens M lam X Xs Es F -
      zeroClusterIntegralInf χ N β lam M X Xs Es F| * (P₀ * (N : ℝ) ^ (k - 1)) ≤
      (D * (2 / Z) ^ k) * η * ∏ S ∈ X, multipoleIntegral χ N β lam M S := by
    calc _ ≤ D * N * (lam ^ ((2 - β) * k) * η) * (P₀ * (N : ℝ) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_right hterm hPT.le
      _ = D * η * (∏ S ∈ X, multipoleIntegral χ N β lam M S) *
            ((N : ℝ) * lam ^ ((2 - β) * k) * b ^ k * (N : ℝ) ^ (k - 1)) := by rw [hP₀eq]; ring
      _ ≤ D * η * (∏ S ∈ X, multipoleIntegral χ N β lam M S) * (2 / Z) ^ k := by gcongr
      _ = _ := by ring
  have hrr1 : |clusterIntegral N β w ψ dens M lam X Xs Es F -
      zeroClusterIntegralInf χ N β lam M X Xs Es F| / (∏ S ∈ X, I₁ S) ≤
      (D * (2 / Z) ^ k * CB ^ k) * η / (P₀ * (N : ℝ) ^ (k - 1)) := by
    rw [div_le_div_iff₀ hQ₁ hPT]
    calc _ ≤ (D * (2 / Z) ^ k) * η * ∏ S ∈ X, multipoleIntegral χ N β lam M S := hS
      _ ≤ (D * (2 / Z) ^ k) * η * (CB ^ k * ∏ S ∈ X, I₁ S) := by gcongr
      _ = _ := by ring
  -- Keep the total-size power in (4.80) until multiplication by the reciprocal error.
  have hborn : |zeroClusterIntegralInf χ N β lam M X Xs Es F| * (P₀ * (N : ℝ) ^ (k - 1)) ≤
      (CK * (2 / Z) ^ k) * r * ∏ S ∈ X, multipoleIntegral χ N β lam M S := by
    calc _ ≤ CK * N * (lam ^ ((2 - β) * k) * r) * (P₀ * (N : ℝ) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_right hnum hPT.le
      _ = CK * r * (∏ S ∈ X, multipoleIntegral χ N β lam M S) *
            ((N : ℝ) * lam ^ ((2 - β) * k) * b ^ k * (N : ℝ) ^ (k - 1)) := by rw [hP₀eq]; ring
      _ ≤ CK * r * (∏ S ∈ X, multipoleIntegral χ N β lam M S) * (2 / Z) ^ k := by gcongr
      _ = _ := by ring
  have hrr2 := internal_fixed_normalization_error hQ₁ hQ₀ hPT hℓ (by positivity) hr hrℓ hborn hd'
  refine ⟨hrr1, hrr2, ?_⟩
  exact internal_fixed_expectation_error hQ₁ hQ₀ hid₁ hid₀ hrr1 hrr2

open scoped Classical in
/-- Internal summation of the already bounded expectation differences.
The supplied numerator estimate is termwise, never an activity estimate. -/
theorem activity_diff_of_blocks (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card) {k : ℕ}
    (hXk : (X.biUnion id).card = k) {ρ : Measure (ℂ × ℂ)} {w : ℂ × ℂ → ℂ × ℂ → ℝ}
    {ψ : ℂ × ℂ → ℝ} {K : Set (ℂ × ℂ)} (h : ModelHyp ρ β w ψ K) {a : ℝ} (ha : 0 < a)
    {dens : ℂ × ℂ → ℝ} {I₁ : Finset ℕ → ℝ}
    (hM₁ : ∀ S ∈ X, modelPartitionFunction ρ β w ψ M lam S = a ^ S.card * I₁ S)
    (hconv₁ : ∀ Φ : (ℕ → ℂ × ℂ) → ℝ, Measurable Φ →
      DependsOn Φ ((X.biUnion id : Finset ℕ) : Set ℕ) →
      ∫ c, Φ c ∂labelField ρ = a ^ (X.biUnion id).card *
        ∫ y in boxConfig (X.biUnion id) N, Φ (extendConfig (X.biUnion id) y) * ∏ i, dens (y i))
    {CB ℓ η : ℝ} (hCB : 1 ≤ CB) (hℓ : 0 < ℓ)
    (hblocks : ∀ S ∈ X, BlockComparison CB ℓ η (I₁ S) (multipoleIntegral χ N β lam M S))
    {D : ℝ} (hD : 0 ≤ D)
    (hterm : ∀ n (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
        |clusterIntegral N β w ψ dens M lam X Xs Es F -
            zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤
          D * N * (lam ^ ((2 - β) * k) * η))
    {Z : ℝ} (hZ : 0 < Z) (hC : Z / 2 * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam)
    {CK : ℝ} (hCK : 0 ≤ CK)
    (hnum : ∀ n (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
        |zeroClusterIntegralInf χ N β lam M X Xs Es F| ≤
          CK * N * (lam ^ ((2 - β) * k) * ℓ)) :
    |modelActivity ρ β w ψ M lam X - zeroActivityInf χ N β lam M X| ≤
      (countBound k * (D * (2 / Z) ^ k * CB ^ k + CK * (2 / Z) ^ k * (CB ^ k * (k * CB)))) * η /
        ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) := by
  have hη : 0 ≤ η := by
    obtain ⟨S, hS⟩ := card_pos.1 (by omega : 0 < X.card)
    exact (hblocks S hS).1
  have hsum := abs_clusterSum_le hX
    (D := (D * (2 / Z) ^ k * CB ^ k + CK * (2 / Z) ^ k * (CB ^ k * (k * CB))) * η /
      ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)))
    (div_nonneg (by positivity) (mul_nonneg
      (prod_nonneg fun S _ => (by simpa only [modelPartitionFunction_dipoleMeasure] using
        (modelHyp_infinity hχ hlam β hN).modelPartitionFunction_nonneg M lam S))
      (by positivity)))
    (f := fun _ Xs Es F =>
      (∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X) -
      (∫ y, clusterTerm β (dipoleInteraction χ lam) M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1) M lam X))
    (fun n Xs hXs hdisj Es hEs F hF =>
      (internal_fixed_errors_of_blocks hχ hlam hN hM hX h2 hXk h ha hM₁ hconv₁ hCB hℓ hblocks
        hXs hEs hF hD hCK hZ hC (hterm n Xs hXs hdisj Es hEs F hF)
        hℓ.le le_rfl (hnum n Xs hXs hdisj Es hEs F hF)).2.2)
  have hid₁ : modelActivity ρ β w ψ M lam X = clusterSum X (fun _ Xs Es F =>
      ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X) := modelActivity_eq_grouped h2
  have hid₀ : zeroActivityInf χ N β lam M X = clusterSum X (fun _ Xs Es F =>
      ∫ y, clusterTerm β (dipoleInteraction χ lam) M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical (dipoleMeasure χ N β lam) β (dipoleInteraction χ lam) (fun _ => 1) M lam X) :=
    modelActivity_eq_grouped h2
  rw [← clusterSum_sub, ← hid₁, ← hid₀, hXk] at hsum
  exact hsum.trans_eq (by ring)

end ExpansionErrors

end MultipoleBKT

end
