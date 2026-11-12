/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.Definitions
public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.SourceIntegral
public import MultipoleBKT.LowerBound.BoundedLowerEps.BoxBound
public import MultipoleBKT.LowerBound.Peeling.Quadratic
public import MultipoleBKT.LowerBound.Peeling.Dipole

/-!
# Lemma A.4: the integral `J` of bounded clusters

See Lemma A.4,
eqs. (A.17) and (A.19). Let `X` be a subpartition with `|X| ≥ 2` and `|V_X| = k`, let
`X_1, …, X_n ⊆ X` be disjoint, `T^a_l ∈ 𝖳^{X_l}`, `T^a = ⋃_l T^a_l`,
`T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}`, and for every configuration let `Ŝ_l ∈ X_l` be a block with
the largest radius `r_{Ŝ_l} = max_{S ∈ X_l} r_S`. Then

`J = ∫_{(Λ²)^{V_X}} min(max_i r_i / max_{e ∈ T^a} d_e, 1)² ∏_l ∏_{S ∈ X_l, S ≠ Ŝ_l} r_S²
  ∏_{ij ∈ T^a} d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c} ∏_{ij ∈ T^b} b^abs_ij ∏_{S ∈ X} 𝟙_{𝓑_S}
  ∏_{i ∈ V_X} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄} dx_i dy_i ≤ C N λ^{(2-β)k} γ_{β,λ,k}`

(`lemma_A6`), with `C` depending only on `χ, β, M, ε₀, k`, for `λ ≤ Appendix.lamBound ε₀ k`.

**Formalization.** The trees are edge sets of pairs (`edgesOf` of `MultipoleBKT.relTrees`,
`MultipoleBKT.relTrees₀`), read on `V_X` with `graphOf`. The weights are those of the peeling
(`Peeling.keptWeight`, `Peeling.absWeight` with `Peeling.absIndicator`, `Peeling.blockRadius`) and
`𝟙_{𝓑_S}` is the multipole event `ConnOn S (linkedPairs …)` of the hierarchical models. The
selection `Ŝ_l` is an argument `hatS` (a function of the configuration) with the stated
maximality, as in the paper ("choose `Ŝ_l`"). The maxima `max_i r_i` and `max_e d_e` are
`Finset.fold max 0` and `Finset.sup'` (all radii and distances are `≥ 0`) and the convention
`max_∅ d_e = 0⁺` of the paper is the value `1` of the tail factor for `T^a = ∅` (`tailJ`).

The bad points `V_bad` of the paper do not enter `J` (only `J_ext` and (A.20) involve them),
so (A.19) holds for every subpartition `X`, in particular for `X` a subpartition of
`V_good = [N] ∖ V_bad`.

**Proof.** `RouteJ.source_integral_le_logRadial` retains the near, odd and even
trees, uses the Prüfer count, expands the four endpoint sectors and integrates
the odd edges with one maximum tail. Two applications of Lemma A.1 allocate
the radii. The largest-radius split and polar coordinates reduce the vector
integral to the logarithmic ordered family. `lemma_A6_hat_infinity` uses its
direct infinite-cutoff convergence under the size restriction in Lemma A.4. The
original estimate `lemma_A6` follows by `integralJ_le_hatJ`.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps

variable {χ : ℂ → ℝ} {β lam M ε₀ : ℝ} {X : Finset (Finset ℕ)}

/-! ### The integrand -/

/-! ### The peeling weights and the weights of the core bound -/

section Weights

variable {V : Type*}

theorem keptWeight_nonneg' (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (e : Sym2 V) :
    0 ≤ keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ R z) e :=
  div_nonneg (absIndicator_nonneg M lam ε₀ R z e) (sq_nonneg _)

/-- `d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R} 𝟙_{𝓑_ij^c} ≤ d_ij^{-2} 𝟙_{𝓑_ij^c}`. -/
theorem keptWeight_le_keptE (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (e : Sym2 V) :
    keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ R z) e ≤ keptE M lam z e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show absIndicator M lam ε₀ R z s(i, j) / dipoleDistOn z s(i, j) ^ 2 ≤
      (if MultipoleLinked M lam (z i) (z j) then 0 else (dipoleDist (z i) (z j) ^ 2)⁻¹)
    simp only [absIndicator, Sym2.lift_mk, dipoleDistOn_mk]
    split_ifs <;> simp [div_eq_mul_inv, sq_nonneg]

/-- `(a^abs_ij)² ≤ â_ij² 𝟙_{𝓑_ij^c}`. -/
theorem absWeight_sq_le_aSqE (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (e : Sym2 V) :
    absWeight (fun i => dipoleLength (z i)) (dipoleDistOn z) (absIndicator M lam ε₀ R z) e ^ 2 ≤
      aSqE M lam z e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show (radProd (fun i => dipoleLength (z i)) s(i, j) / (dipoleDistOn z s(i, j) *
        max (radMax (fun i => dipoleLength (z i)) s(i, j)) (dipoleDistOn z s(i, j))) *
          absIndicator M lam ε₀ R z s(i, j)) ^ 2 ≤
      (if MultipoleLinked M lam (z i) (z j) then 0 else ahat (z i) (z j) ^ 2)
    have hahat : radProd (fun i => dipoleLength (z i)) s(i, j) / (dipoleDistOn z s(i, j) *
        max (radMax (fun i => dipoleLength (z i)) s(i, j)) (dipoleDistOn z s(i, j))) =
          ahat (z i) (z j) := by
      rw [radProd_mk, radMax_mk, dipoleDistOn_mk]
      unfold ahat dipoleLength
      rw [max_comm (max _ _)]
    rw [hahat]
    simp only [absIndicator, Sym2.lift_mk]
    split_ifs <;> simp [sq_nonneg]

end Weights

/-- Removing the spatial cutoffs increases the integrand.
See Lemma A.4. -/
theorem integrandJ_le_hatJ (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (p₀ : ℕ) (z : X.biUnion id → ℂ × ℂ) :
    integrandJ χ β lam M ε₀ p₀ hX Xs Ta Tb hatS z ≤
      integrandHatJ χ β lam M ε₀ p₀ hX Xs Ta Tb hatS z := by
  classical
  unfold integrandJ integrandHatJ
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _ => cutDens_nonneg _ _)
  apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun S _ => by split_ifs <;> norm_num)
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left
    · exact prod_le_prod₀ (fun e _ => keptWeight_nonneg' _ _ _ _ _ e)
        fun e _ => keptWeight_le_keptE _ _ _ _ _ e
    · exact mul_nonneg (by unfold tailJ; split_ifs <;> positivity)
        (prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _)
  · exact prod_le_prod₀ (fun e _ => add_nonneg (sq_nonneg _) (linkE_nonneg z e))
      fun e _ => add_le_add (absWeight_sq_le_aSqE _ _ _ _ _ e) le_rfl
  · exact prod_nonneg fun e _ => add_nonneg (sq_nonneg _) (linkE_nonneg z e)
  · exact mul_nonneg (mul_nonneg (by unfold tailJ; split_ifs <;> positivity)
      (prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _))
      (prod_nonneg fun e _ => keptE_nonneg z e)

/-- The first comparison in the proof of Lemma A.4. -/
theorem integralJ_le_hatJ (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (p₀ N : ℕ) :
    integralJ χ β lam M ε₀ p₀ N hX Xs Ta Tb hatS ≤
      integralHatJ χ β lam M ε₀ p₀ N hX Xs Ta Tb hatS :=
  lintegral_mono fun z => ENNReal.ofReal_le_ofReal (integrandJ_le_hatJ hX Xs Ta Tb hatS p₀ z)

/-- Removing the radial cutoff increases the hatted integrand.
See Lemma A.4. -/
theorem integrandHatJ_le_infinity (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (p₀ : ℕ) (z : X.biUnion id → ℂ × ℂ) :
    integrandHatJ χ β lam M ε₀ p₀ hX Xs Ta Tb hatS z ≤
      integrandHatJInfinity χ β lam M hX Xs Ta Tb hatS z := by
  classical
  unfold integrandHatJ integrandHatJInfinity
  apply mul_le_mul_of_nonneg_left
  · exact prod_le_prod₀ (fun i _ => cutDens_nonneg _ _) fun i _ => by
      unfold cutDens
      exact mul_le_of_le_one_right (pairDensity_pos _ _ _ _).le (by by_cases h : ‖(z i).1 - (z i).2‖ ≤ ε₀ * truncationScale p₀ β lam <;> simp [Set.indicator, Set.mem_Iic, h])
  · apply mul_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · unfold tailJ
            split_ifs <;> positivity
          · exact prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _
        · exact prod_nonneg fun e _ => keptE_nonneg z e
      · exact prod_nonneg fun e _ => add_nonneg (aSqE_nonneg z e) (linkE_nonneg z e)
    · exact prod_nonneg fun S _ => by split_ifs <;> norm_num

/-- Radial truncation of the hatted integral. The upper bound for the infinite
integral requires the separate size condition in Lemma A.4. -/
theorem integralHatJ_le_infinity (hX : IsSubpartition X) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X)
    (p₀ N : ℕ) :
    integralHatJ χ β lam M ε₀ p₀ N hX Xs Ta Tb hatS ≤
      integralHatJInfinity χ β lam M N hX Xs Ta Tb hatS :=
  lintegral_mono fun z => ENNReal.ofReal_le_ofReal (integrandHatJ_le_infinity hX Xs Ta Tb hatS p₀ z)

/-! ### Lemma A.4 -/

section Main

open scoped Classical in
/-- **Lemma A.4 for `Ĵ`, eq. (A.19)**: for `β > 2`,
`M ≥ 1`, `ε₀ ∈ (0, 1)` and `k ∈ ℕ`, there is `C > 0` (depending on `χ, β, M, ε₀, k`) such that
for every subpartition `X` with `|X| ≥ 2` and `|V_X| = k`, disjoint groups `X_l ⊆ X`, trees
`T^a_l ∈ 𝖳^{X_l}`, `T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}`, every selection `Ŝ_l` of a block of
largest radius in `X_l`, and all `p₀`, `λ ∈ (0, Appendix.lamBound ε₀ k]`, `N`,
`Ĵ ≤ C N λ^{(2-β)k} γ_{β,λ,k}`. -/
theorem lemma_A6_hat (hχ : IsMollifier χ) (hβ : 2 < β) (k : ℕ) (hM : 1 ≤ M) (hε₀ : 0 < ε₀)
    (hε₁ : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X), 2 ≤ X.card →
      (X.biUnion id).card = k → ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) → ∀ Ta : Fin n → Finset (ℕ × ℕ),
      (∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf) → ∀ Tb : Finset (ℕ × ℕ),
      Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf →
      ∀ hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X,
      (∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (z i)) S ≤
          blockRadius hX (fun i => dipoleLength (z i)) (hatS l z)) →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam ≤ Appendix.lamBound ε₀ k → ∀ N : ℕ,
        integralHatJ χ β lam M ε₀ p₀ N hX Xs Ta Tb hatS ≤
          ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k)) := by
  by_cases hk : 2 ≤ k
  swap
  · refine ⟨1, one_pos, fun X hX h2 hV => ?_⟩
    have h := Fintype.card_le_of_surjective _ (Limits.blockOf_surjective hX)
    rw [Fintype.card_coe, Fintype.card_coe, hV] at h
    omega
  obtain ⟨Cs, hCs, hs⟩ := RouteJ.source_integral_le_logRadial (β := β) hχ (by linarith) hM k hk
  obtain ⟨Cr, hCr, hr⟩ := RouteJ.logRadialWeight_bound_any hβ hε₀ hε₁ (k - 2) (k - 1)
  have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
  have hcast : ((k - 2 : ℕ) : ℝ) + 2 = k := by exact_mod_cast hk2
  simp only [hk2, hcast] at hr
  refine ⟨Cs * Cr, mul_pos hCs hCr, ?_⟩
  intro X hX h2 hV n Xs hXs hdisj Ta hTa Tb hTb hatS hhat p₀ lam hlam hlamB N
  have := RouteJ.labels_nonempty hX h2
  have hV' : Fintype.card (X.biUnion id) = k := by rw [Fintype.card_coe, hV]
  have hsource := hs X hX h2 hV Xs hXs hdisj Ta hTa Tb hTb hatS hhat lam hlam
    (Set.Iic (ε₀ * truncationScale p₀ β lam)) measurableSet_Iic N
  have heq : integralHatJ χ β lam M ε₀ p₀ N hX Xs Ta Tb hatS =
      ∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal (RouteJ.hatJCore M lam hX Xs Ta Tb (fun l => hatS l c) c) *
          ∏ i, ENNReal.ofReal (RouteJ.restrictedPairDensity χ β lam
            (Set.Iic (ε₀ * truncationScale p₀ β lam)) (c i)) := by
    unfold integralHatJ
    apply lintegral_congr
    intro c
    change ENNReal.ofReal (RouteJ.hatJCore M lam hX Xs Ta Tb (fun l => hatS l c) c *
      ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)) = _
    rw [ENNReal.ofReal_mul' (prod_nonneg fun _ _ => cutDens_nonneg _ _),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => cutDens_nonneg _ _)]
    rfl
  rw [← heq] at hsource
  simp only [Set.mem_Iic] at hsource
  have hrad := hr (X.biUnion id) hV' p₀ lam hlam hlamB
  refine hsource.trans ((mul_le_mul_right hrad _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul (mul_nonneg hCs.le (Nat.cast_nonneg _))]
  congr 1
  ring



/-- The infinite-cutoff hatted bound, with the size restriction in Lemma A.4.
The outer logarithmic moment converges directly under `k ≤ p*(β)`.
See Lemma A.4. -/
theorem lemma_A6_hat_infinity (hχ : IsMollifier χ) (hβ : 2 < β) (k : ℕ) (hM : 1 ≤ M)
    (hsize : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X), 2 ≤ X.card →
      (X.biUnion id).card = k → ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) → ∀ Ta : Fin n → Finset (ℕ × ℕ),
      (∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf) → ∀ Tb : Finset (ℕ × ℕ),
      Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf →
      ∀ hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X,
      (∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (z i)) S ≤
          blockRadius hX (fun i => dipoleLength (z i)) (hatS l z)) →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → ∀ N : ℕ,
        integralHatJInfinity χ β lam M N hX Xs Ta Tb hatS ≤
          ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k)) := by
  by_cases hk : 2 ≤ k
  swap
  · refine ⟨1, one_pos, fun X hX h2 hV => ?_⟩
    have h := Fintype.card_le_of_surjective _ (Limits.blockOf_surjective hX)
    rw [Fintype.card_coe, Fintype.card_coe, hV] at h
    omega
  obtain ⟨Cs, hCs, hs⟩ := RouteJ.source_integral_le_logRadial (β := β) hχ (by linarith) hM k hk
  have hk2 : k - 2 + 2 = k := Nat.sub_add_cancel hk
  have hcast : ((k - 2 : ℕ) : ℝ) + 2 = k := by exact_mod_cast hk2
  obtain ⟨Cr, hCr, hr⟩ := RouteJ.logRadialWeightInfinity_bound_any hβ (k - 2) (k - 1)
    (by simpa only [hk2] using hsize)
  simp only [hk2, hcast] at hr
  refine ⟨Cs * Cr, mul_pos hCs hCr, ?_⟩
  intro X hX h2 hV n Xs hXs hdisj Ta hTa Tb hTb hatS hhat p₀ lam hlam N
  have := RouteJ.labels_nonempty hX h2
  have hV' : Fintype.card (X.biUnion id) = k := by rw [Fintype.card_coe, hV]
  have hsource := hs X hX h2 hV Xs hXs hdisj Ta hTa Tb hTb hatS hhat lam hlam
    Set.univ MeasurableSet.univ N
  have heq : integralHatJInfinity χ β lam M N hX Xs Ta Tb hatS =
      ∫⁻ c in boxConfig (X.biUnion id) N,
        ENNReal.ofReal (RouteJ.hatJCore M lam hX Xs Ta Tb (fun l => hatS l c) c) *
          ∏ i, ENNReal.ofReal (RouteJ.restrictedPairDensity χ β lam Set.univ (c i)) := by
    unfold integralHatJInfinity
    apply lintegral_congr
    intro c
    change ENNReal.ofReal (RouteJ.hatJCore M lam hX Xs Ta Tb (fun l => hatS l c) c *
      ∏ i, pairDensity χ β lam (c i)) = _
    rw [ENNReal.ofReal_mul' (prod_nonneg fun _ _ => (pairDensity_pos _ _ _ _).le),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => (pairDensity_pos _ _ _ _).le)]
    simp only [RouteJ.restrictedPairDensity, Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← heq] at hsource
  simp only [Set.mem_univ, implies_true, Set.ofPred_true, Measure.restrict_univ] at hsource
  have hrad := hr (X.biUnion id) hV' p₀ lam hlam
  refine hsource.trans ((mul_le_mul_right hrad _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul (mul_nonneg hCs.le (Nat.cast_nonneg _))]
  congr 1
  ring

/-- The original spatially truncated estimate, obtained by `J ≤ Ĵ`.
See (A.19). -/
theorem lemma_A6 (hχ : IsMollifier χ) (hβ : 2 < β) (k : ℕ) (hM : 1 ≤ M) (hε₀ : 0 < ε₀)
    (hε₁ : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : Finset (Finset ℕ)) (hX : IsSubpartition X), 2 ≤ X.card →
      (X.biUnion id).card = k → ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) → ∀ Ta : Fin n → Finset (ℕ × ℕ),
      (∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf) → ∀ Tb : Finset (ℕ × ℕ),
      Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf →
      ∀ hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X,
      (∀ l z, hatS l z ∈ (Xs l).subtype (· ∈ X) ∧ ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (z i)) S ≤
          blockRadius hX (fun i => dipoleLength (z i)) (hatS l z)) →
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam ≤ Appendix.lamBound ε₀ k → ∀ N : ℕ,
        integralJ χ β lam M ε₀ p₀ N hX Xs Ta Tb hatS ≤
          ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k)) := by
  obtain ⟨C, hC, hbound⟩ := lemma_A6_hat hχ hβ k hM hε₀ hε₁
  refine ⟨C, hC, ?_⟩
  intro X hX h2 hV n Xs hXsX hdisj Ta hTa Tb hTb hatS hhat p₀ lam hlam hlamB N
  exact (integralJ_le_hatJ hX Xs Ta Tb hatS p₀ N).trans
    (hbound X hX h2 hV Xs hXsX hdisj Ta hTa Tb hTb hatS hhat p₀ lam hlam hlamB N)

end Main

end SmallIntegral

end MultipoleBKT

end
