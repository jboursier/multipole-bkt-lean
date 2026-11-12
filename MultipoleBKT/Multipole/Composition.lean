/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.Expansion
public import MultipoleBKT.Multipole.Regrouping
public import MultipoleBKT.Multipole.RouteGrouping.Mobius

/-!
# Dipole composition and the component expansion of Corollary 4.61

See the paper, Corollary 4.61 and (5.165).

Write `W(V) = 𝔼_{μ^{⊗ V}} ∏_{i<j ∈ V} e^{-β v_ij} 𝟙_{𝒜_ij}`. The proof of equation (5.165)
expands `W(V)` in two ways:

* the Mayer expansion `e^{-β v_ij} 𝟙_{𝒜_ij} = 1 + f_ij`, grouped by connected components, gives
  `W = ∑_{ρ ∈ 𝚷(V)} ∏_{D ∈ ρ} K^c(D)` (`fullIntegral_eq_partitionSum_mayer`), where
  `K^c(D) = 𝔼 ∑_{E connects D} ∏_{ij ∈ E} f_ij` (`mayerActivity`) is `𝖪^dip(D)` for `|D| ≥ 2`
  (`mayerActivity_eq_dipoleActivity`).
* the decomposition by the connected components of the near graph, then the expansion
  `e^{-β v_ij} 𝟙_{𝓑_ij^c} = 1 + (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)` of the inter-block factors
  (`𝓑_ij^c ⊂ 𝒜_ij`), grouped by connected components, gives `W = ∑_{ρ ∈ 𝚷(V)} ∏_{D ∈ ρ} L(D)` with
  `L(D) = 𝖬(D) + ∑_{π ∈ 𝚷(D), |π| ≥ 2} 𝖬^0_∞(π) 𝖪^mult(π)` (`fullIntegral_eq_partitionSum_mult`).

Lemma 4.60 (1) gives the same explicit Möbius sum for both connected weights
(`RouteGrouping.connectedWeight_mobius`), identifying them:

* `dipoleActivity_eq_sum_partitions`: **equation (5.165)**,
  `𝖪^dip(V) = 𝖬(V) + ∑_{π ∈ 𝚷(V), |π| ≥ 2} (∏_{S ∈ π} 𝖬(S)) 𝖪^mult(π)` for `|V| ≥ 2`, `M ≥ 1`
 (the paper has `M > 20`), `λ > 0`, `N ≥ 1`.

**Corollary 4.61.** `coro_4_61_expansion` is the second component expansion
in the proof of Corollary 4.61. Its comparison with the
zero-model expansion and the induction identifying the activities remain
separate from the explicit Möbius inversion used for dipole composition.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace Multipole

open SetPartition
open scoped Classical

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### The two pair weights -/

/-- The Mayer bond `f_ij = e^{-β v_ij} 𝟙_{𝒜_ij} - 1`. -/
noncomputable def mayerBond (χ : ℂ → ℝ) (β lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  stablePairWeight χ β lam d e - 1

/-- The interblock bond `e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1` of `𝖪^mult`. -/
noncomputable def unlinkedBond (χ : ℂ → ℝ) (β lam M : ℝ) (d e : ℂ × ℂ) : ℝ :=
  unlinkedPairWeight χ β lam M d e - 1

section Bonds

variable (hχ : IsMollifier χ) (hlam : 0 < lam)
include hχ hlam

theorem measurable_mayerBond (β : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => mayerBond χ β lam q.1 q.2 :=
  (measurable_stablePairWeight hχ hlam β).sub_const 1

theorem measurable_unlinkedBond (β M : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => unlinkedBond χ β lam M q.1 q.2 :=
  (measurable_unlinkedPairWeight hχ hlam β M).sub_const 1

theorem boxBounded_mayerBond (β : ℝ) (N : ℕ) (i j : ℕ) :
    BoxBounded N fun c => mayerBond χ β lam (c i) (c j) :=
  (boxBounded_stablePairWeight hχ hlam β N i j).sub (BoxBounded.const N 1)

theorem boxBounded_unlinkedBond (β M : ℝ) (N : ℕ) (i j : ℕ) :
    BoxBounded N fun c => unlinkedBond χ β lam M (c i) (c j) :=
  (boxBounded_unlinkedPairWeight hχ hlam β M N i j).sub (BoxBounded.const N 1)

end Bonds

/-! ### The full weight and its two expansions -/

/-- `∏_{i<j ∈ V} e^{-β v_ij} 𝟙_{𝒜_ij}` at a configuration of all labels. -/
noncomputable def fullWeight (χ : ℂ → ℝ) (β lam : ℝ) (V : Finset ℕ) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∏ p ∈ pairsOn V, stablePairWeight χ β lam (c p.1) (c p.2)

/-- `W(V) = 𝔼_{μ^{⊗ V}} ∏_{i<j ∈ V} e^{-β v_ij} 𝟙_{𝒜_ij}`. -/
noncomputable def fullIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (V : Finset ℕ) : ℝ :=
  ∫ c, fullWeight χ β lam V c ∂dipoleField χ N β lam

/-- The connected Mayer weight `K^c(D) = 𝔼 ∑_{E connects D} ∏_{ij ∈ E} f_ij`. -/
noncomputable def mayerActivity (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (D : Finset ℕ) : ℝ :=
  connIntegral χ N β lam (fun _ _ => 1) (mayerBond χ β lam) (singletons D)

/-- The connected multipole weight
`κ(Y) = 𝔼 (∏_{B ∈ Y} 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij}) ∑_{E ∈ 𝖤'(Y)} ∏_{ij ∈ E}
(e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)`. -/
noncomputable def multipoleConnIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (Y : Finset (Finset ℕ)) : ℝ :=
  connIntegral χ N β lam (blockWeight χ β lam M) (unlinkedBond χ β lam M) Y

/-- The hierarchical-model integral
`Ξ(σ) = 𝔼 (∏_{B ∈ σ} 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij}) ∏_{ij ∈ ℰ^inter(σ)}
e^{-β v_ij} 𝟙_{𝓑_ij^c}`. -/
noncomputable def multipoleClusterIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (σ : Finset (Finset ℕ)) : ℝ :=
  clusterIntegral χ N β lam (blockWeight χ β lam M) (unlinkedBond χ β lam M) σ

theorem clusterWeight_mayer (β lam : ℝ) (V : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    clusterWeight (fun _ _ => 1) (mayerBond χ β lam) (singletons V) c = fullWeight χ β lam V c := by
  simp only [clusterWeight, Finset.prod_const_one, one_mul, interPairs_singletons, mayerBond,
    fullWeight, add_sub_cancel]

section Expansions

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
include hχ hlam hN

/-- **The Mayer expansion grouped by components**: `W = ∑_{ρ ∈ 𝚷(V)} ∏_{D ∈ ρ} K^c(D)`. -/
theorem fullIntegral_eq_partitionSum_mayer (β : ℝ) (V : Finset ℕ) :
    fullIntegral χ N β lam V = partitionSum (mayerActivity χ N β lam) V := by
  have hrec : ∀ U : Finset ℕ, fullIntegral χ N β lam U =
      clusterIntegral χ N β lam (fun _ _ => 1) (mayerBond χ β lam) (singletons U) := by
    intro U
    unfold fullIntegral clusterIntegral
    simp only [clusterWeight_mayer]
  refine eq_partitionSum_of_root _ V ?_ (fun U _ a ha => ?_) V le_rfl
  · rw [hrec, singletons, Finset.image_empty]
    exact clusterIntegral_empty hχ hlam hN β
  · rw [hrec, clusterIntegral_root hχ hlam hN (fun _ => measurable_const)
      (fun _ _ _ _ => rfl) (fun _ => BoxBounded.const N 1) (measurable_mayerBond hχ hlam β)
      (boxBounded_mayerBond hχ hlam β N) β (isSubpartition_singletons U)
      (singleton_mem_singletons.2 ha), sum_powerset_singletons]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [singletons_sdiff, ← hrec]
    rfl

/-- **The near-graph decomposition, integrated**: `W(V) = ∑_{σ ∈ 𝚷(V)} Ξ(σ)`. -/
theorem fullIntegral_eq_sum (hM : 1 ≤ M) (β : ℝ) (V : Finset ℕ) :
    fullIntegral χ N β lam V = ∑ σ ∈ partitions V, multipoleClusterIntegral χ N β lam M σ := by
  unfold fullIntegral multipoleClusterIntegral clusterIntegral
  have hpt : ∀ c, fullWeight χ β lam V c = ∑ σ ∈ partitions V,
      clusterWeight (blockWeight χ β lam M) (unlinkedBond χ β lam M) σ c := by
    intro c
    rw [fullWeight, prod_stablePairWeight_eq_sum hM c V]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [clusterWeight, unlinkedBond, add_sub_cancel]
  simp_rw [hpt]
  exact integral_finsetSum _ fun σ _ => integrable_of_boxBounded hχ hlam hN β
    (measurable_clusterWeight (measurable_blockWeight hχ hlam β M)
      (measurable_unlinkedBond hχ hlam β M) σ)
    (boxBounded_clusterWeight (boxBounded_blockWeight hχ hlam β M N)
      (boxBounded_unlinkedBond hχ hlam β M N) σ)

/-- **The multipole expansion grouped by components**:
`W = ∑_{ρ ∈ 𝚷(V)} ∏_{D ∈ ρ} ∑_{π ∈ 𝚷(D)} κ(π)`. -/
theorem fullIntegral_eq_partitionSum_mult (hM : 1 ≤ M) (β : ℝ) (V : Finset ℕ) :
    fullIntegral χ N β lam V = partitionSum
      (fun D => ∑ π ∈ partitions D, multipoleConnIntegral χ N β lam M π) V := by
  rw [fullIntegral_eq_sum hχ hlam hN hM β V, ← sum_partitionSum_partitions]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  exact clusterIntegral_eq_partitionSum hχ hlam hN (measurable_blockWeight hχ hlam β M)
    (dependsOn_blockWeight χ β lam M) (boxBounded_blockWeight hχ hlam β M N)
    (measurable_unlinkedBond hχ hlam β M) (boxBounded_unlinkedBond hχ hlam β M N) β
    (mem_partitions.1 hσ).1 σ le_rfl

/-- **Identification of the connected weights by Lemma 4.60 (1)**, as cited in
the proof of equation (5.165).
Both component expansions have the same explicit Möbius sum. -/
theorem mayerActivity_eq_sum (hM : 1 ≤ M) (β : ℝ) {D : Finset ℕ} (hD : D.Nonempty) :
    mayerActivity χ N β lam D = ∑ π ∈ partitions D, multipoleConnIntegral χ N β lam M π := by
  have hm := RouteGrouping.connectedWeight_mobius
    (mayerActivity χ N β lam) hD
  have hc := RouteGrouping.connectedWeight_mobius
    (fun U => ∑ π ∈ partitions U, multipoleConnIntegral χ N β lam M π) hD
  rw [hm, hc]
  refine Finset.sum_congr rfl fun π hπ => congrArg _ (Finset.prod_congr rfl fun B _ => ?_)
  rw [← fullIntegral_eq_partitionSum_mayer hχ hlam hN β B,
    ← fullIntegral_eq_partitionSum_mult hχ hlam hN hM β B]

end Expansions

/-! ### The connected weights are the frozen activities -/

section Transport

theorem relConnSum_singletons {R : Type*} [CommSemiring R] (g : ℕ × ℕ → R) (D : Finset ℕ) :
    relConnSum g (singletons D) =
      ∑ E ∈ (pairsOn D).powerset.filter (ConnOn D), ∏ p ∈ E, g p := by
  unfold relConnSum
  rw [interPairs_singletons, biUnion_singletons, intraPairs_singletons]
  simp only [Finset.union_empty]

theorem interPairs_singleton (D : Finset ℕ) : interPairs ({D} : Finset (Finset ℕ)) = ∅ := by
  simp [interPairs, intraPairs]

theorem relConnSum_singleton {R : Type*} [CommSemiring R] {g : ℕ × ℕ → R} {D : Finset ℕ}
    (hD : D.Nonempty) : relConnSum g {D} = 1 := by
  unfold relConnSum
  have hint : intraPairs ({D} : Finset (Finset ℕ)) = pairsOn D := Finset.singleton_biUnion
  have hU : ({D} : Finset (Finset ℕ)).biUnion id = D := by simp
  rw [interPairs_singleton, Finset.powerset_empty, Finset.filter_singleton, hU, hint,
    Finset.empty_union, ite_eq_left (connOn_pairsOn hD)]
  simp

theorem dipoleActivityIntegrand_restrict {D : Finset ℕ} (G : SimpleGraph D) (c : ℕ → ℂ × ℂ) :
    dipoleActivityIntegrand χ β lam G (D.restrict c) =
      ∏ p ∈ edgesOf G, mayerBond χ β lam (c p.1) (c p.2) :=
  prod_prod_ite_adj G fun i j => stablePairWeight χ β lam (c i) (c j) - 1

theorem multipoleActivityIntegrand_restrict {X : Finset (Finset ℕ)} (E : SimpleGraph (X.biUnion id))
    (c : ℕ → ℂ × ℂ) :
    multipoleActivityIntegrand χ β lam M E ((X.biUnion id).restrict c) =
      ∏ p ∈ edgesOf E, unlinkedBond χ β lam M (c p.1) (c p.2) :=
  prod_prod_ite_adj E fun i j => unlinkedPairWeight χ β lam M (c i) (c j) - 1

theorem hierarchicalBlockWeight_restrict {X : Finset (Finset ℕ)} {S : Finset ℕ} (hS : S ∈ X)
    (c : ℕ → ℂ × ℂ) :
    hierarchicalBlockWeight χ β lam M X S ((X.biUnion id).restrict c) =
      blockWeight χ β lam M S c := by
  unfold hierarchicalBlockWeight blockWeight
  congr 1
  · exact if_congr (connected_induce_iff c (subset_biUnion_of_mem hS)) rfl rfl
  · exact prod_prod_ite_mem_lt (subset_biUnion_of_mem hS)
      fun i j => stablePairWeight χ β lam (c i) (c j)

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
include hχ hlam hN

/-- `K^c(D) = 𝖪^dip(D)` for `|D| ≥ 2`. -/
theorem mayerActivity_eq_dipoleActivity (β : ℝ) {D : Finset ℕ} (hD : 2 ≤ D.card) :
    mayerActivity χ N β lam D = dipoleActivity χ N β lam D := by
  rw [dipoleActivity_eq_sum]
  have h1 : ∀ G : SimpleGraph D, ∫ y, dipoleActivityIntegrand χ β lam G y
      ∂Measure.pi (fun _ : D => dipoleMeasure χ N β lam) =
        ∫ c, ∏ p ∈ edgesOf G, mayerBond χ β lam (c p.1) (c p.2) ∂dipoleField χ N β lam := by
    intro G
    rw [integral_pi_eq_integral_dipoleField hχ hlam hN β
      (measurable_dipoleActivityIntegrand hχ hlam β G)]
    simp_rw [dipoleActivityIntegrand_restrict]
  rw [Finset.sum_congr rfl fun G _ => h1 G]
  have hfilter : (Finset.univ : Finset (SimpleGraph D)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty) =
        (Finset.univ : Finset (SimpleGraph D)).filter (fun G => ConnOn D (edgesOf G)) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [connected_iff_connOn_edgesOf, edgeSet_nonempty_iff]
    refine ⟨And.left, fun h => ⟨h, fun h0 => ?_⟩⟩
    rw [h0] at h
    exact absurd (card_le_one_of_connOn_empty h) (by omega)
  rw [hfilter, sum_graphs_eq_sum_edgeSets (U := D) (fun E => ConnOn D E)
    (fun E => ∫ c, ∏ p ∈ E, mayerBond χ β lam (c p.1) (c p.2) ∂dipoleField χ N β lam)]
  unfold mayerActivity connIntegral connWeight
  simp only [Finset.prod_const_one, one_mul, relConnSum_singletons]
  exact integral_finsetSum _ fun E _ => integrable_of_boxBounded hχ hlam hN β
    (Finset.measurable_prod _ fun p _ => measurable_pairWeight (measurable_mayerBond hχ hlam β) p)
    (BoxBounded.prod _ fun p _ => boxBounded_mayerBond hχ hlam β N p.1 p.2)

/-- `κ({D}) = 𝖬(D)`. -/
theorem multipoleConnIntegral_singleton (β M : ℝ) {D : Finset ℕ} (hD : D.Nonempty) :
    multipoleConnIntegral χ N β lam M {D} = multipolePartitionFunction χ N β lam M D := by
  unfold multipoleConnIntegral connIntegral connWeight
  simp only [relConnSum_singleton hD, Finset.prod_singleton, mul_one]
  rw [multipolePartitionFunction_eq_integral, integral_pi_eq_integral_dipoleField hχ hlam hN β
    (measurable_multipolePartitionFunctionIntegrand hχ hlam β M)]
  simp_rw [blockWeight_eq]

/-- **The hierarchical model in density form.** For a subpartition `X` and `M > 0`,
`𝖬^0_∞(X) 𝔼_{𝖯^X}[f] = 𝔼_{μ^{⊗ ℕ}}[(∏_{B ∈ X} 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij}) f]`. -/
theorem prod_mul_integral_hierarchicalModel (hM : 0 < M) (β : ℝ) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {f : (X.biUnion id → ℂ × ℂ) → ℝ} (hf : Measurable f) :
    (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
        ∫ y, f y ∂hierarchicalModel χ N β lam M X =
      ∫ c, (∏ B ∈ X, blockWeight χ β lam M B c) * f ((X.biUnion id).restrict c)
        ∂dipoleField χ N β lam := by
  have hMpos : ∀ S ∈ X, 0 < multipolePartitionFunction χ N β lam M S := fun S hS =>
    multipolePartitionFunction_pos hχ hlam β hM hN (hX.1 S hS)
  rw [hierarchicalModel_eq, integral_withDensity_eq_integral_toReal_smul
    (measurable_hierarchicalModelDensity hχ hlam N β M)
    (Filter.Eventually.of_forall fun y => ENNReal.prod_lt_top fun S _ => ENNReal.ofReal_lt_top)]
  have hdens : ∀ y : X.biUnion id → ℂ × ℂ, (hierarchicalModelDensity χ N β lam M X y).toReal =
      ∏ S ∈ X, ((multipolePartitionFunction χ N β lam M S)⁻¹ *
        hierarchicalBlockWeight χ β lam M X S y) := by
    intro y
    rw [hierarchicalModelDensity, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun S hS => ENNReal.toReal_ofReal (mul_nonneg ?_ ?_)
    · exact inv_nonneg.2 (hMpos S hS).le
    · exact hierarchicalBlockWeight_nonneg χ β lam M X S y
  simp_rw [hdens, smul_eq_mul, Finset.prod_mul_distrib]
  rw [← integral_const_mul]
  have hcancel : ∀ y : X.biUnion id → ℂ × ℂ,
      (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
        ((∏ S ∈ X, (multipolePartitionFunction χ N β lam M S)⁻¹) *
          (∏ S ∈ X, hierarchicalBlockWeight χ β lam M X S y) * f y) =
        (∏ S ∈ X, hierarchicalBlockWeight χ β lam M X S y) * f y := by
    intro y
    rw [← mul_assoc, ← mul_assoc, ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl fun S hS => mul_inv_cancel₀ (hMpos S hS).ne', Finset.prod_const_one,
      one_mul]
  simp_rw [hcancel]
  rw [integral_pi_eq_integral_dipoleField hχ hlam hN β
    (f := fun y => (∏ S ∈ X, hierarchicalBlockWeight χ β lam M X S y) * f y)
    ((Finset.measurable_prod _ fun S _ => measurable_hierarchicalBlockWeight hχ hlam β M S).mul hf)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only
  rw [Finset.prod_congr rfl fun S hS => hierarchicalBlockWeight_restrict hS c]

/-- `κ(Y) = 𝖬^0_∞(Y) 𝖪^mult(Y)` for a subpartition `Y` with at least two blocks. -/
theorem multipoleConnIntegral_eq (hM : 0 < M) (β : ℝ) {Y : Finset (Finset ℕ)}
    (hY : IsSubpartition Y) (h2 : 2 ≤ Y.card) :
    multipoleConnIntegral χ N β lam M Y =
      (∏ S ∈ Y, multipolePartitionFunction χ N β lam M S) * multipoleActivity χ N β lam M Y := by
  rw [multipoleActivity_eq_sum, Finset.mul_sum]
  have h1 : ∀ G : SimpleGraph (Y.biUnion id),
      (∏ S ∈ Y, multipolePartitionFunction χ N β lam M S) *
          ∫ y, multipoleActivityIntegrand χ β lam M G y ∂hierarchicalModel χ N β lam M Y =
        ∫ c, (∏ B ∈ Y, blockWeight χ β lam M B c) *
          ∏ p ∈ edgesOf G, unlinkedBond χ β lam M (c p.1) (c p.2) ∂dipoleField χ N β lam := by
    intro G
    rw [prod_mul_integral_hierarchicalModel hχ hlam hN hM β hY
      (measurable_multipoleActivityIntegrand hχ hlam β M G)]
    simp_rw [multipoleActivityIntegrand_restrict]
  rw [Finset.sum_congr rfl fun G _ => h1 G]
  have hfilter : (Finset.univ : Finset (SimpleGraph (Y.biUnion id))).filter (fun E =>
      (∀ i j : Y.biUnion id, E.Adj i j →
          ∃ S ∈ Y, ∃ S' ∈ Y, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
        E.edgeSet.Nonempty ∧
        (E ⊔ SimpleGraph.fromRel fun i j : Y.biUnion id =>
          ∃ S ∈ Y, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected) =
      (Finset.univ : Finset (SimpleGraph (Y.biUnion id))).filter (fun G =>
        edgesOf G ⊆ interPairs Y ∧ ConnOn (Y.biUnion id) (edgesOf G ∪ intraPairs Y)) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [forall_adj_iff_edgesOf_subset_interPairs hY, edgeSet_nonempty_iff, connected_sup_iff]
    refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun h0 => ?_, h.2⟩⟩
    have h' := h.2
    rw [h0, Finset.empty_union] at h'
    exact absurd (card_le_one_of_connOn_intraPairs hY h') (by omega)
  rw [hfilter, sum_graphs_eq_sum_edgeSets (U := Y.biUnion id)
    (fun E => E ⊆ interPairs Y ∧ ConnOn (Y.biUnion id) (E ∪ intraPairs Y))
    (fun E => ∫ c, (∏ B ∈ Y, blockWeight χ β lam M B c) *
      ∏ p ∈ E, unlinkedBond χ β lam M (c p.1) (c p.2) ∂dipoleField χ N β lam)]
  have hset : (pairsOn (Y.biUnion id)).powerset.filter
      (fun E => E ⊆ interPairs Y ∧ ConnOn (Y.biUnion id) (E ∪ intraPairs Y)) =
      (interPairs Y).powerset.filter (fun E => ConnOn (Y.biUnion id) (E ∪ intraPairs Y)) := by
    ext E
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨h.1.trans interPairs_subset_pairsOn, h⟩⟩
  rw [hset]
  unfold multipoleConnIntegral connIntegral connWeight relConnSum
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ fun E _ => integrable_of_boxBounded hχ hlam hN β
    ((Finset.measurable_prod _ fun B _ => measurable_blockWeight hχ hlam β M B).mul
      (Finset.measurable_prod _ fun p _ =>
        measurable_pairWeight (measurable_unlinkedBond hχ hlam β M) p))
    ((BoxBounded.prod _ fun B _ => boxBounded_blockWeight hχ hlam β M N B).mul
      (BoxBounded.prod _ fun p _ => boxBounded_unlinkedBond hχ hlam β M N p.1 p.2))

/-- `∑_{π ∈ 𝚷(D)} κ(π) = 𝖬(D) + ∑_{π ∈ 𝚷(D), |π| ≥ 2} 𝖬^0_∞(π) 𝖪^mult(π)`. -/
theorem sum_partitions_multipoleConnIntegral (hM : 0 < M) (β : ℝ) {D : Finset ℕ}
    (hD : D.Nonempty) :
    ∑ π ∈ partitions D, multipoleConnIntegral χ N β lam M π =
      multipolePartitionFunction χ N β lam M D +
        ∑ π ∈ (partitions D).filter (fun π => 2 ≤ π.card),
          (∏ S ∈ π, multipolePartitionFunction χ N β lam M S) *
            multipoleActivity χ N β lam M π := by
  rw [← Finset.sum_filter_add_sum_filter_not (partitions D) (fun π => 2 ≤ π.card), add_comm]
  congr 1
  · have hone : (partitions D).filter (fun π => ¬ 2 ≤ π.card) = {{D}} := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_singleton, not_le]
      constructor
      · rintro ⟨hπ, h2⟩
        exact eq_singleton_of_mem_partitions hπ
          (by have := card_pos_of_mem_partitions hπ hD; omega)
      · rintro rfl
        exact ⟨singleton_mem_partitions hD, by simp⟩
    rw [hone, Finset.sum_singleton, multipoleConnIntegral_singleton hχ hlam hN β M hD]
  · refine Finset.sum_congr rfl fun π hπ => ?_
    rw [Finset.mem_filter] at hπ
    exact multipoleConnIntegral_eq hχ hlam hN hM β (mem_partitions.1 hπ.1).1 hπ.2

end Transport

/-! ### Equation (5.165) -/

/-- **Equation (5.165)** (proof of Lemma 5.46): for `|V| ≥ 2`,
`𝖪^dip_{β,λ}(V) = 𝖬^0_∞(V) + ∑_{π ∈ 𝚷(V), |π| ≥ 2} 𝖬^0_∞(π) 𝖪^mult_{β,λ}(π)`, where
`𝖬^0_∞(π) = ∏_{S ∈ π} 𝖬_{β,λ}(S)` (eq. (4.17) with `ε₀ = ∞`) and `𝖬^0_∞(V)` is the
single-block term `𝖬_{β,λ}(V)`. The paper has `M > 20`. Here `M ≥ 1` suffices (`𝓑_ij^c ⊂ 𝒜_ij`,
Remark 4.6). -/
theorem dipoleActivity_eq_sum_partitions (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (hM : 1 ≤ M) (β : ℝ) {V : Finset ℕ} (hV : 2 ≤ V.card) :
    dipoleActivity χ N β lam V =
      multipolePartitionFunction χ N β lam M V +
        ∑ π ∈ (partitions V).filter (fun π => 2 ≤ π.card),
          (∏ S ∈ π, multipolePartitionFunction χ N β lam M S) *
            multipoleActivity χ N β lam M π := by
  have hVne : V.Nonempty := Finset.card_pos.1 (by omega)
  rw [← mayerActivity_eq_dipoleActivity hχ hlam hN β hV, mayerActivity_eq_sum hχ hlam hN hM β hVne,
    sum_partitions_multipoleConnIntegral hχ hlam hN (by linarith) β hVne]

/-! ### Corollary 4.61: the cluster expansion of the hierarchical model -/

section Corollary

theorem biUnion_powerset_id {α : Type*} [DecidableEq α] (U : Finset α) :
    U.powerset.biUnion id = U := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_powerset, id]
  exact ⟨fun ⟨S, hS, hx⟩ => hS hx, fun hx => ⟨{x}, Finset.singleton_subset_iff.2 hx,
    Finset.mem_singleton_self x⟩⟩

/-- The product over `ℰ^inter(X)`, written over the labels of `V_X` as in the frozen
definitions. -/
theorem prod_prod_ite_inter {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (c : ℕ → ℂ × ℂ)
    (F : ℂ × ℂ → ℂ × ℂ → ℝ) :
    ∏ i : X.biUnion id, ∏ j : X.biUnion id,
        (if i < j ∧ ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S' then
          F (c i) (c j) else 1) =
      ∏ p ∈ interPairs X, F (c p.1) (c p.2) := by
  refine (prod_prod_ite_pred (U := X.biUnion id)
    (fun a b => a < b ∧ ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ a ∈ S ∧ b ∈ S')
    fun a b => F (c a) (c b)).trans ?_
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨-, h12, S, hS, S', hS', hSS', h1, h2⟩
    exact mem_interPairs_of hX hS hS' hSS' h1 h2 h12
  · intro hp
    obtain ⟨S, hS, S', hS', hSS', h1, h2⟩ := exists_of_mem_interPairs hp
    have := mem_pairsOn.1 (interPairs_subset_pairsOn hp)
    exact ⟨⟨this.1, this.2.1⟩, this.2.2, S, hS, S', hS', hSS', h1, h2⟩

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
include hχ hlam hN

/-- `κ(Y) = 𝖬^0_∞(Y) 𝖪̃(Y)` for every nonempty subpartition `Y`, with `𝖪̃(Y) = 𝖪^mult(Y)` if
`|Y| ≥ 2` and `𝖪̃({B}) = 1`. -/
theorem multipoleConnIntegral_eq_prod_mul (hM : 0 < M) (β : ℝ) {Y : Finset (Finset ℕ)}
    (hY : IsSubpartition Y) (hne : Y.Nonempty) :
    multipoleConnIntegral χ N β lam M Y =
      (∏ S ∈ Y, multipolePartitionFunction χ N β lam M S) *
        (if 2 ≤ Y.card then multipoleActivity χ N β lam M Y else if Y.card = 1 then 1 else 0) := by
  by_cases h2 : 2 ≤ Y.card
  · rw [ite_eq_left h2, multipoleConnIntegral_eq hχ hlam hN hM β hY h2]
  · have h1 : Y.card = 1 := by
      have := Finset.card_pos.2 hne
      omega
    obtain ⟨B, rfl⟩ := Finset.card_eq_one.1 h1
    rw [ite_eq_right h2, ite_eq_left h1, mul_one, Finset.prod_singleton,
      multipoleConnIntegral_singleton hχ hlam hN β M (hY.1 B (Finset.mem_singleton_self B))]

/-- **Corollary 4.61**, the second component expansion in its proof:
`𝔼_{𝖯^X}[∏_{ij ∈ ℰ^inter(X)} e^{-β v_ij} 𝟙_{𝓑_ij^c}]
= ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∏ₗ 𝖪^mult(Xₗ)`.
Grouping the inter-block edges gives this expansion. Comparing it with the
zero-model expansion identifies the activities by induction, separately from
Lemma 4.60 in the dipole-composition argument. Here `M > 0` suffices. -/
theorem coro_4_61_expansion (hM : 0 < M) (β : ℝ) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) :
    ∫ c, ∏ i : X.biUnion id, ∏ j : X.biUnion id,
        (if i < j ∧ ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S' then
          (if MultipoleLinked M lam (c i) (c j) then 0 else
            Real.exp (-β * dipoleInteraction χ lam (c i) (c j)))
        else 1) ∂hierarchicalModel χ N β lam M X =
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∏ i, multipoleActivity χ N β lam M (Xs i) := by
  set K := multipoleActivity χ N β lam M
  set w : Finset (Finset ℕ) → ℝ := fun Y => if 2 ≤ Y.card then K Y else if Y.card = 1 then 1 else 0
  have hMpos : ∀ S ∈ X, 0 < multipolePartitionFunction χ N β lam M S := fun S hS =>
    multipolePartitionFunction_pos hχ hlam β hM hN (hX.1 S hS)
  have hM0 : (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) ≠ 0 :=
    (Finset.prod_pos hMpos).ne'
  -- the integrand
  set f : (X.biUnion id → ℂ × ℂ) → ℝ := fun c => ∏ i : X.biUnion id, ∏ j : X.biUnion id,
    (if i < j ∧ ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S' then
      (if MultipoleLinked M lam (c i) (c j) then 0 else
        Real.exp (-β * dipoleInteraction χ lam (c i) (c j))) else 1) with hfdef
  have hfm : Measurable f := by
    refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases h : i < j ∧ ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S'
    · simp only [h, and_self, ite_true]
      exact measurable_unlinkedPairWeight_apply hχ hlam β M i j
    · simp only [h, ite_false]
      exact measurable_const
  -- step 1: density form
  have h1 : (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) *
      ∫ y, f y ∂hierarchicalModel χ N β lam M X = multipoleClusterIntegral χ N β lam M X := by
    rw [prod_mul_integral_hierarchicalModel hχ hlam hN hM β hX hfm]
    unfold multipoleClusterIntegral clusterIntegral clusterWeight
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [hfdef, unlinkedBond, add_sub_cancel]
    congr 1
    exact prod_prod_ite_inter hX c (unlinkedPairWeight χ β lam M)
  -- step 2: partition sum of the connected weights
  have h2 : multipoleClusterIntegral χ N β lam M X =
      (∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * partitionSum w X := by
    rw [multipoleClusterIntegral, clusterIntegral_eq_partitionSum hχ hlam hN
      (measurable_blockWeight hχ hlam β M) (dependsOn_blockWeight χ β lam M)
      (boxBounded_blockWeight hχ hlam β M N) (measurable_unlinkedBond hχ hlam β M)
      (boxBounded_unlinkedBond hχ hlam β M N) β hX X le_rfl]
    unfold partitionSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝒴 h𝒴 => ?_
    have h𝒴s := (mem_partitions.1 h𝒴).1
    have hY : ∀ Y ∈ 𝒴,
        connIntegral χ N β lam (blockWeight χ β lam M) (unlinkedBond χ β lam M) Y =
          (∏ S ∈ Y, multipolePartitionFunction χ N β lam M S) * w Y := fun Y hY =>
      multipoleConnIntegral_eq_prod_mul hχ hlam hN hM β
        (isSubpartition_mono hX (subset_of_mem_partitions h𝒴 hY)) (h𝒴s.1 Y hY)
    rw [Finset.prod_congr rfl hY, Finset.prod_mul_distrib]
    congr 1
    have := Finset.prod_biUnion (f := fun S => multipolePartitionFunction χ N β lam M S) h𝒴s.2
    rw [(mem_partitions.1 h𝒴).2] at this
    exact this.symm
  -- step 3: disjoint families
  have h3 : partitionSum w X =
      ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card), ∏ Y ∈ 𝒱, K Y :=
    (sum_disjointFamilies X (fun Y => 2 ≤ Y.card) (fun _ h => h) K).symm
  -- step 4: the tuples
  have h4 : ∀ n : ℕ, ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)), ∏ i, K (Xs i) =
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) ∧ ∀ i, 2 ≤ (Xs i).card),
        ∏ i, K (Xs i) := by
    intro n
    rw [← Finset.filter_filter]
    refine (Finset.sum_filter_of_ne fun Xs _ hne => fun i => ?_).symm
    by_contra hlt
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i)
      (multipoleActivity_eq_zero_of_card_le_one χ N β lam M (by omega)))
  have h5 := tsum_tuples_eq_sum X.powerset (fun Y => 2 ≤ Y.card)
    (fun Y h => Finset.card_pos.1 (by omega)) K
  rw [biUnion_powerset_id] at h5
  have hfilt : (disjointFamilies X (fun Y => 2 ≤ Y.card)).filter (· ⊆ X.powerset) =
      disjointFamilies X (fun Y => 2 ≤ Y.card) := by
    refine Finset.filter_true_of_mem fun 𝒱 h𝒱 Y hY => ?_
    exact Finset.mem_powerset.2 ((mem_disjointFamilies.1 h𝒱).1 Y hY)
  rw [hfilt] at h5
  have key : ∫ y, f y ∂hierarchicalModel χ N β lam M X = partitionSum w X :=
    mul_left_cancel₀ hM0 (h1.trans h2)
  rw [key, h3, ← h5]
  refine tsum_congr fun n => ?_
  congr 1
  rw [h4 n]
  congr 1
  ext Xs
  simp only [Finset.mem_filter]

end Corollary

end Multipole

end MultipoleBKT

end
