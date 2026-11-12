/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Multipole.Transport
public import MultipoleBKT.Multipole.Factorization
public import MultipoleBKT.Matching.Pair

/-!
# Cluster expansions relative to a family of blocks

The two expansions in the proofs of Corollary 4.61 and of equation (5.165).

**Expansion relative to blocks.** Given block weights `h_B` (functions of the dipoles of `B`)
and pair weights `φ_ij = φ(x_i, y_i, x_j, y_j)`, the integral against `μ^{⊗ ℕ}` of
`clusterWeight h φ X = (∏_{B ∈ X} h_B) ∏_{ij ∈ ℰ^inter(X)} (1 + φ_ij)` satisfies the root recursion
`Ξ(X) = ∑_{B₀ ∈ Y ⊆ X} κ(Y) Ξ(X \ Y)` (`clusterIntegral_root`), with
`κ(Y) = ∫ (∏_{B ∈ Y} h_B) ∑_{E ∈ 𝖤'(Y)} ∏_{ij ∈ E} φ_ij`: expand the product over `ℰ^inter(X)`,
group the edge sets by connected components (`sum_powerset_interPairs_root`) and factorize the
integral over the disjoint blocks (`integral_mul_of_dependsOn`). Hence `Ξ` is the partition sum
of `κ` on the subfamilies of a subpartition (`clusterIntegral_eq_partitionSum`).

**Decomposition by the near graph** (`prod_stablePairWeight_eq_sum`). For `M ≥ 1`, pointwise,
`∏_{i<j ∈ U} e^{-β v_ij} 𝟙_{𝒜_ij}
= ∑_{σ ∈ 𝚷(U)} (∏_{B ∈ σ} 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij})
∏_{ij ∈ ℰ^inter(σ)} e^{-β v_ij} 𝟙_{𝓑_ij^c}`: only the partition into the connected components
of the near graph contributes, and `𝓑_ij^c ⊂ 𝒜_ij` (Remark 4.6).
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace Multipole

open SetPartition
open scoped Classical

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### Weights relative to a family of blocks -/

section Weights

/-- `∑_{E ∈ 𝖤'(Y)} ∏_{p ∈ E} g(p)`, where `𝖤'(Y)` is the set of edge sets `E ⊆ ℰ^inter(Y)` such
that `E ∪ ℰ^intra(Y)` connects `V_Y`. -/
noncomputable def relConnSum {R : Type*} [CommSemiring R] (g : ℕ × ℕ → R)
    (Y : Finset (Finset ℕ)) : R :=
  ∑ E ∈ (interPairs Y).powerset.filter (fun E => ConnOn (Y.biUnion id) (E ∪ intraPairs Y)),
    ∏ p ∈ E, g p

/-- The weight `(∏_{B ∈ X} h_B) ∏_{ij ∈ ℰ^inter(X)} (1 + φ_ij)` of a family of blocks. -/
noncomputable def clusterWeight (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ)
    (X : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ B ∈ X, h B c) * ∏ p ∈ interPairs X, (1 + φ (c p.1) (c p.2))

/-- The connected weight `(∏_{B ∈ Y} h_B) ∑_{E ∈ 𝖤'(Y)} ∏_{ij ∈ E} φ_ij`. -/
noncomputable def connWeight (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ)
    (Y : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ B ∈ Y, h B c) * relConnSum (fun p => φ (c p.1) (c p.2)) Y

variable (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ)

/-- The pointwise root recursion. -/
theorem clusterWeight_root {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {B₀ : Finset ℕ}
    (hB₀ : B₀ ∈ X) (c : ℕ → ℂ × ℂ) :
    clusterWeight h φ X c =
      ∑ Y ∈ X.powerset.filter (B₀ ∈ ·), connWeight h φ Y c * clusterWeight h φ (X \ Y) c := by
  unfold clusterWeight connWeight relConnSum
  rw [Finset.prod_one_add, sum_powerset_interPairs_root hX hB₀, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y hY => ?_
  rw [Finset.prod_one_add]
  have hYX : Y ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hY).1
  rw [← Finset.prod_sdiff hYX]
  ring

variable {h φ}

theorem measurable_pairWeight (hφ : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => φ q.1 q.2)
    (p : ℕ × ℕ) : Measurable fun c : ℕ → ℂ × ℂ => φ (c p.1) (c p.2) := by
  have : Measurable fun c : ℕ → ℂ × ℂ => (c p.1, c p.2) := by fun_prop
  exact hφ.comp this

theorem measurable_clusterWeight (hh : ∀ B, Measurable (h B))
    (hφ : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => φ q.1 q.2) (X : Finset (Finset ℕ)) :
    Measurable (clusterWeight h φ X) := by
  unfold clusterWeight
  exact (Finset.measurable_prod _ fun B _ => hh B).mul
    (Finset.measurable_prod _ fun p _ => measurable_const.add (measurable_pairWeight hφ p))

theorem measurable_connWeight (hh : ∀ B, Measurable (h B))
    (hφ : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => φ q.1 q.2) (Y : Finset (Finset ℕ)) :
    Measurable (connWeight h φ Y) := by
  unfold connWeight relConnSum
  exact (Finset.measurable_prod _ fun B _ => hh B).mul
    (Finset.measurable_sum _ fun _ _ => Finset.measurable_prod _ fun p _ =>
      measurable_pairWeight hφ p)

theorem dependsOn_clusterWeight (hh : ∀ B, DependsOn (h B) (B : Set ℕ)) (X : Finset (Finset ℕ)) :
    DependsOn (clusterWeight h φ X) ((X.biUnion id : Finset ℕ) : Set ℕ) := by
  intro c c' hcc'
  unfold clusterWeight
  congr 1
  · refine Finset.prod_congr rfl fun B hB => hh B fun i hi => hcc' i ?_
    exact Finset.mem_coe.2 (subset_biUnion_of_mem hB (Finset.mem_coe.1 hi))
  · refine Finset.prod_congr rfl fun p hp => ?_
    have := mem_pairsOn.1 (interPairs_subset_pairsOn hp)
    rw [hcc' _ (Finset.mem_coe.2 this.1), hcc' _ (Finset.mem_coe.2 this.2.1)]

theorem dependsOn_connWeight (hh : ∀ B, DependsOn (h B) (B : Set ℕ)) (Y : Finset (Finset ℕ)) :
    DependsOn (connWeight h φ Y) ((Y.biUnion id : Finset ℕ) : Set ℕ) := by
  intro c c' hcc'
  unfold connWeight relConnSum
  congr 1
  · refine Finset.prod_congr rfl fun B hB => hh B fun i hi => hcc' i ?_
    exact Finset.mem_coe.2 (subset_biUnion_of_mem hB (Finset.mem_coe.1 hi))
  · refine Finset.sum_congr rfl fun E hE => Finset.prod_congr rfl fun p hp => ?_
    have hEY := Finset.mem_powerset.1 (Finset.mem_filter.1 hE).1
    have := mem_pairsOn.1 (interPairs_subset_pairsOn (hEY hp))
    dsimp only
    rw [hcc' _ (Finset.mem_coe.2 this.1), hcc' _ (Finset.mem_coe.2 this.2.1)]

theorem boxBounded_clusterWeight (hh : ∀ B, BoxBounded N (h B))
    (hφ : ∀ i j, BoxBounded N fun c => φ (c i) (c j)) (X : Finset (Finset ℕ)) :
    BoxBounded N (clusterWeight h φ X) :=
  (BoxBounded.prod _ fun B _ => hh B).mul
    (BoxBounded.prod _ fun p _ => (BoxBounded.const N 1).add (hφ p.1 p.2))

theorem boxBounded_connWeight (hh : ∀ B, BoxBounded N (h B))
    (hφ : ∀ i j, BoxBounded N fun c => φ (c i) (c j)) (Y : Finset (Finset ℕ)) :
    BoxBounded N (connWeight h φ Y) :=
  (BoxBounded.prod _ fun B _ => hh B).mul
    (BoxBounded.sum _ fun _ _ => BoxBounded.prod _ fun p _ => hφ p.1 p.2)

end Weights

/-! ### The integrated root recursion -/

section Integrated

/-- `Ξ(X) = ∫ (∏_{B ∈ X} h_B) ∏_{ij ∈ ℰ^inter(X)} (1 + φ_ij) dμ^{⊗ ℕ}`. -/
noncomputable def clusterIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ)
    (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ) (X : Finset (Finset ℕ)) : ℝ :=
  ∫ c, clusterWeight h φ X c ∂dipoleField χ N β lam

/-- `κ(Y) = ∫ (∏_{B ∈ Y} h_B) ∑_{E ∈ 𝖤'(Y)} ∏_{ij ∈ E} φ_ij dμ^{⊗ ℕ}`. -/
noncomputable def connIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ)
    (h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ) (φ : ℂ × ℂ → ℂ × ℂ → ℝ) (Y : Finset (Finset ℕ)) : ℝ :=
  ∫ c, connWeight h φ Y c ∂dipoleField χ N β lam

variable {h : Finset ℕ → (ℕ → ℂ × ℂ) → ℝ} {φ : ℂ × ℂ → ℂ × ℂ → ℝ}
variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
variable (hhm : ∀ B, Measurable (h B)) (hhd : ∀ B, DependsOn (h B) (B : Set ℕ))
  (hhb : ∀ B, BoxBounded N (h B)) (hφm : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => φ q.1 q.2)
  (hφb : ∀ i j, BoxBounded N fun c => φ (c i) (c j))
include hχ hlam hN hhm hhd hhb hφm hφb

/-- **Root recursion of `Ξ`.** -/
theorem clusterIntegral_root (β : ℝ) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {B₀ : Finset ℕ} (hB₀ : B₀ ∈ X) :
    clusterIntegral χ N β lam h φ X =
      ∑ Y ∈ X.powerset.filter (B₀ ∈ ·),
        connIntegral χ N β lam h φ Y * clusterIntegral χ N β lam h φ (X \ Y) := by
  unfold clusterIntegral connIntegral
  rw [show (fun c => clusterWeight h φ X c) = fun c => ∑ Y ∈ X.powerset.filter (B₀ ∈ ·),
      connWeight h φ Y c * clusterWeight h φ (X \ Y) c from
    funext fun c => clusterWeight_root h φ hX hB₀ c]
  rw [integral_finsetSum (f := fun Y c => connWeight h φ Y c * clusterWeight h φ (X \ Y) c) _
    fun Y _ => integrable_of_boxBounded hχ hlam hN β
    ((measurable_connWeight hhm hφm Y).mul (measurable_clusterWeight hhm hφm (X \ Y)))
    ((boxBounded_connWeight hhb hφb Y).mul (boxBounded_clusterWeight hhb hφb (X \ Y)))]
  refine Finset.sum_congr rfl fun Y hY => ?_
  have hYX : Y ⊆ X := Finset.mem_powerset.1 (Finset.mem_filter.1 hY).1
  exact integral_mul_of_dependsOn hχ hlam hN β (disjoint_biUnion_sdiff hX hYX)
    (measurable_connWeight hhm hφm Y) (measurable_clusterWeight hhm hφm (X \ Y))
    (dependsOn_connWeight hhd Y) (dependsOn_clusterWeight hhd (X \ Y))

omit hhm hhd hhb hφm hφb in
theorem clusterIntegral_empty (β : ℝ) : clusterIntegral χ N β lam h φ ∅ = 1 := by
  have := isProbabilityMeasure_dipoleField hχ hlam hN β
  have hint : interPairs (∅ : Finset (Finset ℕ)) = ∅ := by
    simp [interPairs, pairsOn]
  simp [clusterIntegral, clusterWeight, hint]

/-- `Ξ` is the partition sum of `κ` on the subfamilies of a subpartition. -/
theorem clusterIntegral_eq_partitionSum (β : ℝ) {X₀ : Finset (Finset ℕ)}
    (hX₀ : IsSubpartition X₀) :
    ∀ X ⊆ X₀, clusterIntegral χ N β lam h φ X =
      partitionSum (connIntegral χ N β lam h φ) X :=
  eq_partitionSum_of_root _ X₀ (clusterIntegral_empty hχ hlam hN β)
    fun _ hX _ hB₀ => clusterIntegral_root hχ hlam hN hhm hhd hhb hφm hφb β
      (isSubpartition_mono hX₀ hX) hB₀

end Integrated

/-! ### The block weight of the hierarchical model -/

section BlockWeight

/-- The integrand `𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij}` of `𝖬(B)` (eq. (2.41)), as a
function of a configuration of all labels. -/
noncomputable def blockWeight (χ : ℂ → ℝ) (β lam M : ℝ) (B : Finset ℕ) (c : ℕ → ℂ × ℂ) : ℝ :=
  (if ConnOn B (linkedPairs M lam c B) then 1 else 0) *
    ∏ p ∈ pairsOn B, stablePairWeight χ β lam (c p.1) (c p.2)

theorem blockWeight_eq (χ : ℂ → ℝ) (β lam M : ℝ) (B : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    blockWeight χ β lam M B c = multipolePartitionFunctionIntegrand χ β lam M (B.restrict c) := by
  unfold blockWeight multipolePartitionFunctionIntegrand
  congr 1
  · exact if_congr (connected_fromRel_iff c B).symm rfl rfl
  · exact (prod_prod_ite_lt (U := B) fun i j => stablePairWeight χ β lam (c i) (c j)).symm

theorem measurable_blockWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (B : Finset ℕ) :
    Measurable (blockWeight χ β lam M B) := by
  have h := (measurable_multipolePartitionFunctionIntegrand (S := B) hχ hlam β M).comp
    (Finset.measurable_restrict (X := fun _ : ℕ => ℂ × ℂ) B)
  convert h using 1
  funext c
  exact blockWeight_eq χ β lam M B c

theorem dependsOn_blockWeight (χ : ℂ → ℝ) (β lam M : ℝ) (B : Finset ℕ) :
    DependsOn (blockWeight χ β lam M B) (B : Set ℕ) := by
  intro c c' hcc'
  rw [blockWeight_eq, blockWeight_eq]
  congr 1
  funext i
  exact hcc' i (Finset.mem_coe.2 i.2)

theorem boxBounded_blockWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (N : ℕ)
    (B : Finset ℕ) : BoxBounded N (blockWeight χ β lam M B) := by
  obtain ⟨b, hb⟩ := exists_bound_multipolePartitionFunctionIntegrand (S := B) hχ hlam β M N
  refine ⟨b, fun c hc => ?_⟩
  rw [blockWeight_eq]
  exact hb _ fun i => hc i

/-- `e^{-β v_ij} 𝟙_{𝓑_ij^c} = 𝟙_{𝓑_ij^c} e^{-β v_ij} 𝟙_{𝒜_ij}`, by Remark 4.6 (`M ≥ 1`). -/
theorem unlinkedPairWeight_eq (hM : 1 ≤ M) (d e : ℂ × ℂ) :
    unlinkedPairWeight χ β lam M d e =
      (if MultipoleLinked M lam d e then 0 else 1) * stablePairWeight χ β lam d e := by
  unfold unlinkedPairWeight stablePairWeight
  by_cases h : MultipoleLinked M lam d e
  · simp [h]
  · simp [h, remark_4_6 hM h]

end BlockWeight

/-! ### Decomposition by the near graph -/

section NearGraph

/-- **Decomposition by the connected components of the near graph** (proof of equation (5.165)). For `M ≥ 1`, pointwise,
`∏_{i<j ∈ U} e^{-β v_ij} 𝟙_{𝒜_ij}
= ∑_{σ ∈ 𝚷(U)} (∏_{B ∈ σ} 𝟙_{𝓑_B} ∏_{i<j ∈ B} e^{-β v_ij} 𝟙_{𝒜_ij})
∏_{ij ∈ ℰ^inter(σ)} e^{-β v_ij} 𝟙_{𝓑_ij^c}`. -/
theorem prod_stablePairWeight_eq_sum (hM : 1 ≤ M) (c : ℕ → ℂ × ℂ) (U : Finset ℕ) :
    ∏ p ∈ pairsOn U, stablePairWeight χ β lam (c p.1) (c p.2) =
      ∑ σ ∈ partitions U, (∏ B ∈ σ, blockWeight χ β lam M B c) *
        ∏ p ∈ interPairs σ, unlinkedPairWeight χ β lam M (c p.1) (c p.2) := by
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · have hint : interPairs (∅ : Finset (Finset ℕ)) = ∅ := by
        simp [interPairs, pairsOn]
      simp [partitions_empty, hint, pairsOn]
    set sw : ℕ × ℕ → ℝ := fun p => stablePairWeight χ β lam (c p.1) (c p.2) with hsw
    set uw : ℕ × ℕ → ℝ := fun p => unlinkedPairWeight χ β lam M (c p.1) (c p.2) with huw
    rw [sum_partitions_root ha]
    have hterm : ∀ B ∈ U.powerset.filter (a ∈ ·),
        ∑ σ ∈ partitions (U \ B), (∏ B' ∈ insert B σ, blockWeight χ β lam M B' c) *
            ∏ p ∈ interPairs (insert B σ), uw p =
          (if ConnOn B (linkedPairs M lam c U ∩ pairsOn B) ∧
              Disjoint (linkedPairs M lam c U) (crossPairs B (U \ B)) then 1 else 0) *
            ∏ p ∈ pairsOn U, sw p := by
      intro B hB
      rw [Finset.mem_filter, Finset.mem_powerset] at hB
      have hBne : B.Nonempty := ⟨a, hB.2⟩
      have hd : Disjoint B (U \ B) := Finset.disjoint_sdiff
      have h1 : ∀ σ ∈ partitions (U \ B), (∏ B' ∈ insert B σ, blockWeight χ β lam M B' c) *
            ∏ p ∈ interPairs (insert B σ), uw p =
          (blockWeight χ β lam M B c * ∏ p ∈ crossPairs B (U \ B), uw p) *
            ((∏ B' ∈ σ, blockWeight χ β lam M B' c) * ∏ p ∈ interPairs σ, uw p) := by
        intro σ hσ
        rw [Finset.prod_insert (notMem_of_mem_partitions_sdiff hBne hσ),
          interPairs_insert hB.1 hσ hBne,
          Finset.prod_union (disjoint_interPairs_crossPairs hσ)]
        ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← ih (U \ B)
        (Finset.sdiff_ssubset hB.1 hBne)]
      -- the cross factor
      have hcross : ∏ p ∈ crossPairs B (U \ B), uw p =
          (if Disjoint (linkedPairs M lam c U) (crossPairs B (U \ B)) then 1 else 0) *
            ∏ p ∈ crossPairs B (U \ B), sw p := by
        simp only [huw, hsw, unlinkedPairWeight_eq hM, Finset.prod_mul_distrib]
        congr 1
        have hne : ∀ x ∈ crossPairs B (U \ B),
            (if MultipoleLinked M lam (c x.1) (c x.2) then (0 : ℝ) else 1) =
              if ¬ MultipoleLinked M lam (c x.1) (c x.2) then 1 else 0 := fun x _ => by
          split_ifs <;> simp_all
        rw [Finset.prod_congr rfl hne, Finset.prod_boole]
        refine if_congr ?_ rfl rfl
        rw [Finset.disjoint_right]
        refine forall₂_congr fun p hp => ?_
        rw [mem_linkedPairs]
        have hpU : p ∈ pairsOn U := by
          rw [← Finset.union_sdiff_of_subset hB.1, pairsOn_union]
          exact Finset.mem_union_right _ hp
        simp [hpU]
      have hblock : blockWeight χ β lam M B c =
          (if ConnOn B (linkedPairs M lam c U ∩ pairsOn B) then 1 else 0) *
            ∏ p ∈ pairsOn B, sw p := by
        rw [linkedPairs_inter_pairsOn hB.1]
        rfl
      rw [hblock, hcross]
      have hU : ∏ p ∈ pairsOn U, sw p =
          (∏ p ∈ pairsOn B, sw p) * (∏ p ∈ pairsOn (U \ B), sw p) *
            ∏ p ∈ crossPairs B (U \ B), sw p := by
        rw [← prod_pairsOn_union hd, Finset.union_sdiff_of_subset hB.1]
      rw [hU, ite_and]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      sum_conn_crossPairs_eq_one ha linkedPairs_subset, one_mul]

end NearGraph

end Multipole

end MultipoleBKT

end
