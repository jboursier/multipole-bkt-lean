/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteBase.Integrand
public import MultipoleBKT.Frozen.IsSubpartition
public import MultipoleBKT.Frozen.BlockProfile
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteChain.Positivity

/-!
# Block maps and the integral formula for multipole activities

See (4.51),
 and proof of Lemma 4.26.

The block map, graph translation and exact finite-box normalization are shared
with the appendix below the limiting-integrand proof. The displayed integral
coefficient is defined here. Positivity uses the chain construction for `M ≥ 9`.
The stronger range `0 < M < 9` uses the finite-box positivity argument.
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### Blocks of a subpartition -/

section Blocks

variable {X : Finset (Finset ℕ)}

/-- The block of `X` containing a label of `V_X`. -/
noncomputable def blockOf (X : Finset (Finset ℕ)) (i : X.biUnion id) : X :=
  ⟨(mem_biUnion.1 i.2).choose, (mem_biUnion.1 i.2).choose_spec.1⟩

theorem mem_blockOf (i : X.biUnion id) : (i : ℕ) ∈ (blockOf X i : Finset ℕ) :=
  (mem_biUnion.1 i.2).choose_spec.2

theorem blockOf_eq (hX : IsSubpartition X) {i : X.biUnion id} {S : Finset ℕ} (hS : S ∈ X)
    (hi : (i : ℕ) ∈ S) : blockOf X i = ⟨S, hS⟩ := by
  by_contra hne
  have hne' : (blockOf X i : Finset ℕ) ≠ S := fun h => hne (Subtype.ext h)
  have hdisj := hX.2 (blockOf X i).2 hS hne'
  exact Finset.disjoint_left.1 hdisj (mem_blockOf i) hi

theorem blockOf_eq_iff (hX : IsSubpartition X) (i : X.biUnion id) (S : X) :
    blockOf X i = S ↔ (i : ℕ) ∈ (S : Finset ℕ) := by
  constructor
  · rintro rfl
    exact mem_blockOf i
  · intro h
    exact blockOf_eq hX S.2 h

theorem blockOf_surjective (hX : IsSubpartition X) : Function.Surjective (blockOf X) := by
  intro S
  obtain ⟨x, hx⟩ := hX.1 S S.2
  have hxV : x ∈ X.biUnion id := mem_biUnion.2 ⟨S, S.2, hx⟩
  exact ⟨⟨x, hxV⟩, blockOf_eq hX S.2 hx⟩

theorem card_biUnion_eq_sum (hX : IsSubpartition X) :
    (X.biUnion id).card = ∑ S ∈ X, S.card :=
  card_biUnion fun _ hS _ hS' h => hX.2 hS hS' h

end Blocks

/-! ### The activity as a ratio of box integrals -/

section Activity

variable {X : Finset (Finset ℕ)}

theorem hierarchicalBlockWeight_eq (hX : IsSubpartition X) {S : Finset ℕ} (hS : S ∈ X)
    (c : X.biUnion id → ℂ × ℂ) :
    hierarchicalBlockWeight χ β lam M X S c = blockW χ β lam M (blockOf X) ⟨S, hS⟩ c := by
  have hset : {i : X.biUnion id | (i : ℕ) ∈ S} = {i | blockOf X i = ⟨S, hS⟩} := by
    ext i
    simp only [Set.mem_ofPred_eq]
    exact (blockOf_eq_iff hX i ⟨S, hS⟩).symm
  have hiff : ((SimpleGraph.fromRel fun i j : X.biUnion id =>
      MultipoleLinked M lam (c i) (c j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected ↔
      ((nearGraph M lam c).induce {i | blockOf X i = ⟨S, hS⟩}).Connected := by
    let e : ↥{i : X.biUnion id | (i : ℕ) ∈ S} ≃ ↥{i | blockOf X i = ⟨S, hS⟩} :=
      Equiv.subtypeEquivRight fun i => (blockOf_eq_iff hX i ⟨S, hS⟩).symm
    let iso : ((SimpleGraph.fromRel fun i j : X.biUnion id =>
        MultipoleLinked M lam (c i) (c j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}) ≃g
        ((nearGraph M lam c).induce {i | blockOf X i = ⟨S, hS⟩}) :=
      { toEquiv := e
        map_rel_iff' := by intro a b; rfl }
    exact iso.connected_iff
  unfold hierarchicalBlockWeight blockW
  congr 1
  · split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  simp only [blockOf_eq_iff hX]

theorem prod_hierarchicalBlockWeight (hX : IsSubpartition X) (c : X.biUnion id → ℂ × ℂ) :
    ∏ S ∈ X, hierarchicalBlockWeight χ β lam M X S c = ∏ S : X, blockW χ β lam M (blockOf X) S c := by
  rw [← Finset.prod_coe_sort X]
  exact prod_congr rfl fun S _ => hierarchicalBlockWeight_eq hX S.2 c

theorem adj_blockOf_ne (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : ∀ i j : X.biUnion id, E.Adj i j →
      ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') :
    ∀ i j, E.Adj i j → blockOf X i ≠ blockOf X j := by
  intro i j hij h
  obtain ⟨S, hS, S', hS', hne, hi, hj⟩ := hE i j hij
  rw [blockOf_eq hX hS hi, blockOf_eq hX hS' hj] at h
  exact hne (congrArg Subtype.val h)

open scoped Classical in
theorem reachable_blockOf (hX : IsSubpartition X) {E : SimpleGraph (X.biUnion id)}
    (hE : ∀ i j : X.biUnion id, E.Adj i j →
      ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S')
    (hconn : (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
      ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected) :
    ∀ S S' : X, (nodeGraph (Sym2.map (blockOf X)) E.edgeFinset).Reachable S S' := by
  have hwalk : ∀ u v (p : (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
      ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Walk u v),
      (nodeGraph (Sym2.map (blockOf X)) E.edgeFinset).Reachable (blockOf X u) (blockOf X v) := by
    intro u v p
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b c h p ih =>
      refine Reachable.trans ?_ ih
      rcases h with h | h
      · have hne := adj_blockOf_ne hX hE a b h
        refine (nodeGraph_adj_of_mem (e := s(a, b)) ?_ (by rw [Sym2.map_mk]) hne).reachable
        rw [mem_edgeFinset]
        exact h
      · rw [fromRel_adj] at h
        obtain ⟨-, ⟨S, hS, ha, hb⟩ | ⟨S, hS, hb, ha⟩⟩ := h <;>
          rw [blockOf_eq hX hS ha, blockOf_eq hX hS hb]
  intro S S'
  obtain ⟨i, rfl⟩ := blockOf_surjective hX S
  obtain ⟨j, rfl⟩ := blockOf_surjective hX S'
  obtain ⟨p⟩ := hconn.preconnected i j
  exact hwalk i j p

open scoped Classical in
/-- **`𝖪^mult` as box integrals.** -/
theorem multipoleActivity_eq_box (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (hX : IsSubpartition X) :
    multipoleActivity χ N β lam M X = (∏ S ∈ X, multipolePartitionFunction χ N β lam M S)⁻¹ *
      (((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ (X.biUnion id).card *
        ∑ E ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
          (∀ i j : X.biUnion id, E.Adj i j →
              ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
            E.edgeSet.Nonempty ∧
            (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
              ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected),
          ∫ c in boxConfig (X.biUnion id) N, multBox χ β lam M (blockOf X) E c) := by
  rw [multipoleActivity_eq_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun E _ => ?_
  have hdens := measurable_hierarchicalModelDensity hχ hlam N β M (X := X)
  rw [hierarchicalModel_eq, integral_withDensity_eq_integral_toReal_smul hdens
    (Eventually.of_forall fun c => ENNReal.prod_lt_top fun S _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ c, (hierarchicalModelDensity χ N β lam M X c).toReal •
      multipoleActivityIntegrand χ β lam M E c =
      (∏ S ∈ X, multipolePartitionFunction χ N β lam M S)⁻¹ *
        (bondProd χ β lam M E c * ∏ S : X, blockW χ β lam M (blockOf X) S c) := by
    intro c
    unfold hierarchicalModelDensity
    rw [smul_eq_mul, ENNReal.toReal_prod]
    have : ∀ S ∈ X, (ENNReal.ofReal ((multipolePartitionFunction χ N β lam M S)⁻¹ *
        hierarchicalBlockWeight χ β lam M X S c)).toReal =
        (multipolePartitionFunction χ N β lam M S)⁻¹ * hierarchicalBlockWeight χ β lam M X S c :=
      fun S _ => ENNReal.toReal_ofReal (mul_nonneg
        (inv_nonneg.2 (multipolePartitionFunction_nonneg χ N β lam M S))
        (hierarchicalBlockWeight_nonneg χ β lam M X S c))
    rw [prod_congr rfl this, prod_mul_distrib, prod_inv_distrib, prod_hierarchicalBlockWeight hX]
    show _ = _ * (multipoleActivityIntegrand χ β lam M E c * _)
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_pi_dipoleMeasure hχ hlam β hN, Fintype.card_coe]
  congr 2

end Activity

/-! ### The limit -/

section Limit

variable {X : Finset (Finset ℕ)}

/-- The limit `I_S` of `(1/N) ∫_{(Λ²)^S} Φ_S` is positive (for `M > 0`). -/
theorem multipoleBox_limit_pos (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 < M)
    {S : Finset ℕ} (hk : (S.card : ℕ∞) ≤ pStar β) (i₀ : S) :
    0 < ∫ c, anchorR i₀ c * multipoleBox χ β lam M c := by
  by_cases hchain : 9 ≤ M
  · exact MultipoleIntegral.RouteChain.anchored_integral_pos_of_chain hχ hβ hlam hchain hk i₀
  have hne : Nonempty S := ⟨i₀⟩
  have hSne : S.Nonempty := ⟨i₀, i₀.2⟩
  have hk' : (Fintype.card S : ℕ∞) ≤ pStar β := by rwa [Fintype.card_coe]
  have hint := integrable_anchor_multipoleBox (M := M) hχ hβ hlam hM.le hk' i₀
  obtain ⟨-, hJ⟩ := integral_boxConfig_eq 1 i₀ (measurable_multipoleBox hχ hlam β M)
    translationInvariant_multipoleBox hint
  have hpos := multipolePartitionFunction_pos hχ hlam β hM (le_refl 1) hSne
  rw [multipolePartitionFunction_eq_box hχ hlam (le_refl 1)] at hpos
  have hC := natCast_mul_dipoleNormalization_pos hχ hlam β (le_refl 1) (N := 1)
  have hJpos : 0 < ∫ c in boxConfig S 1, multipoleBox χ β lam M c := by
    by_contra h
    push Not at h
    have : ((1 : ℕ) * dipoleNormalization χ 1 β lam : ℝ)⁻¹ ^ S.card *
        ∫ c in boxConfig S 1, multipoleBox χ β lam M c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    push_cast at this hpos
    linarith
  rw [hJ] at hJpos
  refine lt_of_lt_of_le hJpos (integral_mono_of_nonneg (Eventually.of_forall fun c => ?_)
    hint (Eventually.of_forall fun c => ?_))
  · exact mul_nonneg (mul_nonneg (anchorR_nonneg i₀ c) (multipoleBox_nonneg χ β lam M c))
      ENNReal.toReal_nonneg
  · have h1 : (overlap 1 c).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using overlap_le 1 c)
    exact mul_le_of_le_one_right (mul_nonneg (anchorR_nonneg i₀ c)
      (multipoleBox_nonneg χ β lam M c)) h1

open scoped Classical in
/-- The displayed coefficient (4.51), with one unit-area translation
coordinate in every integral.
-/
noncomputable def multipoleIntegralCoefficient (χ : ℂ → ℝ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) (root : X.biUnion id) (roots : ∀ S : X, S.val) : ℝ :=
  (∑ E ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
      (∀ i j : X.biUnion id, E.Adj i j →
        ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
      E.edgeSet.Nonempty ∧
      (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
        ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected),
    ∫ c, anchorR root c * symBox χ β lam M (blockOf X) E c) /
    ∏ S : X, ∫ c, anchorR (roots S) c * multipoleBox χ β lam M c

end Limit

end Limits

end MultipoleBKT

end
