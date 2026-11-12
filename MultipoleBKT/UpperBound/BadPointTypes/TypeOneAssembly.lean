/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeOne.Successive
public import MultipoleBKT.Matching.RouteGeneric.Distance

/-!
# Lemma 5.40: assembling the combinatorial bound

The paper: proof of Lemma 5.40. The matching is removed first. The actual configuration then selects
bad-charge sets, injective partner maps and same-sign partitions. Only after these choices
are fixed are the dyadic scales summed and the fixed-data integral applied.
The successive cardinality bounds are proved in `RouteTypeOne/Counting.lean`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset MeasureTheory
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {n : ℕ}

theorem chargePos_eq_configEquivSum (c : Fin n → ℂ × ℂ) :
    chargePos c = configEquivSum (Fin n) c := by
  funext v
  rcases v with i | j <;> rfl

/-- Almost every configuration has no same-sign isosceles coincidence.
As in Section 4.1, the paper, square each
distance equality to obtain a nonzero polynomial, then take a finite union. -/
theorem ae_noIsosceles_config : ∀ᵐ c ∂(volume : Measure (Fin n → ℂ × ℂ)),
    NoIsosceles (fun k => (c k).1) ∧ NoIsosceles (fun k => (c k).2) := by
  have hz : ∀ᵐ z ∂(volume : Measure (Charge n → ℂ)),
      NoIsosceles (fun k => z (Sum.inl k)) ∧ NoIsosceles (fun k => z (Sum.inr k)) := by
    have hsub : ∀ f : Fin n → Charge n, Function.Injective f →
        ∀ᵐ z ∂(volume : Measure (Charge n → ℂ)), NoIsosceles (fun k => z (f k)) := by
      intro f hf
      have hsub' : {z : Charge n → ℂ | ¬ NoIsosceles fun k => z (f k)} ⊆
          ⋃ i : Fin n, ⋃ j : Fin n, ⋃ j' : Fin n, ⋃ (_ : j ≠ i ∧ j' ≠ i ∧ j ≠ j'),
            {z : Charge n → ℂ | ‖z (f i) - z (f j)‖ = ‖z (f i) - z (f j')‖} := by
        intro z hz
        simp only [NoIsosceles, not_forall, Set.mem_ofPred_eq, not_not] at hz
        obtain ⟨i, j, j', hji, hj'i, hjj', heq⟩ := hz
        exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨j',
          Set.mem_iUnion.2 ⟨⟨hji, hj'i, hjj'⟩, heq⟩⟩⟩⟩
      refine ae_iff.2 (measure_mono_null hsub' (measure_iUnion_null fun i => measure_iUnion_null
        fun j => measure_iUnion_null fun j' => measure_iUnion_null fun hne => ?_))
      -- The exceptional equation is |z_{f i}-z_{f j}|² - |z_{f i}-z_{f j'}|² = 0.
      let P := RouteGeneric.squaredDistance (f i) (f j) -
        RouteGeneric.squaredDistance (f i) (f j')
      have hp : P ≠ 0 := RouteGeneric.distanceDifference_ne_zero
        (hf.ne hne.1.symm) (hf.ne hne.2.1.symm) (by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact hne.2.2 (hf h)
          · exact hne.2.1 (hf h).symm)
      have hzero := RouteGeneric.volume_polynomial_zero P hp
      have he := (RouteGeneric.measurePreserving_realCoordinates (ι := Charge n)).measure_preimage_equiv
        {x | MvPolynomial.eval x P = 0}
      refine measure_mono_null (fun z hz => ?_) (he.trans hzero)
      change MvPolynomial.eval (RouteGeneric.realCoordinates (Charge n) z) P = 0
      simp only [P, map_sub, RouteGeneric.eval_squaredDistance]
      rw [hz, sub_self]
    filter_upwards [hsub Sum.inl Sum.inl_injective, hsub Sum.inr Sum.inr_injective] with z h1 h2
    exact ⟨h1, h2⟩
  have hqmp := (measurePreserving_configEquivSum (Fin n)).quasiMeasurePreserving
  exact hqmp.ae hz

theorem measurable_typeOneFactor {β lam h : ℝ} (hlam : 0 < lam) (Nₐ : ℕ) (D : TOData n)
    (v : Charge n) : Measurable fun z : Charge n → ℂ => typeOneFactor β lam h Nₐ D z v := by
  unfold typeOneFactor
  have hb : Measurable fun z : Charge n → ℂ => (box Nₐ).indicator (1 : ℂ → ℝ≥0∞) (z v) :=
    (measurable_const.indicator (TwoComponentCoulomb.measurableSet_box Nₐ)).comp
      (measurable_pi_apply v)
  have hd : Measurable fun z : Charge n → ℂ => z v - z (D.2.1 v) :=
    (measurable_pi_apply v).sub (measurable_pi_apply _)
  split_ifs
  · exact hb.mul measurable_const
  · exact hb.mul measurable_const
  · exact ((measurable_const.indicator measurableSet_closedBall).comp hd).mul measurable_const
  · exact (measurable_goodKernel hlam β h).comp hd

open scoped Classical in
/-- Removing the matching, then fixing bad sets, partner injections and same-sign
partitions before the dyadic scales. The sum is over the admissible unscaled data,
whose successive enumeration is `RouteTypeOne.card_blockFiber_eq_successive`. -/
theorem typeOnePartitionFunction_le_successive {p₀ : ℕ} {β lam ε₀ Kg : ℝ}
    (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀) (hlam : 0 < lam)
    (hlh : lam ≤ cutoff p₀ β lam ε₀) (hβ : 0 ≤ β) (hKg0 : 0 ≤ Kg)
    (hKg : ∫⁻ u, goodKernel β lam (cutoff p₀ β lam ε₀) u ≤ ENNReal.ofReal Kg) (Nₐ : ℕ) :
    (n.factorial : ℝ≥0∞) * typeOnePartitionFunction p₀ β lam ε₀ Nₐ n ≤
      ENNReal.ofReal (RouteTypeOne.successiveSum (clusterThreshold p₀ β) (fun B : RouteTypeOne.Base n =>
        (∑ s ∈ range (Nat.log 2 ⌊cutoff p₀ β lam ε₀ / lam⌋₊ + 1),
          crowdTerm (clusterThreshold p₀ β) β lam Nₐ s) ^ kindCount B.1 0 *
        ((Nₐ : ℝ) * (cutoff p₀ β lam ε₀ / 4) ^ (-(β / 2))) ^ kindCount B.1 1 *
        Kg ^ kindCount B.1 3)) := by
  classical
  rw [← RouteTypeOne.sum_bases_eq_successive]
  let q := clusterThreshold p₀ β
  let h := cutoff p₀ β lam ε₀
  let K := Nat.log 2 ⌊h / lam⌋₊
  let F : (Fin n → ℂ × ℂ) → ℝ≥0∞ := fun d =>
    (if badPointsTypeOne p₀ β lam ε₀ d = Finset.univ then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d)
  have hdyad : ∀ s, 0 < dyad lam s := fun s => by unfold dyad; positivity
  have hY : 0 ≤ (Nₐ : ℝ) * (h / 4) ^ (-(β / 2)) := by
    have : 0 ≤ (h / 4) ^ (-(β / 2)) := Real.rpow_nonneg (by positivity) _
    positivity
  have hbound : ∀ D : TOData n, 0 ≤ typeOneBound q β lam h Kg Nₐ D := fun D =>
    mul_nonneg (mul_nonneg (prod_nonneg fun v _ => by
      have := hdyad (D.2.2 v)
      positivity) (pow_nonneg hY _)) (pow_nonneg hKg0 _)
  -- Step 1: remove the pairing, retaining its factorial.
  have hZ : (n.factorial : ℝ≥0∞) * typeOnePartitionFunction p₀ β lam ε₀ Nₐ n =
      ∫⁻ c in boxPi Nₐ n, F (matched c) := by
    rw [← lintegral_stablePairs_eq F Nₐ]
    unfold typeOnePartitionFunction
    congr 1
    refine lintegral_congr fun c => ?_
    simp only [F]
    by_cases h1 : badPointsTypeOne p₀ β lam ε₀ c = Finset.univ <;>
      by_cases h2 : StablePairs c <;> simp [h1, h2]
  rw [hZ]
  -- Steps 2–4: actual data select their bad sets, injections and partitions.
  -- Step 5: only the overcrowded roots carry dyadic scales.
  have hpt : ∀ᵐ c ∂(volume.restrict (boxPi Nₐ n)), F (matched c) ≤
      ∑ B ∈ RouteTypeOne.bases (n := n) q, ∑ sc ∈ RouteTypeOne.scales K B.1,
        ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v := by
    filter_upwards [ae_restrict_mem (measurableSet_boxPi Nₐ n),
      ae_restrict_of_ae ae_noIsosceles_config] with c hc hiso
    by_cases hI : badPointsTypeOne p₀ β lam ε₀ (matched c) = Finset.univ
    · let D := typeOneData p₀ β lam ε₀ c
      let B : RouteTypeOne.Base n := (D.1, D.2.1)
      have hV : TypeOneValid q D := typeOneData_valid hI
      have hB : B ∈ RouteTypeOne.bases q := by
        apply mem_filter.2
        refine ⟨mem_univ _, ?_, ?_⟩
        · exact ⟨hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2.1, fun _ _ => rfl⟩
        · exact RouteTypeOne.typeOneData_compatible p₀ β lam ε₀ c
      have hsc : D.2.2 ∈ RouteTypeOne.scales K B.1 := by
        apply Fintype.mem_piFinset.2
        intro v
        by_cases hv : D.1 v = 0
        · rw [ite_eq_left hv]
          exact mem_range.2 (Nat.lt_succ_of_le (typeOneData_sc_le hlam hlh v))
        · rw [ite_eq_right hv, mem_singleton]
          exact hV.2.2.2.2.2 v hv
      have hscsum : (∏ v, typeOneFactor β lam h Nₐ D (chargePos c) v) ≤
          ∑ sc ∈ RouteTypeOne.scales K B.1,
            ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v := by
        exact single_le_sum (f := fun sc => ∏ v,
          typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v) (fun _ _ => zero_le) hsc
      have hBsum : (∑ sc ∈ RouteTypeOne.scales K B.1,
          ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v) ≤
          ∑ B ∈ RouteTypeOne.bases (n := n) q, ∑ sc ∈ RouteTypeOne.scales K B.1,
            ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v :=
        single_le_sum (f := fun B : RouteTypeOne.Base n =>
          ∑ sc ∈ RouteTypeOne.scales K B.1,
            ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v)
          (fun _ _ => zero_le) hB
      exact (typeOneIntegrand_le hq hh hlam hβ hc hiso.1 hiso.2).trans (hscsum.trans hBsum)
    · simp only [F, hI, ite_false, zero_mul]
      exact zero_le
  refine (lintegral_mono_ae hpt).trans ?_
  have hmeasD : ∀ D : TOData n, Measurable fun z : Charge n → ℂ =>
      ∏ v, typeOneFactor β lam h Nₐ D z v :=
    fun D => Finset.measurable_prod _ fun v _ => measurable_typeOneFactor hlam Nₐ D v
  calc ∫⁻ c in boxPi Nₐ n, ∑ B ∈ RouteTypeOne.bases (n := n) q,
        ∑ sc ∈ RouteTypeOne.scales K B.1,
          ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v
      ≤ ∫⁻ c, ∑ B ∈ RouteTypeOne.bases (n := n) q,
        ∑ sc ∈ RouteTypeOne.scales K B.1,
          ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v :=
        setLIntegral_le_lintegral _ _
    _ = ∑ B ∈ RouteTypeOne.bases (n := n) q, ∑ sc ∈ RouteTypeOne.scales K B.1,
        ∫⁻ c, ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) (chargePos c) v := by
      rw [lintegral_finsetSum]
      · apply sum_congr rfl
        intro B _
        apply lintegral_finsetSum
        intro sc _
        simp_rw [chargePos_eq_configEquivSum]
        exact (hmeasD _).comp (configEquivSum (Fin n)).measurable
      · intro B _
        apply Finset.measurable_sum
        intro sc _
        simp_rw [chargePos_eq_configEquivSum]
        exact (hmeasD _).comp (configEquivSum (Fin n)).measurable
    _ = ∑ B ∈ RouteTypeOne.bases (n := n) q, ∑ sc ∈ RouteTypeOne.scales K B.1,
        ∫⁻ z : Charge n → ℂ, ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) z v := by
      apply sum_congr rfl
      intro B _
      apply sum_congr rfl
      intro sc _
      simp_rw [chargePos_eq_configEquivSum]
      exact (measurePreserving_configEquivSum (Fin n)).lintegral_comp_emb
        (configEquivSum (Fin n)).measurableEmbedding
        (fun z => ∏ v, typeOneFactor β lam h Nₐ (B.1, B.2, sc) z v)
    _ ≤ ∑ B ∈ RouteTypeOne.bases (n := n) q, ∑ sc ∈ RouteTypeOne.scales K B.1,
        ENNReal.ofReal (typeOneBound q β lam h Kg Nₐ (B.1, B.2, sc)) := by
      apply sum_le_sum
      intro B hB
      apply sum_le_sum
      intro sc hsc
      exact lintegral_typeOneFactor_le hlam hh.le hKg0 hKg (RouteTypeOne.valid_scales hB hsc)
    _ = ENNReal.ofReal (∑ B ∈ RouteTypeOne.bases (n := n) q,
        ∑ sc ∈ RouteTypeOne.scales K B.1, typeOneBound q β lam h Kg Nₐ (B.1, B.2, sc)) := by
      simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun sc _ => hbound _)]
      exact (ENNReal.ofReal_sum_of_nonneg fun B _ => sum_nonneg fun sc _ => hbound _).symm
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro B _
      simp_rw [typeOneBound_eq]
      rw [← sum_mul, ← sum_mul, RouteTypeOne.scales, sum_scales]

end BadPointTypes

end MultipoleBKT

end
