/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.RouteExchange.Integrals
public import MultipoleBKT.UpperBound.Hierarchical.GoodIntegral
public import MultipoleBKT.UpperBound.Hierarchical.FrozenCongr

/-!
# Lemma 5.16: the fixed-choice starting upper bound

The paper: Lemma 5.16.
First apply the two equal-integral identities `RouteExchange.eqFcond1` and
`RouteExchange.eqFcond2`. Then estimate the one fixed event by the energy
bound (5.50), split bad and good coordinates by Tonelli, and integrate the
good dipoles using the hierarchical expansion.

`lemma_5_16_fixed_of_energyLowerBound` is the literal fixed-choice estimate.
The sum and uniform estimates are also provided.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBound

open Hierarchical Multipole SetPartition Parity TheoremTwo PropFiveFortyFive

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

theorem badWeightZ_nonneg (hlam : 0 < lam) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    0 ≤ badWeightZ χ p₀ β lam M ε₀ V Z := by
  classical
  unfold badWeightZ
  refine mul_nonneg (mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)) (Finset.prod_nonneg fun i _ => ?_)
  have h1 := hlam.trans_le (lam_le_badRadiusPlusOn (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (d := Z) i)
  have h2 := hlam.trans_le (lam_le_badRadiusMinusOn (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (d := Z) i)
  positivity

theorem goodClusterWeight_congr {L : ℝ} {V : Finset (Fin N)} {Z Z' : Fin N → ℂ × ℂ}
    (hZ : ∀ i ∈ V, Z i = Z' i) (π : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    goodClusterWeight χ p₀ β lam M ε₀ L V Z π c = goodClusterWeight χ p₀ β lam M ε₀ L V Z' π c := by
  unfold goodClusterWeight
  rw [interactionGoodZ_congr hZ, hatDipoleWeightZ_congr hZ]

/-- The fixed-event estimate in Steps 3–5 of the proof of Lemma 5.16,
from (5.62) to (5.59). The energy bound (5.50) is followed by Tonelli and the
good-coordinate expansion. -/
theorem frozenEvent_lintegral_le (hχ : IsMollifier χ) {L₀ : ℝ} (hb1 : EnergyLowerBound χ L₀)
    (hN : 1 ≤ N) (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 ≤ M) (hε₀ : 0 < ε₀)
    (V : Finset (Fin N)) {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions ((univ \ V).map Fin.valEmbedding)) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ frozenEvent p₀ β lam M ε₀ V π,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
      ENNReal.ofReal (Real.exp (β * L₀ * V.card)) *
        ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
          Fintype.card {i : Fin N // i ∉ V}) *
        ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
            (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
              clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) := by
  classical
  set L := β * L₀
  set C := (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀
  set T := (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ frozenEvent p₀ β lam M ε₀ V π
  have hT : MeasurableSet T :=
    (MeasurableSet.univ_pi fun _ => measurableSet_box_prod N).inter (measurableSet_frozenEvent V π)
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℂ × ℂ) (· ∈ V)
  -- the bound, as a function of the bad and the good dipoles
  set A : ({i // i ∈ V} → ℂ × ℂ) → ENNReal := fun Z' =>
    ENNReal.ofReal (Real.exp (β * L₀ * V.card)) *
      ENNReal.ofReal ((if ∀ i, Z' i ∈ box N ×ˢ box N then 1 else 0) *
        badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z'))
  set B : ({i // i ∈ V} → ℂ × ℂ) → ({i // i ∉ V} → ℂ × ℂ) → ENNReal := fun Z' g =>
    ENNReal.ofReal ((if ∀ i, g i ∈ box N ×ˢ box N then 1 else 0) *
      ((∏ i, cutoffDensity χ p₀ β lam ε₀ (g i)) *
        goodClusterWeight χ p₀ β lam M ε₀ L V (extendBad V Z') π (natGood V g)))
  set H : (Fin N → ℂ × ℂ) → ENNReal := fun c => A (e c).1 * B (e c).1 (e c).2
  -- step 1: the pointwise bound
  have hbound : ∀ᵐ c ∂(volume : Measure (Fin N → ℂ × ℂ)),
      T.indicator (fun c => ENNReal.ofReal (Real.exp (-β * energy χ lam c))) c ≤ H c := by
    filter_upwards [ae_clusterGeneric] with c hgen
    by_cases hc : c ∈ T
    · rw [Set.indicator_of_mem hc]
      obtain ⟨hbox, hσ, hV, hconn, hinter⟩ := hc
      have hbox' : ∀ i, c i ∈ box N ×ˢ box N := fun i => hbox i (Set.mem_univ i)
      have key := exp_neg_energy_le (p₀ := p₀) (ε₀ := ε₀) hχ hb1 hβ hlam hM hπ hσ hV hconn hinter
        hgen
      -- the bad coordinates
      have hZ : ∀ i ∈ V, c i = extendBad V (e c).1 i := fun i hi => by
        simp [extendBad, hi, e, MeasurableEquiv.piEquivPiSubtypeProd]
      have hgood : ∀ n ∈ π.biUnion id, natConfig c n = natGood V (e c).2 n := by
        intro n hn
        rw [(mem_partitions.1 hπ).2] at hn
        obtain ⟨h, h'⟩ := (mem_goodLabels V).1 hn
        simp [natConfig, natGood, h, h', e, MeasurableEquiv.piEquivPiSubtypeProd]
      have hgcw : goodClusterWeight χ p₀ β lam M ε₀ L V c π (natConfig c) =
          goodClusterWeight χ p₀ β lam M ε₀ L V (extendBad V (e c).1) π (natGood V (e c).2) := by
        rw [goodClusterWeight_congr hZ]
        unfold goodClusterWeight
        have hm := modelHyp_hat (p₀ := p₀) (β := β) (M := M) (L := L) (V := V)
          (Z := extendBad V (e c).1) hχ hlam hε₀ hN
        exact dependsOn_clusterWeight (fun B => dependsOn_blockWeightOf M lam B) π
          fun n hn => hgood n (Finset.mem_coe.1 hn)
      have hdens : ∏ i ∈ univ \ V, cutoffDensity χ p₀ β lam ε₀ (c i) =
          ∏ i : {i // i ∉ V}, cutoffDensity χ p₀ β lam ε₀ ((e c).2 i) := by
        exact Finset.prod_subtype (univ \ V) (p := fun i => i ∉ V) (fun i => by simp)
          (fun i => cutoffDensity χ p₀ β lam ε₀ (c i))
      have hboxZ : ∀ i, (e c).1 i ∈ box N ×ˢ box N := fun i => hbox' i
      have hboxg : ∀ i, (e c).2 i ∈ box N ×ˢ box N := fun i => hbox' i
      simp only [H, A, B, ite_eq_left hboxZ, ite_eq_left hboxg, one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (mul_nonneg
        (Real.exp_pos _).le (badWeightZ_nonneg hlam _ _))]
      refine ENNReal.ofReal_le_ofReal (key.trans_eq ?_)
      rw [badWeightZ_congr hZ, hdens, hgcw]
      ring
    · rw [Set.indicator_of_notMem hc]
      exact bot_le
  -- step 2: integrate, split the coordinates and use Tonelli
  rw [← lintegral_indicator hT]
  refine (lintegral_mono_ae hbound).trans ?_
  have hmp : MeasurePreserving e volume (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℂ × ℂ) (· ∈ V) using 4
  rw [hmp.symm.lintegral_map_equiv H e.symm]
  simp only [H, MeasurableEquiv.apply_symm_apply]
  refine (lintegral_prod_le (fun x : ({i // i ∈ V} → ℂ × ℂ) × ({i // i ∉ V} → ℂ × ℂ) =>
    A x.1 * B x.1 x.2)).trans ?_
  -- step 3: the good dipoles
  have hgoodint : ∀ Z', ∫⁻ g, A Z' * B Z' g =
      A Z' * (ENNReal.ofReal (C ^ Fintype.card {i : Fin N // i ∉ V}) *
        ENNReal.ofReal (hatPartitionFunctions χ N p₀ β lam M ε₀ L V (extendBad V Z') π *
          clusterSeriesW χ N p₀ β lam M ε₀ L V (extendBad V Z') π)) := by
    intro Z'
    rw [lintegral_const_mul' _ _ (by simp [A, ENNReal.mul_ne_top])]
    congr 1
    exact lintegral_good_eq hχ hlam hε₀ hN hπ (extendBad V Z')
  simp only [hgoodint]
  -- step 4: the bad dipoles
  have hA : ∀ Z' : {i // i ∈ V} → ℂ × ℂ, A Z' * (ENNReal.ofReal (C ^ Fintype.card {i : Fin N // i ∉ V}) *
        ENNReal.ofReal (hatPartitionFunctions χ N p₀ β lam M ε₀ L V (extendBad V Z') π *
          clusterSeriesW χ N p₀ β lam M ε₀ L V (extendBad V Z') π)) =
      ENNReal.ofReal (Real.exp (β * L₀ * V.card)) *
        ENNReal.ofReal (C ^ Fintype.card {i : Fin N // i ∉ V}) *
        (Set.univ.pi fun _ : V => box N ×ˢ box N).indicator (fun Z' =>
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
            (hatPartitionFunctions χ N p₀ β lam M ε₀ L V (extendBad V Z') π *
              clusterSeriesW χ N p₀ β lam M ε₀ L V (extendBad V Z') π))) Z' := by
    intro Z'
    by_cases hZ' : ∀ i, Z' i ∈ box N ×ˢ box N
    · have hmem : Z' ∈ Set.univ.pi fun _ : V => box N ×ˢ box N := fun i _ => hZ' i
      simp only [A, ite_eq_left hZ', one_mul, Set.indicator_of_mem hmem]
      rw [ENNReal.ofReal_mul (badWeightZ_nonneg hlam _ _)]
      ring
    · have hmem : Z' ∉ Set.univ.pi fun _ : V => box N ×ˢ box N := fun h =>
        hZ' fun i => h i (Set.mem_univ i)
      simp only [A, ite_eq_right hZ', zero_mul, ENNReal.ofReal_zero, mul_zero,
        Set.indicator_of_notMem hmem, zero_mul]
  simp only [hA]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_box_prod N)]

/-- **Lemma 5.16 with fixed choices**, the paper, (5.58). The binomial and factorial factors arise from
the equal-integral identities before estimating the fixed event. -/
theorem lemma_5_16_fixed_of_energyLowerBound (hχ : IsMollifier χ) {L₀ : ℝ}
    (hb1 : EnergyLowerBound χ L₀) (hN : 1 ≤ N) (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hε₀ : 0 < ε₀) (n : Fin (pBeta p₀ β) → ℕ)
    (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N)
    (V : Finset (Fin N))
    (hV : V.card = N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)
    {π : Finset (Finset ℕ)} (hπ : π ∈ RouteExchange.choices V (pBeta p₀ β) n) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
        {c | stableMatching c = Equiv.refl _ ∧
          ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
      ENNReal.ofReal (Real.exp (β * L₀ * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) *
        ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
          ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
        (((N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)) *
          ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n) : ℕ) :
            ENNReal) *
        ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
            (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
              clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) := by
  classical
  change (∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
    RouteExchange.profileEvent p₀ β lam M ε₀ n,
    ENNReal.ofReal (Real.exp (-β * energy χ lam c))) ≤ _
  rw [RouteExchange.eqFcond1 (χ := χ) (lam := lam) (ε₀ := ε₀) hM n hn V hV,
    RouteExchange.eqFcond2 (χ := χ) (lam := lam) (ε₀ := ε₀) hM n hn V hV hπ]
  have hgood : Fintype.card {i : Fin N // i ∉ V} =
      ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hV]
    omega
  have hfixed := (lintegral_mono_set (Set.inter_subset_inter_right
    (Set.univ.pi fun _ : Fin N => box N ×ˢ box N)
    (fun c hc => (RouteExchange.choiceEvent_subset hπ hc).2))).trans
      (frozenEvent_lintegral_le hχ hb1 hN hβ hlam hM hε₀ V (Finset.mem_filter.1 hπ).1)
  rw [hV, hgood] at hfixed
  have hscaled := mul_le_mul_left
    (mul_le_mul_left hfixed
      (((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n : ℕ) : ENNReal))
    (N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) : ENNReal)
  simpa only [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- **Lemma 5.16**, for every fixed bad-label set and good partition. -/
theorem lemma_5_16_fixed (hχ : IsMollifier χ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ),
      1 ≤ N → 2 < β → 0 < lam → 0 ≤ M → 0 < ε₀ →
      ∀ n : Fin (pBeta p₀ β) → ℕ,
        ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
      ∀ V : Finset (Fin N), V.card = N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i →
      ∀ π : Finset (Finset ℕ), π ∈ RouteExchange.choices V (pBeta p₀ β) n →
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | stableMatching c = Equiv.refl _ ∧
            ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
        ENNReal.ofReal (Real.exp (β * L₀ * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) *
          ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
            ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
          (((N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)) *
            ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n) : ℕ) :
              ENNReal) *
          ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
            ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
              (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
                clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) := by
  obtain ⟨L₀, hL₀, hb1⟩ := exists_energyLowerBound hχ
  exact ⟨L₀, hL₀, fun _ _ _ _ _ hN hβ hlam hM hε₀ n hn V hV π hπ =>
    lemma_5_16_fixed_of_energyLowerBound hχ hb1 hN hβ hlam hM hε₀ n hn V hV hπ⟩

/-- Finite averaging for the compatibility consequence of (5.58),
the paper. -/
private theorem sum_compatibility_of_fixed_choice {α γ : Type*}
    (s : Finset α) (t : α → Finset γ) {K : ℕ} (hK : 0 < K)
    (hcard : ∑ a ∈ s, (t a).card = K) {I A : ENNReal} {B : α → γ → ENNReal}
    (h : ∀ a ∈ s, ∀ b ∈ t a, I ≤ A * (K : ENNReal) * B a b) :
    I ≤ A * ∑ a ∈ s, ∑ b ∈ t a, B a b := by
  have hsum := sum_le_sum (s := s) fun a ha => sum_le_sum (h a ha)
  have hcount : (∑ a ∈ s, ∑ _b ∈ t a, I) = (K : ENNReal) * I := by
    simp_rw [sum_const, nsmul_eq_mul]
    rw [← sum_mul, ← Nat.cast_sum, hcard]
  rw [hcount] at hsum
  simp_rw [← mul_sum] at hsum
  apply (ENNReal.mul_le_mul_iff_right (Nat.cast_ne_zero.2 hK.ne')
    (ENNReal.natCast_ne_top K)).1
  simpa only [mul_assoc, mul_left_comm] using hsum

/-- Compatibility sum form of Lemma 5.16, derived by summing the fixed-choice
inequality of the paper, (5.58),
over all choices and cancelling their positive finite count. -/
theorem lemma_5_16_of_energyLowerBound (hχ : IsMollifier χ) {L₀ : ℝ} (hb1 : EnergyLowerBound χ L₀)
    (hN : 1 ≤ N) (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 ≤ M) (hε₀ : 0 < ε₀)
    (n : Fin (pBeta p₀ β) → ℕ) (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
        {c | stableMatching c = Equiv.refl _ ∧
          ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
      ENNReal.ofReal (Real.exp (β * L₀ * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) *
        ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
          ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
        ∑ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
            (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
          ∑ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
              (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
            ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
              ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
                (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
                  clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) := by
  classical
  let s := (univ : Finset (Fin N)).powersetCard
    (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)
  let q := (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n
  let K := N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) * q
  have hcard : ∀ V ∈ s, (RouteExchange.choices V (pBeta p₀ β) n).card = q :=
    fun V hV => RouteExchange.card_choices (mem_powersetCard.1 hV).2 hn
  obtain ⟨V, hV⟩ : s.Nonempty :=
    powersetCard_nonempty.2 (by simp only [card_univ, Fintype.card_fin]; omega)
  have hq : 0 < q := by
    rw [← hcard V hV]
    exact card_pos.2 (RouteExchange.choices_nonempty (mem_powersetCard.1 hV).2 hn)
  have hcount : (∑ V ∈ s, (RouteExchange.choices V (pBeta p₀ β) n).card) = K := by
    rw [sum_congr rfl hcard, sum_const, nsmul_eq_mul]
    simp only [s, card_powersetCard, card_univ, Fintype.card_fin]
    rw [Nat.choose_symm hn]
    rfl
  apply sum_compatibility_of_fixed_choice s (fun V => RouteExchange.choices V (pBeta p₀ β) n)
    (Nat.mul_pos (Nat.choose_pos hn) hq) hcount
  intro V hV π hπ
  exact lemma_5_16_fixed_of_energyLowerBound hχ hb1 hN hβ hlam hM hε₀ n hn V
    (mem_powersetCard.1 hV).2 hπ

/-- Compatibility uniform form of Lemma 5.16, obtained by choosing a single
admissible pair in the fixed-choice estimate (the paper, (5.58)). -/
theorem lemma_5_16_uniform_of_energyLowerBound (hχ : IsMollifier χ) {L₀ : ℝ}
    (hb1 : EnergyLowerBound χ L₀) (hN : 1 ≤ N) (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 ≤ M)
    (hε₀ : 0 < ε₀) (n : Fin (pBeta p₀ β) → ℕ)
    (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N) (B : ENNReal)
    (hB : ∀ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
        (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
      ∀ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
          (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
        ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
            (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
              clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) ≤ B) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
        {c | stableMatching c = Equiv.refl _ ∧
          ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
      ENNReal.ofReal (Real.exp (β * L₀ * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) *
        ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
          ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
        (((N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)) *
          ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n) : ℕ) :
            ENNReal) * B := by
  classical
  obtain ⟨V, hV⟩ : ((Finset.univ : Finset (Fin N)).powersetCard
      (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hVcard := (Finset.mem_powersetCard.1 hV).2
  obtain ⟨π, hπ⟩ := RouteExchange.choices_nonempty hVcard hn
  exact (lemma_5_16_fixed_of_energyLowerBound hχ hb1 hN hβ hlam hM hε₀ n hn V hVcard hπ).trans
    (mul_le_mul_right (hB V hV π hπ) _)

/-- Compatibility sum form of Lemma 5.16 with the energy coefficient supplied
by (5.50). -/
theorem lemma_5_16 (hχ : IsMollifier χ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ), 1 ≤ N → 2 < β → 0 < lam → 0 ≤ M →
      0 < ε₀ → ∀ n : Fin (pBeta p₀ β) → ℕ, ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | stableMatching c = Equiv.refl _ ∧
            ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
        ENNReal.ofReal (Real.exp (β * L₀ * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) *
          ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
            ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
          ∑ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
              (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
            ∑ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
                (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
              ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
                ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
                  (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
                    clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) := by
  obtain ⟨L₀, hL₀, hb1⟩ := exists_energyLowerBound hχ
  exact ⟨L₀, hL₀, fun _ _ _ _ _ hN hβ hlam hM hε₀ n hn =>
    lemma_5_16_of_energyLowerBound hχ hb1 hN hβ hlam hM hε₀ n hn⟩

/-- Compatibility uniform form of Lemma 5.16 with the energy coefficient
supplied by (5.50). -/
theorem lemma_5_16_uniform (hχ : IsMollifier χ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ), 1 ≤ N → 2 < β → 0 < lam → 0 ≤ M →
      0 < ε₀ → ∀ n : Fin (pBeta p₀ β) → ℕ, ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
      ∀ B : ENNReal, (∀ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
          (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
        ∀ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
            (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
          ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
            ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z') *
              (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π *
                clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V (extendBad V Z') π)) ≤ B) →
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | stableMatching c = Equiv.refl _ ∧
            ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
        ENNReal.ofReal (Real.exp (β * L₀ * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) *
          ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
            ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
          (((N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)) *
            ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n) : ℕ) :
              ENNReal) * B := by
  obtain ⟨L₀, hL₀, hb1⟩ := exists_energyLowerBound hχ
  exact ⟨L₀, hL₀, fun _ _ _ _ _ hN hβ hlam hM hε₀ n hn B hB =>
    lemma_5_16_uniform_of_energyLowerBound hχ hb1 hN hβ hlam hM hε₀ n hn B hB⟩

end UpperBound

end MultipoleBKT

end
