/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.BadRelabel
public import MultipoleBKT.UpperBound.Hierarchical.StartUpper
public import MultipoleBKT.UpperBound.AbsoluteUpper.Majorant
public import MultipoleBKT.LowerBound.LowerBoundLDP.Relabel
public import MultipoleBKT.Main.TheoremTwo.Master

/-!
# Proposition 5.43: the bookkeeping at fixed `N` and profile

The paper: Proposition 5.43.
Write `N' = ∑ k n_k` and `m = N - N'`. Bound the extra weight by `exp(t m)`
and use the `N!` relabeling identity. Fix one bad-label set of size `m` and
one good partition with profile `n`. Apply the fixed-choice Lemma 5.16,
whose combinatorial factors come from (5.60) and (5.61).

The good-coordinate estimate bounds `𝖬̂^{+,Z}(π) W(Z)` by `exp G` for this
fixed choice. Eq. (5.112) controls its bad-coordinate integral, then Proposition
5.38 and the normalization arithmetic give `upper_bound_of_estimates`.
The statements of the supplied good and bad estimates retain their uniform
interfaces for downstream callers.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical PropFiveFortyFive UpperBound TheoremTwo SetPartition

variable {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-! ### The weight `e^{t |I_bad|}` on `𝒜` -/

open scoped Classical in
/-- The good multipoles of sizes `1, …, p` are disjoint sets of good points:
`∑_{k=1}^{p} k 𝒩_k^good ≤ |I_good|`. -/
theorem sum_mul_goodMultipoleCount_le (c : Fin N → ℂ × ℂ) (p : ℕ) :
    ∑ k ∈ Finset.Icc 1 p, k * goodMultipoleCount p₀ β lam M ε₀ c k ≤
      (goodPoints p₀ β lam M ε₀ (matched c)).card := by
  set G := multipoleGraph M lam c
  set good := goodPoints p₀ β lam M ε₀ (matched c)
  set Pg : G.ConnectedComponent → Prop := fun C =>
    Nat.card C.supp ∈ Finset.Icc 1 p ∧ C.supp ⊆ ↑good
  set fib : G.ConnectedComponent → Finset (Fin N) := fun C =>
    Finset.univ.filter fun v => G.connectedComponentMk v = C
  have h2 : ∑ C ∈ Finset.univ.filter Pg, Nat.card C.supp =
      ∑ k ∈ Finset.Icc 1 p, k * goodMultipoleCount p₀ β lam M ε₀ c k := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter Pg)
      (t := Finset.Icc 1 p) (g := fun C => Nat.card C.supp)
      (fun C hC => (Finset.mem_filter.mp hC).2.1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [goodMultipoleCount_eq_card,
      mul_card_eq_sum_of_forall _ _ _ fun C hC => (Finset.mem_filter.mp hC).2.1]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext C
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pg]
    constructor
    · rintro ⟨⟨-, hsub⟩, rfl⟩; exact ⟨rfl, hsub⟩
    · rintro ⟨rfl, hsub⟩; exact ⟨⟨hk, hsub⟩, rfl⟩
  have h3 : ∑ C ∈ Finset.univ.filter Pg, Nat.card C.supp =
      ((Finset.univ.filter Pg).biUnion fib).card := by
    rw [Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun C _ => natCard_supp_eq C
    · intro C _ C' _ hCC'
      rw [Function.onFun, Finset.disjoint_left]
      intro v hv hv'
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
      exact hCC' (hv.symm.trans hv')
  have h4 : (Finset.univ.filter Pg).biUnion fib ⊆ good := by
    intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, fib, Pg] at hv
    obtain ⟨C, ⟨-, hsub⟩, hvC⟩ := hv
    have : v ∈ C.supp := by rw [SimpleGraph.ConnectedComponent.mem_supp_iff]; exact hvC
    exact Finset.mem_coe.1 (hsub this)
  rw [← h2, h3]
  exact Finset.card_le_card h4

/-- On `𝒜`, `|I_bad| ≤ N - N'`. -/
theorem card_badPoints_le_of_profile {p : ℕ} {n : Fin p → ℕ} {c : Fin N → ℂ × ℂ}
    (hc : ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i) :
    (badPoints p₀ β lam M ε₀ (matched c)).card ≤ N - ∑ i : Fin p, ((i : ℕ) + 1) * n i := by
  have h1 := sum_mul_goodMultipoleCount_le (p₀ := p₀) (β := β) (lam := lam) (M := M)
    (ε₀ := ε₀) c p
  rw [← sum_fin_eq_sum_Icc p (goodMultipoleCount p₀ β lam M ε₀ c)] at h1
  simp_rw [hc] at h1
  have hN : N = (goodPoints p₀ β lam M ε₀ (matched c)).card +
      (badPoints p₀ β lam M ε₀ (matched c)).card := by
    have := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (badPoints p₀ β lam M ε₀ (matched c)))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  omega

/-- `𝒜` depends only on the matched dipoles. -/
theorem goodMultipoleCount_eq_of_matchedDipoles_eq {c c' : Fin N → ℂ × ℂ}
    (h : LowerBoundLDP.matchedDipoles c = LowerBoundLDP.matchedDipoles c') (k : ℕ) :
    goodMultipoleCount p₀ β lam M ε₀ c k = goodMultipoleCount p₀ β lam M ε₀ c' k := by
  have hG := LowerBoundLDP.multipoleGraph_eq_of_matchedDipoles_eq (M := M) (lam := lam) h
  have hm : (fun i => ((c i).1, (c (stableMatching c i)).2)) =
      fun i => ((c' i).1, (c' (stableMatching c' i)).2) := h
  unfold goodMultipoleCount
  rw [hm]
  congr 1
  exact hG ▸ rfl

/-! ### Frozen configurations from the weight -/

open scoped Classical in
/-- Where the weight of the bad points does not vanish, the configuration is frozen. -/
theorem isFrozenConfig_of_badWeightZ_ne_zero {χ : ℂ → ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} (h : badWeightZ χ p₀ β lam M ε₀ V Z ≠ 0) :
    AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z := by
  unfold badWeightZ at h
  refine ⟨?_, fun i hi j hj hij => ?_⟩
  · by_contra hc
    rw [ite_eq_right hc, zero_mul, zero_mul] at h
    exact h rfl
  · by_contra hs
    have hzero : ∏ i ∈ V, ∏ j ∈ V with i < j,
        (if IsStableDipolePair (Z i) (Z j) then
          Real.exp (-β * interactionBadZ χ p₀ β lam ε₀ V Z i j) else 0) = 0 :=
      Finset.prod_eq_zero hi (Finset.prod_eq_zero (Finset.mem_filter.2 ⟨hj, hij⟩) (ite_eq_right hs))
    rw [hzero, mul_zero, zero_mul] at h
    exact h rfl

/-! ### The bookkeeping -/

open scoped Classical in
/-- **The bookkeeping at fixed `N` and profile** (see the module docstring). -/
theorem upper_bound_of_estimates {χ : ℂ → ℝ} (hχ : IsMollifier χ) {n : Fin (pBeta p₀ β) → ℕ}
    (hN : 1 ≤ N) (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 ≤ M) (hε₀ : 0 < ε₀)
    (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N) {t t' L₀ Cbb C₃₈ G : ℝ}
    (ht : 0 ≤ t) (hb1 : EnergyLowerBound χ L₀)
    (hgood : ∀ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
        (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
      ∀ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
          (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
        ∀ Z : Fin N → ℂ × ℂ, AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
          hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V Z π *
              clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V Z π ≤ Real.exp G)
    (hbb : ∀ V : Finset (Fin N),
      ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z')) ≤
        ENNReal.ofReal (Real.exp (β * Cbb * V.card)) *
          badPartitionFunction p₀ β lam M ε₀ N V.card)
    (h38 : (N.choose (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) : ℝ≥0∞) *
        badPartitionFunction p₀ β lam M ε₀ N (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
          ENNReal.ofReal (Real.exp (t' * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) ≤
        ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^
            (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) *
          Real.exp (C₃₈ * N * errorRate p₀ β lam))) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
        {c | ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
      ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
          fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
      ENNReal.ofReal ((N.factorial : ℝ) *
        ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀) ^ N *
        (((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial : ℝ) / profileWeight n) *
        Real.exp (G + (t + β * L₀ + β * Cbb - t') *
            (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ) +
          C₃₈ * N * errorRate p₀ β lam)) := by
  set N' := ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i with hN'
  set V := N - N' with hV
  set A := (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ with hA
  have hA0 : 0 < A := mul_pos (by exact_mod_cast hN)
    (cutoffDipoleNormalization_pos hχ hlam β hε₀ hN)
  set 𝒜 : Set (Fin N → ℂ × ℂ) :=
    {c | ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i} with h𝒜
  set B : Set (Fin N → ℂ × ℂ) := Set.univ.pi fun _ : Fin N => box N ×ˢ box N
  -- Step 1: the weight `e^{t |I_bad|}`
  have hmeasf : Measurable fun c : Fin N → ℂ × ℂ =>
      ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀ (matched c)).card)) *
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_from_top.comp (measurable_card_badPoints p₀ β M lam ε₀ N)).const_mul t))).mul
      (measurable_ofReal_exp_neg_mul_energy hχ hlam β)
  have hmeasg : Measurable fun c : Fin N → ℂ × ℂ =>
      ENNReal.ofReal (Real.exp (t * V)) * ENNReal.ofReal (Real.exp (-β * energy χ lam c)) :=
    (measurable_ofReal_exp_neg_mul_energy hχ hlam β).const_mul _
  have hstep1 : ∫⁻ c in B ∩ 𝒜,
      ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀ (matched c)).card)) *
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) ≤
      ENNReal.ofReal (Real.exp (t * V)) * ∫⁻ c in B ∩ 𝒜,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono_of_measurableSet (measurableSet_le hmeasf hmeasg) fun c hc => ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) _
    have hcard := card_badPoints_le_of_profile (p₀ := p₀) (β := β) (lam := lam) (M := M)
      (ε₀ := ε₀) hc.2
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) ht
  -- Step 2: the label symmetry
  have hE : ∀ c c', LowerBoundLDP.matchedDipoles c = LowerBoundLDP.matchedDipoles c' →
      (c ∈ 𝒜 ↔ c' ∈ 𝒜) := by
    intro c c' h
    simp only [h𝒜, Set.mem_ofPred_eq, goodMultipoleCount_eq_of_matchedDipoles_eq h]
  have hstep2 := LowerBoundLDP.setLIntegral_inter_eq_factorial_mul χ β lam hE
  have hset : (B ∩ 𝒜) ∩ {c | stableMatching c = Equiv.refl _} =
      B ∩ {c | stableMatching c = Equiv.refl _ ∧
        ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i} := by
    ext c
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, h𝒜]
    tauto
  -- Step 3: fix one bad-label set and good partition, then apply Lemma 5.16
  set Zb := badPartitionFunction p₀ β lam M ε₀ N V
  set Bnd : ℝ≥0∞ := ENNReal.ofReal (Real.exp G) *
    (ENNReal.ofReal (Real.exp (β * Cbb * V)) * Zb) with hBnd
  obtain ⟨V', hV'⟩ : ((Finset.univ : Finset (Fin N)).powersetCard (N - N')).Nonempty :=
    Finset.powersetCard_nonempty.2 (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hV'card : V'.card = N - N' := (Finset.mem_powersetCard.1 hV').2
  obtain ⟨π, hπ⟩ := RouteExchange.choices_nonempty (n := n) hV'card hn
  have hB :
        ∫⁻ Z' in Set.univ.pi (fun _ : V' => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z') *
            (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V' (extendBad V' Z') π *
              clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V' (extendBad V' Z') π)) ≤ Bnd := by
    have hcard : V'.card = V := (Finset.mem_powersetCard.1 hV').2
    have hpt : ∀ Z' : V' → ℂ × ℂ,
        ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z') *
          (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V' (extendBad V' Z') π *
            clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V' (extendBad V' Z') π)) ≤
        ENNReal.ofReal (Real.exp G) *
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z')) := by
      intro Z'
      set bw := badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z')
      have hbw0 : 0 ≤ bw := badWeightZ_nonneg hlam V' (extendBad V' Z')
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hbw : bw = 0
      · rw [hbw, zero_mul, mul_zero]
      · have hfr := isFrozenConfig_of_badWeightZ_ne_zero hbw
        rw [mul_comm (Real.exp G)]
        exact mul_le_mul_of_nonneg_left (hgood V' hV' π hπ _ hfr) hbw0
    calc ∫⁻ Z' in Set.univ.pi (fun _ : V' => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z') *
            (hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V' (extendBad V' Z') π *
              clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V' (extendBad V' Z') π))
        ≤ ∫⁻ Z' in Set.univ.pi (fun _ : V' => box N ×ˢ box N), ENNReal.ofReal (Real.exp G) *
            ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z')) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (Real.exp G) * ∫⁻ Z' in Set.univ.pi (fun _ : V' => box N ×ˢ box N),
            ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V' (extendBad V' Z')) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ Bnd := by
          rw [hBnd]
          refine mul_le_mul_right ?_ _
          have := hbb V'
          rw [hcard] at this
          exact this
  have h516 := (lemma_5_16_fixed_of_energyLowerBound hχ hb1 hN hβ hlam hM hε₀
    n hn V' hV'card hπ).trans (mul_le_mul_right hB _)
  rw [← hN', ← hV, ← hset] at h516
  -- Step 4: Proposition 5.38 and the arithmetic
  set q := N'.factorial / profileWeight n with hq
  have hdvd : profileWeight n ∣ N'.factorial := by
    have h := card_partitions_filter_mul (pBeta p₀ β) (Finset.range N') n
      (by rw [Finset.card_range])
    rw [Finset.card_range] at h
    exact Dvd.intro_left _ h
  have hqr : (q : ℝ) = (N'.factorial : ℝ) / profileWeight n := by
    rw [hq, Nat.cast_div hdvd (by exact_mod_cast (profileWeight_pos n).ne')]
  have hch : N.choose N' = N.choose V := (Nat.choose_symm hn).symm
  set Y : ℝ≥0∞ := ENNReal.ofReal (Real.exp (t * V)) * (N.factorial : ℝ≥0∞) *
    ENNReal.ofReal (Real.exp (β * L₀ * V)) * ENNReal.ofReal (A ^ N') * (q : ℝ≥0∞) *
    ENNReal.ofReal (Real.exp G) * ENNReal.ofReal (Real.exp (β * Cbb * V)) *
    ENNReal.ofReal (Real.exp (-(t' * V))) with hY
  have hcancel :
      ENNReal.ofReal (Real.exp (t' * V)) * ENNReal.ofReal (Real.exp (-(t' * V))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  calc ∫⁻ c in B ∩ 𝒜,
        ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀ (matched c)).card)) *
          ENNReal.ofReal (Real.exp (-β * energy χ lam c))
      ≤ ENNReal.ofReal (Real.exp (t * V)) * ∫⁻ c in B ∩ 𝒜,
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := hstep1
    _ = ENNReal.ofReal (Real.exp (t * V)) * ((N.factorial : ℝ≥0∞) *
          ∫⁻ c in (B ∩ 𝒜) ∩ {c | stableMatching c = Equiv.refl _},
            ENNReal.ofReal (Real.exp (-β * energy χ lam c))) := by rw [hstep2]
    _ ≤ ENNReal.ofReal (Real.exp (t * V)) * ((N.factorial : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp (β * L₀ * V)) * ENNReal.ofReal (A ^ N') *
            ((N.choose N' * q : ℕ) : ℝ≥0∞) * Bnd)) := by
        gcongr
    _ = ((N.choose V : ℝ≥0∞) * Zb * ENNReal.ofReal (Real.exp (t' * V))) * Y := by
        rw [hY, hBnd, hch]
        push_cast
        calc ENNReal.ofReal (Real.exp (t * V)) * ((N.factorial : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (β * L₀ * V)) * ENNReal.ofReal (A ^ N') *
                ((N.choose V : ℝ≥0∞) * (q : ℝ≥0∞)) *
                (ENNReal.ofReal (Real.exp G) * (ENNReal.ofReal (Real.exp (β * Cbb * V)) * Zb))))
            = ENNReal.ofReal (Real.exp (t * V)) * ((N.factorial : ℝ≥0∞) *
              (ENNReal.ofReal (Real.exp (β * L₀ * V)) * ENNReal.ofReal (A ^ N') *
                ((N.choose V : ℝ≥0∞) * (q : ℝ≥0∞)) *
                (ENNReal.ofReal (Real.exp G) * (ENNReal.ofReal (Real.exp (β * Cbb * V)) * Zb)))) *
              (ENNReal.ofReal (Real.exp (t' * V)) * ENNReal.ofReal (Real.exp (-(t' * V)))) := by
              rw [hcancel, mul_one]
          _ = _ := by ring
    _ ≤ ENNReal.ofReal (A ^ V * Real.exp (C₃₈ * N * errorRate p₀ β lam)) * Y :=
        mul_le_mul_left h38 _
    _ = ENNReal.ofReal ((N.factorial : ℝ) * A ^ N * ((N'.factorial : ℝ) / profileWeight n) *
          Real.exp (G + (t + β * L₀ + β * Cbb - t') * V + C₃₈ * N * errorRate p₀ β lam)) := by
        have hA0' : 0 ≤ A := hA0.le
        rw [hY, ← ENNReal.ofReal_natCast (N.factorial), ← ENNReal.ofReal_natCast q, hqr]
        simp (disch := positivity) only [← ENNReal.ofReal_mul]
        congr 1
        have hAN : A ^ N = A ^ V * A ^ N' := by rw [← pow_add]; congr 1; omega
        rw [hAN, show G + (t + β * L₀ + β * Cbb - t') * V + C₃₈ * N * errorRate p₀ β lam =
          C₃₈ * N * errorRate p₀ β lam + t * V + β * L₀ * V + G + β * Cbb * V + -(t' * V) by ring]
        simp only [Real.exp_add]
        ring

end UpperBoundLDP

end MultipoleBKT

end
