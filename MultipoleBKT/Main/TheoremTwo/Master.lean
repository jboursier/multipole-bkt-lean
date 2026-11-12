/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Inputs
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.Main.TheoremTwo.GoodPoints
public import MultipoleBKT.Gibbs.Basic

/-!
# Theorem 2 from the gates: the master bounds

The two gates of the proof of Theorem 2,
at fixed parameters:

* Proposition 4.62 bounds `∫_{(Λ²)^N ∩ 𝒜} e^{-βF_λ}` from below
  for one profile (`MultipoleBKT.TheoremTwo.LowerProfileBound`); hence the integral over any
  event containing `𝒜` (`master_lower`).
* Proposition 5.43 bounds `∫_{(Λ²)^N ∩ {𝒩^good = n}} e^{t|I_bad|}
  e^{-βF_λ}` from above for one good profile `n` (`UpperProfileBound`). Summing over the at most
  `(N+1)^p` good profiles (Remark 5.6 gives `∑ i n_i ≤ N` and (5.56) for every configuration,
  `MultipoleBKT.TheoremTwo.good_profile_le`), an event `E` on which
  `-t|I_bad| - N ℐ(𝒩^good/N) ≤ K` has `∫_{(Λ²)^N ∩ E} e^{-βF_λ} ≤ (N+1)^p e^{L_N + K + CNδ}`
 (`master_upper`). This is the computation in Steps 1, 2 and 5 of the proof of Theorem 2.

`master_upper` takes the measurability of `c ↦ |I_bad(c)|` as a hypothesis: the gate integrates
the weight `e^{t|I_bad|}` over the good-profile sets, and transferring a pointwise bound from
those sets to the integral needs it (`MultipoleBKT.TheoremTwo.measurable_card_badPoints`
provides it).

The Gibbs probabilities are `ℙ(E) = Z⁻¹ ∫_{(Λ²)^N ∩ E} e^{-βF_λ}` (`gibbsMeasure_eq`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace TheoremTwo

/-- `(Λ²)^N`. -/
abbrev configBox (N : ℕ) : Set (Fin N → ℂ × ℂ) := Set.univ.pi fun _ : Fin N => box N ×ˢ box N

/-- The Boltzmann weight `e^{-βF_λ}`. -/
noncomputable abbrev boltz (χ : ℂ → ℝ) (β lam : ℝ) {N : ℕ} (c : Fin N → ℂ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * energy χ lam c))

/-- The leading part `N log N + log N! + N(2-β) log λ + N log 𝒵_β` of the gates. -/
noncomputable def freeTerm (χ : ℂ → ℝ) (β lam : ℝ) (N : ℕ) : ℝ :=
  N * Real.log N + Real.log (N.factorial : ℝ) + N * (2 - β) * Real.log lam +
    N * Real.log (dipoleConstant χ β)

/-- The good profile `(𝒩_1^good, …, 𝒩_p^good)` of a configuration. -/
noncomputable abbrev goodProfile (p₀ : ℕ) (β lam M ε₀ : ℝ) {N : ℕ} (c : Fin N → ℂ × ℂ) :
    Fin (pBeta p₀ β) → ℕ :=
  fun i => goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1)

open scoped Classical in
/-- Proposition 5.43 at fixed `M, ε₀, t, C, λ, N` and fixed coefficient families. -/
def UpperProfileBound (χ : ℂ → ℝ) (p₀ : ℕ) (β M ε₀ t C lam : ℝ) (msf : ℝ → ℕ → ℝ)
    (kmult : ℝ → (ℕ →₀ ℕ) → ℝ) (N : ℕ) : Prop :=
  ∀ n : Fin (pBeta p₀ β) → ℕ,
    ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
    (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
      (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
        {c | ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
      ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
          fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
        ENNReal.ofReal (Real.exp (-β * energy χ lam c))
      ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
          + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
          - N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
          + C * N * errorRate p₀ β lam))

open scoped Classical in
/-- Proposition 5.43 at fixed `M` and fixed coefficient families (after the limit hypotheses). -/
def UpperGateAt (χ : ℂ → ℝ) (p₀ : ℕ) (β M : ℝ) (msf : ℝ → ℕ → ℝ)
    (kmult : ℝ → (ℕ →₀ ℕ) → ℝ) : Prop :=
  ∀ t : ℝ, 1 ≤ t →
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex (pBeta p₀ β) x,
          Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
            ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → UpperProfileBound χ p₀ β M ε₀ t C lam msf kmult N

open scoped Classical in
/-- Proposition 4.62 at fixed `M, ε₀, C, λ, N` and fixed coefficient families. -/
def LowerProfileBound (χ : ℂ → ℝ) (p₀ : ℕ) (β M ε₀ C lam : ℝ) (msf : ℝ → ℕ → ℝ)
    (kmult : ℝ → (ℕ →₀ ℕ) → ℝ) (N : ℕ) : Prop :=
  ∀ n : Fin (pBeta p₀ β) → ℕ,
    ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i = N →
    (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
      (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
    ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
        + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
        - N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
        - C * N * errorRate p₀ β lam))
      ≤ ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | (∀ i : Fin (pBeta p₀ β), multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
            ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤
              ε₀ * truncationScale p₀ β lam},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c))

open scoped Classical in
/-- Proposition 4.62 at fixed `M` and fixed coefficient families (after the limit hypotheses). -/
def LowerGateAt (χ : ℂ → ℝ) (p₀ : ℕ) (β M : ℝ) (msf : ℝ → ℕ → ℝ)
    (kmult : ℝ → (ℕ →₀ ℕ) → ℝ) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        (∀ γ ∈ simplex (pBeta p₀ β) 0, Summable fun nm : ℕ+ × (Fin (pBeta p₀ β) → ℕ) =>
          ‖rateSeriesTerm (pBeta p₀ β) (kmult lam) γ nm.1 nm.2‖) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → LowerProfileBound χ p₀ β M ε₀ C lam msf kmult N

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β M ε₀ t C lam : ℝ} {msf : ℝ → ℕ → ℝ}
  {kmult : ℝ → (ℕ →₀ ℕ) → ℝ} {N : ℕ}

/-! ### Gibbs probabilities -/

theorem gibbsMeasure_eq (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (E : Set (Fin N → ℂ × ℂ)) :
    gibbsMeasure χ N β lam E =
      (partitionFunction χ N β lam)⁻¹ * ∫⁻ c in configBox N ∩ E, boltz χ β lam c := by
  unfold gibbsMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply',
    Measure.restrict_restrict' (measurableSet_pi_box_prod N), Set.inter_comm]

theorem partitionFunction_eq (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) :
    partitionFunction χ N β lam = ∫⁻ c in configBox N ∩ Set.univ, boltz χ β lam c := by
  rw [Set.inter_univ]; rfl

/-! ### The lower bound -/

/-- **Proposition 4.62 for an event**: if `E` contains the event `𝒜` of the gate for the
profile `n`, then `∫_{(Λ²)^N ∩ E} e^{-βF_λ} ≥ e^{L_N - N ℐ(n/N) - C N δ}`. -/
theorem master_lower (hL : LowerProfileBound χ p₀ β M ε₀ C lam msf kmult N)
    (n : Fin (pBeta p₀ β) → ℕ) (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i = N)
    (h420 : ∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
      (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N)
    (E : Set (Fin N → ℂ × ℂ))
    (hE : {c : Fin N → ℂ × ℂ | (∀ i : Fin (pBeta p₀ β), multipoleCount M lam c ((i : ℕ) + 1) = n i) ∧
      ∀ i : Fin N, ‖(c i).1 - (c (stableMatching c i)).2‖ ≤ ε₀ * truncationScale p₀ β lam} ⊆ E) :
    ENNReal.ofReal (Real.exp (freeTerm χ β lam N -
        N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N) -
        C * N * errorRate p₀ β lam)) ≤
      ∫⁻ c in configBox N ∩ E, boltz χ β lam c := by
  have h := hL n hn h420
  have heq : freeTerm χ β lam N -
      N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N) -
      C * N * errorRate p₀ β lam =
      N * Real.log N + Real.log (N.factorial : ℝ)
        + (2 - β) * N * Real.log lam + N * Real.log (dipoleConstant χ β)
        - N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
        - C * N * errorRate p₀ β lam := by
    unfold freeTerm; ring
  rw [heq]
  refine h.trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) le_rfl)
  exact Set.inter_subset_inter_right _ hE

/-! ### The upper bound -/

/-- A pointwise bound on a (possibly non-measurable) set transfers to the restricted integral
when the set where it fails is measurable. -/
theorem setLIntegral_mono_of_measurableSet {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : Set α} {f g : α → ℝ≥0∞} (hm : MeasurableSet {x | f x ≤ g x})
    (h : ∀ x ∈ S, f x ≤ g x) : ∫⁻ x in S, f x ∂μ ≤ ∫⁻ x in S, g x ∂μ := by
  refine lintegral_mono_ae ?_
  rw [ae_iff, show {a | ¬f a ≤ g a} = {x | f x ≤ g x}ᶜ from rfl, Measure.restrict_apply hm.compl]
  convert measure_empty (μ := μ)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  exact fun hx hxS => hx (h x hxS)

theorem goodProfile_le (c : Fin N → ℂ × ℂ) (i : Fin (pBeta p₀ β)) :
    goodProfile p₀ β lam M ε₀ c i ≤ N := by
  have h1 := sum_good_profile_le (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) c
    (pBeta p₀ β)
  have h2 : ((i : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c i ≤
      ∑ j : Fin (pBeta p₀ β), ((j : ℕ) + 1) * goodMultipoleCount p₀ β lam M ε₀ c ((j : ℕ) + 1) :=
    Finset.single_le_sum (f := fun j : Fin (pBeta p₀ β) =>
      ((j : ℕ) + 1) * goodMultipoleCount p₀ β lam M ε₀ c ((j : ℕ) + 1))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : goodProfile p₀ β lam M ε₀ c i ≤ ((i : ℕ) + 1) * goodProfile p₀ β lam M ε₀ c i :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  omega

/-- **Proposition 5.43 for an event** (the summation over good profiles): if
`-t |I_bad| - N ℐ(𝒩^good/N) ≤ K` on `E`, then
`∫_{(Λ²)^N ∩ E} e^{-βF_λ} ≤ e^{L_N + K + C N δ + p log (N+1)}`. -/
theorem master_upper (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 0 ≤ M) (hε₀ : 0 ≤ ε₀)
    (hmeas : Measurable fun c : Fin N → ℂ × ℂ =>
      (badPoints p₀ β lam M ε₀ (matched c)).card)
    (hU : UpperProfileBound χ p₀ β M ε₀ t C lam msf kmult N) (E : Set (Fin N → ℂ × ℂ)) (K : ℝ)
    (hK : ∀ c ∈ E, -t * (badPoints p₀ β lam M ε₀ (matched c)).card -
      N * rateFunction (pBeta p₀ β) (msf lam) (kmult lam)
        (fun i => (goodProfile p₀ β lam M ε₀ c i : ℝ) / N) ≤ K) :
    ∫⁻ c in configBox N ∩ E, boltz χ β lam c ≤
      ENNReal.ofReal (Real.exp (freeTerm χ β lam N + K + C * N * errorRate p₀ β lam +
        (pBeta p₀ β) * Real.log ((N : ℝ) + 1))) := by
  classical
  set p := pBeta p₀ β
  set A : (Fin p → Fin (N + 1)) → Set (Fin N → ℂ × ℂ) := fun m =>
    {c | ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = (m i : ℕ)}
  set X : ℝ≥0∞ := ENNReal.ofReal (Real.exp (freeTerm χ β lam N + K + C * N * errorRate p₀ β lam))
  -- the weight `e^{t |I_bad|} e^{-βF_λ}`
  set g : (Fin N → ℂ × ℂ) → ℝ≥0∞ := fun c =>
    ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀ (matched c)).card)) *
      boltz χ β lam c
  have hgm : Measurable g := by
    refine Measurable.mul ?_ (measurable_ofReal_exp_neg_mul_energy hχ hlam β)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_from_top.comp hmeas).const_mul t))
  -- the covering by good profiles
  have hcover : configBox N ∩ E ⊆ ⋃ m, configBox N ∩ A m ∩ E := by
    intro c hc
    refine Set.mem_iUnion.mpr ⟨fun i => ⟨goodProfile p₀ β lam M ε₀ c i,
      Nat.lt_succ_of_le (goodProfile_le c i)⟩, ⟨hc.1, fun i => rfl⟩, hc.2⟩
  -- each profile
  have hterm : ∀ m, ∫⁻ c in configBox N ∩ A m ∩ E, boltz χ β lam c ≤ X := by
    intro m
    by_cases hne : (A m ∩ E).Nonempty
    · obtain ⟨c₀, hc₀A, -⟩ := hne
      set n : Fin p → ℕ := fun i => (m i : ℕ)
      have hprof : goodProfile p₀ β lam M ε₀ c₀ = n := funext fun i => hc₀A i
      have hsum : ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N := by
        rw [← hprof]; exact sum_good_profile_le c₀ p
      have h556 : ∀ i : Fin p, 1 ≤ (i : ℕ) →
          (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N := by
        intro i _
        rw [← hprof]
        exact good_profile_le hM hε₀ c₀ i
      have hgate := hU n hsum h556
      set Iv := rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
      set Y : ℝ≥0∞ := ENNReal.ofReal (Real.exp (K + N * Iv))
      have hpt : ∀ c ∈ configBox N ∩ A m ∩ E, boltz χ β lam c ≤ Y * g c := by
        rintro c ⟨⟨-, hcA⟩, hcE⟩
        have hcp : goodProfile p₀ β lam M ε₀ c = n := funext fun i => hcA i
        have hk := hK c hcE
        rw [hcp] at hk
        simp only [g, Y]
        rw [← mul_assoc, ofReal_exp_mul_ofReal_exp]
        conv_lhs => rw [← one_mul (boltz χ β lam c)]
        gcongr
        rw [← ENNReal.ofReal_one, ← Real.exp_zero]
        exact ofReal_exp_le_ofReal_exp (by linarith)
      have hmeasS : MeasurableSet {c | boltz χ β lam c ≤ Y * g c} :=
        measurableSet_le (measurable_ofReal_exp_neg_mul_energy hχ hlam β) (hgm.const_mul Y)
      calc ∫⁻ c in configBox N ∩ A m ∩ E, boltz χ β lam c
          ≤ ∫⁻ c in configBox N ∩ A m ∩ E, Y * g c := setLIntegral_mono_of_measurableSet hmeasS hpt
        _ = Y * ∫⁻ c in configBox N ∩ A m ∩ E, g c :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ Y * ∫⁻ c in configBox N ∩ A m, g c :=
            mul_le_mul_right (lintegral_mono' (Measure.restrict_mono Set.inter_subset_left le_rfl)
              le_rfl) Y
        _ ≤ Y * ENNReal.ofReal (Real.exp (freeTerm χ β lam N - N * Iv +
              C * N * errorRate p₀ β lam)) := by
            gcongr
            have heq : freeTerm χ β lam N - N * Iv + C * N * errorRate p₀ β lam =
                N * Real.log N + Real.log (N.factorial : ℝ)
                  + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                  - N * Iv + C * N * errorRate p₀ β lam := by
              unfold freeTerm; ring
            rw [heq]
            exact hgate
        _ = X := by
            rw [ofReal_exp_mul_ofReal_exp]
            congr 2
            ring
    · have hempty : configBox N ∩ A m ∩ E = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, hcA⟩, hcE⟩
        exact hne ⟨c, hcA, hcE⟩
      rw [hempty, setLIntegral_empty]
      exact bot_le
  calc ∫⁻ c in configBox N ∩ E, boltz χ β lam c
      ≤ ∫⁻ c in ⋃ m, configBox N ∩ A m ∩ E, boltz χ β lam c :=
        lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
    _ ≤ ∑' m, ∫⁻ c in configBox N ∩ A m ∩ E, boltz χ β lam c := lintegral_iUnion_le _ _
    _ = ∑ m, ∫⁻ c in configBox N ∩ A m ∩ E, boltz χ β lam c := tsum_fintype _
    _ ≤ ∑ _m : Fin p → Fin (N + 1), X := Finset.sum_le_sum fun m _ => hterm m
    _ = ((N + 1 : ℕ) : ℝ≥0∞) ^ p * X := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rfl
    _ = _ := natCast_pow_mul_ofReal_exp N p _

end TheoremTwo

end MultipoleBKT

end
