/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.RateFunction.Comparison
public import MultipoleBKT.RateFunction.Uniform
public import MultipoleBKT.RateFunction.RouteHessian.Gap
public import MultipoleBKT.Main.TheoremTwo.ProfileFacts

/-!
# Theorem 2 from the gates: the rate function at a fixed small `λ`

Facts about `ℐ = ℐ_{β,p,λ}` under uniform coefficient bounds, used in the proof of
Theorem 2, Steps 1–5.

* Continuity, boundedness below, and the infima on `Δ_{p,x}`.
* The pointwise missing-mass comparison of (5.153).
* The weighted quadratic gap from integrating (5.157) along
 proper subsegments and taking the boundary limit.
  `RateSetup.source_gap` exports the displayed one-coordinate estimate for the tail proof.
* The one-sided derivative bound in Step 3, and uniform continuity.

Here `B = 16 K² 2^p λ²` (`rateB`) bounds the cluster part `h` and its first two derivatives.
-/

@[expose] public section

open Finset Filter Topology Set

namespace MultipoleBKT

namespace TheoremTwo

/-- `B = 16 K² 2^p λ²`, the bound on the cluster part `h` and its first two derivatives. -/
noncomputable def rateB (p : ℕ) (C lam : ℝ) : ℝ := 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2

theorem rateB_nonneg (p : ℕ) (C lam : ℝ) : 0 ≤ rateB p C lam := by
  unfold rateB; positivity

/-- The hypotheses on the coefficients at a fixed small `λ`. -/
structure RateSetup (p : ℕ) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ) (C lam : ℝ) : Prop where
  hp : 1 ≤ p
  hC : 0 < C
  hlam : 0 < lam
  hlam1 : lam < 1
  hk : KmultBound p kmult C lam
  hmsf : MsfBound p msf C lam
  hsmall : rateSeriesConst p C * lam ^ 2 ≤ 1 / 4
  hB : rateB p C lam ≤ 1 / 8

/-- For `λ` small, the uniform bounds (2.47), (2.48) give a `RateSetup`, and the conclusions of
`MultipoleBKT.rateFunction_minimizer` hold. -/
theorem exists_rateSetup {p : ℕ} (hp : 1 ≤ p) {C : ℝ} (hC : 0 < C) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∃ C'' : ℝ, 0 < C'' ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∀ (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ), MsfBound p msf C lam →
        KmultBound p kmult C lam →
        RateSetup p msf kmult C lam ∧
        (∃! γ, γ ∈ simplex p 0 ∧ IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) ∧
        ∀ γ ∈ simplex p 0, IsMinOn (rateFunction p msf kmult) (simplex p 0) γ →
          (∀ i, 0 < γ i) ∧ ∀ i : Fin p, 1 ≤ (i : ℕ) →
            C''⁻¹ * lam ^ (2 * (i : ℕ)) ≤ γ i ∧ γ i ≤ C'' * lam ^ (2 * (i : ℕ)) := by
  obtain ⟨l₁, hl₁, C'', hC'', hmin⟩ := rateFunction_minimizer p hp hC
  set X := 16 * rateSeriesConst p C ^ 2 * 2 ^ p
  have hX : 0 ≤ X := by positivity
  set l₂ : ℝ := 1 / (128 * X + 1)
  have hl₂ : 0 < l₂ := by positivity
  have hl₂1 : l₂ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  refine ⟨min (min l₁ (rateSeriesLam₀ p C)) l₂, lt_min (lt_min hl₁ (rateSeriesLam₀_pos p C)) hl₂,
    (min_le_right _ _).trans hl₂1, C'', hC'', fun lam hlam hlaml msf kmult hm hk => ?_⟩
  have hlam1 : lam < l₁ := lt_of_lt_of_le hlaml ((min_le_left _ _).trans (min_le_left _ _))
  have hlam2 : lam < rateSeriesLam₀ p C :=
    lt_of_lt_of_le hlaml ((min_le_left _ _).trans (min_le_right _ _))
  have hlam3 : lam < l₂ := lt_of_lt_of_le hlaml (min_le_right _ _)
  have hlamone : lam < 1 := lt_of_lt_of_le hlam3 hl₂1
  obtain ⟨-, h2, h3⟩ := hmin lam hlam hlam1 msf kmult hm hk
  refine ⟨⟨hp, hC, hlam, hlamone, hk, hm, rateSeriesConst_mul_sq_le p C hlam.le hlam2, ?_⟩, h2, h3⟩
  -- `B = X λ² ≤ X λ ≤ X/(128 X + 1) ≤ 1/8`
  have hsq : lam ^ 2 ≤ lam := by nlinarith
  have h1 : X * lam ≤ X * l₂ := mul_le_mul_of_nonneg_left hlam3.le hX
  have h2' : X * l₂ ≤ 1 / 8 := by
    simp only [l₂]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  show X * lam ^ 2 ≤ 1 / 8
  nlinarith [mul_le_mul_of_nonneg_left hsq hX]

namespace RateSetup

variable {p : ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {C lam : ℝ}

theorem msf_one (hs : RateSetup p msf kmult C lam) : msf 1 = 1 := hs.hmsf.1

theorem mem_rateDomain {x : ℝ} {γ : Fin p → ℝ} (hγ : γ ∈ simplex p x) : γ ∈ rateDomain p :=
  unitBox_subset_rateDomain (simplex_subset_unitBox x hγ)

theorem continuousOn (hs : RateSetup p msf kmult C lam) (x : ℝ) :
    ContinuousOn (rateFunction p msf kmult) (simplex p x) :=
  (continuousOn_rateFunction hs.hk hs.hlam.le hs.hsmall).mono fun _ h => mem_rateDomain h

theorem bddBelow (hs : RateSetup p msf kmult C lam) (x : ℝ) :
    BddBelow (rateFunction p msf kmult '' simplex p x) :=
  (isCompact_simplex x).bddBelow_image (hs.continuousOn x)

theorem sInf_le (hs : RateSetup p msf kmult C lam) {x : ℝ} {γ : Fin p → ℝ}
    (hγ : γ ∈ simplex p x) : sInf (rateFunction p msf kmult '' simplex p x) ≤
      rateFunction p msf kmult γ :=
  csInf_le (hs.bddBelow x) ⟨γ, hγ, rfl⟩

theorem sInf_eq_of_isMinOn {γ : Fin p → ℝ} (hγ : γ ∈ simplex p 0)
    (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ) :
    sInf (rateFunction p msf kmult '' simplex p 0) = rateFunction p msf kmult γ :=
  IsLeast.csInf_eq ⟨⟨γ, hγ, rfl⟩, by rintro _ ⟨η, hη, rfl⟩; exact hmin hη⟩

theorem summable (hs : RateSetup p msf kmult C lam) {x : ℝ} {γ : Fin p → ℝ}
    (hγ : γ ∈ simplex p x) :
    Summable fun nm : ℕ+ × (Fin p → ℕ) => ‖rateSeriesTerm p kmult γ nm.1 nm.2‖ :=
  summable_abs_rateSeriesTerm hs.hk hs.hlam.le hs.hsmall fun i => abs_le_two_of_mem_simplex hγ i

/-- The comparison of infima: `inf_{Δ_{p,0}} ℐ - B x ≤ ℐ(u)` for `u ∈ Δ_{p,x}`. -/
theorem sInf_sub_le (hs : RateSetup p msf kmult C lam) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    {u : Fin p → ℝ} (hu : u ∈ simplex p x) :
    sInf (rateFunction p msf kmult '' simplex p 0) - rateB p C lam * x ≤
      rateFunction p msf kmult u :=
  (sInf_rateFunction_comparison hs.hp hs.hk hs.hlam.le hs.hsmall hs.msf_one hx).trans
    (hs.sInf_le hu)

/-- **Pointwise comparison** (the paper, (5.153)): for `u ∈ Δ_{p,x}`, the point
`η = (u₁ + x, u₂, …, u_p)` lies in `Δ_{p,0}` and `ℐ(η) ≤ ℐ(u) + B x`. -/
theorem exists_shift (hs : RateSetup p msf kmult C lam) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    {u : Fin p → ℝ} (hu : u ∈ simplex p x) :
    ∃ η ∈ simplex p 0, (∀ i : Fin p, 1 ≤ (i : ℕ) → η i = u i) ∧
      rateFunction p msf kmult η ≤ rateFunction p msf kmult u + rateB p C lam * x := by
  have hB0 := rateB_nonneg p C lam
  set e0 : Fin p := ⟨0, hs.hp⟩
  set w : Fin p → ℝ := Pi.single e0 1 with hw_def
  have hwe : w e0 = 1 := by simp [hw_def]
  have hwk : ∀ k, k ≠ e0 → w k = 0 := fun k hk => by simp [hw_def, hk]
  set η : Fin p → ℝ := u + x • w with hη_def
  have hηk : ∀ k, η k = u k + x * w k := fun k => by simp [hη_def]
  have hu0 : u e0 + x ≤ 1 := by
    have h1 : ∑ k ∈ ({e0} : Finset (Fin p)), ((k : ℕ) + 1 : ℝ) * u k ≤
        ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * u k :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) fun k _ _ =>
        mul_nonneg (by positivity) (hu.1 k).1
    rw [sum_singleton, hu.2] at h1
    simp only [e0, Nat.cast_zero, zero_add, one_mul] at h1
    linarith
  have hηmem : η ∈ simplex p 0 := by
    refine ⟨fun k => ?_, ?_⟩
    · rw [hηk]
      by_cases hk : k = e0
      · rw [hk, hwe, mul_one]
        exact ⟨by linarith [(hu.1 e0).1, hx.1], hu0⟩
      · rw [hwk k hk, mul_zero, add_zero]
        exact hu.1 k
    · have : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * η k =
          ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * u k + x * ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * w k := by
        rw [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun k _ => ?_
        rw [hηk]
        ring
      have hw : ∑ k : Fin p, ((k : ℕ) + 1 : ℝ) * w k = 1 := by
        rw [Fintype.sum_eq_single e0 fun k hk => by rw [hwk k hk, mul_zero], hwe]
        simp [e0]
      rw [this, hu.2, hw]
      ring
  refine ⟨η, hηmem, fun i hi => ?_, ?_⟩
  · have hie : i ≠ e0 := fun h => by rw [h] at hi; simp [e0] at hi
    rw [hηk, hwk i hie, mul_zero, add_zero]
  have h2 : rateFunction p msf kmult η - rateFunction p msf kmult u ≤ rateB p C lam * x := by
    rw [rateFunction_sub_eq]
    have hsum : ∑ k, (rateEntTerm msf k (η k) - rateEntTerm msf k (u k)) =
        rateEntTerm msf e0 (η e0) - rateEntTerm msf e0 (u e0) := by
      refine Fintype.sum_eq_single e0 fun k hk => ?_
      rw [hηk, hwk k hk, mul_zero, add_zero, sub_self]
    have hent : rateEntTerm msf e0 (η e0) - rateEntTerm msf e0 (u e0) ≤ 0 := by
      rw [hηk, hwe, mul_one]
      have hform : ∀ s : ℝ, rateEntTerm msf e0 s = s * (Real.log s - 1) := by
        intro s
        simp only [rateEntTerm, e0, zero_add, Nat.factorial_one, Nat.cast_one,
          Real.log_one, hs.msf_one]
        ring
      rw [hform, hform]
      have := mul_log_sub_one_le (hu.1 e0).1 (by linarith [hx.1] : u e0 ≤ u e0 + x) hu0
      linarith
    have hH : rateCluster p kmult η - rateCluster p kmult u ≤ rateB p C lam * x := by
      have h := abs_rateCluster_sub_le hs.hk hs.hlam.le hs.hsmall (mem_rateDomain hu)
        (mem_rateDomain hηmem)
      have hn : ‖η - u‖ ≤ x := by
        rw [hη_def, add_sub_cancel_left]
        refine (pi_norm_le_iff_of_nonneg hx.1).mpr fun k => ?_
        simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1]
        by_cases hk : k = e0
        · rw [hk, hwe, abs_one, mul_one]
        · rw [hwk k hk, abs_zero, mul_zero]
          exact hx.1
      calc rateCluster p kmult η - rateCluster p kmult u
          ≤ 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * ‖η - u‖ := (le_abs_self _).trans h
        _ ≤ rateB p C lam * x := mul_le_mul_of_nonneg_left hn hB0
    rw [hsum]
    linarith
  linarith

/-! ### The quadratic gap at the minimizer -/

/-- The displayed one-coordinate estimate in Step 5 of the proof of Theorem 2. It follows from the
full Hessian bound on proper subsegments and continuity at the boundary. -/
theorem source_gap (hs : RateSetup p msf kmult C lam) {γ η : Fin p → ℝ}
    (hγ : γ ∈ simplex p 0) (hmin : IsMinOn (rateFunction p msf kmult) (simplex p 0) γ)
    (hη : η ∈ simplex p 0) (i : Fin p) :
    (η i - γ i) ^ 2 / (4 * max (η i) (γ i)) ≤
      rateFunction p msf kmult η - rateFunction p msf kmult γ :=
  rateFunction_coordinate_gap hs.hk hs.hlam.le hs.hsmall (by
    have h := hs.hB
    unfold rateB at h
    linarith) hγ hmin hη i

/-! ### The Lipschitz-type bound of Step 3 -/

/-- **Step 3 of the proof of Theorem 2**: if `η ∈ Δ_{p,0}` with `ηᵢ ≤ A λ^{2i}` for `i ≥ 1` (`A > 0`) and
`0 ≤ u ≤ η`, then `ℐ(η) - ℐ(u) ≤ (log p! + |log A| + |log C| + 1) ∑ᵢ (ηᵢ - uᵢ)`. -/
theorem sub_le_of_le (hs : RateSetup p msf kmult C lam) {A : ℝ} (hA : 0 < A) {η u : Fin p → ℝ}
    (hη : η ∈ simplex p 0) (hηA : ∀ i : Fin p, 1 ≤ (i : ℕ) → η i ≤ A * lam ^ (2 * (i : ℕ)))
    (hu0 : ∀ i, 0 ≤ u i) (huη : ∀ i, u i ≤ η i) :
    rateFunction p msf kmult η - rateFunction p msf kmult u ≤
      (Real.log (p.factorial : ℝ) + |Real.log A| + |Real.log C| + 1) * ∑ i, (η i - u i) := by
  set L := Real.log (p.factorial : ℝ) + |Real.log A| + |Real.log C|
  have hlogp : 0 ≤ Real.log (p.factorial : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero p))
  have hL : 0 ≤ L := by positivity
  have hu1 : ∀ i, u i ≤ 1 := fun i => (huη i).trans (hη.1 i).2
  have huD : u ∈ rateDomain p :=
    mem_rateDomain_of_mem_Icc fun i => ⟨hu0 i, hu1 i⟩
  rw [rateFunction_sub_eq]
  -- the entropy terms
  have hent : ∀ i, rateEntTerm msf i (η i) - rateEntTerm msf i (u i) ≤ L * (η i - u i) := by
    intro i
    rcases (hη.1 i).1.eq_or_lt with h0 | hpos
    · have hu : u i = 0 := le_antisymm (h0 ▸ huη i) (hu0 i)
      rw [← h0, hu, sub_self, sub_self, mul_zero]
    · have htan := entropy_sub_le_tangent (A := Real.log ((i : ℕ) + 1).factorial - 1 -
        Real.log (msf ((i : ℕ) + 1))) (hu0 i) hpos
      have hE : ∀ s, rateEntTerm msf i s = s * ((Real.log ((i : ℕ) + 1).factorial - 1 -
          Real.log (msf ((i : ℕ) + 1))) + Real.log s) := fun s => by unfold rateEntTerm; ring
      rw [hE, hE]
      refine htan.trans (mul_le_mul_of_nonneg_right ?_ (sub_nonneg.mpr (huη i)))
      -- the coefficient `log (i+1)! + log ηᵢ - log 𝗆(i+1) ≤ L`
      have hcoef : Real.log ((i : ℕ) + 1).factorial + Real.log (η i) -
          Real.log (msf ((i : ℕ) + 1)) ≤ L := by
        rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hi1
        · rw [hi0, zero_add, Nat.factorial_one, Nat.cast_one, Real.log_one, zero_add, hs.msf_one,
            Real.log_one, sub_zero]
          exact (Real.log_nonpos (hη.1 i).1 (hη.1 i).2).trans hL
        · have hfact : Real.log ((i : ℕ) + 1).factorial ≤ Real.log (p.factorial : ℝ) := by
            refine Real.log_le_log (by exact_mod_cast Nat.factorial_pos _) ?_
            exact_mod_cast Nat.factorial_le (by omega : (i : ℕ) + 1 ≤ p)
          have hm := (hs.hmsf.2 ((i : ℕ) + 1) (by omega) (by omega))
          simp only [Nat.add_sub_cancel] at hm
          have hlp : 0 < lam ^ (2 * (i : ℕ)) := pow_pos hs.hlam _
          have hC := hs.hC
          have hmpos : 0 < msf ((i : ℕ) + 1) := lt_of_lt_of_le (by positivity) hm.1
          have hlogη : Real.log (η i) ≤ Real.log A + Real.log (lam ^ (2 * (i : ℕ))) := by
            rw [← Real.log_mul hA.ne' hlp.ne']
            exact Real.log_le_log hpos (hηA i hi1)
          have hlogm : Real.log (C⁻¹) + Real.log (lam ^ (2 * (i : ℕ))) ≤
              Real.log (msf ((i : ℕ) + 1)) := by
            rw [← Real.log_mul (inv_ne_zero hs.hC.ne') hlp.ne']
            exact Real.log_le_log (by positivity) hm.1
          rw [Real.log_inv] at hlogm
          have h1 := le_abs_self (Real.log A)
          have h2 := le_abs_self (Real.log C)
          simp only [L]
          linarith
      linarith
  -- the cluster part
  have hH : rateCluster p kmult η - rateCluster p kmult u ≤ ∑ i, (η i - u i) := by
    have h := abs_rateCluster_sub_le hs.hk hs.hlam.le hs.hsmall huD (mem_rateDomain hη)
    have hn : ‖η - u‖ ≤ ∑ i, (η i - u i) := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ =>
        sub_nonneg.mpr (huη i))).mpr fun i => ?_
      rw [Real.norm_eq_abs, Pi.sub_apply, abs_of_nonneg (sub_nonneg.mpr (huη i))]
      exact Finset.single_le_sum (f := fun j => η j - u j)
        (fun j _ => sub_nonneg.mpr (huη j)) (Finset.mem_univ i)
    have hB1 : 16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 ≤ 1 := by
      have := hs.hB; unfold rateB at this; linarith
    calc rateCluster p kmult η - rateCluster p kmult u ≤
          16 * rateSeriesConst p C ^ 2 * 2 ^ p * lam ^ 2 * ‖η - u‖ := (le_abs_self _).trans h
      _ ≤ 1 * ∑ i, (η i - u i) := mul_le_mul hB1 hn (norm_nonneg _) zero_le_one
      _ = ∑ i, (η i - u i) := one_mul _
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hent i
  rw [← Finset.mul_sum] at hsum
  have : (L + 1) * ∑ i, (η i - u i) = L * ∑ i, (η i - u i) + ∑ i, (η i - u i) := by ring
  simp only [L] at this ⊢
  linarith

/-! ### Uniform continuity -/

theorem uniformContinuous (hs : RateSetup p msf kmult C lam) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ∀ a ∈ simplex p 0, ∀ b ∈ simplex p 0, ‖a - b‖ < ε' →
      |rateFunction p msf kmult a - rateFunction p msf kmult b| < ε := by
  have huc := (isCompact_simplex 0).uniformContinuousOn_of_continuous (hs.continuousOn 0)
  obtain ⟨ε', hε', h⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨ε', hε', fun a ha b hb hab => ?_⟩
  have := h a ha b hb (by rwa [dist_eq_norm])
  rwa [Real.dist_eq] at this

end RateSetup

end TheoremTwo

end MultipoleBKT

end
