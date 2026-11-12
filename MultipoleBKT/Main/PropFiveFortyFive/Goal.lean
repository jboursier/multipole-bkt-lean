/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.LogEstimate
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.Main.TheoremTwo.ProfileFacts

/-!
# Proposition 5.45: the sum over partitions into bounded blocks (eq. (5.163))

The last steps of the proof of Proposition 5.45: for a partition `π ∈ 𝚷_p([N])` with `n_i` blocks of size `i + 1` and
`γᵢ = n_i/N`,

  `log (N!/∏ᵢ ((i+1)!)^{n_i} n_i! · 𝖬^0_∞(π) polymerSum(π)) = -N ℐ(γ) + o(N)`

uniformly in `π` (`eventually_abs_log_count_mul_le`, from (4.27), (2.45),
Stirling's formula and the logarithm of the polymer gas), and summing over the at most `(N+1)^p`
profiles with the continuity of `ℐ` on `Δ_{p,0}` (`eventually_abs_log_sum_le`, eq. (5.163)):

  `log ∑_{π ∈ 𝚷_p([N])} 𝖬^0_∞(π) polymerSum(π) = -N inf_{Δ_{p,0}} ℐ + o(N)`.

Here the factor `(N C_{β,λ})^N` of `Ẑ(π)` is kept apart.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace PropFiveFortyFive

/-- The number of partitions in `𝚷_p([N])` with block counts `ν`. -/
noncomputable def partitionCount (N p : ℕ) (ν : Fin p → ℕ) : ℕ :=
  ((boundedBlockPartitions N p).filter fun σ => blockCount p σ = ν).card

theorem partitionCount_mul {N p : ℕ} {ν : Fin p → ℕ}
    (hν : ∑ i : Fin p, ((i : ℕ) + 1) * ν i = N) :
    partitionCount N p ν * profileWeight ν = N.factorial :=
  card_boundedBlockPartitions_mul hν

theorem partitionCount_pos {N p : ℕ} {ν : Fin p → ℕ}
    (hν : ∑ i : Fin p, ((i : ℕ) + 1) * ν i = N) : 0 < partitionCount N p ν := by
  have h := partitionCount_mul hν
  rcases Nat.eq_zero_or_pos (partitionCount N p ν) with h0 | h0
  · rw [h0, zero_mul] at h
    exact absurd h.symm (Nat.factorial_ne_zero N)
  · exact h0

/-- `log #{π : π has profile ν} = log N! - ∑ᵢ (νᵢ log (i+1)! + log νᵢ!)`. -/
theorem log_partitionCount {N p : ℕ} {ν : Fin p → ℕ}
    (hν : ∑ i : Fin p, ((i : ℕ) + 1) * ν i = N) :
    Real.log (partitionCount N p ν) = Real.log (N.factorial : ℝ) -
      ∑ i, ((ν i : ℝ) * Real.log (((i : ℕ) + 1).factorial : ℝ) +
        Real.log ((ν i).factorial : ℝ)) := by
  have h := partitionCount_mul hν
  have hP : (0 : ℝ) < profileWeight ν := by exact_mod_cast profileWeight_pos ν
  have hc : (partitionCount N p ν : ℝ) = N.factorial / profileWeight ν := by
    rw [eq_div_iff hP.ne']
    exact_mod_cast h
  rw [hc, Real.log_div (by positivity) hP.ne']
  congr 1
  unfold profileWeight
  push_cast
  rw [Real.log_prod (fun i _ => by positivity)]
  refine sum_congr rfl fun i _ => ?_
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]

/-! ### The entropy identity -/

/-- `N γ log γ = ν log ν - ν log N` for `γ = ν/N`. -/
theorem natCast_mul_log_div {N ν : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * (((ν : ℝ) / N) * Real.log ((ν : ℝ) / N)) =
      (ν : ℝ) * Real.log ν - ν * Real.log N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · simp
  · have hν0 : (0 : ℝ) < ν := by exact_mod_cast hν
    rw [Real.log_div hν0.ne' hN0.ne']
    field_simp

/-- **The entropy identity** behind (5.163): with `γᵢ = νᵢ/N`, `∑ᵢ (i+1) νᵢ = N`,
`log N! - ∑ᵢ (νᵢ log (i+1)! + Lᵢ) + ∑ᵢ νᵢ ℓᵢ + X + N ℐ(γ)` equals
`(log N! - (N log N - N)) - ∑ᵢ (Lᵢ - (νᵢ log νᵢ - νᵢ)) + ∑ᵢ νᵢ (ℓᵢ + i log N - log 𝗆(i+1))
+ (X + N h(γ))`. -/
theorem entropy_identity {N p : ℕ} (hN : 1 ≤ N) {ν : Fin p → ℕ}
    (hν : ∑ i : Fin p, ((i : ℕ) + 1) * ν i = N) (msf : ℕ → ℝ) (kmult : (ℕ →₀ ℕ) → ℝ)
    (L : Fin p → ℝ) (ℓ : Fin p → ℝ) (X : ℝ) :
    Real.log (N.factorial : ℝ) -
        ∑ i, ((ν i : ℝ) * Real.log (((i : ℕ) + 1).factorial : ℝ) + L i) +
        ∑ i, (ν i : ℝ) * ℓ i + X +
        N * rateFunction p msf kmult (fun i => (ν i : ℝ) / N) =
      (Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)) +
        ∑ i, (-(L i - ((ν i : ℝ) * Real.log (ν i) - ν i)) +
          (ν i : ℝ) * (ℓ i + (i : ℕ) * Real.log N - Real.log (msf ((i : ℕ) + 1)))) +
        (X + N * rateCluster p kmult (fun i => (ν i : ℝ) / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [rateFunction_eq]
  have hsumN : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * ν i = N := by exact_mod_cast hν
  have hNsum : (N : ℝ) * ∑ i : Fin p, (ν i : ℝ) / N * (Real.log ((i : ℕ) + 1).factorial - 1 +
      Real.log ((ν i : ℝ) / N) - Real.log (msf ((i : ℕ) + 1))) =
      ∑ i : Fin p, ((ν i : ℝ) * Real.log ((i : ℕ) + 1).factorial - ν i +
        ((ν i : ℝ) * Real.log (ν i) - ν i * Real.log N) - ν i * Real.log (msf ((i : ℕ) + 1))) := by
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have h := natCast_mul_log_div (ν := ν i) hN
    have e : (N : ℝ) * ((ν i : ℝ) / N * (Real.log ((i : ℕ) + 1).factorial - 1 +
        Real.log ((ν i : ℝ) / N) - Real.log (msf ((i : ℕ) + 1)))) =
        (ν i : ℝ) * Real.log ((i : ℕ) + 1).factorial - ν i +
          (N : ℝ) * ((ν i : ℝ) / N * Real.log ((ν i : ℝ) / N)) -
          ν i * Real.log (msf ((i : ℕ) + 1)) := by
      field_simp
    rw [e, h]
  have hlogsum : ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * ν i * Real.log N = N * Real.log N := by
    rw [← sum_mul, hsumN]
  -- reduce to a single sum
  have hgoal : ∀ A B : ℝ, A = B → A = B := fun _ _ h => h
  refine hgoal _ _ ?_
  rw [mul_add, mul_add, hNsum, mul_one]
  have e1 : ∑ i : Fin p, ((ν i : ℝ) * Real.log ((i : ℕ) + 1).factorial - ν i +
        ((ν i : ℝ) * Real.log (ν i) - ν i * Real.log N) - ν i * Real.log (msf ((i : ℕ) + 1))) =
      ∑ i : Fin p, ((ν i : ℝ) * Real.log (((i : ℕ) + 1).factorial : ℝ) + L i) -
        ∑ i : Fin p, (ν i : ℝ) * ℓ i +
        ∑ i, (-(L i - ((ν i : ℝ) * Real.log (ν i) - ν i)) +
          (ν i : ℝ) * (ℓ i + (i : ℕ) * Real.log N - Real.log (msf ((i : ℕ) + 1)))) -
        ∑ i : Fin p, ((i : ℕ) + 1 : ℝ) * ν i * Real.log N := by
    rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [e1, hlogsum]
  ring

/-! ### The profile asymptotics -/

/-- **Profile asymptotics**: uniformly over `π ∈ 𝚷_p([N])` with profile `ν`,
`log(#{π' with profile ν} ∏_{S ∈ π} 𝖬(S) Ξ(π)) = -N ℐ(ν/N) + o(N)`, where `𝖬(S) = Mf_N(|S|)`
with `N^{k-1} Mf_N(k) → 𝗆(k) > 0` (eq. (2.45)) and `log Ξ(π) = -N h(ν/N) + o(N)`. -/
theorem eventually_abs_log_count_mul_le {p : ℕ} {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ}
    {Mf : ℕ → ℕ → ℝ} {Ξ : ℕ → Finset (Finset ℕ) → ℝ}
    (hmsf : ∀ k ∈ Icc 1 p, 0 < msf k)
    (hMf : ∀ k ∈ Icc 1 p, Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * Mf N k) atTop (𝓝 (msf k)))
    (hΞ : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π ∈ boundedBlockPartitions N p,
      0 < Ξ N π ∧ |Real.log (Ξ N π) + N * rateCluster p kmult (profileVec p N π)| ≤ ε * N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π ∈ boundedBlockPartitions N p,
      0 < (∏ S ∈ π, Mf N S.card) * Ξ N π ∧
        |Real.log (partitionCount N p (blockCount p π)) +
            Real.log ((∏ S ∈ π, Mf N S.card) * Ξ N π) +
            N * rateFunction p msf kmult (profileVec p N π)| ≤ ε * N := by
  intro ε hε
  set ε₁ := ε / 4
  have hε₁ : 0 < ε₁ := by positivity
  -- the limits of `log (N^{k-1} Mf_N(k))`
  have hlog : ∀ k ∈ Icc 1 p, ∀ᶠ N : ℕ in atTop, 0 < (N : ℝ) ^ (k - 1) * Mf N k ∧
      |Real.log ((N : ℝ) ^ (k - 1) * Mf N k) - Real.log (msf k)| ≤ ε₁ := by
    intro k hk
    have hT := ((Real.continuousAt_log (hmsf k hk).ne').tendsto).comp (hMf k hk)
    filter_upwards [(hMf k hk).eventually (lt_mem_nhds (hmsf k hk)),
      (Metric.tendsto_nhds.1 hT) ε₁ hε₁] with N h1 h2
    rw [Real.dist_eq] at h2
    exact ⟨h1, h2.le⟩
  filter_upwards [(eventually_all_finset (Icc 1 p)).2 hlog, hΞ ε₁ hε₁, eventually_ge_atTop 1,
    TheoremTwo.eventually_log_le ε₁ hε₁ ((p : ℝ) + 1)] with N hlogN hΞN hN hlogle π hπ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hπ1 := card_mem_Icc_of_mem_boundedBlockPartitions hπ
  set ν := blockCount p π with hν_def
  have hν : ∑ i : Fin p, ((i : ℕ) + 1) * ν i = N :=
    sum_mul_blockCount_of_mem_boundedBlockPartitions hπ
  have hνN : ∀ i, ν i ≤ N := fun i => by
    rw [← hν]
    calc ν i ≤ ((i : ℕ) + 1) * ν i := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      _ ≤ _ := single_le_sum (f := fun j : Fin p => ((j : ℕ) + 1) * ν j)
          (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hMpos : ∀ i : Fin p, 0 < Mf N ((i : ℕ) + 1) := fun i => by
    have h := (hlogN ((i : ℕ) + 1) (mem_Icc.2 ⟨by omega, i.2⟩)).1
    exact pos_of_mul_pos_right h (by positivity)
  obtain ⟨hΞpos, hΞb⟩ := hΞN π hπ
  have hprod : ∏ S ∈ π, Mf N S.card = ∏ i : Fin p, Mf N ((i : ℕ) + 1) ^ ν i :=
    prod_card_eq_prod_blockCount hπ1 (Mf N)
  have hprodpos : 0 < ∏ S ∈ π, Mf N S.card := by
    rw [hprod]
    exact prod_pos fun i _ => pow_pos (hMpos i) _
  refine ⟨mul_pos hprodpos hΞpos, ?_⟩
  have hlogprod : Real.log ((∏ S ∈ π, Mf N S.card) * Ξ N π) =
      ∑ i : Fin p, (ν i : ℝ) * Real.log (Mf N ((i : ℕ) + 1)) + Real.log (Ξ N π) := by
    rw [Real.log_mul hprodpos.ne' hΞpos.ne', hprod,
      Real.log_prod (fun i _ => (pow_pos (hMpos i) _).ne')]
    simp only [Real.log_pow]
  rw [hlogprod, log_partitionCount hν]
  have hγ : profileVec p N π = fun i => (ν i : ℝ) / N := rfl
  rw [hγ, ← add_assoc, entropy_identity hN hν msf kmult _ _ (Real.log (Ξ N π))]
  rw [← hγ]
  -- the three error terms
  have hS := TheoremTwo.abs_log_factorial_sub_le hN
  have hlogN1 : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log hN0 (by linarith)
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hterm : ∀ i : Fin p,
      |-(Real.log ((ν i).factorial : ℝ) - ((ν i : ℝ) * Real.log (ν i) - ν i)) +
        (ν i : ℝ) * (Real.log (Mf N ((i : ℕ) + 1)) + (i : ℕ) * Real.log N -
          Real.log (msf ((i : ℕ) + 1)))| ≤ (1 + Real.log ((N : ℝ) + 1)) + ν i * ε₁ := by
    intro i
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg]
      rcases Nat.eq_zero_or_pos (ν i) with h0 | h0
      · rw [h0]
        simp only [Nat.factorial_zero, Nat.cast_one, Real.log_one, Nat.cast_zero, zero_mul,
          sub_self, abs_zero]
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ N + 1)
        linarith
      · refine (TheoremTwo.abs_log_factorial_sub_le h0).trans ?_
        have : Real.log (ν i) ≤ Real.log ((N : ℝ) + 1) :=
          Real.log_le_log (by exact_mod_cast h0) (by
            have : (ν i : ℝ) ≤ N := by exact_mod_cast hνN i
            linarith)
        linarith
    · rw [abs_mul, Nat.abs_cast]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hk := hlogN ((i : ℕ) + 1) (mem_Icc.2 ⟨by omega, i.2⟩)
      rw [Real.log_mul (by positivity) (hMpos i).ne', Real.log_pow,
        Nat.add_sub_cancel] at hk
      have e : Real.log (Mf N ((i : ℕ) + 1)) + (i : ℕ) * Real.log N -
          Real.log (msf ((i : ℕ) + 1)) =
          (i : ℕ) * Real.log N + Real.log (Mf N ((i : ℕ) + 1)) -
            Real.log (msf ((i : ℕ) + 1)) := by ring
      rw [e]
      exact hk.2
  have hsumν : ∑ i : Fin p, (ν i : ℝ) ≤ N := by
    have : ∑ i : Fin p, ν i ≤ N := by
      rw [← hν]
      exact sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact_mod_cast this
  calc |(Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)) +
        ∑ i, (-(Real.log ((ν i).factorial : ℝ) - ((ν i : ℝ) * Real.log (ν i) - ν i)) +
          (ν i : ℝ) * (Real.log (Mf N ((i : ℕ) + 1)) + (i : ℕ) * Real.log N -
            Real.log (msf ((i : ℕ) + 1)))) +
        (Real.log (Ξ N π) + N * rateCluster p kmult (profileVec p N π))|
      ≤ (1 + Real.log ((N : ℝ) + 1)) +
          ∑ i : Fin p, ((1 + Real.log ((N : ℝ) + 1)) + ν i * ε₁) + ε₁ * N := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) hΞb)
        · linarith
        · exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => hterm i)
    _ = ((p : ℝ) + 1) * (Real.log ((N : ℝ) + 1) + 1) + ε₁ * ∑ i : Fin p, (ν i : ℝ) + ε₁ * N := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul]
        ring
    _ ≤ ε₁ * N + ε₁ * N + ε₁ * N :=
        add_le_add (add_le_add hlogle (mul_le_mul_of_nonneg_left hsumν hε₁.le)) le_rfl
    _ ≤ ε * N := by
        simp only [ε₁]
        nlinarith

/-! ### Summing over the profiles (eq. (5.163)) -/

/-- `∑_{π ∈ 𝚷_p([N])} 1/#{π' with the profile of π} = #{profiles} ≤ (N + 1)^p`. -/
theorem sum_inv_partitionCount_le {N p : ℕ} :
    ∑ π ∈ boundedBlockPartitions N p, (1 : ℝ) / partitionCount N p (blockCount p π) ≤
      ((N : ℝ) + 1) ^ p := by
  set PP := boundedBlockPartitions N p
  have hmaps : ∀ π ∈ PP, blockCount p π ∈ PP.image (blockCount p) := fun π hπ =>
    mem_image_of_mem _ hπ
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ ν ∈ PP.image (blockCount p),
      ∑ π ∈ PP.filter (fun π => blockCount p π = ν),
        (1 : ℝ) / partitionCount N p (blockCount p π) = 1 := by
    intro ν hν
    obtain ⟨π₀, hπ₀, rfl⟩ := mem_image.1 hν
    have hpos : (0 : ℝ) < partitionCount N p (blockCount p π₀) := by
      exact_mod_cast partitionCount_pos (sum_mul_blockCount_of_mem_boundedBlockPartitions hπ₀)
    rw [sum_congr rfl fun π hπ => by rw [(mem_filter.1 hπ).2], sum_const, nsmul_eq_mul]
    have hcard : (PP.filter fun π => blockCount p π = blockCount p π₀).card =
        partitionCount N p (blockCount p π₀) := rfl
    rw [hcard]
    field_simp
  rw [sum_congr rfl hfib, sum_const, nsmul_eq_mul, mul_one]
  -- the profiles lie in a box
  have hsub : PP.image (blockCount p) ⊆ Fintype.piFinset fun _ : Fin p => range (N + 1) := by
    intro ν hν
    obtain ⟨π, hπ, rfl⟩ := mem_image.1 hν
    rw [Fintype.mem_piFinset]
    intro i
    rw [mem_range, Nat.lt_succ_iff]
    have h := sum_mul_blockCount_of_mem_boundedBlockPartitions hπ
    rw [← h]
    calc blockCount p π i ≤ ((i : ℕ) + 1) * blockCount p π i :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      _ ≤ _ := single_le_sum (f := fun j : Fin p => ((j : ℕ) + 1) * blockCount p π j)
          (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hc := card_le_card hsub
  rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, card_range] at hc
  exact_mod_cast hc

/-- The profile of a partition in `𝚷_p([N])` lies in `Δ_{p,0}`. -/
theorem profileVec_mem_simplex {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ : π ∈ boundedBlockPartitions N p) : profileVec p N π ∈ simplex p 0 := by
  have hν := sum_mul_blockCount_of_mem_boundedBlockPartitions hπ
  have h := (TheoremTwo.profile_mem_simplex hN hν.le).1
  rw [hν] at h
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  rwa [div_self hN0, sub_self] at h

/-- **The sum over partitions** (eq. (5.163)): if, uniformly over `π ∈ 𝚷_p([N])`,
`log(#{π' with the profile of π} W_N(π)) = -N Φ(γ(π)) + o(N)` with `γ(π)` the profile, and `Φ`
has a minimizer `γ*` on `Δ_{p,0}` at which it is continuous along `Δ_{p,0}`, then
`log ∑_{π ∈ 𝚷_p([N])} W_N(π) = -N Φ(γ*) + o(N)`. -/
theorem eventually_abs_log_sum_le {p : ℕ} (hp : 1 ≤ p) {Φ : (Fin p → ℝ) → ℝ}
    {γs : Fin p → ℝ} (hγs : γs ∈ simplex p 0) (hmin : IsMinOn Φ (simplex p 0) γs)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ simplex p 0, ‖γ - γs‖ < δ →
      Φ γ ≤ Φ γs + ε)
    {W : ℕ → Finset (Finset ℕ) → ℝ}
    (hW : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ π ∈ boundedBlockPartitions N p,
      0 < W N π ∧ |Real.log (partitionCount N p (blockCount p π)) + Real.log (W N π) +
        N * Φ (profileVec p N π)| ≤ ε * N) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      0 < ∑ π ∈ boundedBlockPartitions N p, W N π ∧
        |Real.log (∑ π ∈ boundedBlockPartitions N p, W N π) + N * Φ γs| ≤ ε * N := by
  intro ε hε
  set ε₁ := ε / 3
  have hε₁ : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ, hcontδ⟩ := hcont ε₁ hε₁
  have hev : ∀ᶠ N : ℕ in atTop, ((p : ℝ) ^ 2) / N < δ := by
    have := tendsto_const_div_atTop_nhds_zero_nat ((p : ℝ) ^ 2)
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [hW ε₁ hε₁, eventually_ge_atTop 1, hev,
    TheoremTwo.eventually_log_le ε₁ hε₁ (p : ℝ)] with N hWN hN hNδ hlogle
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set PP := boundedBlockPartitions N p
  -- per-partition two-sided bounds on `W`
  have hcount : ∀ π ∈ PP, (0 : ℝ) < partitionCount N p (blockCount p π) := fun π hπ => by
    exact_mod_cast partitionCount_pos (sum_mul_blockCount_of_mem_boundedBlockPartitions hπ)
  have hWexp : ∀ π ∈ PP, W N π =
      Real.exp (Real.log (partitionCount N p (blockCount p π)) + Real.log (W N π) +
        N * Φ (profileVec p N π) - N * Φ (profileVec p N π)) /
          partitionCount N p (blockCount p π) := by
    intro π hπ
    rw [add_sub_cancel_right, Real.exp_add, Real.exp_log (hcount π hπ),
      Real.exp_log (hWN π hπ).1]
    field_simp [(hcount π hπ).ne']
  -- the lower bound, from a profile close to the minimizer
  obtain ⟨ν, hν, -, hνclose⟩ := TheoremTwo.exists_profile hp hγs hN
  have hνpos := partitionCount_pos (p := p) hν
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀, π₀ ∈ PP.filter fun σ => blockCount p σ = ν :=
    card_pos.1 hνpos
  have hπ₀P := (mem_filter.1 hπ₀).1
  have hπ₀ν := (mem_filter.1 hπ₀).2
  have hγν : profileVec p N π₀ = fun i => (ν i : ℝ) / N := by
    funext i; simp only [profileVec, hπ₀ν]
  have hΦν : Φ (profileVec p N π₀) ≤ Φ γs + ε₁ := by
    refine hcontδ _ (profileVec_mem_simplex hN hπ₀P) ?_
    rw [hγν]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_) hNδ
    rw [Real.norm_eq_abs, Pi.sub_apply]
    exact hνclose i
  have hpos : 0 < ∑ π ∈ PP, W N π := sum_pos (fun π hπ => (hWN π hπ).1) ⟨π₀, hπ₀P⟩
  refine ⟨hpos, ?_⟩
  have hlower : Real.exp (-(N * Φ γs) - 2 * ε₁ * N) ≤ ∑ π ∈ PP, W N π := by
    have hfib : ∑ π ∈ PP.filter (fun σ => blockCount p σ = ν), W N π ≤ ∑ π ∈ PP, W N π :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun π hπ _ => (hWN π hπ).1.le
    refine le_trans ?_ hfib
    have hterm : ∀ π ∈ PP.filter (fun σ => blockCount p σ = ν),
        Real.exp (-(N * Φ γs) - 2 * ε₁ * N) / partitionCount N p ν ≤ W N π := by
      intro π hπ
      have hπP := (mem_filter.1 hπ).1
      have hπν := (mem_filter.1 hπ).2
      rw [hWexp π hπP, hπν]
      refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
      have hb := (hWN π hπP).2
      have hγπ : profileVec p N π = profileVec p N π₀ := by
        funext i; simp only [profileVec, hπν, hπ₀ν]
      rw [hγπ] at hb ⊢
      have h1 : N * Φ (profileVec p N π₀) ≤ N * Φ γs + N * ε₁ :=
        by nlinarith [mul_le_mul_of_nonneg_left hΦν hN0.le]
      rw [abs_le, hπν] at hb
      linarith [hb.1]
    calc Real.exp (-(N * Φ γs) - 2 * ε₁ * N)
        = ∑ _π ∈ PP.filter (fun σ => blockCount p σ = ν),
            Real.exp (-(N * Φ γs) - 2 * ε₁ * N) / partitionCount N p ν := by
          have hcard : (PP.filter fun σ => blockCount p σ = ν).card = partitionCount N p ν := rfl
          rw [sum_const, nsmul_eq_mul, hcard]
          field_simp
      _ ≤ _ := sum_le_sum hterm
  have hupper : ∑ π ∈ PP, W N π ≤ Real.exp (-(N * Φ γs) + ε₁ * N) * ((N : ℝ) + 1) ^ p := by
    have hterm : ∀ π ∈ PP, W N π ≤
        Real.exp (-(N * Φ γs) + ε₁ * N) * (1 / partitionCount N p (blockCount p π)) := by
      intro π hπ
      rw [hWexp π hπ, mul_one_div]
      refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (Nat.cast_nonneg _)
      have hb := (hWN π hπ).2
      have hmin' : Φ γs ≤ Φ (profileVec p N π) := hmin (profileVec_mem_simplex hN hπ)
      rw [abs_le] at hb
      nlinarith [mul_le_mul_of_nonneg_left hmin' hN0.le]
    calc ∑ π ∈ PP, W N π
        ≤ ∑ π ∈ PP, Real.exp (-(N * Φ γs) + ε₁ * N) *
            (1 / partitionCount N p (blockCount p π)) := sum_le_sum hterm
      _ = Real.exp (-(N * Φ γs) + ε₁ * N) *
            ∑ π ∈ PP, (1 : ℝ) / partitionCount N p (blockCount p π) := by rw [mul_sum]
      _ ≤ Real.exp (-(N * Φ γs) + ε₁ * N) * ((N : ℝ) + 1) ^ p :=
          mul_le_mul_of_nonneg_left sum_inv_partitionCount_le (Real.exp_pos _).le
  have hlo := Real.log_le_log (Real.exp_pos _) hlower
  rw [Real.log_exp] at hlo
  have hhi := Real.log_le_log hpos hupper
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow] at hhi
  have hlp : (p : ℝ) * Real.log ((N : ℝ) + 1) ≤ ε₁ * N := by
    have h0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
    nlinarith [hlogle]
  have hεε : ε * N = 3 * (ε₁ * N) := by simp only [ε₁]; ring
  have hε₁N : 0 ≤ ε₁ * N := by positivity
  rw [abs_le]
  constructor <;> linarith

end PropFiveFortyFive

end MultipoleBKT

end
