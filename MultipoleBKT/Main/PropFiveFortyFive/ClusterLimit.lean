/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.PropFiveFortyFive.Grouping
public import MultipoleBKT.Main.TheoremOne.Grouping
public import MultipoleBKT.Frozen.RateSeriesTerm

/-!
# Proposition 5.45: the hypertree limit of a cluster term over a partition

The hypertree calculation (4.155), used without the restriction (4.22) in the proof of Proposition 5.45 (Step 3
of the proof of Proposition 4.62 only uses the activity bound). Fix the order `n` of the cluster
term and let `K_N` be activities depending only on the block profile, with
`N^{|X|-1} K_N(X) → k((#_j X)_j)` for the polymers `X ⊂ Y(m)`.

* `tendsto_unionSum` (eqs. (4.148)–(4.154)): `N^{|m|} N⁻¹ unionSum(m) → hypertreeSum(m)`,
  the sum over the hypertrees `X ∈ Htrees_n(Y(m))` covering `Y(m)` of
  `𝟙_{|V_{X_i}| ≤ p} ∏ᵢ k((#_j X_i)_j) I(G(X))`: the exponent of `N` is
  `|⋃ᵢ X_i| + n - ∑ᵢ |X_i| - 1 ≤ 0`, with equality exactly for hypertrees.
* `rateSeriesTerm_eq` (eq. (4.150)): `I(G(X)) = (-1)^{n-1} ω(X)` on hypertrees identifies
  `-(1/n!) ∏ᵢ (γᵢ^{mᵢ}/mᵢ!) hypertreeSum(m)` with the `(n, m)` term of the rate function.
* `eventually_abs_clusterSum_sub_le` (eq. (4.155), uniformly in the profile): for every
  `ε > 0`, for `N` large and every subpartition `A` with `|A| ≤ N` and blocks of sizes at most
  `p`, `|N⁻¹ ∑_{X_1, …, X_n ⊂ A} clusterWeight(X) - ∑_m ∏ᵢ (γᵢ^{mᵢ}/mᵢ!) hypertreeSum(m)| ≤ ε`,
 where `γᵢ = #_{i+1} A / N`. The paper asserts this uniformity; here it
  follows from the exact count `∏ᵢ C(n_i, m_i)` of the subfamilies with a given profile and
  `|C(n, k)/N^k - (n/N)^k/k!| ≤ k²/N`.
-/

@[expose] public section

open Finset Filter Topology

namespace MultipoleBKT

namespace PropFiveFortyFive

variable {p n : ℕ}

open scoped Classical in
/-- The hypertree sum
`∑_{X ∈ Htrees_n(Y(m)), ⋃ᵢ X_i = Y(m)} 𝟙_{|V_{X_i}| ≤ p} ∏ᵢ k((#_j X_i)_j) I(G(X))`,
the limit of the normalized cluster terms with union `Y(m)`. -/
noncomputable def hypertreeSum (p n : ℕ) (k : (ℕ →₀ ℕ) → ℝ) (m : Fin p → ℕ) : ℝ :=
  ∑ X ∈ (hypertrees n (canonicalPartition m)).filter
      (fun X => univ.biUnion X = canonicalPartition m),
    (if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, k (blockProfile (X i)) else 0) *
      (ursell (connectionGraph X) : ℝ)

/-! ### The limit for a fixed union -/

/-- The algebra of the exponent count, for `N ≥ 1`. -/
theorem pow_mul_div_eq {N s t d : ℕ} (hN : 1 ≤ N) (hsd : s + d = t + 1) (P G : ℝ) :
    (N : ℝ) ^ s * (P * G) / N = (1 / (N : ℝ)) ^ d * (((N : ℝ) ^ t * P) * G) := by
  have hx : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have h : (N : ℝ) ^ s * (N : ℝ) ^ d = (N : ℝ) ^ t * N := by
    rw [← pow_add, hsd, pow_succ]
  have hNd : (N : ℝ) ^ d ≠ 0 := pow_ne_zero d hx
  rw [one_div_pow, div_eq_iff hx]
  field_simp
  calc (N : ℝ) ^ s * P * G * (N : ℝ) ^ d = ((N : ℝ) ^ s * (N : ℝ) ^ d) * (P * G) := by ring
    _ = ((N : ℝ) ^ t * N) * (P * G) := by rw [h]
    _ = _ := by ring

open scoped Classical in
/-- The limit of one family's contribution `N^{|m|} N⁻¹ clusterWeight_N(X)`, for `X` with union
`Y(m)` (eqs. (4.148), (4.149)). -/
theorem tendsto_clusterWeight {K : ℕ → Finset (Finset ℕ) → ℝ} {k : (ℕ →₀ ℕ) → ℝ}
    {m : Fin p → ℕ}
    (hlim : ∀ X ⊆ canonicalPartition m, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop (𝓝 (k (blockProfile X))))
    {X : Fin n → Finset (Finset ℕ)}
    (hX : X ∈ Fintype.piFinset fun _ : Fin n => (canonicalPartition m).powerset)
    (hU : univ.biUnion X = canonicalPartition m) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (∑ i, m i) * clusterWeight p (K N) X / N) atTop
      (𝓝 (if X ∈ hypertrees n (canonicalPartition m) then
        (if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, k (blockProfile (X i)) else 0) *
          (ursell (connectionGraph X) : ℝ) else 0)) := by
  rw [Fintype.mem_piFinset] at hX
  have hXsub : ∀ i, X i ⊆ canonicalPartition m := fun i => mem_powerset.1 (hX i)
  have hmem : X ∈ hypertrees n (canonicalPartition m) ↔ (∀ i, 2 ≤ (X i).card) ∧
      (connectionGraph X).Connected ∧
      ((univ.biUnion X).card : ℤ) + n - ∑ i, ((X i).card : ℤ) = 1 := by
    simp only [hypertrees, mem_filter, Fintype.mem_piFinset, mem_powerset, hXsub, implies_true,
      true_and]
  by_cases hc : (connectionGraph X).Connected ∧
      ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p
  swap
  · have hL : (if X ∈ hypertrees n (canonicalPartition m) then
        (if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, k (blockProfile (X i)) else 0) *
          (ursell (connectionGraph X) : ℝ) else 0) = 0 := by
      split_ifs with hH hp
      · exact absurd ⟨(hmem.mp hH).2.1, fun i => ⟨(hmem.mp hH).1 i, hp i⟩⟩ hc
      · simp
      · rfl
    have hz : ∀ N, clusterWeight p (K N) X = 0 := fun N => by
      unfold clusterWeight
      rw [ite_eq_right hc]
    simp only [hz, mul_zero, zero_div, hL]
    exact tendsto_const_nhds
  have h2 : ∀ i, 2 ≤ (X i).card := fun i => (hc.2 i).1
  set t : ℕ := ∑ i, ((X i).card - 1) with ht
  have hsum : ∑ i, (X i).card = t + n := by
    have h1' : ∀ i, (X i).card = ((X i).card - 1) + 1 := fun i => by have := h2 i; omega
    rw [sum_congr rfl fun i _ => h1' i, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one]
  have hcount := TheoremOne.card_biUnion_add_le hc.1
  rw [hU, card_canonicalPartition, hsum] at hcount
  set s : ℕ := ∑ i, m i with hs
  set d : ℕ := t + 1 - s with hd
  have hsd : s + d = t + 1 := by omega
  have hHd : X ∈ hypertrees n (canonicalPartition m) ↔ d = 0 := by
    rw [hmem, hU, card_canonicalPartition, ← hs]
    have hcast : ∑ i, ((X i).card : ℤ) = ((t + n : ℕ) : ℤ) := by rw [← hsum]; push_cast; rfl
    rw [hcast]
    constructor
    · rintro ⟨-, -, h⟩
      push_cast at h
      omega
    · intro h
      refine ⟨h2, hc.1, ?_⟩
      push_cast
      omega
  have hlimP : Tendsto (fun N : ℕ => ∏ i, ((N : ℝ) ^ ((X i).card - 1) * K N (X i))) atTop
      (𝓝 (∏ i, k (blockProfile (X i)))) :=
    tendsto_finsetProd _ fun i _ => hlim (X i) (hXsub i) (h2 i) (hc.2 i).2
  have hinv : Tendsto (fun N : ℕ => (1 / (N : ℝ)) ^ d) atTop (𝓝 ((0 : ℝ) ^ d)) :=
    tendsto_one_div_atTop_nhds_zero_nat.pow d
  have htot := hinv.mul (hlimP.mul_const (ursell (connectionGraph X) : ℝ))
  have hval : (if X ∈ hypertrees n (canonicalPartition m) then
      (if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, k (blockProfile (X i)) else 0) *
        (ursell (connectionGraph X) : ℝ) else 0) =
      (0 : ℝ) ^ d * ((∏ i, k (blockProfile (X i))) * (ursell (connectionGraph X) : ℝ)) := by
    by_cases hd0 : d = 0
    · rw [ite_eq_left (hHd.mpr hd0), ite_eq_left fun i => (hc.2 i).2, hd0, pow_zero, one_mul]
    · rw [ite_eq_right (fun h => hd0 (hHd.mp h)), zero_pow hd0, zero_mul]
  rw [hval]
  refine htot.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  unfold clusterWeight
  rw [ite_eq_left hc]
  have hprod : ∏ i, ((N : ℝ) ^ ((X i).card - 1) * K N (X i)) =
      (N : ℝ) ^ t * ∏ i, K N (X i) := by
    rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  rw [hprod]
  exact (pow_mul_div_eq hN hsd _ _).symm

open scoped Classical in
/-- **Only hypertrees survive** (eqs. (4.148)–(4.154)), for a fixed union
`Y(m)`: `N^{|m|} N⁻¹ unionSum_N(m) → hypertreeSum(m)`. -/
theorem tendsto_unionSum {K : ℕ → Finset (Finset ℕ) → ℝ} {k : (ℕ →₀ ℕ) → ℝ}
    {m : Fin p → ℕ}
    (hlim : ∀ X ⊆ canonicalPartition m, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (X.card - 1) * K N X) atTop (𝓝 (k (blockProfile X)))) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (∑ i, m i) * unionSum p n (K N) m / N) atTop
      (𝓝 (hypertreeSum p n k m)) := by
  have hR : hypertreeSum p n k m =
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => (canonicalPartition m).powerset).filter
          (fun X => univ.biUnion X = canonicalPartition m),
        if X ∈ hypertrees n (canonicalPartition m) then
          (if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, k (blockProfile (X i)) else 0) *
            (ursell (connectionGraph X) : ℝ) else 0 := by
    unfold hypertreeSum
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext X
    simp only [mem_filter]
    constructor
    · rintro ⟨hH, hU⟩
      have hH' := hH
      simp only [hypertrees, mem_filter] at hH'
      exact ⟨⟨hH'.1, hU⟩, hH⟩
    · rintro ⟨⟨-, hU⟩, hH⟩
      exact ⟨hH, hU⟩
  rw [hR]
  unfold unionSum
  simp_rw [mul_sum, sum_div]
  exact tendsto_finsetSum _ fun X hX =>
    tendsto_clusterWeight hlim (mem_filter.1 hX).1 (mem_filter.1 hX).2

/-! ### The rate function -/

open scoped Classical in
theorem hypertreeSum_eq (p : ℕ) (n : ℕ) (k : (ℕ →₀ ℕ) → ℝ) (m : Fin p → ℕ) :
    hypertreeSum p n k m = (-1) ^ (n - 1) *
      ∑ X ∈ (hypertrees n (canonicalPartition m)).filter
          (fun X => univ.biUnion X = canonicalPartition m),
        (hypertreeWeight X : ℝ) *
          if ∀ i, ((X i).biUnion id).card ≤ p then ∏ i, k (blockProfile (X i)) else 0 := by
  unfold hypertreeSum
  rw [mul_sum]
  refine sum_congr rfl fun X hX => ?_
  rw [ursell_connectionGraph_of_mem_hypertrees (mem_filter.1 hX).1]
  push_cast
  ring

/-- **The `(n, m)` term of the rate function** (Definition 2.15 with (4.150)):
`rateSeriesTerm(γ, n, m) = -(1/n!) ∏ᵢ (γᵢ^{mᵢ}/mᵢ!) hypertreeSum(m)`. -/
theorem rateSeriesTerm_eq (p : ℕ) (k : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) (n : ℕ+)
    (m : Fin p → ℕ) :
    rateSeriesTerm p k γ n m =
      -(1 / ((n : ℕ).factorial : ℝ)) * (∏ i, γ i ^ m i / (m i).factorial) *
        hypertreeSum p n k m := by
  rw [hypertreeSum_eq]
  unfold rateSeriesTerm
  have hn : (-1 : ℝ) ^ (n : ℕ) = -(-1) ^ ((n : ℕ) - 1) := by
    obtain ⟨j, hj⟩ : ∃ j, (n : ℕ) = j + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [hj, Nat.add_sub_cancel, pow_succ]
    ring
  rw [hn]
  ring

open scoped Classical in
theorem hypertreeSum_eq_zero_of_notMem {k : (ℕ →₀ ℕ) → ℝ} {m : Fin p → ℕ}
    (hm : m ∉ profileBox p n) : hypertreeSum p n k m = 0 := by
  refine sum_eq_zero fun X hX => ?_
  rw [ite_eq_right, zero_mul]
  intro hP
  obtain ⟨hH, hU⟩ := mem_filter.1 hX
  have hXsub : ∀ j, X j ⊆ canonicalPartition m := fun j => by
    simp only [hypertrees, mem_filter, Fintype.mem_piFinset, mem_powerset] at hH
    exact hH.1 j
  apply hm
  rw [profileBox, Fintype.mem_piFinset]
  intro i
  rw [mem_range, Nat.lt_succ_iff]
  have hXi : ∀ j, (X j).card ≤ p := fun j =>
    (card_le_card_biUnion (isSubpartition_of_subset_canonicalPartition (hXsub j))).trans (hP j)
  have h1 : (canonicalPartition m).card ≤ n * p := by
    rw [← hU]
    calc (univ.biUnion X).card ≤ ∑ j, (X j).card := card_biUnion_le
      _ ≤ ∑ _j : Fin n, p := sum_le_sum fun j _ => hXi j
      _ = n * p := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [card_canonicalPartition] at h1
  exact (single_le_sum (fun j _ => Nat.zero_le (m j)) (mem_univ i)).trans h1

/-- The `n`-th cluster term of the rate function is a finite sum over the box `m_i ≤ n p`. -/
theorem tsum_rateSeriesTerm_eq (p : ℕ) (k : (ℕ →₀ ℕ) → ℝ) (γ : Fin p → ℝ) (n : ℕ+) :
    ∑' m : Fin p → ℕ, rateSeriesTerm p k γ n m =
      -(1 / ((n : ℕ).factorial : ℝ)) *
        ∑ m ∈ profileBox p n, (∏ i, γ i ^ m i / (m i).factorial) * hypertreeSum p n k m := by
  rw [tsum_eq_sum (s := profileBox p n) fun m hm => by
    rw [rateSeriesTerm_eq, hypertreeSum_eq_zero_of_notMem hm, mul_zero], mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [rateSeriesTerm_eq]
  ring

/-! ### Uniformity in the partition -/

/-- The normalized count of subfamilies with profile `m` is close to `∏ᵢ γᵢ^{mᵢ}/mᵢ!`. -/
theorem abs_prod_choose_sub_le {N : ℕ} (hN : 1 ≤ N) {ν : Fin p → ℕ} (hν : ∀ i, ν i ≤ N)
    {m : Fin p → ℕ} (hm : m ∈ profileBox p n) :
    |(∏ i, ((ν i).choose (m i) : ℝ)) / (N : ℝ) ^ (∑ i, m i) -
        ∏ i, ((ν i : ℝ) / N) ^ m i / (m i).factorial| ≤ p * ((n * p : ℕ) : ℝ) ^ 2 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfac : (∏ i, ((ν i).choose (m i) : ℝ)) / (N : ℝ) ^ (∑ i, m i) =
      ∏ i, ((ν i).choose (m i) : ℝ) / (N : ℝ) ^ m i := by
    rw [prod_div_distrib, prod_pow_eq_pow_sum]
  rw [hfac]
  have hb := fun i => choose_div_pow_le (k := m i) (hν i) hN
  have hle : ∀ i ∈ (univ : Finset (Fin p)), ((ν i : ℝ) / N) ^ m i / (m i).factorial ≤ 1 := by
    intro i _
    have h1 : (ν i : ℝ) / N ≤ 1 := by rw [div_le_one hN0]; exact_mod_cast hν i
    have h2 : ((ν i : ℝ) / N) ^ m i ≤ 1 := pow_le_one₀ (by positivity) h1
    have h3 : (1 : ℝ) ≤ (m i).factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    exact (div_le_one (by positivity)).2 (h2.trans h3)
  obtain ⟨h0, h1⟩ := prod_sub_prod_le_sum univ
    (a := fun i => ((ν i).choose (m i) : ℝ) / (N : ℝ) ^ m i)
    (b := fun i => ((ν i : ℝ) / N) ^ m i / (m i).factorial) (fun i _ => by positivity)
    (fun i _ => (hb i).1) hle
  rw [abs_sub_comm, abs_of_nonneg h0]
  refine h1.trans ?_
  have hmi : ∀ i, m i ≤ n * p := fun i => by
    have := Fintype.mem_piFinset.1 hm i
    rw [mem_range] at this
    omega
  calc ∑ i, (((ν i : ℝ) / N) ^ m i / (m i).factorial - ((ν i).choose (m i) : ℝ) / (N : ℝ) ^ m i)
      ≤ ∑ _i : Fin p, ((n * p : ℕ) : ℝ) ^ 2 / N := by
        refine sum_le_sum fun i _ => (hb i).2.trans ?_
        gcongr
        exact_mod_cast hmi i
    _ = p * ((n * p : ℕ) : ℝ) ^ 2 / N := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The normalized count of subfamilies with profile `m` lies in `[0, 1]`. -/
theorem prod_choose_div_mem_Icc {N : ℕ} (hN : 1 ≤ N) {ν : Fin p → ℕ} (hν : ∀ i, ν i ≤ N)
    (m : Fin p → ℕ) :
    0 ≤ (∏ i, ((ν i).choose (m i) : ℝ)) / (N : ℝ) ^ (∑ i, m i) ∧
      (∏ i, ((ν i).choose (m i) : ℝ)) / (N : ℝ) ^ (∑ i, m i) ≤ 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨by positivity, ?_⟩
  rw [← prod_pow_eq_pow_sum, ← prod_div_distrib]
  refine prod_le_one₀ (fun i _ => by positivity) fun i _ => ?_
  refine (choose_div_pow_le (k := m i) (hν i) hN).1.trans ?_
  have h1 : (ν i : ℝ) / N ≤ 1 := by rw [div_le_one hN0]; exact_mod_cast hν i
  have h2 : ((ν i : ℝ) / N) ^ m i ≤ 1 := pow_le_one₀ (by positivity) h1
  have h3 : (1 : ℝ) ≤ (m i).factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  exact (div_le_one (by positivity)).2 (h2.trans h3)

/-- **The hypertree calculation (4.155), uniformly in the partition**: for every `ε > 0`, for `N` large and every subpartition `A` with `|A| ≤ N` and
blocks of sizes at most `p`,
`|N⁻¹ ∑_{X_1, …, X_n ⊂ A} clusterWeight_N(X) - ∑_m ∏ᵢ (γᵢ^{mᵢ}/mᵢ!) hypertreeSum(m)| ≤ ε`, with
`γᵢ = #_{i+1} A / N`. -/
theorem eventually_abs_clusterSum_sub_le {K : ℕ → Finset (Finset ℕ) → ℝ} {k : (ℕ →₀ ℕ) → ℝ}
    (hK : ∀ N, 1 ≤ N → IsProfileInvariant (K N))
    (hlim : ∀ m ∈ profileBox p n, Tendsto (fun N : ℕ =>
      (N : ℝ) ^ (∑ i, m i) * unionSum p n (K N) m / N) atTop (𝓝 (hypertreeSum p n k m)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset (Finset ℕ), IsSubpartition A → (∀ S ∈ A, S.card ≤ p) →
      A.card ≤ N →
      |(∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset), clusterWeight p (K N) X) / N -
        ∑ m ∈ profileBox p n, (∏ i, ((blockCount p A i : ℝ) / N) ^ m i / (m i).factorial) *
          hypertreeSum p n k m| ≤ ε := by
  set B := profileBox p n
  set H : ℝ := ∑ m ∈ B, |hypertreeSum p n k m|
  set c : ℝ := p * ((n * p : ℕ) : ℝ) ^ 2
  have hH : 0 ≤ H := sum_nonneg fun _ _ => abs_nonneg _
  have hc : 0 ≤ c := by positivity
  set δ : ℝ := ε / (2 * (B.card + 1))
  have hδ : 0 < δ := by positivity
  have hev1 : ∀ᶠ N : ℕ in atTop, ∀ m ∈ B,
      |(N : ℝ) ^ (∑ i, m i) * unionSum p n (K N) m / N - hypertreeSum p n k m| ≤ δ := by
    refine (eventually_all_finset B).2 fun m hm => ?_
    filter_upwards [(Metric.tendsto_nhds.1 (hlim m hm)) δ hδ] with N hN
    rw [Real.dist_eq] at hN
    exact hN.le
  have hev2 : ∀ᶠ N : ℕ in atTop, c * H / N ≤ ε / 2 := by
    have := tendsto_const_div_atTop_nhds_zero_nat (c * H)
    filter_upwards [(Metric.tendsto_nhds.1 this) (ε / 2) (by positivity)] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    exact (le_abs_self _).trans hN.le
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with N h1 h2 hN A hA hAp hAN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hν : ∀ i, blockCount p A i ≤ N := fun i => (blockCount_le_card p A i).trans hAN
  rw [sum_piFinset_clusterWeight_eq (hK N hN) hA hAp, sum_div]
  set a : (Fin p → ℕ) → ℝ := fun m =>
    (∏ i, ((blockCount p A i).choose (m i) : ℝ)) / (N : ℝ) ^ (∑ i, m i)
  set u : (Fin p → ℕ) → ℝ := fun m => (N : ℝ) ^ (∑ i, m i) * unionSum p n (K N) m / N
  set b : (Fin p → ℕ) → ℝ := fun m => ∏ i, ((blockCount p A i : ℝ) / N) ^ m i / (m i).factorial
  have hsplit : ∀ m ∈ B, (∏ i, ((blockCount p A i).choose (m i) : ℝ)) * unionSum p n (K N) m / N -
      b m * hypertreeSum p n k m =
      a m * (u m - hypertreeSum p n k m) + (a m - b m) * hypertreeSum p n k m := by
    intro m _
    have hNs : (N : ℝ) ^ (∑ i, m i) ≠ 0 := pow_ne_zero _ hN0.ne'
    simp only [a, u]
    field_simp
    ring
  rw [← sum_sub_distrib, sum_congr rfl hsplit, sum_add_distrib]
  have hA1 : ∀ m ∈ B, |a m * (u m - hypertreeSum p n k m)| ≤ δ := by
    intro m hm
    obtain ⟨ha0, ha1⟩ := prod_choose_div_mem_Icc hN hν m
    rw [abs_mul, abs_of_nonneg ha0]
    exact (mul_le_of_le_one_left (abs_nonneg _) ha1).trans (h1 m hm)
  have hA2 : ∀ m ∈ B, |(a m - b m) * hypertreeSum p n k m| ≤ c / N * |hypertreeSum p n k m| := by
    intro m hm
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_prod_choose_sub_le hN hν hm) (abs_nonneg _)
  calc |∑ m ∈ B, a m * (u m - hypertreeSum p n k m) + ∑ m ∈ B, (a m - b m) * hypertreeSum p n k m|
      ≤ ∑ m ∈ B, |a m * (u m - hypertreeSum p n k m)| +
          ∑ m ∈ B, |(a m - b m) * hypertreeSum p n k m| :=
        (abs_add_le _ _).trans (add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _m ∈ B, δ + ∑ m ∈ B, c / N * |hypertreeSum p n k m| :=
        add_le_add (sum_le_sum hA1) (sum_le_sum hA2)
    _ = B.card * δ + c * H / N := by
        rw [sum_const, nsmul_eq_mul, ← mul_sum]
        ring
    _ ≤ ε / 2 + ε / 2 := by
        refine add_le_add ?_ h2
        have hB : (B.card : ℝ) * δ = ε / 2 * (B.card / (B.card + 1)) := by
          simp only [δ]
          field_simp
        rw [hB]
        exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
    _ = ε := by ring

end PropFiveFortyFive

end MultipoleBKT

end
