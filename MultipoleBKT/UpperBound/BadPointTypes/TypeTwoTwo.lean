/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.Defs
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Bound
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoCount.Normalization
public import MultipoleBKT.UpperBound.BadPointTypes.Normalization

/-!
# Lemma 5.42: explicit equal-size partition enumeration

The paper: Lemma 5.42.
Handle the empty family and nondivisible cardinalities first. Enumerate the
partitions into `n/k` blocks of size `k`, integrate each block, and apply the
factorial estimate to the exact quotient `n! / ((k!)^(n/k) (n/k)!)`.
Normalize the resulting powers using the dipole normalization lower bound.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset TheoremTwo MultipoleIntegral Filter
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ} {n : ℕ}

/-! ### The weight of one dipole -/

/-- `𝟙_{Λ²}(x, y) e^{β g_λ(x - y)}`, `Λ = box Nₐ`. -/
noncomputable def boxDipoleWeight (χ : ℂ → ℝ) (β lam : ℝ) (Nₐ : ℕ) (p : ℂ × ℂ) : ℝ≥0∞ :=
  (box Nₐ ×ˢ box Nₐ).indicator
    (fun p : ℂ × ℂ => ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (p.1 - p.2)))) p

theorem measurable_boxDipoleWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (Nₐ : ℕ) :
    Measurable (boxDipoleWeight χ β lam Nₐ) :=
  Measurable.indicator (ENNReal.measurable_ofReal.comp
    (continuous_exp_smearedKernel_sub hχ hlam β).measurable) (measurableSet_box_prod Nₐ)

/-- `∏_i 𝟙_{Λ²}(y_i) e^{β g_λ(y_i)} = 𝟙_{(Λ²)^ι}(y) ∏_i e^{β g_λ(y_i)}`. -/
theorem prod_boxDipoleWeight {ι : Type*} [Fintype ι] (χ : ℂ → ℝ) (β lam : ℝ) (Nₐ : ℕ)
    (y : ι → ℂ × ℂ) :
    ∏ i, boxDipoleWeight χ β lam Nₐ (y i) =
      (Set.univ.pi fun _ : ι => box Nₐ ×ˢ box Nₐ).indicator
        (fun y => ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2))))
        y := by
  by_cases hy : y ∈ Set.univ.pi fun _ : ι => box Nₐ ×ˢ box Nₐ
  · rw [Set.indicator_of_mem hy]
    refine prod_congr rfl fun i _ => ?_
    unfold boxDipoleWeight
    rw [Set.indicator_of_mem (Set.mem_univ_pi.1 hy i)]
  · rw [Set.indicator_of_notMem hy]
    obtain ⟨i, hi⟩ : ∃ i, y i ∉ box Nₐ ×ˢ box Nₐ :=
      not_forall.1 fun h => hy (Set.mem_univ_pi.2 h)
    refine prod_eq_zero (mem_univ i) ?_
    unfold boxDipoleWeight
    rw [Set.indicator_of_notMem hi]

/-- The block weight with `boxDipoleWeight` is the integrand `connectedWeight` of Lemma A.3. -/
theorem blockWeight_boxDipoleWeight {ι : Type*} [Fintype ι] (Nₐ : ℕ) (y : ι → ℂ × ℂ) :
    blockWeight M lam (boxDipoleWeight χ β lam Nₐ) y = connectedWeight χ Nₐ β lam M y := by
  classical
  unfold blockWeight connectedWeight
  rw [prod_boxDipoleWeight]
  by_cases hy : y ∈ Set.univ.pi fun _ : ι => box Nₐ ×ˢ box Nₐ
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    congr 2
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

/-- **One multipole** of `|T| = k` dipoles, `2 - 2/k - β < -2`:
`∫_{(Λ²)^T} 𝟙_{connected} ∏ e^{β g_λ} ≤ C N λ^{(4-β)k-2}`, `C = upperConst χ β M k`. -/
theorem lintegral_blockWeight_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hlam : 0 < lam) (Nₐ : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hk : 2 - 2 / (Fintype.card ι : ℝ) - β < -2) :
    ∫⁻ y : ι → ℂ × ℂ, blockWeight M lam (boxDipoleWeight χ β lam Nₐ) y ≤
      ENNReal.ofReal (upperConst χ β M (Fintype.card ι) * Nₐ *
        lam ^ ((4 - β) * Fintype.card ι - 2)) := by
  simp_rw [blockWeight_boxDipoleWeight]
  exact lintegral_connectedWeight_le hχ hβ hM hk hlam Nₐ

/-! ### The multipoles of a configuration with `I^{2,2,k}_bad = [n]` -/

/-- On `{I^{2,2,k}_bad = [n]}` every multipole, computed on all labels, has `k` elements. -/
theorem classes_of_typeTwoTwoBad_eq_univ {Nₐ k p₀ : ℕ} {ε₀ : ℝ} {d : Fin n → ℂ × ℂ}
    (h : typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = Finset.univ) (i : Fin n) :
    (multipoleClassOn M lam d Finset.univ i).card = k := by
  have h1 := badPointsTypeOne_eq_empty_of_typeTwoTwoBad h
  have hi : i ∈ typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d := h ▸ mem_univ i
  unfold typeTwoTwoBad at hi
  rw [h1, sdiff_empty] at hi
  dsimp only at hi
  split_ifs at hi
  · exact (mem_filter.1 hi).2
  · exact absurd hi (Finset.notMem_empty i)

open scoped Classical in
/-- The integrand of `Z^{(2,2,k)}` (on the box) is at most `classWeight (· = k)`. -/
theorem indicator_le_classWeight (k p₀ : ℕ) (ε₀ : ℝ) (Nₐ : ℕ) (d : Fin n → ℂ × ℂ) :
    (boxPi Nₐ n).indicator (fun d =>
      (if typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = Finset.univ ∧ StablePairs d then 1 else 0) *
        ENNReal.ofReal (dipoleWeight χ β lam d)) d ≤
      classWeight M lam (· = k) (boxDipoleWeight χ β lam Nₐ) Finset.univ d := by
  by_cases hd : d ∈ boxPi Nₐ n
  · rw [Set.indicator_of_mem hd]
    split_ifs with h
    · rw [one_mul]
      unfold classWeight
      rw [ite_eq_left fun i _ => classes_of_typeTwoTwoBad_eq_univ h.1 i, one_mul,
        prod_boxDipoleWeight, Set.indicator_of_mem hd, dipoleWeight,
        ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
    · rw [zero_mul]
      exact zero_le
  · rw [Set.indicator_of_notMem hd]
    exact zero_le

/-- The empty family contributes one, as in Lemma 5.42, the paper. -/
theorem typeTwoTwoPartitionFunction_empty (k p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ : ℕ) :
    typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ Nₐ 0 = 1 := by
  simp [typeTwoTwoPartitionFunction, typeTwoTwoBad, StablePairs, dipoleWeight,
    Finset.eq_empty_of_isEmpty]
  rw [boxPi, MeasureTheory.volume_pi_pi]
  simp

/-- The nondivisible case contributes zero, before any factorial is cancelled. -/
theorem typeTwoTwoPartitionFunction_eq_zero_of_not_dvd {k p₀ : ℕ} {ε₀ : ℝ} (Nₐ : ℕ)
    (hdiv : ¬ k ∣ n) : typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ Nₐ n = 0 := by
  classical
  have hevent : ∀ d : Fin n → ℂ × ℂ,
      typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d ≠ univ := by
    intro d hd
    have hπ := componentPartition_mem (M := M) (lam := lam) univ d
    have hhom : componentPartition M lam univ d ∈
        RouteTypeTwoCount.homogeneous univ k := by
      refine RouteTypeTwoCount.mem_homogeneous.2 ⟨hπ, ?_⟩
      intro T hT
      obtain ⟨i, _, rfl⟩ := mem_image.1 hT
      exact classes_of_typeTwoTwoBad_eq_univ hd i
    rw [RouteTypeTwoCount.homogeneous_eq_empty_of_not_dvd univ k (by simpa using hdiv)] at hhom
    exact notMem_empty _ hhom
  unfold typeTwoTwoPartitionFunction
  have hz : ∀ d : Fin n → ℂ × ℂ,
      (if typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = univ ∧ StablePairs d then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (dipoleWeight χ β lam d) = 0 := by
    intro d
    rw [ite_eq_right (fun h => hevent d h.1), zero_mul]
  simp_rw [hz, lintegral_zero]

/-- One block contributes its integrated `2k`-pole factor. The number of
partitions is exactly `n! / ((k!)^q q!)`, with `n = kq`. -/
theorem typeTwoTwoPartitionFunction_le_homogeneous (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hM : 0 ≤ M) (hlam : 0 < lam) {k q : ℕ} (hk1 : 1 ≤ k)
    (hk : 2 - 2 / (k : ℝ) - β < -2) (hn : k * q = n) (p₀ : ℕ) (ε₀ : ℝ) (Nₐ : ℕ) :
    typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ Nₐ n ≤
      ENNReal.ofReal (n.factorial / (k.factorial ^ q * q.factorial) *
        (upperConst χ β M k * Nₐ * lam ^ ((4 - β) * k - 2)) ^ q) := by
  classical
  unfold typeTwoTwoPartitionFunction
  rw [← lintegral_indicator (measurableSet_pi_box_prod Nₐ)]
  refine (lintegral_mono fun d => indicator_le_classWeight k p₀ ε₀ Nₐ d).trans ?_
  apply lintegral_classWeight_homogeneous_le (measurable_boxDipoleWeight hχ hlam β Nₐ) hk1 hn
    (by have := upperConst_nonneg χ β M k; positivity)
  intro T hT
  have hTk : Fintype.card T = k := by rw [Fintype.card_coe, hT]
  have : Nonempty T := Fintype.card_pos_iff.1 (by omega)
  have h := lintegral_blockWeight_le (ι := T) hχ hβ hM hlam Nₐ (by rw [hTk]; exact hk)
  rwa [hTk] at h

/-- **Lemma 5.42, explicit form** from the equal-size partition count.
The empty and nondivisible cases precede the factorial estimate. -/
theorem typeTwoTwoPartitionFunction_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hlam : 0 < lam) {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 - 2 / (k : ℝ) - β < -2) (p₀ : ℕ) (ε₀ : ℝ)
    {Nₐ : ℕ} (hN : 1 ≤ Nₐ) (n : ℕ) :
    typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ Nₐ n ≤
      ENNReal.ofReal ((Real.exp 1 * max 1 (upperConst χ β M k + 1) * n * lam ^ (2 - β)) ^ n *
        (Nₐ * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [typeTwoTwoPartitionFunction_empty]
    simp
  by_cases hdiv : k ∣ n
  swap
  · rw [typeTwoTwoPartitionFunction_eq_zero_of_not_dvd Nₐ hdiv]
    exact zero_le
  obtain ⟨q, hq⟩ := hdiv
  have hsize : k * q = n := hq.symm
  set U := upperConst χ β M k + 1
  have hU : 0 < U := by have := upperConst_nonneg χ β M k; positivity
  have hNr : (0 : ℝ) < Nₐ := by exact_mod_cast hN
  refine (typeTwoTwoPartitionFunction_le_homogeneous hχ hβ hM hlam hk1 hk hsize p₀ ε₀ Nₐ).trans
    (ENNReal.ofReal_le_ofReal (le_trans ?_
      (RouteTypeTwoCount.homogeneous_multipole_bound hU hNr hlam hn hk1 hsize)))
  have hle : upperConst χ β M k ≤ U := by dsimp [U]; linarith
  have hnonneg := upperConst_nonneg χ β M k
  gcongr

/-- `k ≤ p(β)` (with `k ≥ 1`, `β > 2`) gives the integrability exponent `2 - 2/k - β < -2`. -/
theorem two_sub_two_div_sub_lt_of_le_pBeta {p₀ k : ℕ} (hk1 : 1 ≤ k)
    (hkp : k ≤ pBeta p₀ β) : 2 - 2 / (k : ℝ) - β < -2 := by
  unfold pBeta at hkp
  split_ifs at hkp with h4
  · have hne : pStar β ≠ ⊤ := by
      intro h
      rw [h, ENat.toNat_top] at hkp
      omega
    have hkp' : (k : ℕ∞) ≤ pStar β := by
      rw [← ENat.natCast_toNat hne]
      exact_mod_cast hkp
    exact two_sub_two_div_sub_lt hk1 hkp'
  · have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have : 0 < 2 / (k : ℝ) := by positivity
    linarith

/-- **Lemma 5.42**, in the paper's normalized form: for
`β > 2`, `p₀ ≥ 1`, `k ∈ {1, …, p(β)}` and `M ≥ 0` there is `C > 0` (depending on `χ, β, M, k`)
such that for every `ε₀ ∈ (0, 1]`, for `λ` small enough and `N` large enough, for every `n`,
`(N/n)ⁿ Z^{(2,2,k)}_{bad,n} / (N C_{β,λ,ε₀})ⁿ ≤ Cⁿ (N λ^{2(k-1)} / n)^{n/k}`,
written multiplicatively (`Z ≤ (N C_{β,λ,ε₀})ⁿ (n/N)ⁿ Cⁿ (N λ^{2(k-1)}/n)^{n/k}`), with
`C_{β,λ,ε₀} = truncatedDipoleNormalization χ N β λ (ε₀ R̄_{β,λ})`. "λ small, N large" is used only
for the lower bound (4.12) on `C_{β,λ,ε₀}` (the paper omits this qualifier). -/
theorem lemma_5_42 (hχ : IsMollifier χ) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (hβ : 2 < β) {k : ℕ}
    (hk1 : 1 ≤ k) (hkp : k ≤ pBeta p₀ β) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ ≤ 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        typeTwoTwoPartitionFunction χ k p₀ β lam M ε₀ N n ≤
          ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
              (ε₀ * truncationScale p₀ β lam)) ^ n * ((n : ℝ) / N) ^ n *
            (C ^ n * (N * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k))) := by
  have hZ := dipoleConstant_pos hχ hβ
  have hk := two_sub_two_div_sub_lt_of_le_pBeta hk1 hkp
  set K := Real.exp 1 * max 1 (upperConst χ β M k + 1) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K / (1 / 2 * dipoleConstant χ β), by positivity, fun ε₀ hε₀ hε₀1 => ?_⟩
  obtain ⟨lam₀, hlam₀, hnorm⟩ := eventually_half_le_normalization hχ hβ hp₀ hε₀ hε₀1
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  filter_upwards [hnorm lam hlam hlt, eventually_ge_atTop 1] with N hN hN1 n
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc : 0 < 1 / 2 * dipoleConstant χ β * lam ^ (2 - β) := by positivity
  refine (typeTwoTwoPartitionFunction_le hχ (by linarith) hM hlam hk1 hk p₀ ε₀ hN1 n).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h := le_normalized_of_le (Z := (K * n * lam ^ (2 - β)) ^ n *
      (N * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)) (A := K * lam ^ (2 - β))
    (Y := (N * lam ^ (2 * (k - 1)) / n) ^ ((n : ℝ) / k)) (n := n)
    (le_of_eq (by ring)) hNr hc hN (by positivity) (by positivity)
  refine h.trans (le_of_eq ?_)
  congr 2
  rw [show K * lam ^ (2 - β) / (1 / 2 * dipoleConstant χ β * lam ^ (2 - β)) =
    K / (1 / 2 * dipoleConstant χ β) by field_simp]

end BadPointTypes

end MultipoleBKT

end
