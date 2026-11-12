/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.Basic
public import MultipoleBKT.Appendix.RadialIntegral
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Coordinates
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Weight
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Configuration
import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.LegacyConstant
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Lemma A.3: the upper bound on the multipole integral

See Lemma A.3, upper bound (A.5), proof (A.6) through (A.14), for the model `(v, ∞, 0, ∅)` with infinite cutoff:
`I^0_{mult,∞}(S) ≤ C N λ^{(2-β)|S|} λ^{2(|S|-1)}` for `1 ≤ |S| ≤ p*(β)`.

The connected integral follows the spanning-tree union bound, measurable
endpoint cells, the volume-preserving tree coordinate map, largest-radius
ordering, and the nested polar integral. The low, critical, and high radial
regimes justify its finite real coefficient. `RouteOrdered.Gamma` supplies
the finite-cutoff normalization through (A.2).

The coefficient `upperConst` is verified by a numerical
comparison in `RouteOrdered.LegacyConstant`. The parent-map union bound is also available.

* `parentMaps`, `connectedIndicator_le_sum`, `lintegral_positions_le`.
* `upperConst`, `lintegral_connectedWeight_le`: the bound
  `∫_{(Λ²)^ι} 𝟙_{𝓑} ∏ e^{β g_λ(x_i - y_i)} ≤ upperConst χ β M k · N λ^{(4-β)k-2}`;
* `lintegral_le_of_le_connected`, `setIntegral_le_of_le_connected`: the same bound for any
  integrand dominated by `K 𝟙_{𝓑} ∏ e^{β g_λ}` (internal helpers, shared by the models of (A.4));
* `multipolePartitionFunctionIntegrand_le`: the bond bound removes the interaction;
* `multipoleIntegral_le`: the upper bound of (A.5) for `I^0_{mult,∞}`.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {lam β M : ℝ}

namespace MultipoleIntegral

section Positions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- The (finite) set of parent maps with root `r`. -/
noncomputable def parentMaps (r : ι) : Finset (ι → ι) := univ.filter (IsParentMap r)

theorem card_parentMaps_le (r : ι) :
    (parentMaps r).card ≤ Fintype.card ι ^ Fintype.card ι := by
  classical
  refine (card_filter_le _ _).trans ?_
  rw [card_univ, Fintype.card_fun]

theorem mem_parentMaps {r : ι} {par : ι → ι} : par ∈ parentMaps r ↔ IsParentMap r par := by
  classical
  simp [parentMaps]

/-- The indicator of the connectedness of the linking graph of the dipoles `(y_i + r_i, y_i)`. -/
noncomputable def connectedIndicator (M lam : ℝ) (y r : ι → ℂ) : ℝ≥0∞ := by
  classical
  exact if (SimpleGraph.fromRel fun i j =>
    MultipoleLinked M lam (y i + r i, y i) (y j + r j, y j)).Connected then 1 else 0

/-- If the linking graph is connected, then for some parent map with root `r₀` every non-root
dipole is linked to its parent: `𝟙_{𝓑} ≤ ∑_{par} ∏_{c ≠ r₀} 𝟙_{linkSet}(y_c - y_{par c})`. -/
theorem connectedIndicator_le_sum (M lam : ℝ) (y r : ι → ℂ) (r₀ : ι) :
    connectedIndicator M lam y r ≤ ∑ par ∈ parentMaps r₀,
      ∏ c ∈ univ.erase r₀, (linkSet M lam (r c) (r (par c))).indicator (1 : ℂ → ℝ≥0∞) (y c - y (par c)) := by
  classical
  unfold connectedIndicator
  split_ifs with hG
  · obtain ⟨par, hpar, hadj⟩ := exists_parent_of_connected hG r₀
    refine le_trans (le_of_eq ?_) (single_le_sum (fun _ _ => zero_le)
      (mem_parentMaps.2 hpar))
    symm
    refine prod_eq_one fun c hc => ?_
    have hcr : c ≠ r₀ := (mem_erase.1 hc).1
    have h := hadj c hcr
    rw [SimpleGraph.fromRel_adj] at h
    have hmem : y c - y (par c) ∈ linkSet M lam (r c) (r (par c)) := by
      rcases h.2 with h' | h'
      · exact sub_mem_linkSet h'
      · exact sub_mem_linkSet (Multipole.multipoleLinked_comm.1 h')
    simp [hmem]
  · exact zero_le

/-- **The positions integral.** For fixed dipole vectors `r` and any root `r₀`,
`∫ 𝟙_Λ(y_{r₀}) 𝟙_{𝓑}(y, r) dy ≤ k^k N ∏_{c ≠ r₀} 4π M² max(|r_c|, λ)²`. -/
theorem lintegral_positions_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (N : ℕ) (r : ι → ℂ) (r₀ : ι) :
    ∫⁻ y : ι → ℂ, (box N).indicator (1 : ℂ → ℝ≥0∞) (y r₀) * connectedIndicator M lam y r ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) *
        ∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2) := by
  have h := lintegral_connected_positions_root_le hM hlam N r r₀
  convert h using 1
  · apply lintegral_congr
    intro y
    unfold connectedIndicator
    split_ifs <;> rfl
  · congr 1
    apply prod_congr
    · ext c
      simp
    · intro c _
      rfl

end Positions

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit constant of the upper bound:
`k^k (4π M²)^{k-1} (e^{β c_χ} ∫_ℂ max(|v|, 1)^{2-2/k-β} dv)^k`. -/
noncomputable def upperConst (χ : ℂ → ℝ) (β M : ℝ) (k : ℕ) : ℝ :=
  ((k ^ k : ℕ) : ℝ) * (4 * Real.pi * M ^ 2) ^ (k - 1) *
    (Real.exp (β * kernelConst χ) * ∫ v : ℂ, max ‖v‖ 1 ^ (2 - 2 / (k : ℝ) - β)) ^ k

theorem upperConst_nonneg (χ : ℂ → ℝ) (β M : ℝ) (k : ℕ) : 0 ≤ upperConst χ β M k := by
  have : 0 ≤ ∫ v : ℂ, max ‖v‖ 1 ^ (2 - 2 / (k : ℝ) - β) :=
    integral_nonneg fun v => Real.rpow_nonneg (le_max_of_le_right zero_le_one) _
  unfold upperConst
  positivity

/-- **The upper bound, core.** For `k = |ι| ≥ 1` with `2 - 2/k - β < -2` (i.e. `k ≤ p*(β)`),
`∫_{(Λ²)^ι} 𝟙_{𝓑} ∏_i e^{β g_λ(x_i - y_i)} ≤ C N λ^{(4-β)k-2}` with `C = upperConst χ β M k`,
for every `λ > 0` and every `N`. -/
theorem lintegral_connectedWeight_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    [Nonempty ι] (hk : 2 - 2 / (Fintype.card ι : ℝ) - β < -2) (hlam : 0 < lam) (N : ℕ) :
    ∫⁻ c : ι → ℂ × ℂ, connectedWeight χ N β lam M c ≤
      ENNReal.ofReal (upperConst χ β M (Fintype.card ι) * N *
        lam ^ ((4 - β) * Fintype.card ι - 2)) := by
  classical
  let k := Fintype.card ι
  have hk1 : 1 ≤ k := Fintype.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hβ2 : 2 < β := by
    have hdiv : 2 / (k : ℝ) ≤ 2 := (div_le_iff₀ hkpos).mpr (by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      linarith)
    linarith
  have hE : (4 - β) * k - 2 < 0 := by
    have he : (4 - β) * k - 2 = (2 - 2 / (k : ℝ) - β + 2) * k := by
      field_simp
      ring
    rw [he]
    exact mul_neg_of_neg_of_pos (by linarith) hkpos
  have hscale := orderedRadial_eq_unit_coefficient hβ2 hk1 hE hlam
  have hnum := internal_ordered_coefficient_infinite (Classical.choice ‹Nonempty ι›) hk
  have hfin : orderedRadial β 1 (Ioi 0) (k - 1) ≠ ⊤ := by
    by_cases hk2 : 2 ≤ k
    · exact orderedRadial_infinite_ne_top hβ2 hk2 hE (by norm_num)
    · have hkone : k = 1 := by omega
      rw [hkone]
      exact orderedRadial_singleton_ne_top hβ2 (by norm_num)
  rw [← ENNReal.ofReal_toReal hfin] at hnum
  have hcount : ((k ^ (k - 2) : ℕ) : ℝ≥0∞) * (k : ℝ≥0∞) ≤
      ((k ^ k : ℕ) : ℝ≥0∞) := by
    norm_cast
    rw [← pow_succ]
    gcongr
    omega
  have hbound := lintegral_connectedWeight_ordered_infinite_le (ι := ι) hχ hlam hβ hM N
  rw [hscale] at hbound
  let K : ℝ := ∫ z : ℂ, max ‖z‖ 1 ^ (2 - 2 / (k : ℝ) - β)
  have hK : 0 ≤ K := integral_nonneg fun z => by positivity
  calc
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (k - 1) *
        ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ k *
          (((k ^ (k - 2) : ℕ) : ℝ≥0∞) * (k : ℝ≥0∞)) *
            (ENNReal.ofReal (2 * Real.pi) ^ k *
              ENNReal.ofReal (orderedRadial β 1 (Ioi 0) (k - 1)).toReal) *
                ENNReal.ofReal (lam ^ ((4 - β) * k - 2)) := by
      convert hbound using 1
      ring
    _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ (k - 1) *
        ENNReal.ofReal (Real.exp (β * kernelConst χ)) ^ k * ((k ^ k : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal K ^ k * ENNReal.ofReal (lam ^ ((4 - β) * k - 2)) := by
      exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hcount) hnum) le_rfl
    _ = _ := by
      unfold upperConst
      simp (disch := positivity) only [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
        ENNReal.ofReal_natCast]
      dsimp only [K, k]
      ring

end Main

/-- `λ^{(4-β)k-2} = λ^{(2-β)k} λ^{2(k-1)}` for `λ > 0` and `k ≥ 1`. -/
theorem rpow_four_sub_mul_sub_two (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) :
    lam ^ ((4 - β) * k - 2) = lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  rw [← Real.rpow_natCast lam (2 * (k - 1)), ← Real.rpow_add hlam]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hk]
  push_cast
  ring

open scoped Classical in
/-- The bond bound removes the interaction: the integrand of `multipolePartitionFunction` is at
most `W^{k²} 𝟙_{𝓑_S}`, where `W = e^{β C}` bounds `e^{-β v_ij} 𝟙_{𝒜_ij}`. -/
theorem multipolePartitionFunctionIntegrand_le {S : Finset ℕ} {W : ℝ} (hW : 1 ≤ W)
    (hbond : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W) (c : S → ℂ × ℂ) :
    multipolePartitionFunctionIntegrand χ β lam M c ≤
      W ^ (S.card * S.card) *
        (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
          then 1 else 0) := by
  unfold multipolePartitionFunctionIntegrand
  have hP : ∏ i : S, ∏ j : S, (if i < j then stablePairWeight χ β lam (c i) (c j) else 1) ≤
      W ^ (S.card * S.card) := by
    have h := abs_prod_prod_le (fun i j : S =>
      if i < j then stablePairWeight χ β lam (c i) (c j) else 1) (W := W) (fun i j => by
        split_ifs
        · rw [abs_of_nonneg (stablePairWeight_nonneg χ β lam _ _)]
          exact hbond _ _
        · rw [abs_one]
          exact hW)
    rw [Fintype.card_coe] at h
    exact (le_abs_self _).trans h
  split_ifs
  · rw [one_mul, mul_one]
    exact hP
  · rw [zero_mul, mul_zero]

/-- `k ≤ p*(β)` (with `k ≥ 1`) gives the integrability exponent `2 - 2/k - β < -2`. -/
theorem two_sub_two_div_sub_lt {k : ℕ} (hk : 1 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    2 - 2 / (k : ℝ) - β < -2 := by
  have hkβ : (4 - β) * k - 2 < 0 := (Appendix.transitionBeta_lt_iff hk β).1
    ((Appendix.le_pStar_iff hk).1 hkp)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have : (4 - β) - 2 / (k : ℝ) < 0 := by
    have h2 : (4 - β) * k - 2 = ((4 - β) - 2 / k) * k := by field_simp
    rw [h2] at hkβ
    exact neg_of_mul_neg_left hkβ hk0.le
  linarith

open scoped Classical in
/-- **The upper bound for a general model, Lebesgue form** (the upper-bound half of the proof of
Lemma A.3, (A.6)–(A.14), after the interaction has been removed): if `F` satisfies
`F ≤ K 𝟙_{𝓑_S} ∏_i e^{β g_λ(x_i - y_i)}` on `(Λ²)^S`, `1 ≤ |S| = k ≤ p*(β)`, `K ≥ 0`, then
`∫_{(Λ²)^S} F ≤ K C N λ^{(4-β)k-2}` with `C = upperConst χ β M k`. Internal helper, used for each
model of (A.4). -/
theorem lintegral_le_of_le_connected (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (hlam : 0 < lam) (N : ℕ) {S : Finset ℕ}
    (hS : S.card = k) {F : (S → ℂ × ℂ) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ c ∈ Set.univ.pi (fun _ : S => box N ×ˢ box N), F c ≤ K *
      ((if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
          then 1 else 0) * ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) :
    ∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (F c) ≤
      ENNReal.ofReal (K * (upperConst χ β M k * N * lam ^ ((4 - β) * k - 2))) := by
  have hcard : Fintype.card S = k := by rw [Fintype.card_coe, hS]
  have hneS : Nonempty S := Fintype.card_pos_iff.1 (hcard ▸ hk)
  have hcore := lintegral_connectedWeight_le (ι := S) hχ (by linarith : 0 ≤ β) hM
    (by rw [hcard]; exact two_sub_two_div_sub_lt hk hkp) hlam N
  rw [hcard] at hcore
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  have hpt : ∀ c, P.indicator (fun c => ENNReal.ofReal (F c)) c ≤
      ENNReal.ofReal K * connectedWeight χ N β lam M c := by
    intro c
    unfold connectedWeight
    by_cases hc : c ∈ P
    · rw [Set.indicator_of_mem hc, Set.indicator_of_mem hc]
      refine (ENNReal.ofReal_le_ofReal (hF c hc)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul (by split_ifs <;> norm_num),
        ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
      congr 2
      split_ifs <;> simp
    · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem hc]
      exact zero_le
  rw [← lintegral_indicator (measurableSet_pi_box_prod N)]
  calc ∫⁻ c, P.indicator (fun c => ENNReal.ofReal (F c)) c
      ≤ ∫⁻ c, ENNReal.ofReal K * connectedWeight χ N β lam M c := lintegral_mono hpt
    _ = ENNReal.ofReal K * ∫⁻ c, connectedWeight χ N β lam M c :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K *
          ENNReal.ofReal (upperConst χ β M k * N * lam ^ ((4 - β) * k - 2)) := by
        gcongr
    _ = _ := (ENNReal.ofReal_mul hK).symm

open scoped Classical in
/-- **The upper bound for a general model**: if a measurable `F ≥ 0` satisfies
`F ≤ K 𝟙_{𝓑_S} ∏_i e^{β g_λ(x_i - y_i)}` on `(Λ²)^S`, `1 ≤ |S| = k ≤ p*(β)`, then
`∫_{(Λ²)^S} F ≤ K C N λ^{(2-β)k} λ^{2(k-1)}` with `C = upperConst χ β M k`. Internal helper. -/
theorem setIntegral_le_of_le_connected (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) (hlam : 0 < lam) (N : ℕ) {S : Finset ℕ}
    (hS : S.card = k) {F : (S → ℂ × ℂ) → ℝ} (hFm : Measurable F) (hF0 : ∀ c, 0 ≤ F c) {K : ℝ}
    (hK : 0 ≤ K)
    (hF : ∀ c ∈ Set.univ.pi (fun _ : S => box N ×ˢ box N), F c ≤ K *
      ((if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
          then 1 else 0) * ∏ i : S, Real.exp (β * smearedKernel χ lam ((c i).1 - (c i).2)))) :
    ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), F c ≤
      K * upperConst χ β M k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  have hlint := lintegral_le_of_le_connected hχ hβ hk hkp hM hlam N hS hK hF
  have hI : ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), F c =
      (∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (F c)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0)
      hFm.aestronglyMeasurable
  rw [hI]
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity [upperConst_nonneg χ β M k]) hlint).trans
    (le_of_eq ?_)
  rw [rpow_four_sub_mul_sub_two hlam hk]
  ring

end MultipoleIntegral

open MultipoleIntegral

/-- **Lemma A.3, upper bound** (eq. (A.5)), for the model
`(v, ∞, 0, ∅)` with cutoff `ε₀ = ∞` (A.4): for `1 ≤ k ≤ p*(β)` and `M ≥ 0` there is
`C > 0` depending on `χ, β, M, k` such that, for every `λ > 0`, every `N` and every `S` with
`|S| = k`, `I^0_{mult,∞}(S) ≤ C N λ^{(2-β)k} λ^{2(k-1)}`. -/
theorem multipoleIntegral_le (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : 1 ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, ∀ S : Finset ℕ, S.card = k →
      multipoleIntegral χ N β lam M S ≤
        C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  classical
  obtain ⟨Cb, hCb0, hCb⟩ := dipoleBond_le hχ
  set W : ℝ := Real.exp (β * Cb)
  have hW : 1 ≤ W := Real.one_le_exp (mul_nonneg (by linarith) hCb0)
  refine ⟨W ^ (k * k) * (upperConst χ β M k + 1),
    mul_pos (by positivity) (by linarith [upperConst_nonneg χ β M k]),
    fun lam hlam N S hS => ?_⟩
  have hbond : ∀ d e : ℂ × ℂ, stablePairWeight χ β lam d e ≤ W := fun d e =>
    hCb β (by linarith) lam hlam d e
  refine (setIntegral_le_of_le_connected hχ hβ hk hkp hM hlam N hS
    (measurable_multipoleIntegrand hχ hlam β M) multipoleIntegrand_nonneg
    (K := W ^ (k * k)) (by positivity) fun c _ => ?_).trans ?_
  · have h1 := multipolePartitionFunctionIntegrand_le (M := M) hW hbond c
    rw [hS] at h1
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (prod_nonneg fun i _ => (Real.exp_pos _).le)
  · have hU := upperConst_nonneg χ β M k
    have : 0 ≤ (N : ℝ) * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by positivity
    have hW0 : 0 ≤ W ^ (k * k) := by positivity
    calc W ^ (k * k) * upperConst χ β M k * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
        = W ^ (k * k) * upperConst χ β M k * (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
          ring
      _ ≤ W ^ (k * k) * (upperConst χ β M k + 1) *
            (N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by
          gcongr
          linarith
      _ = W ^ (k * k) * (upperConst χ β M k + 1) * N * lam ^ ((2 - β) * k) *
            lam ^ (2 * (k - 1)) := by ring

end MultipoleBKT

end
