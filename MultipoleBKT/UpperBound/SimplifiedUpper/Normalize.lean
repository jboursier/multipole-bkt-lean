/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.Activity
public import MultipoleBKT.UpperBound.AbsoluteUpper.Uniform
public import MultipoleBKT.UpperBound.AbsoluteUpper.Bounded
public import MultipoleBKT.UpperBound.BoundedUpper.Integration

/-!
# The normalizations of Lemma 5.37

The paper: proof of Lemma 5.37
and Proposition 5.18 (eq. (5.65)):

* `blockCmp_uniform`: `𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)` for `1 ≤ |S| ≤ p(β)`, with `C` depending on
  `χ`, `p₀`, `β`, `M`, `L` but **not on `ε₀`** (from the two-sided bounds of `𝖬^{+,Z}`
  (`plusPartitionFunction_two_sided`, eq. (5.65)) and of `𝖬^0` (Proposition 4.23 for `𝖬^0`,
  `zeroPartitionFunction_two_sided`), and `𝖬^0(S) = 1` for `|S| = 1`);
* `lintegral_majSum`: the expectation of `majSum` under `μ_{β,λ,ε₀}^{⊗ V_X}` is
  `(N C_{β,λ,ε₀})^{-|V_X|} ∑_{n ≤ |X|} (1/n!) ∑ ∑ ∑ J_{large,C₀}` (the density of
  `μ_{β,λ,ε₀}` is `e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄} / (N C_{β,λ,ε₀})` on `Λ²`).
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Hierarchical Multipole SetPartition AbsoluteLower Parity BoundedUpper AbsoluteUpper

/-! ### The block comparison, uniformly in `ε₀` -/

section Comparison

variable {χ : ℂ → ℝ} {β : ℝ}

/-- The statement of the block comparison for blocks of `k` labels and the constant `C`. -/
def BlockCmp (χ : ℂ → ℝ) (p₀ : ℕ) (β M L : ℝ) (k : ℕ) (C : ℝ) : Prop :=
  ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (3 : ℝ) ^ pBeta p₀ β ≤ M →
    ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
    ∀ S : Finset ℕ, S.card = k → 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
      0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
      zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
        C * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S

/-- The block comparison for blocks of `k` labels, `1 ≤ k ≤ p(β)`. -/
theorem blockCmp_card (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ) {M : ℝ}
    (hM : 20 < M) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k ≤ pBeta p₀ β) :
    ∃ C : ℝ, 1 ≤ C ∧ BlockCmp χ p₀ β M L k C := by
  have hkp' := TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp
  obtain ⟨Cp, hCp, hplus⟩ := plusPartitionFunction_two_sided hχ hβ hk1 hkp' (by linarith) L
  rcases Nat.lt_or_ge k 2 with hk | hk2
  · -- `k = 1`: `𝖬^0(S) = 1`
    have hk1' : k = 1 := by omega
    subst hk1'
    refine ⟨max Cp 1, le_max_right _ _, fun ε₀ hε₀ hε₁ => ?_⟩
    obtain ⟨l, hl, h⟩ := hplus ε₀ hε₀ hε₁
    refine ⟨l, hl, fun lam hlam hlt => ?_⟩
    obtain ⟨N₀, hN₀⟩ := h p₀ lam hlam hlt
    refine ⟨max N₀ 1, fun N hN hMp V Z hVZ S hS => ?_⟩
    have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    have h1 := (hN₀ N ((le_max_left _ _).trans hN) hMp V Z hVZ S hS).1
    simp only [Nat.sub_self, mul_zero, pow_zero, mul_one] at h1
    have hz := zeroPartitionFunction_singleton (p₀ := p₀) (β := β) (M := M) hχ hlam hε₀ hN1 hS
    have hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
      lt_of_lt_of_le (by positivity) h1
    refine ⟨hpos, by rw [hz]; norm_num, ?_⟩
    rw [hz]
    calc (1 : ℝ) = Cp * (1 / Cp) := by field_simp
      _ ≤ Cp * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_left h1 hCp.le
      _ ≤ max Cp 1 * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le
  · -- `k ≥ 2`: the two-sided bounds
    obtain ⟨C0, hC0, hzero⟩ := BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ hk2 hkp' hM
    refine ⟨max (C0 * Cp) 1, le_max_right _ _, fun ε₀ hε₀ hε₁ => ?_⟩
    obtain ⟨l₁, hl₁, h₁⟩ := hplus ε₀ hε₀ hε₁
    obtain ⟨l₂, hl₂, -, h₂⟩ := hzero ε₀ hε₀ hε₁
    refine ⟨min l₁ l₂, lt_min hl₁ hl₂, fun lam hlam hlt => ?_⟩
    obtain ⟨N₁, hN₁⟩ := h₁ p₀ lam hlam (hlt.trans_le (min_le_left _ _))
    obtain ⟨N₂, hN₂⟩ := h₂ p₀ lam hlam (hlt.trans_le (min_le_right _ _))
    refine ⟨max (max N₁ N₂) 1, fun N hN hMp V Z hVZ S hS => ?_⟩
    have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    obtain ⟨hp1, -⟩ := hN₁ N ((le_max_left _ _).trans ((le_max_left _ _).trans hN)) hMp V Z hVZ S hS
    obtain ⟨hz1, hz2⟩ := hN₂ N ((le_max_right _ _).trans ((le_max_left _ _).trans hN)) S hS
    set a : ℝ := lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) with ha
    have ha0 : 0 < a := by positivity
    have e1 : lam ^ (2 * (k - 1)) / (Cp * (N : ℝ) ^ (k - 1)) = a / Cp := by
      rw [ha]
      field_simp
    have e2 : lam ^ (2 * (k - 1)) / (C0 * (N : ℝ) ^ (k - 1)) = a / C0 := by
      rw [ha]
      field_simp
    have e3 : C0 * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) = C0 * a := by
      rw [ha]
      ring
    rw [e1] at hp1
    rw [e2] at hz1
    rw [e3] at hz2
    have hpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
      lt_of_lt_of_le (by positivity) hp1
    refine ⟨hpos, lt_of_lt_of_le (by positivity) hz1, ?_⟩
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤ C0 * a := hz2
      _ = C0 * Cp * (a / Cp) := by field_simp
      _ ≤ C0 * Cp * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_left hp1 (by positivity)
      _ ≤ max (C0 * Cp) 1 * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le

/-- **The block comparison, uniformly in `ε₀`**: `𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)` for
`1 ≤ |S| ≤ p(β)`, `λ` small and `N` large, with `C` independent of `ε₀`. -/
theorem blockCmp_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    {M : ℝ} (hM : 20 < M) :
    ∃ Cb : ℝ, 1 ≤ Cb ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      badPointsOn p₀ β lam M ε₀ V Z = V → ∀ S : Finset ℕ, 1 ≤ S.card → S.card ≤ pBeta p₀ β →
      0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
        0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
          Cb * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
  set p := pBeta p₀ β with hp
  have h : ∀ k : ℕ, ∃ C : ℝ, 1 ≤ C ∧ (1 ≤ k → k ≤ p → BlockCmp χ p₀ β M L k C) := by
    intro k
    by_cases hk : 1 ≤ k ∧ k ≤ p
    · obtain ⟨C, hC, hcmp⟩ := blockCmp_card hχ hβ hp₀ L hM hk.1 hk.2
      exact ⟨C, hC, fun _ _ => hcmp⟩
    · exact ⟨1, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose C hC1 hCQ using h
  set Cb := ∑ k ∈ range (p + 1), C k with hCb
  have hCk : ∀ k ≤ p, C k ≤ Cb := fun k hk =>
    single_le_sum (fun j _ => zero_le_one.trans (hC1 j)) (mem_range.2 (by omega))
  refine ⟨Cb, (hC1 0).trans (hCk 0 (Nat.zero_le _)), fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lam₀, hlam₀, hall⟩ := exists_lam_N_forall_le (P := fun k lam N => 1 ≤ k → k ≤ p →
    (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      badPointsOn p₀ β lam M ε₀ V Z = V → ∀ S : Finset ℕ, S.card = k →
      0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
        0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
          C k * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S) p fun k hk => by
    by_cases hk1 : 1 ≤ k
    · obtain ⟨l, hl, h'⟩ := hCQ k hk1 hk ε₀ hε₀ hε₁
      refine ⟨l, hl, fun lam hlam hlt => ?_⟩
      obtain ⟨N₀, hN₀⟩ := h' lam hlam hlt
      exact ⟨N₀, fun N hN _ _ => hN₀ N hN⟩
    · exact exists_lam_N_of_forall fun lam N h1 => absurd h1 hk1
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hall lam hlam hlt
  refine ⟨N₀, fun N hN hMp V Z hVZ S hS1 hSp => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN₀ N hN S.card hSp hS1 hSp hMp V Z hVZ S rfl
  exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right (hCk _ hSp) h1.le)⟩

end Comparison

/-! ### The integrands of `J_{large,C₀}` -/

section Integrands

open scoped Classical

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ C₀ : ℝ}

theorem jLargeIntegrand_eq (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) :
    jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb c =
      treeProd M lam ε₀ (truncationScale p₀ β lam) Xs Ta Tb c *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
        ((∏ i ∈ X.biUnion id,
          (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
          ∏ i ∈ X.biUnion id,
            SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)) := by
  unfold jLargeIntegrand treeProd
  rw [prod_mul_distrib]

theorem jLargeIntegrand_nonneg (hlam : 0 < lam) (hε₀ : 0 < ε₀) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (c : ℕ → ℂ × ℂ) : 0 ≤ jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb c := by
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  rw [jLargeIntegrand_eq]
  refine mul_nonneg (mul_nonneg (treeProd_nonneg _ _ _ _ _ _ _ _)
    (prod_nonneg fun S _ => by split_ifs <;> norm_num)) (mul_nonneg ?_ ?_)
  · exact prod_nonneg fun i _ => Real.rpow_nonneg (div_nonneg (by positivity) (norm_nonneg _)) _
  · exact prod_nonneg fun i _ => SmallIntegral.cutDens_nonneg _ _

theorem measurable_radFactor (X : Finset (Finset ℕ)) (a b : ℝ) :
    Measurable fun c : ℕ → ℂ × ℂ => ∏ i ∈ X.biUnion id, (a / ‖(c i).1 - (c i).2‖) ^ b :=
  Finset.measurable_prod _ fun i _ => (measurable_const.div
    ((measurable_pi_apply i).fst.sub (measurable_pi_apply i).snd).norm).pow_const b

theorem measurable_jLargeIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (X : Finset (Finset ℕ))
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) : Measurable (jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb) := by
  have h : jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb = fun c =>
      treeProd M lam ε₀ (truncationScale p₀ β lam) Xs Ta Tb c *
        (∏ S ∈ X, if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) *
        ((∏ i ∈ X.biUnion id,
          (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
          ∏ i ∈ X.biUnion id,
            SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i)) :=
    funext fun c => jLargeIntegrand_eq X Xs Ta Tb c
  rw [h]
  exact ((measurable_treeProd _ _ _ _ Xs Ta Tb).mul (measurable_prod_connOn_indicator M lam X)).mul
    ((measurable_radFactor X _ _).mul (Finset.measurable_prod _ fun i _ =>
      (SmallIntegral.measurable_cutDens hχ hlam β _).comp (measurable_pi_apply i)))

theorem measurable_majSum (X : Finset (Finset ℕ)) (R : ℝ) :
    Measurable fun c => majSum M lam ε₀ R C₀ X c := by
  unfold majSum
  exact Finset.measurable_sum _ fun n _ => (Finset.measurable_sum _ fun Xs _ =>
    Finset.measurable_sum _ fun Ta _ => Finset.measurable_sum _ fun Tb _ =>
      ((measurable_treeProd _ _ _ _ Xs Ta Tb).mul (measurable_prod_connOn_indicator M lam X)).mul
        (measurable_radFactor X _ _)).const_mul _

/-- `majSum ∏_{V_X} e^{β g_λ} 𝟙_{r ≤ ε₀ R̄} = ∑_{n ≤ |X|} (1/n!) ∑ ∑ ∑ J_{large}`-integrand. -/
theorem majSum_mul_dens (X : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    majSum M lam ε₀ (truncationScale p₀ β lam) C₀ X c *
        ∏ i ∈ X.biUnion id, SmallIntegral.cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (c i) =
      ∑ n ∈ range (X.card + 1), 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
            jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb c := by
  unfold majSum
  rw [sum_mul]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, sum_mul]
  congr 1
  refine sum_congr rfl fun Xs _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun Ta _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun Tb _ => ?_
  rw [jLargeIntegrand_eq]
  ring

end Integrands

/-! ### The expectation of `majSum` -/

section Expectation

open scoped Classical

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ C₀ : ℝ}

/-- The density of `μ_{β,λ,ε₀}` without its normalization is `cutDens`. -/
theorem exp_mul_indicator_eq_cutDens (h : ℝ) (e : ℂ × ℂ) :
    Real.exp (β * smearedKernel χ lam (e.1 - e.2)) *
        (Metric.closedBall (0 : ℂ) h).indicator 1 (e.1 - e.2) =
      SmallIntegral.cutDens χ β lam h e := by
  unfold SmallIntegral.cutDens Limits.pairDensity
  congr 1
  by_cases he : ‖e.1 - e.2‖ ≤ h
  · rw [Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right]),
      Set.indicator_of_mem (Set.mem_Iic.2 he), Pi.one_apply, Pi.one_apply]
  · rw [Set.indicator_of_notMem (by rwa [Metric.mem_closedBall, dist_zero_right]),
      Set.indicator_of_notMem (by rwa [Set.mem_Iic])]

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

/-- **The expectation of `majSum`** under `μ_{β,λ,ε₀}^{⊗ V_X}`, in `[0, ∞]`. -/
theorem lintegral_majSum (X : Finset (Finset ℕ)) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ y, ENNReal.ofReal (K * majSum M lam ε₀ (truncationScale p₀ β lam) C₀ X
        (extendConfig (X.biUnion id) y))
        ∂Measure.pi (fun _ : X.biUnion id => cutoffDipoleMeasure χ N p₀ β lam ε₀) =
      ENNReal.ofReal (((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹ ^
          (X.biUnion id).card) *
        (ENNReal.ofReal K * ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
          ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
            ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
              jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb) := by
  set W := X.biUnion id with hW
  set R := truncationScale p₀ β lam with hR
  have hR0 : 0 < R := Appendix.truncationScale_pos hlam
  have hmeas : Measurable fun y : W → ℂ × ℂ =>
      K * majSum M lam ε₀ R C₀ X (extendConfig W y) :=
    ((measurable_majSum X R).comp (measurable_extendConfig W)).const_mul K
  rw [lintegral_pi_cutoff_eq (p₀ := p₀) (β := β) hχ hlam hε₀ hN W hmeas]
  congr 1
  -- the integrand
  have hjL : ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
      (Tb : Finset (ℕ × ℕ)), Measurable fun y : W → ℂ × ℂ =>
        ENNReal.ofReal (jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb (extendConfig W y)) :=
    fun n Xs Ta Tb => ENNReal.measurable_ofReal.comp
      ((measurable_jLargeIntegrand hχ hlam X Xs Ta Tb).comp (measurable_extendConfig W))
  have hpt : ∀ y : W → ℂ × ℂ, ENNReal.ofReal (K * majSum M lam ε₀ R C₀ X (extendConfig W y) *
      ∏ i : W, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
        (Metric.closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((y i).1 - (y i).2))) =
      ENNReal.ofReal K * ∑ n ∈ range (X.card + 1), ((n.factorial : ℝ≥0∞))⁻¹ *
        ∑ Xs ∈ tuplesD X n, ∑ Ta ∈ Fintype.piFinset (fun l => relTreePairs (Xs l)),
          ∑ Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs)),
            ENNReal.ofReal (jLargeIntegrand χ p₀ β lam M ε₀ C₀ X Xs Ta Tb (extendConfig W y)) := by
    intro y
    have hdens : ∏ i : W, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
        (Metric.closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((y i).1 - (y i).2)) =
        ∏ i ∈ W, SmallIntegral.cutDens χ β lam (ε₀ * R) (extendConfig W y i) := by
      rw [← Finset.prod_coe_sort W]
      refine prod_congr rfl fun i _ => ?_
      have hi : extendConfig W y i = y i := by simp [extendConfig]
      rw [hi, exp_mul_indicator_eq_cutDens]
    rw [hdens, mul_assoc, majSum_mul_dens, ENNReal.ofReal_mul hK]
    congr 1
    rw [ENNReal.ofReal_sum_of_nonneg fun n _ => mul_nonneg (by positivity) (sum_nonneg fun _ _ =>
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => jLargeIntegrand_nonneg hlam hε₀ _ _ _ _ _)]
    refine sum_congr rfl fun n _ => ?_
    rw [ENNReal.ofReal_mul (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_natCast]
    congr 1
    rw [ENNReal.ofReal_sum_of_nonneg fun Xs _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      jLargeIntegrand_nonneg hlam hε₀ _ _ _ _ _]
    refine sum_congr rfl fun Xs _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun Ta _ => sum_nonneg fun _ _ =>
      jLargeIntegrand_nonneg hlam hε₀ _ _ _ _ _]
    refine sum_congr rfl fun Ta _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun Tb _ => jLargeIntegrand_nonneg hlam hε₀ _ _ _ _ _]
  rw [lintegral_congr fun y => hpt y]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  rw [lintegral_finsetSum _ fun n _ => (Finset.measurable_sum _ fun Xs _ =>
    Finset.measurable_sum _ fun Ta _ => Finset.measurable_sum _ fun Tb _ =>
      hjL n Xs Ta Tb).const_mul _]
  refine sum_congr rfl fun n _ => ?_
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun Xs _ =>
    Finset.measurable_sum _ fun Ta _ => Finset.measurable_sum _ fun Tb _ => hjL n Xs Ta Tb)]
  congr 1
  rw [lintegral_finsetSum _ fun Xs _ => Finset.measurable_sum _ fun Ta _ =>
    Finset.measurable_sum _ fun Tb _ => hjL n Xs Ta Tb]
  refine sum_congr rfl fun Xs _ => ?_
  rw [lintegral_finsetSum _ fun Ta _ => Finset.measurable_sum _ fun Tb _ => hjL n Xs Ta Tb]
  refine sum_congr rfl fun Ta _ => ?_
  rw [lintegral_finsetSum _ fun Tb _ => hjL n Xs Ta Tb]
  rfl

end Expectation

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
