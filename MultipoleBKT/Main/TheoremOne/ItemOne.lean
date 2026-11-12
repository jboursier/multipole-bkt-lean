/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.Inputs
public import MultipoleBKT.Main.TheoremOne.Relabel
public import MultipoleBKT.Main.TheoremOne.Coefficients
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.Cluster.Resummation
public import MultipoleBKT.Cluster.Tail
public import MultipoleBKT.Potential.DipoleConstant
public import MultipoleBKT.Frozen.Lemma546

/-!
# Theorem 1 from the gates: item (1)

Item (1) of Theorem 1, eq. (2.38) (the paper, eq. (5.166)):

  `log Z = 2N log N + N((2 - β) log λ + log 𝒵_β - 1)
    + ∑_{n ≥ 1} (1/n!) ∑_{V connected, 2 ≤ |Vᵢ| ≤ p} ∏ᵢ 𝖪^dip(Vᵢ) I(G(V)) + O(N δ)`.

The proof combines:
* the relabeling identity `Z = N! ∫_{σ_N = Id} e^{-βF}`
  (`MultipoleBKT.TheoremOne.partitionFunction_eq_factorial_mul`);
* Proposition 5.45 (a hypothesis, the frozen statement): `log ∫_{σ_N = Id} = log ∑_π Ẑ(π) + O(Nδ)`;
* Lemma 5.46 (`MultipoleBKT.lemma_5_46`):
  `∑_π Ẑ(π) = (N C_{β,λ})^N ∑_n (1/n!) ∑_{V disjoint} ∏ᵢ 𝖪^dip(Vᵢ)`;
* Lemma 4.7 (`MultipoleBKT.lemma_4_7_range`) with the absolute convergence from (4.41) and
  Lemma 4.53 (`MultipoleBKT.abs_cluster_le`);
* `C_{β,λ} → λ^{2-β} 𝒵_β` (`MultipoleBKT.tendsto_dipoleNormalization`) and Stirling, whose errors
  `o_λ(N)` are absorbed in `N δ_{β,λ}` for `N ≥ N₀(λ)`.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace MultipoleBKT

namespace TheoremOne

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}

/-- `log C_{β,λ} = (2 - β) log λ + log 𝒵_β + o(1)`: for `δ > 0`, eventually in `N` the error is
at most `δ` (eq. (2.32)). -/
theorem eventually_abs_log_dipoleNormalization_sub_le (hχ : IsMollifier χ) (hβ : 2 < β)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, |Real.log (dipoleNormalization χ N β lam) -
      ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β))| ≤ δ := by
  have hc₀ : 0 < lam ^ (2 - β) * dipoleConstant χ β :=
    mul_pos (Real.rpow_pos_of_pos hlam _) (dipoleConstant_pos hχ hβ)
  have hT := ((Real.continuousAt_log hc₀.ne').tendsto).comp
    (tendsto_dipoleNormalization hχ hβ hlam)
  have hL : Real.log (lam ^ (2 - β) * dipoleConstant χ β) =
      (2 - β) * Real.log lam + Real.log (dipoleConstant χ β) := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hlam _).ne' (dipoleConstant_pos hχ hβ).ne',
      Real.log_rpow hlam]
  rw [hL] at hT
  filter_upwards [(Metric.tendsto_nhds.mp hT) δ hδ] with N hN
  rw [Real.dist_eq] at hN
  exact hN.le

/-- `|log N! - (N log N - N)| ≤ N δ` for `N` large (Stirling, `δ > 0`). -/
theorem eventually_abs_log_factorial_sub_le {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, |Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)| ≤ N * δ := by
  filter_upwards [eventually_ge_atTop 1, TheoremTwo.eventually_log_le δ hδ 1] with N hN hlog
  have h1 := TheoremTwo.abs_log_factorial_sub_le hN
  have h2 : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
    Real.log_le_log (by exact_mod_cast hN) (by linarith)
  linarith

open scoped Classical in
/-- **Item (1)** of Theorem 1, eq. (2.38), from Proposition 5.45, Lemma 5.46 and a uniform
(4.41) for the sizes `2 ≤ k ≤ p(β)`. -/
theorem item_one (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (h545 : Prop545Statement)
    {C₀ lam₁ : ℝ} (hlam₁1 : lam₁ ≤ 1) (hlam₁ : 0 < lam₁)
    (hb : ∀ lam : ℝ, 0 < lam → lam < lam₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ V : Finset ℕ, V ⊆ Finset.range N → 2 ≤ V.card → V.card ≤ pBeta p₀ β →
          |dipoleActivity χ N β lam V| ≤ C₀ * (lam ^ 2 / N) ^ (V.card - 1)) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        let cluster : ℕ+ → ℝ := fun n =>
          1 / (n : ℕ).factorial *
            ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                (fun V => (connectionGraph V).Connected ∧
                  ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ pBeta p₀ β),
              (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ)
        0 < partitionFunction χ N β lam ∧ partitionFunction χ N β lam < ∞ ∧
        Summable (fun n => ‖cluster n‖) ∧
        |Real.log (partitionFunction χ N β lam).toReal
            - (2 * N * Real.log N
              + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1))
            - ∑' n, cluster n|
          ≤ C * N * errorRate p₀ β lam := by
  obtain ⟨M₀, hM₀, h545'⟩ := h545 χ hχ p₀ hp₀ β hβ
  obtain ⟨C₅, hC₅, lam₅, hlam₅, hlam₅1, h5⟩ := h545' M₀ le_rfl
  obtain ⟨Ct, hCt, htail⟩ := abs_cluster_le C₀ (pBeta p₀ β)
  set lamt : ℝ := 1 / (2 * Ct + 2) with hlamt_def
  have hlamt : 0 < lamt := by positivity
  have hlamt1 : lamt ≤ 1 := by
    rw [hlamt_def, div_le_one (by positivity)]
    linarith
  refine ⟨C₅ + 2, by linarith, min lam₅ (min lam₁ lamt), lt_min hlam₅ (lt_min hlam₁ hlamt),
    (min_le_left _ _).trans hlam₅1, fun lam hlam hlaml => ?_⟩
  have hlam5 : lam < lam₅ := hlaml.trans_le (min_le_left _ _)
  have hlam1' : lam < lam₁ := hlaml.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlamt' : lam < lamt := hlaml.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hlam_lt1 : lam < 1 := hlam1'.trans_le hlam₁1
  have hq0 : 0 ≤ Ct * lam ^ 2 := by positivity
  have hq : Ct * lam ^ 2 < 1 := by
    have h1 : lam ^ 2 ≤ lam := by nlinarith
    have h2 : Ct * lam < 1 := by
      have : Ct * lamt < 1 := by
        rw [hlamt_def, mul_one_div, div_lt_one (by positivity)]
        linarith
      calc Ct * lam ≤ Ct * lamt := mul_le_mul_of_nonneg_left hlamt'.le hCt.le
        _ < 1 := this
    calc Ct * lam ^ 2 ≤ Ct * lam := mul_le_mul_of_nonneg_left h1 hCt.le
      _ < 1 := h2
  have hδ : 0 < errorRate p₀ β lam := TheoremTwo.errorRate_pos hβ hlam
  obtain ⟨N₅, hN₅⟩ := h5 lam hlam hlam5
  obtain ⟨N₁, hN₁⟩ := hb lam hlam hlam1'
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (eventually_abs_log_factorial_sub_le hδ)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp
    (eventually_abs_log_dipoleNormalization_sub_le hχ hβ hlam hδ)
  refine ⟨max (max N₅ N₁) (max (max N₂ N₃) 1), fun N hN => ?_⟩
  intro cluster
  have hN5 : N₅ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN1' : N₁ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hN))
  have hN3 : N₃ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans
    ((le_max_right _ _).trans hN))
  have hN1 : 1 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨partitionFunction_pos hχ hlam β hN1, partitionFunction_lt_top hχ hlam β N, ?_⟩
  -- the cluster series converges absolutely (Lemma 4.53 with (4.41))
  have hcl : ∀ n : ℕ+, ‖cluster n‖ ≤ N * (Ct * lam ^ 2) ^ (n : ℕ) := fun n =>
    htail N (dipoleActivity χ N β lam) lam n hN1 (hN₁ N hN1') hlam (hlam_lt1.le) n.pos
  have hsum : Summable (fun n => ‖cluster n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcl
      (((summable_geometric_of_lt_one hq0 hq).comp_injective PNat.coe_injective).mul_left (N : ℝ))
  refine ⟨hsum, ?_⟩
  -- Lemma 4.7
  have h47 := lemma_4_7_range N (fun V => 2 ≤ V.card ∧ V.card ≤ pBeta p₀ β)
    (dipoleActivity χ N β lam) (fun h => absurd h.1 (by simp)) hsum
  set S : ℝ := ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter (fun V =>
          (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
            ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ pBeta p₀ β),
        ∏ i, dipoleActivity χ N β lam (V i) with hS
  have hSpos : 0 < S := h47.1
  have hSlog : Real.log S = ∑' n, cluster n := h47.2.1
  -- Lemma 5.46
  set zHat : ℝ := ∑ π ∈ boundedBlockPartitions N (pBeta p₀ β),
    truncatedPartitionWeight χ N β lam M₀ (pBeta p₀ β) π with hzHat
  have h546 : (((N : ℝ) * dipoleNormalization χ N β lam) ^ N)⁻¹ * zHat = S :=
    lemma_5_46 χ hχ p₀ hp₀ β hβ M₀ hM₀ lam hlam hlam_lt1 N
  have hNC : 0 < (N : ℝ) * dipoleNormalization χ N β lam :=
    natCast_mul_dipoleNormalization_pos hχ hlam β hN1
  have hC : 0 < dipoleNormalization χ N β lam := dipoleNormalization_pos hχ hlam β hN1
  have hzHat_eq : zHat = ((N : ℝ) * dipoleNormalization χ N β lam) ^ N * S := by
    rw [← h546, ← mul_assoc, mul_inv_cancel₀ (pow_pos hNC N).ne', one_mul]
  have hlogzHat : Real.log zHat = N * Real.log N + N * Real.log (dipoleNormalization χ N β lam) +
      ∑' n, cluster n := by
    rw [hzHat_eq, Real.log_mul (pow_pos hNC N).ne' hSpos.ne', Real.log_pow,
      Real.log_mul hNpos.ne' hC.ne', hSlog]
    ring
  -- Proposition 5.45
  obtain ⟨hz0, hztop, -, hlog⟩ := hN₅ N hN5
  set zId : ℝ≥0∞ := ∫⁻ c in (Set.univ.pi fun _ : Fin N => TwoComponentCoulomb.box N ×ˢ
      TwoComponentCoulomb.box N) ∩ {c | stableMatching c = Equiv.refl (Fin N)},
    ENNReal.ofReal (Real.exp (-β * energy χ lam c)) with hzId
  have hzIdpos : 0 < zId.toReal := ENNReal.toReal_pos hz0.ne' hztop.ne
  -- the relabeling identity
  have hZ : (partitionFunction χ N β lam).toReal = (N.factorial : ℝ) * zId.toReal := by
    rw [partitionFunction_eq_factorial_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast N.factorial_pos
  have hlogZ : Real.log (partitionFunction χ N β lam).toReal =
      Real.log (N.factorial : ℝ) + Real.log zId.toReal := by
    rw [hZ, Real.log_mul hfac.ne' hzIdpos.ne']
  -- the bookkeeping
  set L : ℝ := (2 - β) * Real.log lam + Real.log (dipoleConstant χ β) with hL
  have hkey : Real.log (partitionFunction χ N β lam).toReal
        - (2 * N * Real.log N + N * (L - 1)) - ∑' n, cluster n =
      (Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)) +
        (Real.log zId.toReal - Real.log zHat) +
          N * (Real.log (dipoleNormalization χ N β lam) - L) := by
    rw [hlogZ, hlogzHat]
    ring
  have hsub : (2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1 = L - 1 := rfl
  rw [hsub, hkey]
  have e1 := hN₂ N hN2
  have e2 := hN₃ N hN3
  have e3 : |(N : ℝ) * (Real.log (dipoleNormalization χ N β lam) - L)| ≤ N * errorRate p₀ β lam := by
    rw [abs_mul, abs_of_pos hNpos]
    exact mul_le_mul_of_nonneg_left e2 hNpos.le
  calc |(Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)) +
        (Real.log zId.toReal - Real.log zHat) +
          N * (Real.log (dipoleNormalization χ N β lam) - L)|
      ≤ |Real.log (N.factorial : ℝ) - ((N : ℝ) * Real.log N - N)| +
          |Real.log zId.toReal - Real.log zHat| +
            |(N : ℝ) * (Real.log (dipoleNormalization χ N β lam) - L)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ N * errorRate p₀ β lam + C₅ * N * errorRate p₀ β lam + N * errorRate p₀ β lam := by
        gcongr
    _ = (C₅ + 2) * N * errorRate p₀ β lam := by ring

end TheoremOne

end MultipoleBKT

end
