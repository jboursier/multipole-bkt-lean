/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoTwo
public import MultipoleBKT.UpperBound.BadPointTypes.Radial
public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.CutWeight
import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.Spatial

/-!
# Lemma 5.41: one multipole of short dipoles

The paper: Lemma 5.41,
(5.136), (5.137) and (5.138).

`lintegral_positions_cayley_le` uses the endpoint cells and tree coordinates,
then Cayley's exact tree count. `lintegral_blockWeight_cut_le` retains the choice
of the largest radius. Its weaker count is kept for the existing low-beta
coefficient. `lintegral_star_eq` integrates the other radii below that root.
The high-beta leaf deletion and terminal core are in `RouteTypeTwoIntegral`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset MultipoleIntegral
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- **One multipole, positions integrated** ((5.136) and (5.137),
the paper). -/
theorem lintegral_blockWeight_cut_le (hχ : IsMollifier χ) (hM : 0 ≤ M) (hlam : 0 < lam)
    (h : ℝ) (Nₐ : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    ∫⁻ y : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) y ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) *
        ∑ r₀ : ι, ∫⁻ r : ι → ℂ, (if ∀ c, ‖r c‖ ≤ ‖r r₀‖ then 1 else 0) *
          ((∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) *
            ∏ i, cutFactor χ β lam h (r i)) := by
  classical
  set k := Fintype.card ι
  set P : ι → (ι → ℂ) → ℝ≥0∞ := fun r₀ r => (if ∀ c, ‖r c‖ ≤ ‖r r₀‖ then 1 else 0) *
    ((∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) *
      ∏ i, cutFactor χ β lam h (r i)) with hP
  have hmeasP : ∀ r₀, Measurable (P r₀) := by
    intro r₀
    refine Measurable.mul ?_ ?_
    · refine Measurable.ite ?_ measurable_const measurable_const
      have : {r : ι → ℂ | ∀ c, ‖r c‖ ≤ ‖r r₀‖} = ⋂ c, {r : ι → ℂ | ‖r c‖ ≤ ‖r r₀‖} := by
        ext r; simp
      rw [this]
      exact MeasurableSet.iInter fun c => measurableSet_le
        (measurable_pi_apply c).norm (measurable_pi_apply r₀).norm
    · refine Measurable.mul (Finset.measurable_prod _ fun c _ => ?_)
        (Finset.measurable_prod _ fun i _ => (measurable_cutFactor hχ hlam β h).comp
          (measurable_pi_apply i))
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hmeasB : Measurable (blockWeight (ι := ι) M lam (cutDipoleWeight χ β lam h Nₐ)) :=
    measurable_blockWeight M lam (measurable_cutDipoleWeight hχ hlam β h Nₐ)
  -- the inner integral, for fixed lengths
  have hinner : ∀ r : ι → ℂ, ∫⁻ y : ι → ℂ,
      blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) (fun i => (y i + r i, y i)) ≤
        ((k ^ k : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * ∑ r₀ : ι, P r₀ r := by
    intro r
    obtain ⟨r₀, hr₀⟩ := Finite.exists_max fun i => ‖r i‖
    have hpt : ∀ y : ι → ℂ, blockWeight M lam (cutDipoleWeight χ β lam h Nₐ)
        (fun i => (y i + r i, y i)) ≤ (∏ i, cutFactor χ β lam h (r i)) *
          ((box Nₐ).indicator (1 : ℂ → ℝ≥0∞) (y r₀) * connectedIndicator M lam y r) := by
      intro y
      unfold blockWeight connectedIndicator
      by_cases hc : (SimpleGraph.fromRel fun i j => MultipoleLinked M lam
          (y i + r i, y i) (y j + r j, y j)).Connected
      · rw [ite_eq_left hc, ite_eq_left hc, one_mul, mul_one]
        have hy : ∏ i, cutDipoleWeight χ β lam h Nₐ (y i + r i, y i) ≤
            ∏ i, cutFactor χ β lam h (r i) := by
          refine prod_le_prod fun i _ => ?_
          unfold cutDipoleWeight
          by_cases hb : (y i + r i, y i) ∈ box Nₐ ×ˢ box Nₐ
          · rw [Set.indicator_of_mem hb]
            simp [cutFactor]
          · rw [Set.indicator_of_notMem hb]
            exact zero_le
        by_cases hb : y r₀ ∈ box Nₐ
        · rw [Set.indicator_of_mem hb, Pi.one_apply, mul_one]
          exact hy
        · rw [Set.indicator_of_notMem hb, mul_zero]
          refine le_of_eq (prod_eq_zero (mem_univ r₀) ?_)
          unfold cutDipoleWeight
          exact Set.indicator_of_notMem (fun h' => hb h'.2) _
      · rw [ite_eq_right hc, ite_eq_right hc, zero_mul]
        exact zero_le
    have hfin : (∏ i, cutFactor χ β lam h (r i)) ≠ ⊤ :=
      ENNReal.prod_ne_top fun i _ => by
        unfold cutFactor
        by_cases hi : r i ∈ Metric.closedBall (0 : ℂ) h
        · rw [Set.indicator_of_mem hi]; exact ENNReal.ofReal_ne_top
        · rw [Set.indicator_of_notMem hi]; exact ENNReal.zero_ne_top
    calc ∫⁻ y : ι → ℂ, blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) (fun i => (y i + r i, y i))
        ≤ ∫⁻ y : ι → ℂ, (∏ i, cutFactor χ β lam h (r i)) *
            ((box Nₐ).indicator (1 : ℂ → ℝ≥0∞) (y r₀) * connectedIndicator M lam y r) :=
          lintegral_mono hpt
      _ = (∏ i, cutFactor χ β lam h (r i)) * ∫⁻ y : ι → ℂ,
            (box Nₐ).indicator (1 : ℂ → ℝ≥0∞) (y r₀) * connectedIndicator M lam y r :=
          lintegral_const_mul' _ _ hfin
      _ ≤ (∏ i, cutFactor χ β lam h (r i)) * (((k ^ k : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) *
            ∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) := by
          gcongr
          refine (lintegral_positions_cayley_le hM hlam.le Nₐ r r₀).trans ?_
          have hc : (((k ^ (k - 2) : ℕ) : ℝ≥0∞)) ≤ ((k ^ k : ℕ) : ℝ≥0∞) := by
            exact_mod_cast (show k ^ (k - 2) ≤ k ^ k by gcongr; omega)
          refine mul_le_mul' (mul_le_mul' hc le_rfl) (le_of_eq ?_)
          apply Finset.prod_congr
          · ext i
            simp
          · intro i _
            rfl
      _ = ((k ^ k : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * P r₀ r := by
          simp only [hP, ite_eq_left hr₀, one_mul]
          ring
      _ ≤ ((k ^ k : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * ∑ r₀ : ι, P r₀ r := by
          gcongr
          exact single_le_sum (f := fun r₀ => P r₀ r) (fun _ _ => zero_le) (mem_univ r₀)
  calc ∫⁻ y : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) y
      = ∫⁻ r : ι → ℂ, ∫⁻ y : ι → ℂ,
          blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) (fun i => (y i + r i, y i)) :=
        lintegral_dipole_coords hmeasB
    _ ≤ ∫⁻ r : ι → ℂ, ((k ^ k : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * ∑ r₀ : ι, P r₀ r :=
        lintegral_mono hinner
    _ = ((k ^ k : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * ∑ r₀ : ι, ∫⁻ r : ι → ℂ, P r₀ r := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun r₀ _ => hmeasP r₀),
          lintegral_finsetSum _ fun r₀ _ => hmeasP r₀]

/-- **Integrating around a fixed root**: `∫ F(x_{r₀}) ∏_{c ≠ r₀} G(x_c, x_{r₀}) dx
= ∫ F(t) (∫ G(s, t) ds)^{|ι|-1} dt`. -/
theorem lintegral_star_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (r₀ : ι) {F : ℂ → ℝ≥0∞}
    (hF : Measurable F) {G : ℂ → ℂ → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) :
    ∫⁻ x : ι → ℂ, F (x r₀) * ∏ c ∈ univ.erase r₀, G (x c) (x r₀) =
      ∫⁻ t, F t * (∫⁻ s, G s t) ^ (Fintype.card ι - 1) := by
  set μ : ι → Measure ℂ := fun _ => volume
  set s := univ.erase r₀ with hs
  have hr₀ : r₀ ∉ s := notMem_erase r₀ univ
  have hGm : Measurable fun y : ι → ℂ => ∏ c ∈ s, G (y c) (y r₀) :=
    Finset.measurable_prod _ fun c _ =>
      hG.comp (f := fun y : ι → ℂ => (y c, y r₀))
        ((measurable_pi_apply c).prodMk (measurable_pi_apply r₀))
  have hfm : Measurable fun y : ι → ℂ => F (y r₀) * ∏ c ∈ s, G (y c) (y r₀) :=
    (hF.comp (measurable_pi_apply r₀)).mul hGm
  -- the inner marginal over the non-root coordinates
  have hinner : ∀ z : ι → ℂ, (∫⋯∫⁻_s, (fun y => F (y r₀) * ∏ c ∈ s, G (y c) (y r₀)) ∂μ) z =
      F (z r₀) * (∫⁻ u, G u (z r₀)) ^ (Fintype.card ι - 1) := by
    intro z
    rw [lmarginal_mul_left_of_indep (fun y => F (y r₀)) _ hGm
      (fun x y hxy => by rw [hxy r₀ hr₀])]
    congr 1
    have h1 : (∫⋯∫⁻_s, (fun y => ∏ c ∈ s, G (y c) (y r₀)) ∂μ) z =
        (∫⋯∫⁻_s, (fun y => ∏ c ∈ s, G (y c) (z r₀)) ∂μ) z := by
      unfold lmarginal
      refine lintegral_congr fun w => ?_
      refine prod_congr rfl fun c _ => ?_
      simp [Function.updateFinset_def, hr₀]
    rw [h1, lmarginal_prod_eq (fun c u => G u (z r₀))
      (fun c => hG.comp (measurable_id.prodMk measurable_const)) s z]
    simp only [μ]
    rw [prod_const, card_erase_of_mem (mem_univ r₀), card_univ]
  have huniv : insert r₀ s = (univ : Finset ι) := insert_erase (mem_univ r₀)
  rw [volume_pi, lintegral_eq_lmarginal_univ (μ := μ) (fun _ => (0 : ℂ)), ← huniv,
    lmarginal_insert _ hfm hr₀]
  simp_rw [hinner, Function.update_self]
  rfl

/-- The inner integral for `β < 4`: `∫_{|s| ≤ |t|} 4πM² max(|s|, λ)² 𝟙_{|s| ≤ h} e^{β g_λ(s)} ds
≤ K max(|t|, λ)^{4-β}`. -/
theorem lintegral_inner_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hβ4 : β < 4) (hlam : 0 < lam)
    (h : ℝ) (t : ℂ) :
    ∫⁻ s, (if ‖s‖ ≤ ‖t‖ then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (4 * Real.pi * (M * max ‖s‖ lam) ^ 2) * cutFactor χ β lam h s) ≤
      ENNReal.ofReal (4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ) *
        (2 * Real.pi * (1 + 1 / (4 - β))) * max ‖t‖ lam ^ (4 - β)) := by
  set ρ := max ‖t‖ lam with hρ
  have hlρ : lam ≤ ρ := le_max_right _ _
  have hpt : ∀ s : ℂ, (if ‖s‖ ≤ ‖t‖ then (1 : ℝ≥0∞) else 0) *
      (ENNReal.ofReal (4 * Real.pi * (M * max ‖s‖ lam) ^ 2) * cutFactor χ β lam h s) ≤
        ENNReal.ofReal (4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ)) *
          (Metric.closedBall (0 : ℂ) ρ).indicator
            (fun s => ENNReal.ofReal (max ‖s‖ lam ^ (2 - β))) s := by
    intro s
    by_cases hs : ‖s‖ ≤ ‖t‖
    · have hsρ : s ∈ Metric.closedBall (0 : ℂ) ρ := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hs.trans (le_max_left _ _)
      rw [ite_eq_left hs, one_mul, Set.indicator_of_mem hsρ,
        ← ENNReal.ofReal_mul (by positivity)]
      have hcut : cutFactor χ β lam h s ≤
          ENNReal.ofReal (Real.exp (β * smearedKernel χ lam s)) := by
        unfold cutFactor
        by_cases hsh : s ∈ Metric.closedBall (0 : ℂ) h
        · rw [Set.indicator_of_mem hsh]
        · rw [Set.indicator_of_notMem hsh]; exact zero_le
      refine (mul_le_mul_of_nonneg_left hcut zero_le).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hm : 0 < max ‖s‖ lam := lt_max_of_lt_right hlam
      have he := exp_smearedKernel_le hχ hβ hlam s
      calc 4 * Real.pi * (M * max ‖s‖ lam) ^ 2 * Real.exp (β * smearedKernel χ lam s)
          ≤ 4 * Real.pi * (M * max ‖s‖ lam) ^ 2 *
              (Real.exp (β * kernelConst χ) * max ‖s‖ lam ^ (-β)) := by gcongr
        _ = 4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ) *
              (max ‖s‖ lam ^ (2 : ℝ) * max ‖s‖ lam ^ (-β)) := by
            rw [Real.rpow_two]
            ring
        _ = 4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ) * max ‖s‖ lam ^ (2 - β) := by
            rw [← Real.rpow_add hm]
            ring_nf
    · rw [ite_eq_right hs, zero_mul]
      exact zero_le
  calc ∫⁻ s, (if ‖s‖ ≤ ‖t‖ then (1 : ℝ≥0∞) else 0) *
        (ENNReal.ofReal (4 * Real.pi * (M * max ‖s‖ lam) ^ 2) * cutFactor χ β lam h s)
      ≤ ∫⁻ s, ENNReal.ofReal (4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ)) *
          (Metric.closedBall (0 : ℂ) ρ).indicator
            (fun s => ENNReal.ofReal (max ‖s‖ lam ^ (2 - β))) s := lintegral_mono hpt
    _ = ENNReal.ofReal (4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ)) *
          ∫⁻ s, (Metric.closedBall (0 : ℂ) ρ).indicator
            (fun s => ENNReal.ofReal (max ‖s‖ lam ^ (2 - β))) s :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ)) *
          ENNReal.ofReal (2 * Real.pi * ((1 + 1 / (2 - β + 2)) * ρ ^ (2 - β + 2))) := by
        gcongr
        exact lintegral_closedBall_max_rpow_le_of_pos hlam hlρ (by linarith)
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), show 2 - β + 2 = 4 - β by ring]
        ring_nf

/-- The constant of the inner integral: `4πM² e^{βc_χ} 2π (1 + 1/(4-β))`. -/
noncomputable def innerConst (χ : ℂ → ℝ) (β M : ℝ) : ℝ :=
  4 * Real.pi * M ^ 2 * Real.exp (β * kernelConst χ) * (2 * Real.pi * (1 + 1 / (4 - β)))

theorem innerConst_nonneg (hβ4 : β < 4) : 0 ≤ innerConst χ β M := by
  unfold innerConst
  have : 0 < 4 - β := by linarith
  positivity

/-- **One multipole for `β < 4`** ((5.138), the paper): with `m = |ι|`,
`∫ 𝟙_{𝓑} ∏ 𝟙_{r_i ≤ h} e^{β g_λ} ≤ m^{m+1} N e^{βc_χ} K^{m-1}
  ∫_{|t| ≤ h} max(|t|, λ)^{(4-β)(m-1)-β} dt`, `K = innerConst`. -/
theorem lintegral_blockWeight_cut_le_root (hχ : IsMollifier χ) (hβ : 0 ≤ β) (hβ4 : β < 4)
    (hM : 0 ≤ M) (hlam : 0 < lam) (h : ℝ) (Nₐ : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] :
    ∫⁻ y : ι → ℂ × ℂ, blockWeight M lam (cutDipoleWeight χ β lam h Nₐ) y ≤
      ((Fintype.card ι ^ Fintype.card ι : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * (Fintype.card ι : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (β * kernelConst χ) *
            innerConst χ β M ^ (Fintype.card ι - 1)) *
          ∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) h).indicator (fun t => ENNReal.ofReal
            (max ‖t‖ lam ^ ((4 - β) * (Fintype.card ι - 1 : ℕ) - β))) t) := by
  classical
  set m := Fintype.card ι
  set K := innerConst χ β M with hK
  have hK0 : 0 ≤ K := innerConst_nonneg hβ4
  set G : ℂ → ℂ → ℝ≥0∞ := fun s t => (if ‖s‖ ≤ ‖t‖ then (1 : ℝ≥0∞) else 0) *
    (ENNReal.ofReal (4 * Real.pi * (M * max ‖s‖ lam) ^ 2) * cutFactor χ β lam h s) with hG
  have hGm : Measurable (Function.uncurry G) := by
    refine Measurable.mul ?_ ?_
    · refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_le (measurable_fst.norm) (measurable_snd.norm)
    · refine Measurable.mul ?_ ((measurable_cutFactor hχ hlam β h).comp measurable_fst)
      exact ENNReal.measurable_ofReal.comp (by fun_prop)
  set Rad := ∫⁻ t : ℂ, (Metric.closedBall (0 : ℂ) h).indicator (fun t => ENNReal.ofReal
    (max ‖t‖ lam ^ ((4 - β) * (m - 1 : ℕ) - β))) t
  -- the bound for each root
  have hroot : ∀ r₀ : ι, ∫⁻ r : ι → ℂ, (if ∀ c, ‖r c‖ ≤ ‖r r₀‖ then 1 else 0) *
      ((∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) *
        ∏ i, cutFactor χ β lam h (r i)) ≤
      ENNReal.ofReal (Real.exp (β * kernelConst χ) * K ^ (m - 1)) * Rad := by
    intro r₀
    have hpt : ∀ r : ι → ℂ, (if ∀ c, ‖r c‖ ≤ ‖r r₀‖ then (1 : ℝ≥0∞) else 0) *
        ((∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) *
          ∏ i, cutFactor χ β lam h (r i)) ≤
        cutFactor χ β lam h (r r₀) * ∏ c ∈ univ.erase r₀, G (r c) (r r₀) := by
      intro r
      by_cases hall : ∀ c, ‖r c‖ ≤ ‖r r₀‖
      · rw [ite_eq_left hall, one_mul, ← mul_prod_erase univ _ (mem_univ r₀)]
        refine le_of_eq ?_
        have hR : ∏ c ∈ univ.erase r₀, G (r c) (r r₀) = ∏ c ∈ univ.erase r₀,
            (ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2) *
              cutFactor χ β lam h (r c)) :=
          prod_congr rfl fun c _ => by
            simp only [hG]
            rw [ite_eq_left (hall c), one_mul]
        rw [hR, prod_mul_distrib]
        ring
      · rw [ite_eq_right hall, zero_mul]
        exact zero_le
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_star_eq r₀ (measurable_cutFactor hχ hlam β h) hGm]
    -- the inner integrals and the root weight
    have hpt2 : ∀ t : ℂ, cutFactor χ β lam h t * (∫⁻ s, G s t) ^ (m - 1) ≤
        ENNReal.ofReal (Real.exp (β * kernelConst χ) * K ^ (m - 1)) *
          (Metric.closedBall (0 : ℂ) h).indicator (fun t => ENNReal.ofReal
            (max ‖t‖ lam ^ ((4 - β) * (m - 1 : ℕ) - β))) t := by
      intro t
      have hin : ∫⁻ s, G s t ≤ ENNReal.ofReal (K * max ‖t‖ lam ^ (4 - β)) := by
        have := lintegral_inner_le (M := M) hχ hβ hβ4 hlam h t
        simp only [hG]
        rw [hK]
        unfold innerConst
        exact this.trans (le_of_eq (by ring_nf))
      have hm : 0 < max ‖t‖ lam := lt_max_of_lt_right hlam
      unfold cutFactor
      by_cases ht : t ∈ Metric.closedBall (0 : ℂ) h
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        calc ENNReal.ofReal (Real.exp (β * smearedKernel χ lam t)) * (∫⁻ s, G s t) ^ (m - 1)
            ≤ ENNReal.ofReal (Real.exp (β * kernelConst χ) * max ‖t‖ lam ^ (-β)) *
                ENNReal.ofReal (K * max ‖t‖ lam ^ (4 - β)) ^ (m - 1) := by
              gcongr
              exact exp_smearedKernel_le hχ hβ hlam t
          _ = ENNReal.ofReal (Real.exp (β * kernelConst χ) * K ^ (m - 1)) *
                ENNReal.ofReal (max ‖t‖ lam ^ ((4 - β) * (m - 1 : ℕ) - β)) := by
              rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [mul_pow, ← Real.rpow_natCast (max ‖t‖ lam ^ (4 - β)),
                ← Real.rpow_mul hm.le]
              rw [show (4 - β) * ((m - 1 : ℕ) : ℝ) - β = -β + (4 - β) * ((m - 1 : ℕ) : ℝ) by ring,
                Real.rpow_add hm]
              ring
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul, mul_zero]
    calc ∫⁻ t, cutFactor χ β lam h t * (∫⁻ s, G s t) ^ (Fintype.card ι - 1)
        ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (β * kernelConst χ) * K ^ (m - 1)) *
            (Metric.closedBall (0 : ℂ) h).indicator (fun t => ENNReal.ofReal
              (max ‖t‖ lam ^ ((4 - β) * (m - 1 : ℕ) - β))) t := lintegral_mono hpt2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine (lintegral_blockWeight_cut_le hχ hM hlam h Nₐ).trans ?_
  calc ((m ^ m : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) * ∑ r₀ : ι, ∫⁻ r : ι → ℂ,
        (if ∀ c, ‖r c‖ ≤ ‖r r₀‖ then 1 else 0) *
          ((∏ c ∈ univ.erase r₀, ENNReal.ofReal (4 * Real.pi * (M * max ‖r c‖ lam) ^ 2)) *
            ∏ i, cutFactor χ β lam h (r i))
      ≤ ((m ^ m : ℕ) : ℝ≥0∞) * (Nₐ : ℝ≥0∞) *
          ∑ _r₀ : ι, ENNReal.ofReal (Real.exp (β * kernelConst χ) * K ^ (m - 1)) * Rad := by
        gcongr with r₀
        exact hroot r₀
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]
        ring

end BadPointTypes

end MultipoleBKT

end
