/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.LowerBound
public import MultipoleBKT.Appendix.MultipoleIntegralZ.Geometry

/-!
# Bad-neighbourhood geometry and the frozen compatibility chain

See Lemma A.3.
The written weighted subtraction is in `MultipoleIntegral/RouteChain/`. The set `badNbhd`,
its measurability and its area bound below are shared with that route.

The remaining interfaces support the stronger frozen compatibility interval above the
written weighted-loss threshold. They restrict the smaller `IsGood` chain by excluding
root positions in `badNbhd V Z ((6k + 2M)λ)`. The resulting indicator `goodWeightOn` has
measure `V^k |B| V^{k-1}`, where `V = π (λ/4)²`. On this chain, `isGoodZ_of_isGood` verifies
that every dipole is good. The compatibility consumer is
`internal_le_multipoleIntegralPlus_compat`.
-/

@[expose] public section

namespace MultipoleBKT

namespace MultipoleIntegralZ

open MeasureTheory Set Finset Metric
open scoped ENNReal
open TwoComponentCoulomb (box)
open MultipoleIntegral UpperBound

variable {lam : ℝ}

/-! ### The neighbourhood of the bad charges -/

/-- The union of the closed discs of radius `ρ` around the charges of the bad dipoles. -/
def badNbhd {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (ρ : ℝ) : Set ℂ :=
  ⋃ j ∈ V, (closedBall (Z j).1 ρ ∪ closedBall (Z j).2 ρ)

theorem measurableSet_badNbhd {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (ρ : ℝ) :
    MeasurableSet (badNbhd V Z ρ) :=
  Finset.measurableSet_biUnion V fun _ _ => measurableSet_closedBall.union measurableSet_closedBall

/-- `|badNbhd V Z ρ| ≤ 2π |V| ρ²` for `ρ ≥ 0`. -/
theorem volume_badNbhd_le {N : ℕ} (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    volume (badNbhd V Z ρ) ≤ ENNReal.ofReal (2 * V.card * Real.pi * ρ ^ 2) := by
  have hball : ∀ z : ℂ, volume (closedBall z ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
    intro z
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hρ, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]
  calc volume (badNbhd V Z ρ)
      ≤ ∑ j ∈ V, volume (closedBall (Z j).1 ρ ∪ closedBall (Z j).2 ρ) :=
        measure_biUnion_finset_le V _
    _ ≤ ∑ _j ∈ V, ENNReal.ofReal (2 * Real.pi * ρ ^ 2) := by
        refine Finset.sum_le_sum fun j _ => (measure_union_le _ _).trans (le_of_eq ?_)
        rw [hball, hball, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ = ENNReal.ofReal (2 * V.card * Real.pi * ρ ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        ring_nf

/-! ### Good clusters with a constrained root -/

section Good

variable {ι : Type*} {k : ℕ}

section Weight

variable [Fintype ι] [DecidableEq ι]

/-- The indicator of the smaller `IsGood` clusters with the
root's negative charge in `B` instead of the square `[D, √N - D]²`. -/
noncomputable def goodWeightOn (lam : ℝ) (σ : ι ≃ Fin k) (r₀ : ι) (B : Set ℂ)
    (c : ι → ℂ × ℂ) : ℝ≥0∞ :=
  (∏ i, (Metric.ball ((3 * lam / 2 : ℝ) : ℂ) (lam / 4)).indicator (1 : ℂ → ℝ≥0∞)
      ((c i).1 - (c i).2)) *
    (B.indicator (1 : ℂ → ℝ≥0∞) (c r₀).2 *
      ∏ i ∈ univ.erase r₀, (Metric.ball ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ) (lam / 4)).indicator
        (1 : ℂ → ℝ≥0∞) ((c i).2 - (c r₀).2))

theorem measurable_goodWeightOn (lam : ℝ) (σ : ι ≃ Fin k) (r₀ : ι) {B : Set ℂ}
    (hB : MeasurableSet B) : Measurable (goodWeightOn lam σ r₀ B) := by
  unfold goodWeightOn
  refine Measurable.mul (Finset.measurable_prod _ fun i _ =>
    (measurable_const.indicator measurableSet_ball).comp (by fun_prop)) (Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator hB).comp (by fun_prop)
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_const.indicator measurableSet_ball).comp (by fun_prop)

theorem goodWeightOn_le_one (lam : ℝ) (σ : ι ≃ Fin k) (r₀ : ι) (B : Set ℂ) (c : ι → ℂ × ℂ) :
    goodWeightOn lam σ r₀ B c ≤ 1 := by
  unfold goodWeightOn
  refine mul_le_one' (prod_le_one fun i _ => indicator_one_le_one _ _)
    (mul_le_one' (indicator_one_le_one _ _) (prod_le_one fun i _ => indicator_one_le_one _ _))

/-- A nonzero `goodWeightOn` gives a good cluster whose root lies in `B`, when `B` lies in the
square `[D, √N - D]²`, `D = 6kλ`. -/
theorem isGood_of_goodWeightOn_ne_zero {N : ℕ} {σ : ι ≃ Fin k} {r₀ : ι} {B : Set ℂ}
    (hB : B ⊆ innerBox N (6 * lam * k)) {c : ι → ℂ × ℂ} (h : goodWeightOn lam σ r₀ B c ≠ 0) :
    IsGood N lam σ r₀ c ∧ (c r₀).2 ∈ B := by
  unfold goodWeightOn at h
  obtain ⟨h1, h23⟩ := mul_ne_zero_iff.1 h
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.1 h23
  rw [prod_ne_zero_iff] at h1 h3
  have hroot := mem_of_indicator_one_ne_zero h2
  exact ⟨⟨fun i => mem_of_indicator_one_ne_zero (h1 i (mem_univ i)), hB hroot,
    fun i hi => mem_of_indicator_one_ne_zero (h3 i (mem_erase.2 ⟨hi, mem_univ i⟩))⟩, hroot⟩

/-- The measure of the good clusters with root in `B`: with `V = π (λ/4)²`,
`∫ goodWeightOn = V^{|ι|} |B| V^{|ι| - 1}`. -/
theorem lintegral_goodWeightOn (hlam : 0 ≤ lam) (σ : ι ≃ Fin k) (r₀ : ι) {B : Set ℂ}
    (hBm : MeasurableSet B) :
    ∫⁻ c, goodWeightOn lam σ r₀ B c =
      ENNReal.ofReal (Real.pi * (lam / 4) ^ 2) ^ Fintype.card ι *
        (volume B * ENNReal.ofReal (Real.pi * (lam / 4) ^ 2) ^ (Fintype.card ι - 1)) := by
  set Bl : ℂ → ℝ≥0∞ := (Metric.ball ((3 * lam / 2 : ℝ) : ℂ) (lam / 4)).indicator 1
  set A : ι → Set ℂ := fun i => Metric.ball ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ) (lam / 4)
  have hBl : Measurable Bl := measurable_const.indicator measurableSet_ball
  have hpar : IsParentMap r₀ (fun _ => r₀) :=
    ⟨fun c => if c = r₀ then 0 else 1, fun c hc => by simp [hc]⟩
  have hstar : ∫⁻ y : ι → ℂ, B.indicator (1 : ℂ → ℝ≥0∞) (y r₀) *
      ∏ i ∈ univ.erase r₀, (A i).indicator (1 : ℂ → ℝ≥0∞) (y i - y r₀) =
      volume B * ENNReal.ofReal (Real.pi * (lam / 4) ^ 2) ^ (Fintype.card ι - 1) := by
    have := lintegral_parent_eq hpar (fun i t s => (A i).indicator (1 : ℂ → ℝ≥0∞) (t - s))
      (fun i => (measurable_const.indicator measurableSet_ball).comp
        (measurable_fst.sub measurable_snd))
      (fun _ => ENNReal.ofReal (Real.pi * (lam / 4) ^ 2))
      (fun i _ s => by
        rw [lintegral_sub_right_eq_self (fun t => (A i).indicator (1 : ℂ → ℝ≥0∞) t) s,
          lintegral_indicator_one measurableSet_ball, volume_ball_eq _ (by positivity)])
      (B.indicator 1) (measurable_const.indicator hBm)
    rw [this, lintegral_indicator_one hBm, prod_const, card_erase_of_mem (mem_univ r₀), card_univ]
  have hpt : ∀ r y : ι → ℂ, goodWeightOn lam σ r₀ B (fun i => (y i + r i, y i)) =
      (∏ i, Bl (r i)) * (B.indicator (1 : ℂ → ℝ≥0∞) (y r₀) *
        ∏ i ∈ univ.erase r₀, (A i).indicator (1 : ℂ → ℝ≥0∞) (y i - y r₀)) := by
    intro r y
    unfold goodWeightOn
    simp only [add_sub_cancel_left]
    rfl
  have hfin : ∀ r : ι → ℂ, (∏ i, Bl (r i)) ≠ ⊤ := fun r =>
    ENNReal.prod_ne_top fun i _ => ne_top_of_le_ne_top ENNReal.one_ne_top
      (indicator_one_le_one _ _)
  rw [lintegral_dipole_coords (measurable_goodWeightOn lam σ r₀ hBm)]
  simp_rw [hpt]
  have hconst : ∀ r : ι → ℂ, ∫⁻ y : ι → ℂ, (∏ i, Bl (r i)) *
      (B.indicator (1 : ℂ → ℝ≥0∞) (y r₀) *
        ∏ i ∈ univ.erase r₀, (A i).indicator (1 : ℂ → ℝ≥0∞) (y i - y r₀)) =
      (∏ i, Bl (r i)) * ∫⁻ y : ι → ℂ, B.indicator (1 : ℂ → ℝ≥0∞) (y r₀) *
        ∏ i ∈ univ.erase r₀, (A i).indicator (1 : ℂ → ℝ≥0∞) (y i - y r₀) := fun r =>
    lintegral_const_mul' _ _ (hfin r)
  simp_rw [hconst, hstar]
  have hBm' : Measurable fun r : ι → ℂ => ∏ i, Bl (r i) :=
    Finset.measurable_prod _ fun i _ => hBl.comp (measurable_pi_apply i)
  rw [lintegral_mul_const _ hBm', lintegral_pi_prod_eq (fun _ => Bl) (fun _ => hBl)]
  congr 1
  rw [prod_const, card_univ]
  congr 1
  rw [lintegral_indicator_one measurableSet_ball, volume_ball_eq _ (by positivity)]

end Weight

/-- **The lower bound on good clusters with a constrained root** (the lower-bound half of the
proof of Lemma A.3, with the subtraction (A.15) built into the root set `B`): if
`B ⊆ [D, √N - D]²` (`D = 6kλ`) is measurable with `|B| ≥ b ≥ 0`, and a measurable `F ≥ 0` with
finite integral over `(Λ²)^S` satisfies `F ≥ A ((4λ)^{-β})^k` on the good clusters with root in
`B`, then `∫_{(Λ²)^S} F ≥ A (4^{-β})^k (π/16)^{2k-1} b λ^{(2-β)k} λ^{2(k-1)}`. -/
theorem le_setIntegral_of_isGoodOn {β : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 1 ≤ k) {N : ℕ}
    {S : Finset ℕ} (σ : S ≃ Fin k) {B : Set ℂ} (hBm : MeasurableSet B)
    (hB : B ⊆ innerBox N (6 * lam * k)) {b : ℝ} (hb : 0 ≤ b) (hvol : ENNReal.ofReal b ≤ volume B)
    {F : (S → ℂ × ℂ) → ℝ} (hFm : Measurable F) (hF0 : ∀ c, 0 ≤ F c)
    (hfin : ∫⁻ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), ENNReal.ofReal (F c) ≠ ⊤)
    {A : ℝ} (hA : 0 ≤ A)
    (hF : ∀ c, IsGood N lam σ (σ.symm ⟨0, hk⟩) c → (c (σ.symm ⟨0, hk⟩)).2 ∈ B →
      A * ((4 * lam) ^ (-β)) ^ k ≤ F c) :
    A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 16) ^ (2 * k - 1) * b * lam ^ ((2 - β) * k) *
        lam ^ (2 * (k - 1)) ≤
      ∫ c in Set.univ.pi (fun _ : S => box N ×ˢ box N), F c := by
  classical
  set r₀ : S := σ.symm ⟨0, hk⟩
  have hr₀ : ((σ r₀ : ℕ) : ℝ) = 0 := by simp [r₀]
  have hcard : Fintype.card S = k := by simpa using Fintype.card_congr σ
  set P : Set (S → ℂ × ℂ) := Set.univ.pi fun _ : S => box N ×ˢ box N
  set L : ℝ := A * ((4 * lam) ^ (-β)) ^ k
  have hL : 0 ≤ L := by positivity
  set V : ℝ := Real.pi * (lam / 4) ^ 2
  have hV : 0 ≤ V := by positivity
  have hpt : ∀ c, ENNReal.ofReal L * goodWeightOn lam σ r₀ B c ≤
      P.indicator (fun c => ENNReal.ofReal (F c)) c := by
    intro c
    by_cases h0 : goodWeightOn lam σ r₀ B c = 0
    · rw [h0, mul_zero]
      exact zero_le
    obtain ⟨hgood, hroot⟩ := isGood_of_goodWeightOn_ne_zero hB h0
    have hcP : c ∈ P := Set.mem_univ_pi.2 fun i => hgood.mem_box hlam hr₀ i
    rw [Set.indicator_of_mem hcP]
    calc ENNReal.ofReal L * goodWeightOn lam σ r₀ B c ≤ ENNReal.ofReal L * 1 := by
          gcongr
          exact goodWeightOn_le_one lam σ r₀ B c
      _ = ENNReal.ofReal L := mul_one _
      _ ≤ ENNReal.ofReal (F c) := ENNReal.ofReal_le_ofReal (hF c hgood hroot)
  have hlint : ENNReal.ofReal (L * V ^ k * b * V ^ (k - 1)) ≤
      ∫⁻ c in P, ENNReal.ofReal (F c) := by
    rw [← lintegral_indicator (measurableSet_pi_box_prod N)]
    calc ENNReal.ofReal (L * V ^ k * b * V ^ (k - 1))
        = ENNReal.ofReal L * (ENNReal.ofReal V ^ k *
            (ENNReal.ofReal b * ENNReal.ofReal V ^ (k - 1))) := by
          rw [← ENNReal.ofReal_pow hV, ← ENNReal.ofReal_pow hV, ← ENNReal.ofReal_mul hb,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hL]
          ring_nf
      _ ≤ ENNReal.ofReal L * (ENNReal.ofReal V ^ k *
            (volume B * ENNReal.ofReal V ^ (k - 1))) := by
          gcongr
      _ = ENNReal.ofReal L * ∫⁻ c, goodWeightOn lam σ r₀ B c := by
          rw [lintegral_goodWeightOn hlam.le σ r₀ hBm, hcard]
      _ = ∫⁻ c, ENNReal.ofReal L * goodWeightOn lam σ r₀ B c :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ c, P.indicator (fun c => ENNReal.ofReal (F c)) c := lintegral_mono hpt
  have hI : ∫ c in P, F c = (∫⁻ c in P, ENNReal.ofReal (F c)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0)
      hFm.aestronglyMeasurable
  rw [hI]
  refine le_trans (le_of_eq ?_) ((ENNReal.ofReal_le_iff_le_toReal hfin).1 hlint)
  have h4 : (4 * lam) ^ (-β) = (4 : ℝ) ^ (-β) * lam ^ (-β) :=
    Real.mul_rpow (by norm_num) hlam.le
  have hVk : V ^ k * V ^ (k - 1) = (Real.pi / 16) ^ (2 * k - 1) * (lam ^ 2) ^ (2 * k - 1) := by
    rw [← pow_add, show k + (k - 1) = 2 * k - 1 by omega, ← mul_pow]
    congr 1
    simp only [V]
    ring
  have hexp := rpow_neg_pow_mul_sq_pow (β := β) hlam hk
  calc A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 16) ^ (2 * k - 1) * b *
        lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))
      = A * ((4 : ℝ) ^ (-β)) ^ k * (Real.pi / 16) ^ (2 * k - 1) * b *
          ((lam ^ (-β)) ^ k * (lam ^ 2) ^ (2 * k - 1)) := by rw [hexp]; ring
    _ = L * V ^ k * b * V ^ (k - 1) := by
        simp only [L]
        rw [h4, mul_pow]
        linear_combination (A * ((4 : ℝ) ^ (-β)) ^ k * (lam ^ (-β)) ^ k * b) * hVk.symm

/-! ### Good clusters away from the bad points are in `I_good^Z` -/

/-- On a good cluster (root `r₀`, `σ r₀ = 0`) whose root's negative charge avoids the discs of
radius `(6k + 2M)λ` around the bad charges, every dipole is in `I_good^Z` (`M ≥ 0`). -/
theorem isGoodZ_of_isGood {N : ℕ} {p₀ : ℕ} {β M ε₀ : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} (hlam : 0 < lam) (hM : 0 ≤ M) {σ : ι ≃ Fin k} {r₀ : ι}
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) {c : ι → ℂ × ℂ} (hc : IsGood N lam σ r₀ c)
    (hroot : (c r₀).2 ∉ badNbhd V Z ((6 * k + 2 * M) * lam)) (i : ι) :
    IsGoodZ p₀ β lam M ε₀ V Z (c i) := by
  by_contra hnot
  obtain ⟨j, hj, hd⟩ := exists_near_of_not_isGoodZ hM hnot
  have hr : ‖(c i).1 - (c i).2‖ < 7 * lam / 4 := hc.norm_fst_sub_snd i hlam
  have hmax : max ‖(c i).1 - (c i).2‖ lam ≤ 2 * lam := max_le (by linarith) (by linarith)
  have hd' : dipoleDist (c i) (Z j) ≤ 2 * M * lam := by
    have := mul_le_mul_of_nonneg_left hmax hM
    linarith
  -- every charge of dipole `i` is within `6kλ` of the root's negative charge
  have hx : ‖(c i).1 - goodCentre lam σ (c r₀).2 i‖ < 3 * lam / 2 := by
    linarith [hc.norm_fst_sub_centre hlam hr₀ i]
  have hy : ‖(c i).2 - goodCentre lam σ (c r₀).2 i‖ < 3 * lam / 2 := by
    linarith [hc.norm_snd_sub_centre hlam hr₀ i]
  have hroot' : ‖(c r₀).2 - goodCentre lam σ (c r₀).2 r₀‖ < 3 * lam / 2 := by
    linarith [hc.norm_snd_sub_centre hlam hr₀ r₀]
  have hpx : ‖(c i).1 - (c r₀).2‖ < 6 * lam * k := norm_sub_lt_of_centre hlam σ _ hx hroot'
  have hpy : ‖(c i).2 - (c r₀).2‖ < 6 * lam * k := norm_sub_lt_of_centre hlam σ _ hy hroot'
  apply hroot
  simp only [badNbhd, Set.mem_iUnion, Set.mem_union, mem_closedBall, dist_eq_norm]
  refine ⟨j, hj, ?_⟩
  have key : ∀ p q : ℂ, ‖p - (c r₀).2‖ < 6 * lam * k → ‖p - q‖ ≤ 2 * M * lam →
      ‖(c r₀).2 - q‖ ≤ (6 * k + 2 * M) * lam := by
    intro p q hp hpq
    calc ‖(c r₀).2 - q‖ = ‖(p - q) - (p - (c r₀).2)‖ := by congr 1; ring
      _ ≤ ‖p - q‖ + ‖p - (c r₀).2‖ := norm_sub_le _ _
      _ ≤ (6 * k + 2 * M) * lam := by nlinarith
  unfold dipoleDist at hd'
  rcases min_le_iff.1 hd' with h1 | h1 <;> rcases min_le_iff.1 h1 with h2 | h2
  · exact Or.inl (key _ _ hpx h2)
  · exact Or.inr (key _ _ hpx h2)
  · exact Or.inl (key _ _ hpy h2)
  · exact Or.inr (key _ _ hpy h2)

end Good

end MultipoleIntegralZ

end MultipoleBKT

end
