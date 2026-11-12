/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeThreePointwise
public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneAssembly

/-!
# Lemma 5.39: integrating the type-3 dipoles

The paper: proof of Lemma 5.39 (Lemma 5.39, Steps 2–3).

* `lintegral_nonseedWeight_le` (5.118): at a fixed dipole vector `r⃗ = x - y`, a dipole
  near a given dipole lies in four discs of radius `M max(r, λ)`, so
  `∫ 𝟙_{near b} 𝟙_{r ≤ h} 4^β max(r, λ)^{-β} ≤ K := ∫ 4π M² max(|w|, λ)² 𝟙_{|w| ≤ h}
  4^β max(|w|, λ)^{-β} dw` for every `b`;
* `lintegral_seedWeight_le` (proof of Lemma 5.39): a seed is near one of the `N_1 + N_2` background
  dipoles: `∫ ≤ (N_1 + N_2) K`;
* `lintegral_typeThreeTerm_le`: the forest integration (`lintegral_forest_le`) gives
  `((N_1 + N_2) K)^{|S|} K^{N_3 - |S|}` for each seed set and parent map;
* `typedBadPartitionFunction_le`: with the pointwise bound (a.e., `ae_noIsosceles_config`),
  the splitting of the coordinates and Tonelli's inequality,
  `Z_{bad,N_1,N_2,N_3} ≤ Z^{(1)}_{bad,N_1} Z^{(2)}_{bad,N_2} (12^β)^{N_2}
    ∑_{S} ∑_{par} ((N_1 + N_2) K)^{|S|} K^{N_3 - |S|}` for any real `K ≥ ∫ …`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset TheoremTwo UpperBound MultipoleIntegral
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {n : ℕ} {M β lam h : ℝ}

/-! ### Measurability -/

theorem measurableSet_nearPairs (M lam : ℝ) : MeasurableSet (nearPairs M lam) := by
  unfold nearPairs IsNear
  exact measurableSet_le (by fun_prop) (by fun_prop)

theorem measurable_lengthWeight (β lam h : ℝ) : Measurable (lengthWeight β lam h) := by
  unfold lengthWeight
  refine Measurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
  refine ENNReal.measurable_ofReal.comp (measurable_const.mul ?_)
  exact (continuous_norm.max continuous_const).measurable.pow_const _

theorem measurable_nonseedWeight (M β lam h : ℝ) :
    Measurable (Function.uncurry (nonseedWeight M β lam h)) := by
  have h1 : Measurable fun p : (ℂ × ℂ) × (ℂ × ℂ) => nearIndicator M lam p.1 p.2 :=
    (measurable_const.indicator (measurableSet_nearPairs M lam)).comp
      (measurable_fst.prodMk measurable_snd)
  exact h1.mul ((measurable_lengthWeight β lam h).comp (by fun_prop))

theorem measurable_nonseedWeight_left (M β lam h : ℝ) (b : ℂ × ℂ) :
    Measurable fun a => nonseedWeight M β lam h a b :=
  (measurable_nonseedWeight M β lam h).comp (measurable_id.prodMk measurable_const)

theorem seedWeight_eq {m₁ m₂ : ℕ} (u : Fin m₁ → ℂ × ℂ) (v : Fin m₂ → ℂ × ℂ) (a : ℂ × ℂ) :
    seedWeight M β lam h u v a =
      (∑ j, nonseedWeight M β lam h a (u j)) + ∑ j, nonseedWeight M β lam h a (v j) := by
  unfold seedWeight nonseedWeight
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]

theorem measurable_seedWeight {m₁ m₂ : ℕ} (u : Fin m₁ → ℂ × ℂ) (v : Fin m₂ → ℂ × ℂ) :
    Measurable (seedWeight M β lam h u v) := by
  have : seedWeight M β lam h u v = fun a =>
      (∑ j, nonseedWeight M β lam h a (u j)) + ∑ j, nonseedWeight M β lam h a (v j) :=
    funext (seedWeight_eq u v)
  rw [this]
  exact (Finset.measurable_sum _ fun j _ => measurable_nonseedWeight_left M β lam h _).add
    (Finset.measurable_sum _ fun j _ => measurable_nonseedWeight_left M β lam h _)

/-! ### One dipole -/

/-- The set of positions `y` of a dipole `(y + w, y)` near `b` has area at most
`4π (M max(|w|, λ))²`. -/
theorem volume_isNear_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (w : ℂ) (b : ℂ × ℂ) :
    volume {y : ℂ | IsNear M lam (y + w, y) b} ≤
      ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2) := by
  set ρ := M * max ‖w‖ lam with hρdef
  have hρ0 : 0 ≤ ρ := mul_nonneg hM (le_max_of_le_right hlam)
  have hsub : {y : ℂ | IsNear M lam (y + w, y) b} ⊆
      Metric.closedBall (b.1 - w) ρ ∪ Metric.closedBall (b.2 - w) ρ ∪
        Metric.closedBall b.1 ρ ∪ Metric.closedBall b.2 ρ := by
    intro y hy
    simp only [Set.mem_ofPred_eq, IsNear, add_sub_cancel_left] at hy
    simp only [Set.mem_union, Metric.mem_closedBall, dist_eq_norm]
    rcases min_le_iff.1 hy with h1 | h1 <;> rcases min_le_iff.1 h1 with h2 | h2
    · left; left; left; rwa [show y - (b.1 - w) = y + w - b.1 by ring]
    · left; left; right; rwa [show y - (b.2 - w) = y + w - b.2 by ring]
    · left; right; exact h2
    · right; exact h2
  have hball : ∀ z : ℂ, volume (Metric.closedBall z ρ) ≤ ENNReal.ofReal (Real.pi * ρ ^ 2) := by
    intro z
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hρ0, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity)]
    rw [mul_comm]
  calc volume {y : ℂ | IsNear M lam (y + w, y) b}
      ≤ volume (Metric.closedBall (b.1 - w) ρ) + volume (Metric.closedBall (b.2 - w) ρ) +
          volume (Metric.closedBall b.1 ρ) + volume (Metric.closedBall b.2 ρ) := by
        refine (measure_mono hsub).trans ?_
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.pi * ρ ^ 2) + ENNReal.ofReal (Real.pi * ρ ^ 2) +
          ENNReal.ofReal (Real.pi * ρ ^ 2) + ENNReal.ofReal (Real.pi * ρ ^ 2) := by
        gcongr <;> exact hball _
    _ = ENNReal.ofReal (4 * Real.pi * ρ ^ 2) := by
        have h0 : 0 ≤ Real.pi * ρ ^ 2 := by positivity
        rw [← ENNReal.ofReal_add h0 h0, ← ENNReal.ofReal_add (by positivity) h0,
          ← ENNReal.ofReal_add (by positivity) h0]
        congr 1
        ring

/-- The constant `K = ∫ 4π M² max(|w|, λ)² 𝟙_{|w| ≤ h} 4^β max(|w|, λ)^{-β} dw`. -/
noncomputable def nearConst (M β lam h : ℝ) : ℝ≥0∞ :=
  ∫⁻ w : ℂ, ENNReal.ofReal (4 * Real.pi * (M * max ‖w‖ lam) ^ 2) * lengthWeight β lam h w

/-- **One nonseed** (5.118). -/
theorem lintegral_nonseedWeight_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) (b : ℂ × ℂ) :
    ∫⁻ a : ℂ × ℂ, nonseedWeight M β lam h a b ≤ nearConst M β lam h := by
  have hF := measurable_nonseedWeight_left M β lam h b
  have hvol : (volume : Measure (ℂ × ℂ)) = (volume : Measure ℂ).prod volume := rfl
  rw [hvol, lintegral_prod_symm _ hF.aemeasurable]
  have h1 : ∀ y : ℂ, ∫⁻ x, nonseedWeight M β lam h (x, y) b =
      ∫⁻ w, nonseedWeight M β lam h (y + w, y) b := fun y =>
    (lintegral_add_left_eq_self (fun x => nonseedWeight M β lam h (x, y) b) y).symm
  simp_rw [h1]
  have hG : Measurable (Function.uncurry fun (y w : ℂ) => nonseedWeight M β lam h (y + w, y) b) :=
    hF.comp (by fun_prop)
  rw [lintegral_lintegral_swap hG.aemeasurable]
  unfold nearConst
  refine lintegral_mono fun w => ?_
  simp only [nonseedWeight, add_sub_cancel_left]
  have hset : MeasurableSet {y : ℂ | IsNear M lam (y + w, y) b} := by
    unfold IsNear
    exact measurableSet_le (by fun_prop) (by fun_prop)
  have hind : (fun y => nearIndicator M lam (y + w, y) b) =
      {y : ℂ | IsNear M lam (y + w, y) b}.indicator 1 := by
    funext y
    unfold nearIndicator nearPairs
    by_cases hy : IsNear M lam (y + w, y) b
    · rw [Set.indicator_of_mem (show ((y + w, y), b) ∈ {p : (ℂ × ℂ) × (ℂ × ℂ) |
        IsNear M lam p.1 p.2} from hy), Set.indicator_of_mem (show y ∈ {y : ℂ |
          IsNear M lam (y + w, y) b} from hy)]
      rfl
    · rw [Set.indicator_of_notMem (show ((y + w, y), b) ∉ {p : (ℂ × ℂ) × (ℂ × ℂ) |
        IsNear M lam p.1 p.2} from hy), Set.indicator_of_notMem (show y ∉ {y : ℂ |
          IsNear M lam (y + w, y) b} from hy)]
  rw [lintegral_mul_const _ (by rw [hind]; exact measurable_const.indicator hset), hind,
    lintegral_indicator_one hset]
  exact mul_le_mul_left (volume_isNear_le hM hlam w b) _

/-- **One seed** (proof of Lemma 5.39). -/
theorem lintegral_seedWeight_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) {m₁ m₂ : ℕ}
    (u : Fin m₁ → ℂ × ℂ) (v : Fin m₂ → ℂ × ℂ) :
    ∫⁻ a, seedWeight M β lam h u v a ≤ ((m₁ + m₂ : ℕ) : ℝ≥0∞) * nearConst M β lam h := by
  simp_rw [seedWeight_eq u v]
  rw [lintegral_add_left (Finset.measurable_sum _ fun j _ =>
      measurable_nonseedWeight_left M β lam h _),
    lintegral_finsetSum _ fun j _ => measurable_nonseedWeight_left M β lam h _,
    lintegral_finsetSum _ fun j _ => measurable_nonseedWeight_left M β lam h _]
  refine le_trans (add_le_add (Finset.sum_le_sum fun j _ => lintegral_nonseedWeight_le hM hlam _)
    (Finset.sum_le_sum fun j _ => lintegral_nonseedWeight_le hM hlam _)) (le_of_eq ?_)
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← add_mul]
  push_cast
  rfl

/-- **The forest integration** (Steps 2–3). -/
theorem lintegral_typeThreeTerm_le (hM : 0 ≤ M) (hlam : 0 ≤ lam) {m₁ m₂ k : ℕ}
    (S : Finset (Fin k)) (par : Fin k → Fin k) (u : Fin m₁ → ℂ × ℂ) (v : Fin m₂ → ℂ × ℂ) :
    ∫⁻ w : Fin k → ℂ × ℂ, typeThreeTerm M β lam h S par u v w ≤
      (((m₁ + m₂ : ℕ) : ℝ≥0∞) * nearConst M β lam h) ^ S.card *
        nearConst M β lam h ^ Sᶜ.card := by
  classical
  unfold typeThreeTerm
  by_cases hF : IsForest S par
  swap
  · simp only [hF, ite_false, zero_mul, lintegral_zero]
    exact zero_le
  obtain ⟨dep, hdep⟩ := hF
  simp only [show IsForest S par from ⟨dep, hdep⟩, ite_true, one_mul]
  refine (lintegral_forest_le S par dep hdep (fun _ => nonseedWeight M β lam h)
    (fun _ => measurable_nonseedWeight M β lam h) (fun _ => nearConst M β lam h)
    (fun c _ y => lintegral_nonseedWeight_le hM hlam y) (fun _ => seedWeight M β lam h u v)
    (fun _ => measurable_seedWeight u v)).trans ?_
  rw [Finset.prod_const (nearConst M β lam h)]
  gcongr
  calc ∏ _r ∈ S, ∫⁻ t, seedWeight M β lam h u v t
      ≤ ∏ _r ∈ S, ((m₁ + m₂ : ℕ) : ℝ≥0∞) * nearConst M β lam h :=
        Finset.prod_le_prod fun _ _ => lintegral_seedWeight_le hM hlam u v
    _ = _ := Finset.prod_const _

theorem measurable_typeThreeTerm {m₁ m₂ k : ℕ} (S : Finset (Fin k)) (par : Fin k → Fin k)
    (u : Fin m₁ → ℂ × ℂ) (v : Fin m₂ → ℂ × ℂ) :
    Measurable (typeThreeTerm M β lam h S par u v) := by
  unfold typeThreeTerm
  refine measurable_const.mul (Measurable.mul ?_ ?_)
  · exact Finset.measurable_prod _ fun s _ => (measurable_seedWeight u v).comp
      (measurable_pi_apply s)
  · exact Finset.measurable_prod _ fun c _ => (measurable_nonseedWeight M β lam h).comp
      (f := fun w : Fin k → ℂ × ℂ => (w c, w (par c))) (by fun_prop)

/-! ### Finiteness -/

theorem volume_box_prod_lt_top (Nₐ : ℕ) :
    (volume : Measure (ℂ × ℂ)) (box Nₐ ×ˢ box Nₐ) < ⊤ := by
  have h : (volume : Measure (ℂ × ℂ)) (box Nₐ ×ˢ box Nₐ) =
      (volume : Measure ℂ) (box Nₐ) * (volume : Measure ℂ) (box Nₐ) :=
    Measure.prod_prod (box Nₐ) (box Nₐ)
  rw [h, TwoComponentCoulomb.volume_box]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.natCast_lt_top _)

theorem volume_boxPi_lt_top (Nₐ m : ℕ) : volume (boxPi Nₐ m) < ⊤ := by
  have h : volume (boxPi Nₐ m) = ∏ _i : Fin m, (volume : Measure (ℂ × ℂ)) (box Nₐ ×ˢ box Nₐ) :=
    volume_pi_pi (fun _ : Fin m => box Nₐ ×ˢ box Nₐ)
  rw [h]
  exact ENNReal.prod_lt_top fun i _ => volume_box_prod_lt_top Nₐ

/-- `Z^{(2)}_{bad,m} < ∞`: the dipole weights are bounded by `(e^{β c_χ} λ^{-β})^m`. -/
theorem typeTwoPartitionFunction_lt_top {χ : ℂ → ℝ} (hχ : IsMollifier χ) {p₀ : ℕ} {ε₀ : ℝ}
    (hβ : 0 ≤ β) (hlam : 0 < lam) (Nₐ m : ℕ) :
    typeTwoPartitionFunction χ p₀ β lam M ε₀ Nₐ m < ⊤ := by
  classical
  set c := Real.exp (β * kernelConst χ) * lam ^ (-β) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ v : Fin m → ℂ × ℂ,
      (if typeTwoBad Nₐ p₀ β lam M ε₀ v = univ ∧ StablePairs v then (1 : ℝ≥0∞) else 0) *
        ENNReal.ofReal (dipoleWeight χ β lam v) ≤ ENNReal.ofReal (c ^ m) := by
    intro v
    have h1 : (if typeTwoBad Nₐ p₀ β lam M ε₀ v = univ ∧ StablePairs v then (1 : ℝ≥0∞) else 0)
        ≤ 1 := by split_ifs <;> simp
    refine (mul_le_of_le_one_left' h1).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold dipoleWeight
    rw [show c ^ m = ∏ _i : Fin m, c by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
    refine Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => ?_
    refine (exp_smearedKernel_le hχ hβ hlam _).trans ?_
    rw [hc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _)
      (by linarith)) (Real.exp_pos _).le
  unfold typeTwoPartitionFunction
  calc ∫⁻ v in boxPi Nₐ m, (if typeTwoBad Nₐ p₀ β lam M ε₀ v = univ ∧ StablePairs v then 1 else 0) *
        ENNReal.ofReal (dipoleWeight χ β lam v)
      ≤ ∫⁻ _v in boxPi Nₐ m, ENNReal.ofReal (c ^ m) := lintegral_mono fun v => hpt v
    _ = ENNReal.ofReal (c ^ m) * volume (boxPi Nₐ m) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volume_boxPi_lt_top Nₐ m)

theorem typeOneIntegrand_le_ofReal {p₀ : ℕ} {ε₀ : ℝ} {Nₐ m : ℕ} (u : Fin m → ℂ × ℂ) :
    typeOneIntegrand p₀ β lam ε₀ Nₐ m u ≤ ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ u) := by
  classical
  unfold typeOneIntegrand
  by_cases hu : u ∈ boxPi Nₐ m
  · rw [Set.indicator_of_mem hu]
    refine mul_le_of_le_one_left' ?_
    split_ifs <;> simp
  · rw [Set.indicator_of_notMem hu]
    exact zero_le

theorem typeTwoIntegrand_le_ofReal {χ : ℂ → ℝ} {p₀ : ℕ} {ε₀ : ℝ} {Nₐ m : ℕ} (v : Fin m → ℂ × ℂ) :
    typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ m v ≤ ENNReal.ofReal (dipoleWeight χ β lam v) := by
  classical
  unfold typeTwoIntegrand
  by_cases hv : v ∈ boxPi Nₐ m
  · rw [Set.indicator_of_mem hv]
    refine mul_le_of_le_one_left' ?_
    split_ifs <;> simp
  · rw [Set.indicator_of_notMem hv]
    exact zero_le

/-! ### Assembly -/

/-- **Lemma 5.39, integrated form** (Steps 1–3): for any real `K` bounding the one-dipole
constant `∫ 4π M² max(|w|, λ)² 𝟙_{|w| ≤ h} 4^β max(|w|, λ)^{-β} dw`,
`Z_{bad,N₁,N₂,N₃} ≤ Z^{(1)}_{bad,N₁} Z^{(2)}_{bad,N₂} (12^β)^{N₂}
  ∑_{S, N₃ ≤ p|S|} ∑_{par} ((N₁ + N₂) K)^{|S|} K^{N₃ - |S|}`. -/
theorem typedBadPartitionFunction_le {χ : ℂ → ℝ} {p₀ : ℕ} {ε₀ : ℝ} {Nₐ : ℕ}
    {V₁ V₂ V₃ : Finset (Fin n)} (hχ : IsMollifier χ) (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hlam : 0 < lam) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (h12 : Disjoint V₁ V₂) (h13 : Disjoint V₁ V₃) (h23 : Disjoint V₂ V₃)
    (hcov : V₁ ∪ V₂ ∪ V₃ = univ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : nearConst M β lam (cutoff p₀ β lam ε₀) ≤ ENNReal.ofReal K) :
    typedBadPartitionFunction p₀ β lam M ε₀ Nₐ n V₁ V₂ V₃ ≤
      typeOnePartitionFunction p₀ β lam ε₀ Nₐ V₁.card *
        typeTwoPartitionFunction χ p₀ β lam M ε₀ Nₐ V₂.card *
        ENNReal.ofReal ((12 ^ β) ^ V₂.card * ∑ S ∈ seedSets V₃.card (pBeta p₀ β),
          ∑ _par ∈ parentSet S, (((V₁.card + V₂.card : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card) := by
  classical
  set hc := cutoff p₀ β lam ε₀
  set C : ℝ≥0∞ := ENNReal.ofReal ((12 ^ β) ^ V₂.card) with hC
  set B : ℝ := ∑ S ∈ seedSets V₃.card (pBeta p₀ β),
    ∑ _par ∈ parentSet S, (((V₁.card + V₂.card : ℕ) : ℝ) * K) ^ S.card * K ^ Sᶜ.card with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  set G : (Fin V₁.card → ℂ × ℂ) × ((Fin V₂.card → ℂ × ℂ) × (Fin V₃.card → ℂ × ℂ)) → ℝ≥0∞ :=
    fun p => typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card p.1 * C *
      typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card p.2.1 *
      ∑ S ∈ seedSets V₃.card (pBeta p₀ β), ∑ par ∈ parentSet S,
        typeThreeTerm M β lam hc S par p.1 p.2.1 p.2.2 with hG
  have hae : ∀ᵐ d ∂(volume : Measure (Fin n → ℂ × ℂ)),
      typedIntegrand p₀ β lam M ε₀ Nₐ n V₁ V₂ V₃ d ≤
        G (d ∘ V₁.orderEmbOfFin rfl, (d ∘ V₂.orderEmbOfFin rfl, d ∘ V₃.orderEmbOfFin rfl)) := by
    filter_upwards [ae_noIsosceles_config] with d hd
    exact typedIntegrand_le hχ hq hh hlam hβ hM h12 h13 h23 hcov d hd.1 hd.2
  -- the type-3 dipoles
  have hinner : ∀ u v, ∫⁻ w, G (u, (v, w)) ≤
      typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card u * C *
        typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card v * ENNReal.ofReal B := by
    intro u v
    simp only [hG]
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun S _ => Finset.measurable_sum _
      fun par _ => measurable_typeThreeTerm S par u v)]
    gcongr
    rw [lintegral_finsetSum _ fun S _ => Finset.measurable_sum _
      fun par _ => measurable_typeThreeTerm S par u v, hB,
      ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [lintegral_finsetSum _ fun par _ => measurable_typeThreeTerm S par u v,
      ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity]
    refine Finset.sum_le_sum fun par _ => ?_
    refine (lintegral_typeThreeTerm_le hM hlam.le S par u v).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow hK0, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    gcongr
  have hZ2 := typeTwoPartitionFunction_lt_top (M := M) (p₀ := p₀) (ε₀ := ε₀) hχ hβ hlam Nₐ
    V₂.card
  rw [typeTwoPartitionFunction_eq_lintegral] at hZ2
  rw [typedBadPartitionFunction_eq_lintegral, typeOnePartitionFunction_eq_lintegral,
    typeTwoPartitionFunction_eq_lintegral]
  have : SFinite (volume : Measure ((Fin V₂.card → ℂ × ℂ) × (Fin V₃.card → ℂ × ℂ))) :=
    @Measure.prod.instSFinite _ _ _ volume (by infer_instance) _ volume (by infer_instance)
  calc ∫⁻ d, typedIntegrand p₀ β lam M ε₀ Nₐ n V₁ V₂ V₃ d
      ≤ ∫⁻ d, G (d ∘ V₁.orderEmbOfFin rfl, (d ∘ V₂.orderEmbOfFin rfl, d ∘ V₃.orderEmbOfFin rfl)) :=
        lintegral_mono_ae hae
    _ = ∫⁻ p, G p := lintegral_split3 h12 h13 h23 hcov G
    _ ≤ ∫⁻ u, ∫⁻ q, G (u, q) := lintegral_prod_le G
    _ ≤ ∫⁻ u, ∫⁻ v, ∫⁻ w, G (u, (v, w)) := lintegral_mono fun u => lintegral_prod_le _
    _ ≤ ∫⁻ u, ∫⁻ v, typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card u * C *
          typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card v * ENNReal.ofReal B :=
        lintegral_mono fun u => lintegral_mono fun v => hinner u v
    _ = ∫⁻ u, typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card u *
          (C * ENNReal.ofReal B * ∫⁻ v, typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card v) := by
        refine lintegral_congr fun u => ?_
        have hfin : typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card u * C * ENNReal.ofReal B ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
            (typeOneIntegrand_le_ofReal u)) ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
        rw [← mul_assoc, ← mul_assoc, ← lintegral_const_mul' _ _ hfin]
        refine lintegral_congr fun v => ?_
        ring
    _ = (∫⁻ u, typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card u) *
          (C * ENNReal.ofReal B * ∫⁻ v, typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card v) :=
        lintegral_mul_const' _ _ (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ENNReal.ofReal_ne_top) hZ2.ne)
    _ = _ := by
        rw [hC, ENNReal.ofReal_mul (by positivity)]
        ring

end BadPointTypes

end MultipoleBKT

end
