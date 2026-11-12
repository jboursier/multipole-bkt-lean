/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.Basic
import TwoComponentCoulomb.Gibbs.Basic

/-!
# Shared lower geometry and the retained compatibility chain

See Lemma A.3.
The square, ball-volume and connectivity facts below support the paper chain in
`RouteChain/`. The smaller event `IsGood` with spacing `6λ` and radius `λ/4` is retained
for the frozen compatibility interval above the written weighted-loss threshold.
Its interaction estimate uses logarithmic kernel bounds. The paper's event `𝒞`
and Hessian interaction estimate are in `RouteChain/Event.lean`, and its specified
endpoint-ball construction is in `RouteChain/Geometry.lean`.
-/

@[expose] public section

namespace MultipoleBKT

open MeasureTheory Set Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {lam M : ℝ}

namespace MultipoleIntegral

/-- The square `[D, √N - D]²`, the allowed positions of the root of a good cluster. -/
def innerBox (N : ℕ) (D : ℝ) : Set ℂ :=
  Complex.reProdIm (Icc D (Real.sqrt N - D)) (Icc D (Real.sqrt N - D))

theorem measurableSet_innerBox (N : ℕ) (D : ℝ) : MeasurableSet (innerBox N D) :=
  (isClosed_Icc.reProdIm isClosed_Icc).measurableSet

theorem volume_innerBox (N : ℕ) (D : ℝ) :
    volume (innerBox N D) =
      ENNReal.ofReal (Real.sqrt N - 2 * D) * ENNReal.ofReal (Real.sqrt N - 2 * D) := by
  rw [innerBox, TwoComponentCoulomb.volume_reProdIm_Icc_Icc]
  ring_nf

/-- For `√N ≥ 4D ≥ 0`, the square `[D, √N - D]²` has area at least `N/4`. -/
theorem ofReal_quarter_le_volume_innerBox {N : ℕ} {D : ℝ} (hD : 0 ≤ D)
    (hN : 4 * D ≤ Real.sqrt N) : ENNReal.ofReal (N / 4) ≤ volume (innerBox N D) := by
  rw [volume_innerBox, ← ENNReal.ofReal_mul (by linarith)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs := Real.sq_sqrt (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

/-- A disc of radius `ρ ≥ 0` in `ℂ` has area `π ρ²`. -/
theorem volume_ball_eq (z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Metric.ball z ρ) = ENNReal.ofReal (Real.pi * ρ ^ 2) := by
  rw [Complex.volume_ball, ← ENNReal.ofReal_pow hρ, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity), mul_comm]

section Good

variable {ι : Type*} {k : ℕ}

theorem indicator_one_le_one {α : Type*} (s : Set α) (x : α) :
    s.indicator (1 : α → ℝ≥0∞) x ≤ 1 := by
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]; rfl
  · rw [Set.indicator_of_notMem hx]; exact zero_le_one

theorem mem_of_indicator_one_ne_zero {α : Type*} {s : Set α} {x : α}
    (h : s.indicator (1 : α → ℝ≥0∞) x ≠ 0) : x ∈ s := by
  by_contra hx
  exact h (Set.indicator_of_notMem hx _)

/-- The good clusters. -/
def IsGood (N : ℕ) (lam : ℝ) (σ : ι ≃ Fin k) (r₀ : ι) (c : ι → ℂ × ℂ) : Prop :=
  (∀ i, (c i).1 - (c i).2 ∈ Metric.ball ((3 * lam / 2 : ℝ) : ℂ) (lam / 4)) ∧
    (c r₀).2 ∈ innerBox N (6 * lam * k) ∧
    ∀ i, i ≠ r₀ → (c i).2 - (c r₀).2 ∈ Metric.ball ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ) (lam / 4)

/-- The centre `z_i = y_{r₀} + 6λ σ(i) + 3λ/4` of the `i`-th dipole of a good cluster. -/
noncomputable def goodCentre (lam : ℝ) (σ : ι ≃ Fin k) (Y : ℂ) (i : ι) : ℂ :=
  Y + ((6 * lam * ((σ i : ℕ) : ℝ) + 3 * lam / 4 : ℝ) : ℂ)

theorem norm_goodCentre_sub (hlam : 0 ≤ lam) (σ : ι ≃ Fin k) (Y : ℂ) (i j : ι) :
    ‖goodCentre lam σ Y i - goodCentre lam σ Y j‖ =
      6 * lam * |((σ i : ℕ) : ℝ) - ((σ j : ℕ) : ℝ)| := by
  have h : goodCentre lam σ Y i - goodCentre lam σ Y j =
      ((6 * lam * (((σ i : ℕ) : ℝ) - ((σ j : ℕ) : ℝ)) : ℝ) : ℂ) := by
    simp only [goodCentre]
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]

theorem norm_real_of_nonneg {t : ℝ} (ht : 0 ≤ t) : ‖(t : ℂ)‖ = t := by
  rw [Complex.norm_real, Real.norm_of_nonneg ht]

variable {N : ℕ} {σ : ι ≃ Fin k} {r₀ : ι} {c : ι → ℂ × ℂ}

/-- In a good cluster, `|y_i - y_{r₀} - 6λ σ(i)| < λ/4` for every `i` (including the root). -/
theorem IsGood.norm_snd_sub (hc : IsGood N lam σ r₀ c) (hlam : 0 < lam)
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) (i : ι) :
    ‖(c i).2 - (c r₀).2 - ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ)‖ < lam / 4 := by
  by_cases hi : i = r₀
  · subst hi
    rw [hr₀]
    simp only [mul_zero, Complex.ofReal_zero, sub_self, norm_zero]
    positivity
  · have := hc.2.2 i hi
    rwa [Metric.mem_ball, dist_eq_norm] at this

theorem IsGood.norm_sub_snd (hc : IsGood N lam σ r₀ c) (i : ι) :
    ‖(c i).1 - (c i).2 - ((3 * lam / 2 : ℝ) : ℂ)‖ < lam / 4 := by
  have := hc.1 i
  rwa [Metric.mem_ball, dist_eq_norm] at this

/-- In a good cluster, `|y_i - z_i| < λ`. -/
theorem IsGood.norm_snd_sub_centre (hc : IsGood N lam σ r₀ c) (hlam : 0 < lam)
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) (i : ι) :
    ‖(c i).2 - goodCentre lam σ (c r₀).2 i‖ < lam := by
  have h1 := hc.norm_snd_sub hlam hr₀ i
  have e : (c i).2 - goodCentre lam σ (c r₀).2 i =
      ((c i).2 - (c r₀).2 - ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ)) - ((3 * lam / 4 : ℝ) : ℂ) := by
    simp only [goodCentre]
    push_cast
    ring
  rw [e]
  calc _ ≤ ‖(c i).2 - (c r₀).2 - ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ)‖ +
        ‖((3 * lam / 4 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ < lam / 4 + 3 * lam / 4 := by
        rw [norm_real_of_nonneg (by positivity)]
        linarith
    _ = lam := by ring

/-- In a good cluster, `|x_i - z_i| < 5λ/4`. -/
theorem IsGood.norm_fst_sub_centre (hc : IsGood N lam σ r₀ c) (hlam : 0 < lam)
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) (i : ι) :
    ‖(c i).1 - goodCentre lam σ (c r₀).2 i‖ < 5 * lam / 4 := by
  have h1 := hc.norm_snd_sub hlam hr₀ i
  have h2 := hc.norm_sub_snd i
  have e : (c i).1 - goodCentre lam σ (c r₀).2 i =
      ((c i).1 - (c i).2 - ((3 * lam / 2 : ℝ) : ℂ)) +
        ((c i).2 - (c r₀).2 - ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ)) +
          ((3 * lam / 4 : ℝ) : ℂ) := by
    simp only [goodCentre]
    push_cast
    ring
  rw [e]
  calc _ ≤ ‖(c i).1 - (c i).2 - ((3 * lam / 2 : ℝ) : ℂ)‖ +
        ‖(c i).2 - (c r₀).2 - ((6 * lam * ((σ i : ℕ) : ℝ) : ℝ) : ℂ)‖ +
          ‖((3 * lam / 4 : ℝ) : ℂ)‖ := norm_add₃_le
    _ < lam / 4 + lam / 4 + 3 * lam / 4 := by
        rw [norm_real_of_nonneg (by positivity)]
        linarith
    _ = 5 * lam / 4 := by ring

/-- In a good cluster, `|x_i - y_i| < 7λ/4`. -/
theorem IsGood.norm_fst_sub_snd (hc : IsGood N lam σ r₀ c) (i : ι) (hlam : 0 < lam) :
    ‖(c i).1 - (c i).2‖ < 7 * lam / 4 := by
  have h2 := hc.norm_sub_snd i
  calc ‖(c i).1 - (c i).2‖ ≤ ‖(c i).1 - (c i).2 - ((3 * lam / 2 : ℝ) : ℂ)‖ +
        ‖((3 * lam / 2 : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
    _ < lam / 4 + 3 * lam / 2 := by
        rw [norm_real_of_nonneg (by positivity)]
        linarith
    _ = 7 * lam / 4 := by ring

/-- In a good cluster, the charges lie in `Λ`. -/
theorem IsGood.mem_box (hc : IsGood N lam σ r₀ c) (hlam : 0 < lam)
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) (i : ι) : c i ∈ box N ×ˢ box N := by
  set Y := (c r₀).2
  have hY := hc.2.1
  simp only [innerBox, Complex.mem_reProdIm, Set.mem_Icc] at hY
  have hsub : Metric.ball Y (6 * lam * k) ⊆ box N :=
    ball_subset_box hY.1.1 (by linarith [hY.1.2]) hY.2.1 (by linarith [hY.2.2])
  have hσ : ((σ i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast (σ i).2
  have hzY : ‖goodCentre lam σ Y i - Y‖ = 6 * lam * ((σ i : ℕ) : ℝ) + 3 * lam / 4 := by
    simp only [goodCentre, add_sub_cancel_left]
    exact norm_real_of_nonneg (by positivity)
  have h1 := hc.norm_fst_sub_centre hlam hr₀ i
  have h2 := hc.norm_snd_sub_centre hlam hr₀ i
  have key : ∀ w : ℂ, ‖w - goodCentre lam σ Y i‖ < 5 * lam / 4 → w ∈ box N := by
    intro w hw
    refine hsub ?_
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖w - Y‖ ≤ ‖w - goodCentre lam σ Y i‖ + ‖goodCentre lam σ Y i - Y‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 5 * lam / 4 + (6 * lam * ((σ i : ℕ) : ℝ) + 3 * lam / 4) := by rw [hzY]; linarith
      _ ≤ 6 * lam * k := by nlinarith
  exact ⟨key _ h1, key _ (by linarith)⟩

/-- In a good cluster, two distinct dipoles form a stable pair. -/
theorem IsGood.isStableDipolePair (hc : IsGood N lam σ r₀ c) (hlam : 0 < lam)
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) {i j : ι} (hij : i ≠ j) : IsStableDipolePair (c i) (c j) := by
  refine isStableDipolePair_of_near (z := goodCentre lam σ (c r₀).2 i)
    (z' := goodCentre lam σ (c r₀).2 j) (ε := 3 * lam / 2)
    (by linarith [hc.norm_fst_sub_centre hlam hr₀ i])
    (by linarith [hc.norm_snd_sub_centre hlam hr₀ i])
    (by linarith [hc.norm_fst_sub_centre hlam hr₀ j])
    (by linarith [hc.norm_snd_sub_centre hlam hr₀ j]) ?_
  rw [norm_goodCentre_sub hlam.le]
  have hne : (σ i : ℕ) ≠ (σ j : ℕ) := fun h => hij (σ.injective (Fin.ext h))
  have h1 : (1 : ℝ) ≤ |((σ i : ℕ) : ℝ) - ((σ j : ℕ) : ℝ)| := by
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : ((σ i : ℕ) : ℝ) + 1 ≤ ((σ j : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · have : ((σ j : ℕ) : ℝ) + 1 ≤ ((σ i : ℕ) : ℝ) := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
  nlinarith

/-- In a good cluster with `M ≥ 9`, consecutive dipoles are linked. -/
theorem IsGood.multipoleLinked (hc : IsGood N lam σ r₀ c) (hlam : 0 < lam)
    (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) (hM : 9 ≤ M) {i j : ι} (hij : (σ j : ℕ) = σ i + 1) :
    MultipoleLinked M lam (c i) (c j) := by
  refine multipoleLinked_of_near (z := goodCentre lam σ (c r₀).2 i)
    (z' := goodCentre lam σ (c r₀).2 j) (ε := 3 * lam / 2) (by linarith)
    (by linarith [hc.norm_fst_sub_centre hlam hr₀ i])
    (by linarith [hc.norm_fst_sub_centre hlam hr₀ j]) ?_
  rw [norm_goodCentre_sub hlam.le]
  have : ((σ j : ℕ) : ℝ) = ((σ i : ℕ) : ℝ) + 1 := by exact_mod_cast hij
  rw [this, show ((σ i : ℕ) : ℝ) - (((σ i : ℕ) : ℝ) + 1) = -1 by ring, abs_neg, abs_one]
  nlinarith

/-- Two points within `3λ/2` of the centres of two dipoles of a good cluster are at distance
less than `6kλ`. -/
theorem norm_sub_lt_of_centre (hlam : 0 < lam) (σ : ι ≃ Fin k) (Y : ℂ) {i j : ι} {a b : ℂ}
    (ha : ‖a - goodCentre lam σ Y i‖ < 3 * lam / 2)
    (hb : ‖b - goodCentre lam σ Y j‖ < 3 * lam / 2) :
    ‖a - b‖ < 6 * lam * k := by
  have hσi : ((σ i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast (σ i).2
  have hσj : ((σ j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast (σ j).2
  have hd : |((σ i : ℕ) : ℝ) - ((σ j : ℕ) : ℝ)| ≤ k - 1 := by
    rw [abs_le]
    constructor <;> linarith [(Nat.cast_nonneg (σ i : ℕ) : (0 : ℝ) ≤ _),
      (Nat.cast_nonneg (σ j : ℕ) : (0 : ℝ) ≤ _)]
  have hz := norm_goodCentre_sub hlam.le σ Y i j
  calc ‖a - b‖ ≤ ‖a - goodCentre lam σ Y i‖ +
        ‖goodCentre lam σ Y i - goodCentre lam σ Y j‖ +
          ‖goodCentre lam σ Y j - b‖ := by
        calc ‖a - b‖ = ‖(a - goodCentre lam σ Y i) +
              (goodCentre lam σ Y i - goodCentre lam σ Y j) +
                (goodCentre lam σ Y j - b)‖ := by congr 1; ring
          _ ≤ _ := norm_add₃_le
    _ < 3 * lam / 2 + 6 * lam * (k - 1) + 3 * lam / 2 := by
        rw [hz, norm_sub_rev (goodCentre lam σ Y j) b]
        have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 6 * lam)
        linarith
    _ ≤ 6 * lam * k := by nlinarith

/-- **The interaction is bounded above on good clusters**: `v_ij ≤ 2 c_χ + 2 log(8k)`. -/
theorem IsGood.dipoleInteraction_le (hχ : IsMollifier χ) (hc : IsGood N lam σ r₀ c)
    (hlam : 0 < lam) (hr₀ : ((σ r₀ : ℕ) : ℝ) = 0) (i j : ι) :
    dipoleInteraction χ lam (c i) (c j) ≤ 2 * kernelConst χ + 2 * Real.log (8 * k) := by
  have hk : (1 : ℝ) ≤ k := by
    have := (σ i).2
    exact_mod_cast (show 1 ≤ k by omega)
  have hx : ∀ l, ‖(c l).1 - goodCentre lam σ (c r₀).2 l‖ < 3 * lam / 2 := fun l => by
    linarith [hc.norm_fst_sub_centre hlam hr₀ l]
  have hy : ∀ l, ‖(c l).2 - goodCentre lam σ (c r₀).2 l‖ < 3 * lam / 2 := fun l => by
    linarith [hc.norm_snd_sub_centre hlam hr₀ l]
  -- the upper bound on `g_λ`
  have hup : ∀ w : ℂ, smearedKernel χ lam w ≤ -Real.log lam + kernelConst χ := fun w => by
    have h := smearedKernel_le_neg_log_max hχ hlam w
    have : Real.log lam ≤ Real.log (max ‖w‖ lam) :=
      Real.log_le_log hlam (le_max_right _ _)
    unfold kernelConst
    linarith
  -- the lower bound on `g_λ` at the cross distances
  have hlow : ∀ w : ℂ, ‖w‖ < 6 * lam * k → -Real.log (8 * k) - Real.log lam ≤
      smearedKernel χ lam w := fun w hw => by
    have h := neg_log_add_le_smearedKernel hχ hlam w
    have h8 : ‖w‖ + 2 * lam ≤ 8 * k * lam := by nlinarith
    have : Real.log (‖w‖ + 2 * lam) ≤ Real.log (8 * k) + Real.log lam := by
      rw [← Real.log_mul (by positivity) hlam.ne']
      exact Real.log_le_log (by positivity) h8
    linarith
  have h1 := hlow _ (norm_sub_lt_of_centre hlam σ (c r₀).2 (hx i) (hy j))
  have h2 := hlow _ (norm_sub_lt_of_centre hlam σ (c r₀).2 (hx j) (hy i))
  have h3 := hup ((c i).1 - (c j).1)
  have h4 := hup ((c i).2 - (c j).2)
  unfold dipoleInteraction
  linarith

end Good

/-- **Chains are connected.** If `σ : ι ≃ Fin k` and `σ⁻¹(m)` is adjacent to `σ⁻¹(m + 1)` for
every `m`, then the graph is connected. -/
theorem connected_of_chain {ι : Type*} {k : ℕ} (σ : ι ≃ Fin k) (hk : 0 < k) {G : SimpleGraph ι}
    (hadj : ∀ i j : ι, (σ j : ℕ) = σ i + 1 → G.Adj i j) : G.Connected := by
  have hreach : ∀ m (hm : m < k), G.Reachable (σ.symm ⟨0, hk⟩) (σ.symm ⟨m, hm⟩) := by
    intro m
    induction m with
    | zero => intro hm; exact SimpleGraph.Reachable.refl _
    | succ m ih =>
      intro hm
      refine (ih (by omega)).trans (SimpleGraph.Adj.reachable (hadj _ _ ?_))
      simp
  have hall : ∀ u, G.Reachable (σ.symm ⟨0, hk⟩) u := fun u => by
    simpa using hreach (σ u) (σ u).2
  exact (SimpleGraph.connected_iff _).2 ⟨fun u v => (hall u).symm.trans (hall v), ⟨σ.symm ⟨0, hk⟩⟩⟩

end MultipoleIntegral

end MultipoleBKT

end
