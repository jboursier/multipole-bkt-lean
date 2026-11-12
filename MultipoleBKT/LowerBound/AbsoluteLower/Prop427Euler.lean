/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.SumEuler
public import MultipoleBKT.LowerBound.AbsoluteLower.ClaimInt2

/-!
# The Eulerian majorant of one group, simplified (first step of Lemma 4.57)

The proof of Lemma 4.57:
"by combining Lemmas 4.54, 4.55 and 4.56, using (4.105) and `(1 + log_M(17t))² ≤ C_M t^{1/M}`
for `t ≥ 1`", for one group `X'` (`|S| ≤ p` for its blocks) and a configuration with
`0 < r_i ≤ ε₀ R̄`,

`𝓛_{C₁}(X') ≤ K^{|V_{X'}|} ∏_{i ∈ V_{X'}} (ε₀ R̄/r_i)^{C₀/M} 𝓛'(X')`

(`eulerMajorant_le_innerSeries`), where `𝓛'(X')` (`innerSeries`, proof of Lemma 4.57) is the series of
Lemma 4.55 (`MultipoleBKT.AbsoluteLower.lemma_4_55_route`) without the factors
`∏_i (1 + log_M(17 ε₀ R̄/r_i))² exp(2C₁ ∑_{ℰ^inter} a^abs) ∏_i (1 + ∑_j ḡ_ij)`, which are bounded by
`K^{|V_{X'}|} ∏_i (ε₀ R̄/r_i)^{C₀/M}` with Lemma 4.56 (`MultipoleBKT.AbsoluteLower.lemma_4_56`).
Here `C₀ = 2 + 2 C₁ C₄` does not depend on `M` (`C₄` the constant of Lemma 4.56), and `K` depends on
`M`, `C₁` and `p`.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity Peeling

/-! ### `(1 + log_M(17t))² ≤ C_M t^{1/M}` -/

/-- `(1 + log_M(17t))² ≤ C_M t^{1/M}` for `t ≥ 1` and `M > 1`. -/
theorem exists_one_add_logb_sq_le {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → (1 + Real.logb M (17 * t)) ^ 2 ≤ C * t ^ (1 / M) := by
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hM0 : 0 < M := by linarith
  set K : ℝ := 1 + Real.log 17 / Real.log M + 2 * M / Real.log M with hK
  have h17 : 0 ≤ Real.log 17 := Real.log_nonneg (by norm_num)
  have hK1 : 1 ≤ K := by
    have : 0 ≤ Real.log 17 / Real.log M := div_nonneg h17 hlogM.le
    have : 0 ≤ 2 * M / Real.log M := by positivity
    linarith
  refine ⟨K ^ 2, one_le_pow₀ hK1, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  set s := t ^ (1 / (2 * M)) with hs
  have hs1 : 1 ≤ s := Real.one_le_rpow ht (by positivity)
  -- `log t ≤ 2M s`
  have hlog : Real.log t ≤ 2 * M * s := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 (1 / (2 * M)))
    rw [Real.log_rpow ht0] at h1
    have h2 : Real.log t = 2 * M * (1 / (2 * M) * Real.log t) := by field_simp
    rw [h2]
    nlinarith
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  have hb0 : 0 ≤ Real.logb M (17 * t) :=
    Real.logb_nonneg hM (by nlinarith)
  have hb : 1 + Real.logb M (17 * t) ≤ K * s := by
    rw [Real.logb, Real.log_mul (by norm_num) ht0.ne', add_div]
    have e1 : Real.log 17 / Real.log M ≤ Real.log 17 / Real.log M * s :=
      le_mul_of_one_le_right (div_nonneg h17 hlogM.le) hs1
    have e2 : Real.log t / Real.log M ≤ 2 * M / Real.log M * s := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hlogM]
      linarith
    have e3 : (1 : ℝ) ≤ 1 * s := by linarith
    calc 1 + (Real.log 17 / Real.log M + Real.log t / Real.log M)
        ≤ 1 * s + (Real.log 17 / Real.log M * s + 2 * M / Real.log M * s) := by linarith
      _ = K * s := by rw [hK]; ring
  have hss : s ^ 2 = t ^ (1 / M) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    congr 1
    field_simp
    norm_num
  calc (1 + Real.logb M (17 * t)) ^ 2 ≤ (K * s) ^ 2 :=
        pow_le_pow_left₀ (by linarith) hb 2
    _ = K ^ 2 * t ^ (1 / M) := by rw [mul_pow, hss]

/-! ### The inner series `𝓛'` -/

section Inner

open scoped Classical

variable (M lam ε₀ R : ℝ) (Y : Finset (Finset ℕ))

/-- **The inner series `𝓛'(Y)`** of the proof of Lemma 4.57, at the configuration
`c`, with `R` in the role of `R̄_{β,λ}`:
`∑_{k ≥ 0} (1/k!) ∑_{X'_1, …, X'_k ⊆ Y disjoint} ∏_j (∏_{S ∈ X'_j, S ≠ Ŝ_j} r_S²
∑_{T^a_j ∈ 𝖳^{X'_j}} ∏_{T^a_j} d^{-2} 𝟙_{d ≤ 17 ε₀ R̄} 𝟙_{𝓑^c})
∑_{T̃^b ∈ 𝖳_0^{Coarse_Y(X')}} ∏_{T̃^b} b^abs`
This retained interface gives the unrestricted series.
`sourceInnerSeries` imposes the paper's zero value on outer groups of at most one block. -/
noncomputable def innerSeries (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑' n : ℕ, 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => Y.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      (∏ l, prodExceptMax c (Xs l) * ∑ T ∈ relTreePairs (Xs l), ∏ p ∈ T, keptPair M lam ε₀ R c p) *
        ∑ Tb ∈ relTreePairs₀ (coarsen Y (Finset.univ.image Xs)),
          ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2)

/-- The factors `∏_i (1 + log_M(17 ε₀ R̄/r_i))² exp(2C₁ ∑_{ℰ^inter} a^abs) ∏_i (1 + ∑_j ḡ_ij)` of
`H_Y` (display (4.96)). -/
noncomputable def logExpFactor (C₁ : ℝ) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ i ∈ Y.biUnion id, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2) *
    Real.exp (2 * C₁ * ∑ p ∈ interPairs Y, absOddWeight M lam ε₀ R (c p.1) (c p.2)) *
    ∏ i ∈ Y.biUnion id, (1 + ∑ j ∈ (Y.biUnion id).erase i, gbar M lam ε₀ R c i j)

end Inner

variable {M lam ε₀ R : ℝ}

theorem innerSeries_nonneg (Y : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ innerSeries M lam ε₀ R Y c := by
  unfold innerSeries
  refine tsum_nonneg fun n => mul_nonneg (by positivity) (sum_nonneg fun Xs _ => mul_nonneg
    (prod_nonneg fun l _ => mul_nonneg (prodExceptMax_nonneg _) (sum_nonneg fun T _ =>
      prod_nonneg fun p _ => keptPair_nonneg p)) (sum_nonneg fun T _ => prod_nonneg fun p _ =>
        absEvenWeight_nonneg _ _ _ _ _ _))

open scoped Classical in
/-- `H_Y(X') = (inner term) · (log-exp factor)`. -/
theorem eulerTreeMajorant_eq (C₁ : ℝ) (Y : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    eulerTreeMajorant M lam ε₀ R C₁ Y Xs c =
      ((∏ l, prodExceptMax c (Xs l) * ∑ T ∈ relTreePairs (Xs l), ∏ p ∈ T, keptPair M lam ε₀ R c p) *
        ∑ Tb ∈ relTreePairs₀ (coarsen Y (Finset.univ.image Xs)),
          ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (c p.1) (c p.2)) *
        logExpFactor M lam ε₀ R Y C₁ c := by
  unfold eulerTreeMajorant logExpFactor
  ring

/-! ### The log-exp factor -/

open scoped Classical in
/-- **The log-exp factor**, on a configuration with `0 < r_i ≤ ε₀ R` whose blocks are unlinked:
`(log-exp factor) ≤ K^{|V_Y|} ∏_i (ε₀R/r_i)^{C₀/M}`, `C₀ = 2 + 2C₁C₄` (Lemma 4.56 and
`(1 + log_M(17t))² ≤ C_M t^{1/M}`). -/
theorem exists_logExpFactor_le (p : ℕ) {C₁ : ℝ} (hC₁ : 0 ≤ C₁) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {M : ℝ}, 20 < M → ∃ K : ℝ, 1 ≤ K ∧
      ∀ (lam ε₀ R : ℝ) {Y : Finset (Finset ℕ)}, IsSubpartition Y → (∀ S ∈ Y, S.card ≤ p) →
      ∀ c : ℕ → ℂ × ℂ,
        (∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
        (∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id, ¬ SameBlock Y i j →
          ¬ MultipoleLinked M lam (c i) (c j)) →
        logExpFactor M lam ε₀ R Y C₁ c ≤ K ^ (Y.biUnion id).card *
          ∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) := by
  obtain ⟨C₄, hC₄, h456⟩ := lemma_4_56 p
  refine ⟨2 + 2 * C₁ * C₄, by positivity, fun {M} hM => ?_⟩
  have hM0 : 0 < M := by linarith
  obtain ⟨CL, hCL1, hlog⟩ := exists_one_add_logb_sq_le (M := M) (by linarith)
  set a := 2 * C₁ * C₄ / M with ha
  have ha0 : 0 ≤ a := by positivity
  set K := CL * (Real.exp a * 17 ^ a) * max 1 (C₄ * M) with hK
  have h17 : 1 ≤ (17 : ℝ) ^ a := Real.one_le_rpow (by norm_num) ha0
  have hK1 : 1 ≤ K := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCL1
    (one_le_mul_of_one_le_of_one_le (Real.one_le_exp ha0) h17)) (le_max_left _ _)
  refine ⟨K, hK1, fun lam ε₀ R Y hY hYp c hpos hunl => ?_⟩
  obtain ⟨hsum, hgbar⟩ := h456 hM lam ε₀ R hY hYp c hpos hunl
  set V := Y.biUnion id with hV
  set t : ℕ → ℝ := fun i => ε₀ * R / ‖(c i).1 - (c i).2‖ with ht
  have ht1 : ∀ i ∈ V, 1 ≤ t i := fun i hi => (one_le_div (hpos i hi).1).2 (hpos i hi).2
  have ht0 : ∀ i ∈ V, 0 < t i := fun i hi => zero_lt_one.trans_le (ht1 i hi)
  have h17t : ∀ i, 17 * ε₀ * R / ‖(c i).1 - (c i).2‖ = 17 * t i := fun i => by
    simp only [ht]
    ring
  -- the logarithms
  have hL : ∏ i ∈ V, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2 ≤
      ∏ i ∈ V, (CL * t i ^ (1 / M)) := by
    refine prod_le_prod₀ (fun i _ => sq_nonneg _) fun i hi => ?_
    rw [h17t]
    exact hlog (t i) (ht1 i hi)
  -- the exponential
  have hE : Real.exp (2 * C₁ * ∑ q ∈ interPairs Y, absOddWeight M lam ε₀ R (c q.1) (c q.2)) ≤
      ∏ i ∈ V, (Real.exp a * 17 ^ a * t i ^ a) := by
    have h1 := sum_interPairs_absOddWeight_le Y M lam ε₀ R c
    have h2 : ∑ i ∈ V, ∑ j ∈ V.filter (fun j => ¬ SameBlock Y i j),
        absOddWeight M lam ε₀ R (c i) (c j) *
          (if ‖(c i).1 - (c i).2‖ ≤ ‖(c j).1 - (c j).2‖ then 1 else 0) ≤
        ∑ i ∈ V, C₄ / M * (Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1) :=
      sum_le_sum fun i hi => hsum i hi
    have h3 : Real.exp (2 * C₁ * ∑ i ∈ V, C₄ / M *
        (Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1)) =
        ∏ i ∈ V, (Real.exp a * 17 ^ a * t i ^ a) := by
      rw [mul_sum, Real.exp_sum]
      refine prod_congr rfl fun i hi => ?_
      have hpos17 : 0 < 17 * t i := by have := ht0 i hi; positivity
      rw [h17t, mul_assoc (Real.exp a), ← Real.mul_rpow (by norm_num) (ht0 i hi).le,
        Real.rpow_def_of_pos hpos17, ← Real.exp_add]
      congr 1
      simp only [ha]
      ring
    calc Real.exp (2 * C₁ * ∑ q ∈ interPairs Y, absOddWeight M lam ε₀ R (c q.1) (c q.2))
        ≤ Real.exp (2 * C₁ * ∑ i ∈ V, C₄ / M *
            (Real.log (17 * ε₀ * R / ‖(c i).1 - (c i).2‖) + 1)) := by
          gcongr
          exact h1.trans h2
      _ = _ := h3
  -- the factors `1 + ∑ ḡ`
  have hG : ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) ≤
      ∏ i ∈ V, (max 1 (C₄ * M) * t i ^ (1 / M)) := by
    refine hgbar.trans ?_
    rw [prod_mul_distrib, prod_const]
    have : (C₄ * M) ^ V.card ≤ max 1 (C₄ * M) ^ V.card :=
      pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    exact mul_le_mul_of_nonneg_right this (prod_nonneg fun i hi =>
      Real.rpow_nonneg (ht0 i hi).le _)
  -- assembling
  have hA0 : 0 ≤ ∏ i ∈ V, (CL * t i ^ (1 / M)) :=
    prod_nonneg fun i hi => mul_nonneg (by linarith) (Real.rpow_nonneg (ht0 i hi).le _)
  have hB0 : 0 ≤ ∏ i ∈ V, (Real.exp a * 17 ^ a * t i ^ a) :=
    prod_nonneg fun i hi => by have := ht0 i hi; positivity
  have hG0 : 0 ≤ ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j) :=
    prod_nonneg fun i _ => add_nonneg zero_le_one (sum_nonneg fun j _ => gbar_nonneg _ _)
  unfold logExpFactor
  calc (∏ i ∈ V, (1 + Real.logb M (17 * ε₀ * R / ‖(c i).1 - (c i).2‖)) ^ 2) *
        Real.exp (2 * C₁ * ∑ q ∈ interPairs Y, absOddWeight M lam ε₀ R (c q.1) (c q.2)) *
        ∏ i ∈ V, (1 + ∑ j ∈ V.erase i, gbar M lam ε₀ R c i j)
      ≤ (∏ i ∈ V, (CL * t i ^ (1 / M))) * (∏ i ∈ V, (Real.exp a * 17 ^ a * t i ^ a)) *
          ∏ i ∈ V, (max 1 (C₄ * M) * t i ^ (1 / M)) :=
        mul_le_mul (mul_le_mul hL hE (Real.exp_pos _).le hA0) hG hG0 (mul_nonneg hA0 hB0)
    _ = ∏ i ∈ V, (K * t i ^ ((2 + 2 * C₁ * C₄) / M)) := by
        rw [← prod_mul_distrib, ← prod_mul_distrib]
        refine prod_congr rfl fun i hi => ?_
        have hti := ht0 i hi
        have hexp : t i ^ ((2 + 2 * C₁ * C₄) / M) = t i ^ (1 / M) * t i ^ a * t i ^ (1 / M) := by
          rw [← Real.rpow_add hti, ← Real.rpow_add hti]
          congr 1
          simp only [ha]
          ring
        rw [hexp, hK]
        ring
    _ = K ^ V.card * ∏ i ∈ V, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((2 + 2 * C₁ * C₄) / M) := by
        rw [prod_mul_distrib, prod_const]

/-! ### The majorant `𝓛_{C₁}` of one group -/

/-- If no inter-block pair of `Y` is linked, then no two dipoles of distinct blocks are. -/
theorem not_linked_of_interPairs {Y : Finset (Finset ℕ)} {c : ℕ → ℂ × ℂ}
    (hl : ∀ q ∈ interPairs Y, ¬ MultipoleLinked M lam (c q.1) (c q.2)) :
    ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id, ¬ SameBlock Y i j →
      ¬ MultipoleLinked M lam (c i) (c j) := by
  intro i hi j hj hij
  have hnot : ∀ a b : ℕ, a ∈ Y.biUnion id → b ∈ Y.biUnion id → a < b → ¬ SameBlock Y a b →
      (a, b) ∈ interPairs Y := fun a b ha hb hab hs => by
    rw [mem_interPairs, mem_pairsOn]
    refine ⟨⟨ha, hb, hab⟩, ?_⟩
    rintro ⟨B, hB, hpB⟩
    exact hs ⟨B, hB, (mem_pairsOn.1 hpB).1, (mem_pairsOn.1 hpB).2.1⟩
  rcases lt_trichotomy i j with h | h | h
  · exact hl _ (hnot i j hi hj h hij)
  · subst h
    obtain ⟨S, hS, hiS⟩ := mem_biUnion.1 hi
    exact absurd ⟨S, hS, hiS, hiS⟩ hij
  · intro hlink
    refine hl _ (hnot j i hj hi h fun ⟨S, hS, h1, h2⟩ => hij ⟨S, hS, h2, h1⟩) ?_
    exact Multipole.multipoleLinked_comm.2 hlink

open scoped Classical in
/-- **The majorant of one group, simplified** (proof of Lemma 4.57, see the module
docstring): for `M > 20` and `0 < r_i ≤ ε₀ R` on `V_Y`,
`𝓛_{C₁}(Y) ≤ K^{|V_Y|} ∏_{i ∈ V_Y} (ε₀R/r_i)^{C₀/M} 𝓛'(Y)`. -/
theorem eulerMajorant_le_innerSeries (p : ℕ) {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {M : ℝ}, 20 < M → ∃ K : ℝ, 1 ≤ K ∧
      ∀ (lam ε₀ R : ℝ), 0 < lam → ∀ {Y : Finset (Finset ℕ)}, IsSubpartition Y →
      (∀ S ∈ Y, S.card ≤ p) → ∀ c : ℕ → ℂ × ℂ,
        (∀ i ∈ Y.biUnion id, 0 < ‖(c i).1 - (c i).2‖ ∧ ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
        eulerMajorant M lam ε₀ R C₁ Y c ≤ K ^ (Y.biUnion id).card *
          (∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
            innerSeries M lam ε₀ R Y c := by
  obtain ⟨C₀, hC₀, hLEG⟩ := exists_logExpFactor_le p (by linarith : 0 ≤ C₁)
  obtain ⟨C₅, hC₅, h455⟩ := lemma_4_55_route p hC₁
  refine ⟨C₀, hC₀, fun {M} hM => ?_⟩
  obtain ⟨K, hK1, hK⟩ := hLEG hM
  have hE1 : 1 ≤ Real.exp C₅ := Real.one_le_exp hC₅.le
  refine ⟨Real.exp C₅ * K, one_le_mul_of_one_le_of_one_le hE1 hK1,
    fun lam ε₀ R hlam Y hY hYp c hpos => ?_⟩
  have hP0 : 0 ≤ ∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M) :=
    prod_nonneg fun i hi => Real.rpow_nonneg (div_nonneg ((hpos i hi).1.le.trans (hpos i hi).2)
      (norm_nonneg _)) _
  have hI0 := innerSeries_nonneg (M := M) (lam := lam) (ε₀ := ε₀) (R := R) Y c
  by_cases hl : ∃ q ∈ interPairs Y, MultipoleLinked M lam (c q.1) (c q.2)
  · rw [eulerMajorant_eq_zero_of_linked hl]
    have : (0 : ℝ) ≤ Real.exp C₅ * K := by positivity
    positivity
  push Not at hl
  have hunl := not_linked_of_interPairs hl
  have h1 := h455 M lam ε₀ R (by linarith) hlam hY hYp c hpos
  have h2 : ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => Y.powerset).filter
          (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
        eulerTreeMajorant M lam ε₀ R C₁ Y Xs c =
      innerSeries M lam ε₀ R Y c * logExpFactor M lam ε₀ R Y C₁ c := by
    unfold innerSeries
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [mul_assoc, sum_mul]
    congr 1
    exact sum_congr rfl fun Xs _ => eulerTreeMajorant_eq C₁ Y Xs c
  rw [h2] at h1
  have h3 := hK lam ε₀ R hY hYp c hpos hunl
  have hexp : Real.exp (C₅ * (Y.biUnion id).card) = Real.exp C₅ ^ (Y.biUnion id).card := by
    rw [← Real.exp_nat_mul, mul_comm]
  calc eulerMajorant M lam ε₀ R C₁ Y c
      ≤ Real.exp (C₅ * (Y.biUnion id).card) *
          (innerSeries M lam ε₀ R Y c * logExpFactor M lam ε₀ R Y C₁ c) := h1
    _ ≤ Real.exp (C₅ * (Y.biUnion id).card) * (innerSeries M lam ε₀ R Y c *
          (K ^ (Y.biUnion id).card *
            ∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M))) := by
        gcongr
    _ = (Real.exp C₅ * K) ^ (Y.biUnion id).card *
          (∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ (C₀ / M)) *
            innerSeries M lam ε₀ R Y c := by
        rw [hexp, mul_pow]
        ring

end AbsoluteLower

end MultipoleBKT

end
