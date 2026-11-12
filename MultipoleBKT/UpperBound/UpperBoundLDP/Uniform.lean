/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.GoodEstimates
public import MultipoleBKT.UpperBound.ExpansionPlus.Proposition
public import MultipoleBKT.UpperBound.NonEmptyMarks.Statement
public import MultipoleBKT.Appendix.GeneralExpansionK.LemmaA8Plus
public import MultipoleBKT.Appendix.GeneralExpansionK.LemmaA8Bis
public import MultipoleBKT.LowerBound.ExpansionErrors.KDiff
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole
public import MultipoleBKT.UpperBound.AbsoluteUpper.Bounded

/-!
# Proposition 5.43: the estimates of §4–5 uniformly in the sizes `k ≤ p(β)`

The paper: proof of Proposition 5.43, which uses, for the finitely many block and cluster sizes `k ≤ p(β)`:

* `prop_5_19_uniform`: Proposition 5.19 (Proposition 5.19, (5.68) and (5.69) for the hatted
  objects), from `MultipoleBKT.UpperBound.ExpansionPlus.prop_5_19_of_inputs` with its inputs
  proved: Lemma A.7 for `(v^Z, τ^Z)` (`MultipoleBKT.ExpansionK.lemmaA8Plus_holds`), Lemma A.7
  (A.50) (`MultipoleBKT.ExpansionK.lemmaA8Bis_holds`) and the claim (5.106)
  (`MultipoleBKT.UpperBound.NonEmptyMarks.nonEmptyMarks_holds`). The constant `C` in front of
  `ε₀^{α(β)k} |V_bad|/N` does not depend on `ε₀`;
* `zero_M_diff_uniform`: `|𝖬^0_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C_{ε₀} N^{1-|S|} R̄^{-2}`
  (`MultipoleBKT.UpperBoundLDP.zero_M_diff`);
* `K_diff0_uniform`: eq. (4.45) of Proposition 4.24
  (`MultipoleBKT.ExpansionErrors.eq_K_diff0_of_lemma_A8`, with Lemma A.7 (A.50));
* `zero_lower_uniform`: the lower bound (4.38) for `𝖬^0_{ε₀}`
  (`MultipoleBKT.BoundedLowerEps.zeroPartitionFunction_two_sided`), whose constant does not depend
  on `ε₀`.

Each is the conjunction over the sizes `k ≤ p(β)` of the statement for one size, with the maximum
of the thresholds and the sum of the constants.
-/

@[expose] public section

open Finset Filter

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical UpperBound

variable {χ : ℂ → ℝ} {β : ℝ}

/-! ### Proposition 5.19 -/

/-- The inputs of `ExpansionPlus.prop_5_19_of_inputs` hold, for `M ≥ 3` and `2 ≤ k ≤ p(β)`. -/
theorem prop_5_19_inputs_hold (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    {M : ℝ} (hM : 3 ≤ M) {k : ℕ} (hkp : k ≤ pBeta p₀ β) :
    ExpansionPlus.LemmaA8PlusStatement χ β M L p₀ k ∧
      ExpansionErrors.LemmaA8BisStatement χ β M p₀ k ∧
      ExpansionPlus.NonEmptyMarksStatement χ β M L p₀ k := by
  have hk := TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp
  exact ⟨ExpansionK.lemmaA8Plus_holds hχ hβ M L p₀ hk,
    ExpansionK.lemmaA8Bis_holds hχ hβ (by linarith) p₀ hk,
    NonEmptyMarks.nonEmptyMarks_holds hχ hβ p₀ L hM k⟩

/-- The two bounds of Proposition 5.19 for one size `s`, with the constants `C` (in front of
`ε₀^{α(β)s} |V_bad|/N`) and `C_{ε₀}` (in front of `R̄^{-2}`). -/
def Prop519At (χ : ℂ → ℝ) (p₀ : ℕ) (β M ε₀ L C : ℝ) (s : ℕ) (Cε lam : ℝ) (N : ℕ) : Prop :=
  1 ≤ N → 0 < lam → ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
    badPointsOn p₀ β lam M ε₀ V Z = V →
    (∀ S : Finset ℕ, S ⊆ BoundedUpper.goodLabels V → S.card = s →
      |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
        (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
          C * ε₀ ^ (alphaExponent β * s) * (V.card / N)) / (N : ℝ) ^ (s - 1)) ∧
    (∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ BoundedUpper.goodLabels V →
      (X.biUnion id).card = s →
      |hatActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
        (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
            C * ε₀ ^ (alphaExponent β * s) * (V.card / N)) /
          ((N : ℝ) ^ (s - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X))

/-- `Prop519At` is monotone in both constants. -/
theorem Prop519At.mono {p₀ : ℕ} {M ε₀ L C C' : ℝ} {s : ℕ} {Cε Cε' lam : ℝ} {N : ℕ}
    (hε₀ : 0 < ε₀) (hCC' : C ≤ C') (hCεCε' : Cε ≤ Cε')
    (h : Prop519At χ p₀ β M ε₀ L C s Cε lam N) : Prop519At χ p₀ β M ε₀ L C' s Cε' lam N := by
  intro hN hlam V Z hVZ
  obtain ⟨h1, h2⟩ := h hN hlam V Z hVZ
  have hR : 0 ≤ truncationScale p₀ β lam ^ (-2 : ℝ) :=
    Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _
  have hnum : Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
      C * ε₀ ^ (alphaExponent β * s) * ((V.card : ℝ) / N) ≤
      Cε' * truncationScale p₀ β lam ^ (-2 : ℝ) +
        C' * ε₀ ^ (alphaExponent β * s) * ((V.card : ℝ) / N) := by
    have he : 0 ≤ ε₀ ^ (alphaExponent β * s) * ((V.card : ℝ) / N) := by positivity
    have := mul_le_mul_of_nonneg_right hCC' he
    have := mul_le_mul_of_nonneg_right hCεCε' hR
    nlinarith
  refine ⟨fun S hS hSs => (h1 S hS hSs).trans ?_, fun X hX hXg hXs => (h2 X hX hXg hXs).trans ?_⟩
  · exact div_le_div_of_nonneg_right hnum (by positivity)
  · exact div_le_div_of_nonneg_right hnum
      (mul_nonneg (by positivity) (AbsoluteUpper.zeroPartitionFunction_nonneg _ _ _ _ _ _ _ _))

/-- **Proposition 5.19 for all sizes `1 ≤ s ≤ p(β)`** (see the module docstring). -/
theorem prop_5_19_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ s, 1 ≤ s → s ≤ pBeta p₀ β → Prop519At χ p₀ β M ε₀ L C s Cε lam N := by
  set p := pBeta p₀ β with hp
  have E : ∀ᶠ M in atTop, ∀ k ∈ range (p + 1), (3 : ℝ) ^ p ≤ M →
      (2 ≤ k → ExpansionPlus.LemmaA8PlusStatement χ β M L p₀ k ∧
        ExpansionErrors.LemmaA8BisStatement χ β M p₀ k ∧
        ExpansionPlus.NonEmptyMarksStatement χ β M L p₀ k) →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
          (1 ≤ k → ∀ S : Finset ℕ, S ⊆ BoundedUpper.goodLabels V → S.card = k →
            |plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
                zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1) ∧
            |hatPartitionFunction χ N p₀ β lam M ε₀ L V Z S -
                zeroPartitionFunction χ N p₀ β lam M ε₀ {S}| ≤
              (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) / (N : ℝ) ^ (k - 1)) ∧
          (∀ X : Finset (Finset ℕ), IsSubpartition X →
            X.biUnion id ⊆ BoundedUpper.goodLabels V → (X.biUnion id).card = k →
            |plusActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
                (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                    C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                  ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) ∧
              |hatActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
                (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                    C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
                  ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X)) :=
    (eventually_all_finset _).2 fun k hk => by
      obtain ⟨M₀, -, hM₀⟩ := ExpansionPlus.prop_5_19_of_inputs (χ := χ) hχ hβ hp₀ L
        (Nat.lt_succ_iff.1 (mem_range.1 hk))
      exact eventually_atTop.2 ⟨M₀, hM₀⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (E.and (eventually_ge_atTop 21))
  refine ⟨max M₀ 21, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun M hM hMp => ?_⟩
  obtain ⟨hE, hM21⟩ := hM₀ M ((le_max_left _ _).trans hM)
  have hk : ∀ k ∈ range (p + 1), ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          1 ≤ k → Prop519At χ p₀ β M ε₀ L C k Cε lam N := by
    intro k hkr
    obtain ⟨C, hC, h⟩ := hE k hkr hMp fun _ =>
      prop_5_19_inputs_hold hχ hβ hp₀ L (by linarith) (Nat.lt_succ_iff.1 (mem_range.1 hkr))
    refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
    obtain ⟨Cε, hCε, lam₀, hlam₀, h'⟩ := h ε₀ hε₀ hε₁
    refine ⟨Cε, hCε, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
    obtain ⟨N₀, hN₀⟩ := h' lam hlam hlt
    refine ⟨N₀, fun N hN hk1 _ _ V Z hVZ => ?_⟩
    obtain ⟨h1, h2⟩ := hN₀ N hN V Z hVZ
    exact ⟨fun S hS hSk => (h1 hk1 S hS hSk).2, fun X hX hXg hXk => (h2 X hX hXg hXk).2⟩
  choose! C hC hCrest using hk
  set Cs : ℝ := ∑ k ∈ range (p + 1), C k with hCs
  have hCs0 : 0 < Cs := by
    have h0 : C 0 ≤ Cs := single_le_sum (f := C) (fun k hk => (hC k hk).le)
      (mem_range.2 (Nat.succ_pos p))
    linarith [hC 0 (mem_range.2 (Nat.succ_pos p))]
  have hCle : ∀ k ∈ range (p + 1), C k ≤ Cs := fun k hk =>
    single_le_sum (f := C) (fun k hk => (hC k hk).le) hk
  refine ⟨Cs, hCs0, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cε, hCε, lam₀, hlam₀, hU⟩ := ExpansionErrors.exists_uniform
    (fun s Cε lam N => Prop519At χ p₀ β M ε₀ L Cs s Cε lam N)
    (fun s Cε Cε' lam N h hP => Prop519At.mono hε₀ le_rfl h hP) p fun s hs1 hsp => by
      have hsr : s ∈ range (p + 1) := mem_range.2 (Nat.lt_succ_of_le hsp)
      obtain ⟨Cε, hCε, l, hl, h⟩ := hCrest s hsr ε₀ hε₀ hε₁
      refine ⟨Cε, hCε, l, hl, fun lam hlam hlt => ?_⟩
      obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
      exact ⟨N₀, fun N hN => Prop519At.mono hε₀ (hCle s hsr) le_rfl (hN₀ N hN hs1)⟩
  exact ⟨Cε, hCε, lam₀, hlam₀, hU⟩

/-! ### `|𝖬^0_{ε₀} - 𝖬^0_∞|` and (4.45) -/

/-- **`|𝖬^0_{ε₀}(S) - 𝖬^0_∞(S)| ≤ C N^{1-|S|} R̄^{-2}` for all sizes `1 ≤ s ≤ p(β)`.** -/
theorem zero_M_diff_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {M : ℝ}
    (hM : 0 ≤ M) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₁ : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
        ∀ S : Finset ℕ, S.card = s →
          |zeroPartitionFunction χ N p₀ β lam M ε₀ {S} -
              multipolePartitionFunction χ N β lam M S| ≤
            C / (N : ℝ) ^ (s - 1) * truncationScale p₀ β lam ^ (-2 : ℝ) := by
  obtain ⟨C, hC, lam₀, hlam₀, h⟩ := ExpansionErrors.exists_uniform
    (fun s C lam N => 0 < lam → ∀ S : Finset ℕ, S.card = s →
      |zeroPartitionFunction χ N p₀ β lam M ε₀ {S} - multipolePartitionFunction χ N β lam M S| ≤
        C / (N : ℝ) ^ (s - 1) * truncationScale p₀ β lam ^ (-2 : ℝ))
    (fun s C C' lam N hCC' h hlam S hS => (h hlam S hS).trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hCC' (by positivity))
      (Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _)))
    (pBeta p₀ β) fun s hs1 hsp => by
      obtain ⟨C, hC, l, hl, -, h⟩ := zero_M_diff hχ hβ hs1
        (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hsp) hM p₀ ε₀ hε₀ hε₁
      refine ⟨C, hC, l, hl, fun lam hlam hlt => ?_⟩
      obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
      exact ⟨N₀, fun N hN _ S hS => hN₀ N hN S hS⟩
  refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
  exact ⟨N₀, fun N hN s hs1 hsp => hN₀ N hN s hs1 hsp hlam⟩

open scoped Classical in
/-- **Eq. (4.45) for all sizes `1 ≤ s ≤ p(β)`** (with Lemma A.7 (A.50)). -/
theorem K_diff0_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ pBeta p₀ β →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = s →
            |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (s - 1)) := by
  set p := pBeta p₀ β with hp
  have E : ∀ᶠ M in atTop, ∀ k ∈ Finset.Icc 2 p,
      ExpansionErrors.LemmaA8BisStatement χ β M p₀ k →
      ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ Finset.range N →
            1 < X.card → (X.biUnion id).card = k →
            |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
              C * truncationScale p₀ β lam ^ (-2 : ℝ) /
                ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (k - 1)) :=
    (eventually_all_finset _).2 fun k hk => by
      obtain ⟨hk2, hkp⟩ := mem_Icc.1 hk
      obtain ⟨M₀, -, hM₀⟩ := ExpansionErrors.eq_K_diff0_of_lemma_A8 hχ hβ hk2
        (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp) p₀
      exact eventually_atTop.2 ⟨M₀, hM₀⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 (E.and (eventually_ge_atTop 21))
  refine ⟨max M₀ 21, lt_of_lt_of_le (by norm_num) (le_max_right _ _),
    fun M hM ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨hE, hM21⟩ := hM₀ M ((le_max_left _ _).trans hM)
  obtain ⟨C, hC, lam₀, hlam₀, h⟩ := ExpansionErrors.exists_uniform
    (fun s C lam N => 0 < lam → ∀ X : Finset (Finset ℕ), IsSubpartition X →
      X.biUnion id ⊆ Finset.range N → 1 < X.card → (X.biUnion id).card = s →
        |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
          C * truncationScale p₀ β lam ^ (-2 : ℝ) /
            ((∏ S ∈ X, multipolePartitionFunction χ N β lam M S) * (N : ℝ) ^ (s - 1)))
    (fun s C C' lam N hCC' h hlam X hX hXN h1 hs => (h hlam X hX hXN h1 hs).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC'
        (Real.rpow_nonneg (Appendix.truncationScale_pos hlam).le _))
        (mul_nonneg (prod_nonneg fun S _ => multipolePartitionFunction_nonneg χ N β lam M S)
          (by positivity))))
    p fun s hs1 hsp => by
      rcases Nat.lt_or_ge s 2 with hs2 | hs2
      · refine ⟨1, one_pos, 1, one_pos, fun lam _ _ => ⟨0, fun N _ _ X hX _ h1 hs => ?_⟩⟩
        have := PropFiveFortyFive.card_le_card_biUnion hX
        omega
      · obtain ⟨C, hC, l, hl, -, h⟩ := hE s (mem_Icc.2 ⟨hs2, hsp⟩)
          (ExpansionK.lemmaA8Bis_holds hχ hβ (by linarith) p₀
            (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hsp)) ε₀ hε₀ hε₁
        refine ⟨C, hC, l, hl, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
        exact ⟨N₀, fun N hN _ X hX hXN h1 hs => hN₀ N hN X hX hXN h1 hs⟩
  refine ⟨C, hC, lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
  exact ⟨N₀, fun N hN s hs1 hsp => hN₀ N hN s hs1 hsp hlam⟩

/-! ### The lower bound (4.38) for `𝖬^0_{ε₀}` -/

/-- **(4.38) for `𝖬^0_{ε₀}`, for all sizes `2 ≤ |S| ≤ p(β)`**, with a constant `C_z ≥ 1` not
depending on `ε₀`. -/
theorem zero_lower_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {M : ℝ}
    (hM : 20 < M) :
    ∃ Cz : ℝ, 1 ≤ Cz ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, 2 ≤ S.card → S.card ≤ pBeta p₀ β →
          lam ^ (2 * (S.card - 1)) / (Cz * (N : ℝ) ^ (S.card - 1)) ≤
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
  set p := pBeta p₀ β with hp
  have hk : ∀ k ∈ Finset.Icc 2 p, ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ (p₀' : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ S : Finset ℕ, S.card = k →
            lam ^ (2 * (k - 1)) / (C * (N : ℝ) ^ (k - 1)) ≤
                zeroPartitionFunction χ N p₀' β lam M ε₀ {S} ∧
              zeroPartitionFunction χ N p₀' β lam M ε₀ {S} ≤
                C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := fun k hk =>
    BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ (mem_Icc.1 hk).1
      (TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ (mem_Icc.1 hk).2) hM
  choose! C hC hCrest using hk
  set Cz : ℝ := 1 + ∑ k ∈ Finset.Icc 2 p, C k with hCz
  have hCz1 : 1 ≤ Cz := le_add_of_nonneg_right (sum_nonneg fun k hk => (hC k hk).le)
  have hCle : ∀ k ∈ Finset.Icc 2 p, C k ≤ Cz := fun k hk => by
    have := single_le_sum (f := C) (fun k hk => (hC k hk).le) hk
    linarith
  refine ⟨Cz, hCz1, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lam₀, hlam₀, h⟩ := AbsoluteUpper.exists_lam_N_forall_le
    (P := fun k lam N => k ∈ Finset.Icc 2 p → ∀ S : Finset ℕ, S.card = k →
      lam ^ (2 * (k - 1)) / (Cz * (N : ℝ) ^ (k - 1)) ≤
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) p fun k _ => by
      by_cases hkI : k ∈ Finset.Icc 2 p
      · obtain ⟨l, hl, -, h⟩ := hCrest k hkI ε₀ hε₀ hε₁
        refine ⟨l, hl, fun lam hlam hlt => ?_⟩
        obtain ⟨N₀, hN₀⟩ := h p₀ lam hlam hlt
        refine ⟨N₀, fun N hN _ S hS => le_trans ?_ (hN₀ N hN S hS).1⟩
        rcases Nat.eq_zero_or_pos N with hN0 | hN0
        · subst hN0
          have hk1 : k - 1 ≠ 0 := by have := (mem_Icc.1 hkI).1; omega
          simp [zero_pow hk1]
        · have hNk : (0 : ℝ) < (N : ℝ) ^ (k - 1) := by positivity
          exact div_le_div_of_nonneg_left (by positivity) (mul_pos (hC k hkI) hNk)
            (mul_le_mul_of_nonneg_right (hCle k hkI) hNk.le)
      · exact ⟨1, one_pos, fun _ _ _ => ⟨0, fun _ _ h => absurd h hkI⟩⟩
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h lam hlam hlt
  exact ⟨N₀, fun N hN S hS2 hSp => hN₀ N hN S.card hSp (mem_Icc.2 ⟨hS2, hSp⟩) S rfl⟩

end UpperBoundLDP

end MultipoleBKT

end
