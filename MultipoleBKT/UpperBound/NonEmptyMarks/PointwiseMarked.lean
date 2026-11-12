/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.PointwiseGain
public import MultipoleBKT.UpperBound.NonEmptyMarks.RouteGain.Parity

/-!
# The three nonempty-mark cases

The paper: (5.106).

An even external mark gives `cosh(β S_i) - 1 ≤ C(r_i/d_i,bad)²`.
When all external marks are odd, a mark in an odd component gives the
gain through `pointwise_bound_gain`. Otherwise a marked multipole has
no odd edge, so parity gives two distinct marks there. Removing both
preserves parity and their product supplies the quadratic gain.

In each case `abs_markedTerm_eq_mul_oddSeparation` retains every
inter-block separation indicator from the raw groups. The first and
third cases use `pointwise_separated_family_bound`. The second uses
the marked family estimate. Replacement-tree tails are bounded by one
after the component estimates, leaving `extGain * jIntegrandNT`.
All prefactors are chosen before `ε₀`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Hierarchical Multipole Parity BoundedUpper SetPartition

open scoped Classical

variable {χ : ℂ → ℝ}

/-! ### The arithmetic of the cases -/

section Arith

variable {M lam ε₀ R : ℝ}

theorem jTail_le_one' (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id)) :
    jTail c X Xs Ta ≤ 1 := by
  unfold jTail
  refine pow_le_one₀ (div_nonneg (blockRad_nonneg c _) (le_max_of_le_right
    (blockRad_nonneg c _))) ?_
  exact div_le_one_of_le₀ (le_max_right _ _) (le_max_of_le_right (blockRad_nonneg c _))

/-- `∑_{T^a} J-integrand ∏ 𝟙_{𝓑_S} ≤ ∑_{T^a} (J-integrand without tail) ∏ 𝟙_{𝓑_S}`. -/
theorem sum_jIntegrand_le (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ)
    (s : Finset (∀ l, SimpleGraph ((Xs l).biUnion id))) :
    ∑ Ta ∈ s, jIntegrand M lam ε₀ R X Xs Ta Tb c *
        ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) ≤
      ∑ Ta ∈ s, jIntegrandNT M lam ε₀ R X Xs Ta Tb c *
        ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
  refine Finset.sum_le_sum fun Ta _ => mul_le_mul_of_nonneg_right ?_
    (prod_nonneg fun S _ => by split_ifs <;> norm_num)
  have e : jIntegrand M lam ε₀ R X Xs Ta Tb c =
      jTail c X Xs Ta * jIntegrandNT M lam ε₀ R X Xs Ta Tb c := by
    unfold jIntegrand jIntegrandNT
    ring
  rw [e]
  exact mul_le_of_le_one_left (jIntegrandNT_nonneg M lam ε₀ R X Xs Ta Tb c) (jTail_le_one' c X Xs Ta)

/-- The arithmetic of the cases with a gain factor `f ≤ C G` in front of a reduced term. -/
theorem case_arith {bw mT rT f C G K₁ K₀ S₁ S₂ S₃ : ℝ} (hbw : 0 ≤ bw) (hrT : 0 ≤ rT)
    (hmT : mT ≤ f * rT) (hf0 : 0 ≤ f) (hf : f ≤ C * G) (hb : bw * rT ≤ K₁ * S₁) (hS : S₁ ≤ S₂)
    (hK₁ : 0 ≤ K₁) (hG : 0 ≤ G) (hC : 0 ≤ C) (hS₃ : G * S₂ = S₃) (hK : K₁ * C ≤ K₀)
    (hS₃0 : 0 ≤ S₃) : bw * mT ≤ K₀ * S₃ := by
  have h0 : 0 ≤ K₁ * S₁ := (mul_nonneg hbw hrT).trans hb
  calc bw * mT ≤ bw * (f * rT) := mul_le_mul_of_nonneg_left hmT hbw
    _ = f * (bw * rT) := by ring
    _ ≤ f * (K₁ * S₁) := mul_le_mul_of_nonneg_left hb hf0
    _ ≤ (C * G) * (K₁ * S₁) := mul_le_mul_of_nonneg_right hf h0
    _ ≤ (C * G) * (K₁ * S₂) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hK₁) (mul_nonneg hC hG)
    _ = (K₁ * C) * (G * S₂) := by ring
    _ = (K₁ * C) * S₃ := by rw [hS₃]
    _ ≤ K₀ * S₃ := mul_le_mul_of_nonneg_right hK hS₃0

end Arith

/-! ### The pointwise bound of a marked term -/

section Pointwise

/-- On a configuration with a dipole outside `I_good^Z`, the block weights vanish. -/
theorem prod_blockWeightOf_eq_zero {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} {X : Finset (Finset ℕ)} {c : ℕ → ℂ × ℂ}
    (hng : ¬ ∀ i ∈ X.biUnion id, IsGoodZ p₀ β lam M ε₀ V Z (c i)) :
    (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) = 0 := by
  push Not at hng
  obtain ⟨i, hi, hng⟩ := hng
  obtain ⟨B, hB, hiB⟩ := mem_biUnion_id.1 hi
  have h0 : blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c = 0 := by
    unfold blockWeightOf
    rw [Finset.prod_eq_zero hiB (by unfold dipoleWeightZ; rw [ite_eq_right hng, mul_zero]),
      mul_zero]
  exact Finset.prod_eq_zero hB h0

theorem prod_blockWeightOf_nonneg {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
    {Z : Fin N → ℂ × ℂ} (X : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ ∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c := by
  refine prod_nonneg fun B _ => ?_
  unfold blockWeightOf
  refine mul_nonneg (mul_nonneg ?_ (prod_nonneg fun p _ => stableWeight_nonneg _ _ _ _))
    (prod_nonneg fun i _ => dipoleWeightZ_nonneg _)
  split_ifs <;> norm_num

/-- **The pointwise bound of a marked term** (the display before (A.20) in the proof of the
claim (5.106)): see the module docstring. The constant `K₀` depends only on
`χ`, `p₀`, `β`, `M`, `L` and `k ≥ |V_X|`. -/
theorem pointwise_marked (hχ : IsMollifier χ) {β : ℝ} (hβ : 0 ≤ β) (p₀ : ℕ) (M L : ℝ)
    (hM3 : 3 ≤ M) (k : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z →
      ∀ X : Finset (Finset ℕ), IsSubpartition X → (X.biUnion id).card ≤ k →
      ∀ {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
      ∀ U ⊆ X.biUnion id, U.Nonempty → ∀ E₁ ∈ (univ.biUnion Es).powerset, ∀ U₁ ∈ U.powerset,
      IsParityPair X E₁ U₁ →
      ∃ (m : ℕ) (Ys : Fin m → Finset (Finset ℕ)), m ≤ k ∧ (∀ l, Ys l ⊆ X) ∧
        (∀ l l', l ≠ l' → Disjoint (Ys l) (Ys l')) ∧
        ∃ Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id),
          IsRelTree₀ (coarsen X (univ.image Ys)) Tb ∧
          ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, c i ∈ supportSet N p₀ β lam ε₀ ∧
              0 < ‖(c i).1 - (c i).2‖) →
            (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
                (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
              |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| ≤
            K₀ * ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
                (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)),
              (SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
                jIntegrandNT M lam ε₀ (truncationScale p₀ β lam) X Ys Ta Tb c) *
                ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
  obtain ⟨K₁, hK₁, hpw⟩ := BoundedUpper.RouteRaw.pointwise_separated_family_bound hχ hβ p₀ M L hM3 k
  obtain ⟨K₂, hK₂, hpg⟩ := pointwise_bound_gain hχ hβ p₀ M L hM3 k
  obtain ⟨Cc, hCc, hcosh⟩ := cosh_sub_one_le_Z hχ p₀ β
  obtain ⟨C₂, hC₂, hinf⟩ := bornesabinfty_Z hχ p₀ β
  set K₀ : ℝ := K₁ * Cc + K₁ * C₂ ^ 2 + K₂ with hK₀
  have hK₀1 : K₁ * Cc ≤ K₀ := by have := mul_nonneg hK₁.le (sq_nonneg C₂); linarith
  have hK₀2 : K₁ * C₂ ^ 2 ≤ K₀ := by have := mul_nonneg hK₁.le (by linarith : (0 : ℝ) ≤ Cc); linarith
  have hK₀3 : K₂ ≤ K₀ := by
    have := mul_nonneg hK₁.le (by linarith : (0 : ℝ) ≤ Cc)
    have := mul_nonneg hK₁.le (sq_nonneg C₂)
    linarith
  refine ⟨K₀, by positivity, ?_⟩
  intro N lam ε₀ V Z hlam hlamh hMp hVZ X hX hk n Xs hXs hXd Es hEs F hF U hU hUne E₁ hE₁ U₁ hU₁ hpar
  have hEs' : ∀ l, Es l ∈ relEdgeSets (Xs l) := Fintype.mem_piFinset.1 hEs
  have hEsi : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs' l)).1
  have hE : univ.biUnion Es ∪ F ∈ relEdgeSets₀ X := union_mem_relEdgeSets₀ hX hXs hEs' hF
  have hdisj := disjoint_biUnion_F hEsi (mem_relEdgeSets₀.1 hF).1
  have hE₁s : E₁ ⊆ univ.biUnion Es := Finset.mem_powerset.1 hE₁
  have hE₁E : E₁ ∈ (univ.biUnion Es ∪ F).powerset :=
    Finset.mem_powerset.2 (hE₁s.trans Finset.subset_union_left)
  have hE₁X : E₁ ⊆ interPairs X := hE₁s.trans ((Finset.subset_union_left).trans
    (mem_relEdgeSets₀.1 hE).1)
  have hU₁U : U₁ ⊆ U := Finset.mem_powerset.1 hU₁
  have hsep (c : ℕ → ℂ × ℂ) :
      |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| =
        |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| *
          BoundedUpper.RouteRaw.oddSeparation M lam X E₁ c :=
    BoundedUpper.RouteRaw.abs_markedTerm_eq_mul_oddSeparation hX hXs hXd hEsi hE₁s F U U₁ c
  have hsep0 (c : ℕ → ℂ × ℂ) : 0 ≤ BoundedUpper.RouteRaw.oddSeparation M lam X E₁ c :=
    BoundedUpper.RouteRaw.oddSeparation_nonneg M lam X E₁ c
  -- the common facts on a configuration
  have hRHS0 : ∀ {m : ℕ} (Ys : Fin m → Finset (Finset ℕ))
      (Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id)) (c : ℕ → ℂ × ℂ),
      0 ≤ ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
          (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)),
        (SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
          jIntegrandNT M lam ε₀ (truncationScale p₀ β lam) X Ys Ta Tb c) *
          ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) :=
    fun Ys Tb c => sum_nonneg fun Ta _ => mul_nonneg (mul_nonneg (sq_nonneg _)
      (jIntegrandNT_nonneg _ _ _ _ X Ys Ta Tb c)) (prod_nonneg fun S _ => by
        split_ifs <;> norm_num)
  have hsum : ∀ {m : ℕ} (Ys : Fin m → Finset (Finset ℕ))
      (Tb : SimpleGraph ((coarsen X (univ.image Ys)).biUnion id)) (c : ℕ → ℂ × ℂ),
      SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
        ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
          (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)),
          jIntegrandNT M lam ε₀ (truncationScale p₀ β lam) X Ys Ta Tb c *
            ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) =
      ∑ Ta ∈ (univ : Finset (∀ l, SimpleGraph ((Ys l).biUnion id))).filter
          (fun Ta => ∀ l, IsRelTree (Ys l) (Ta l)),
        (SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) *
          jIntegrandNT M lam ε₀ (truncationScale p₀ β lam) X Ys Ta Tb c) *
          ∏ S ∈ X, (if ConnOn S (linkedPairs M lam c S) then (1 : ℝ) else 0) := by
    intro m Ys Tb c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun Ta _ => by ring
  have hδX : ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, c i ∈ supportSet N p₀ β lam ε₀) →
      (∀ i ∈ X.biUnion id, IsGoodZ p₀ β lam M ε₀ V Z (c i)) →
      ∀ j ∈ X.biUnion id, lam ≤ badDistZ p₀ β lam ε₀ V Z (c j) := fun c hc hg j hj =>
    lam_le_badDistZ hlam hlamh hMp hVZ (hg j hj) (hc j hj).2
  have hratio : ∀ c : ℕ → ℂ × ℂ, (∀ i ∈ X.biUnion id, c i ∈ supportSet N p₀ β lam ε₀) →
      (∀ i ∈ X.biUnion id, IsGoodZ p₀ β lam M ε₀ V Z (c i)) → ∀ i ∈ X.biUnion id,
      0 ≤ ‖(c i).1 - (c i).2‖ / badDistZ p₀ β lam ε₀ V Z (c i) ∧
      ‖(c i).1 - (c i).2‖ / badDistZ p₀ β lam ε₀ V Z (c i) ≤
        min (univ.fold max 0 (fun j : X.biUnion id => Peeling.dipoleLength (c j)) /
          SmallIntegral.minBadDist p₀ β lam ε₀ V Z (fun j : X.biUnion id => c j)) 1 := by
    intro c hc hg i hi
    refine ⟨div_nonneg (norm_nonneg _) (hlam.trans_le (hδX c hc hg i hi)).le,
      ratio_le_gainRoot (p₀ := p₀) (β := β) (V := V) (Z := Z) hlam hlamh (hδX c hc hg) hi
        (norm_le_badDistZ hlam hlamh hMp hVZ (hg i hi) (hc i hi).2)⟩
  by_cases hA : (U \ U₁).Nonempty
  · -- an even mark
    obtain ⟨i₁, hi₁⟩ := hA
    have hi₁X : i₁ ∈ X.biUnion id := hU (Finset.mem_sdiff.1 hi₁).1
    obtain ⟨m, Ys, hm, hYs, hYd, Tb, hTb, hb⟩ := hpw lam ε₀ V Z hlam hlamh hMp hVZ X hX hk _ hE
      E₁ hE₁E U₁ (Finset.mem_powerset.2 (hU₁U.trans hU)) hpar
    refine ⟨m, Ys, hm, hYs, hYd, Tb, hTb, fun c hc => ?_⟩
    by_cases hgood : ∀ i ∈ X.biUnion id, IsGoodZ p₀ β lam M ε₀ V Z (c i)
    swap
    · rw [prod_blockWeightOf_eq_zero hgood, zero_mul]
      exact mul_nonneg (by positivity) (hRHS0 Ys Tb c)
    have hsupp : OnSupportZ p₀ β lam M ε₀ V Z (c i₁) := ⟨(hc i₁ hi₁X).1, hgood i₁ hi₁X⟩
    obtain ⟨hq0, hq⟩ := hratio c (fun i hi => (hc i hi).1) hgood i₁ hi₁X
    have hf : Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₁)) - 1 ≤
        Cc * SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) := by
      refine (hcosh lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i₁) hsupp).trans ?_
      rw [extGain_eq]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hq 2) (by linarith)
    refine case_arith (prod_blockWeightOf_nonneg X c) (mul_nonneg (abs_nonneg _) (hsep0 c))
      (RouteGain.le_mul_indicator (hsep c)
        (abs_markedTerm_le_even hdisj hE₁s hU hi₁ c) (hsep0 c)) (by linarith [one_le_cosh' (β *
        extSumZ χ p₀ β lam ε₀ V Z (c i₁))]) hf (hb c hc) (sum_jIntegrand_le X Ys Tb c _)
      hK₁.le (sq_nonneg _) (by linarith) (hsum Ys Tb c) hK₀1 (hRHS0 Ys Tb c)
  -- all marks odd
  have hUU : U₁ = U := by
    refine Finset.Subset.antisymm hU₁U fun i hi => ?_
    by_contra h
    exact hA ⟨i, Finset.mem_sdiff.2 ⟨hi, h⟩⟩
  subst hUU
  by_cases hB1 : ∃ Y ∈ oddComponents X E₁, (U₁ ∩ Y.biUnion id).Nonempty
  · -- a mark in an odd component: the gain of the component
    obtain ⟨m, Ys, hm, hYs, hYd, Tb, hTb, hb⟩ := hpg lam ε₀ V Z hlam hlamh hMp hVZ X hX hk _ hE
      E₁ hE₁E U₁ (Finset.mem_powerset.2 hU) hpar hB1
    refine ⟨m, Ys, hm, hYs, hYd, Tb, hTb, fun c hc => ?_⟩
    calc (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
          |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U₁ U₁ E₁ c|
        ≤ (∏ B ∈ X, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam B c) *
          (|reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ U₁ c| *
            BoundedUpper.RouteRaw.oddSeparation M lam X E₁ c) := by
          apply mul_le_mul_of_nonneg_left _ (prod_blockWeightOf_nonneg X c)
          have h := RouteGain.le_mul_indicator (hsep c)
            (show |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U₁ U₁ E₁ c| ≤
                1 * |reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ U₁ c| by
              simpa only [one_mul] using abs_markedTerm_le_odd hdisj hE₁s U₁ c) (hsep0 c)
          simpa only [one_mul] using h
      _ ≤ K₂ * _ := hb c hc
      _ ≤ K₀ * _ := mul_le_mul_of_nonneg_right hK₀3 (hRHS0 Ys Tb c)
  · -- no mark in an odd component: two marks in one block
    obtain ⟨S, hS, _, i₁, hi₁SU, i₂, hi₂, h12⟩ :=
      isolated_mark_pair hE₁X hU hUne hpar hB1
    have hi₁ : i₁ ∈ U₁ := (Finset.mem_inter.1 hi₁SU).2
    set V₁ := (U₁.erase i₁).erase i₂ with hV₁
    have hpar' : IsParityPair X E₁ V₁ := isParityPair_erase_two hX hpar hS hi₁SU hi₂ h12
    have hV₁X : V₁ ⊆ X.biUnion id :=
      (Finset.erase_subset _ _).trans ((Finset.erase_subset _ _).trans hU)
    obtain ⟨m, Ys, hm, hYs, hYd, Tb, hTb, hb⟩ := hpw lam ε₀ V Z hlam hlamh hMp hVZ X hX hk _ hE
      E₁ hE₁E V₁ (Finset.mem_powerset.2 hV₁X) hpar'
    refine ⟨m, Ys, hm, hYs, hYd, Tb, hTb, fun c hc => ?_⟩
    by_cases hgood : ∀ i ∈ X.biUnion id, IsGoodZ p₀ β lam M ε₀ V Z (c i)
    swap
    · rw [prod_blockWeightOf_eq_zero hgood, zero_mul]
      exact mul_nonneg (by positivity) (hRHS0 Ys Tb c)
    have hi₁X : i₁ ∈ X.biUnion id := hU hi₁
    have hi₂X : i₂ ∈ X.biUnion id := hU (Finset.mem_inter.1 hi₂).2
    obtain ⟨hq₁0, hq₁⟩ := hratio c (fun i hi => (hc i hi).1) hgood i₁ hi₁X
    obtain ⟨hq₂0, hq₂⟩ := hratio c (fun i hi => (hc i hi).1) hgood i₂ hi₂X
    have hs₁ := (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i₁)
      ⟨(hc i₁ hi₁X).1, hgood i₁ hi₁X⟩).1
    have hs₂ := (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i₂)
      ⟨(hc i₂ hi₂X).1, hgood i₂ hi₂X⟩).1
    set g := min (univ.fold max 0 (fun j : X.biUnion id => Peeling.dipoleLength (c j)) /
      SmallIntegral.minBadDist p₀ β lam ε₀ V Z (fun j : X.biUnion id => c j)) 1 with hg
    have hf : |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₁))| *
        |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₂))| ≤
        C₂ ^ 2 * SmallIntegral.extGain p₀ β lam ε₀ V Z (fun i : X.biUnion id => c i) := by
      rw [extGain_eq, ← hg]
      calc |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₁))| *
            |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₂))|
          ≤ (C₂ * g) * (C₂ * g) := by
            refine mul_le_mul (hs₁.trans (mul_le_mul_of_nonneg_left hq₁ (by linarith)))
              (hs₂.trans (mul_le_mul_of_nonneg_left hq₂ (by linarith))) (abs_nonneg _)
              (mul_nonneg (by linarith) (hq₁0.trans hq₁))
        _ = C₂ ^ 2 * g ^ 2 := by ring
    refine case_arith (prod_blockWeightOf_nonneg X c) (mul_nonneg (abs_nonneg _) (hsep0 c))
      (RouteGain.le_mul_indicator (hsep c)
        (abs_markedTerm_le_two hdisj hE₁s hi₁ (Finset.mem_inter.1 hi₂).2 h12 c) (hsep0 c))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hf (hb c hc) (sum_jIntegrand_le X Ys Tb c _)
      hK₁.le (sq_nonneg _) (sq_nonneg _) (hsum Ys Tb c) hK₀2 (hRHS0 Ys Tb c)

end Pointwise

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
