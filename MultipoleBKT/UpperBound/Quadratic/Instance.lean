/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.Corollary
public import MultipoleBKT.UpperBound.Quadratic.RelTree
public import MultipoleBKT.UpperBound.Quadratic.WeightBounds
public import MultipoleBKT.Frozen.MultipoleClassOn

/-!
# Corollary 5.34: the quadratic estimate with frozen bad points

The paper: Corollary 5.34 (Corollary 5.34,
eq. (5.89)). The abstract estimate
`MultipoleBKT.UpperBound.Quadratic.squares_of_bounds_sum` is instantiated at the odd weights of the
reduced model: `d : Fin N → ℂ × ℂ` is the dipole configuration, `v^Z = interactionZ`,
`d_{i,bad} = badDist`, `I_good = goodPoints`, `I_bad = badPoints` (as in Lemmas 5.9–5.11 and
`MultipoleBKT.UpperBound.Quadratic.bornesabZ`), `R̄ = truncationScale p₀ β λ`. The subpartition `X`
has labels in `[N]`: `ι : V_X → Fin N` with `ι i = i`, and `z = d ∘ ι` is the configuration seen
from `V_X`.

The weights (written out as in `MultipoleBKT.UpperBound.Quadratic.WeightBounds`):

* for `i < j`, `a^{v^Z}_ij 𝟙_{𝓑_ij^c} = if 𝓑_ij then 0 else if 𝒜_ij then -sinh(β v^Z_ij) else 0`.
* `a^{v^Z}_{i∞} = -sinh(β ∑_{k ∈ I_bad} v^Z_ik)`.
* `r_i = |x_i - y_i|` (`radiiOn z`), `d_ij` on unordered pairs (`distOn z`), and
  `c_ij = 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R̄}` (`cutOn M λ ε₀ R̄ z`): these are, letter for letter,
  `MultipoleBKT.Peeling.dipoleLength`, `MultipoleBKT.Peeling.dipoleDistOn` and
  `MultipoleBKT.Peeling.absIndicator` (`rfl`). `MultipoleBKT.UpperBound.Quadratic.ParityForms`
  restates `coro_5_34` with those names and with `Parity.oddBondUnlinked`.

The events of the statement are hypotheses of the pointwise inequality: `V_X ⊂ I_good` and
`Π_mult^{V_X} = X`, of which only the inclusion "each block of `X` lies in one multipole computed on
`V_X`" is used (`hPi`).

Main result (the constants depend on `χ`, `p₀`, `β` and `M`):

* `coro_5_34`: **eq. (5.89)** in the paper's form: the sum over `T' ∈ B((x_i, y_i), T)` of
  `∏_{ij ∈ T'} d_ij^{-2} 𝟙_{min(r_i, r_j) ≤ d_ij ≤ 17 ε₀ R̄}`.

The hypothesis `|S| ≤ p(β)` of the paper is not needed.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest Peeling TheoremTwo

/-! ### The weights of a configuration -/

section Weights

variable {V : Type*}

/-- `𝓑_ij` is symmetric. -/
theorem multipoleLinked_comm {M lam : ℝ} {a b : ℂ × ℂ} :
    MultipoleLinked M lam a b ↔ MultipoleLinked M lam b a := by
  show dipoleDist a b ≤ _ ↔ dipoleDist b a ≤ _
  rw [dipoleDist_comm, min_comm]

/-- The radii `r_i = |x_i - y_i|` (as `MultipoleBKT.Peeling.dipoleLength`). -/
noncomputable abbrev radiiOn (z : V → ℂ × ℂ) (i : V) : ℝ := ‖(z i).1 - (z i).2‖

/-- The distances `d_ij` on unordered pairs (as `MultipoleBKT.Peeling.dipoleDistOn`). -/
noncomputable abbrev distOn (z : V → ℂ × ℂ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => dipoleDist (z i) (z j), fun _ _ => dipoleDist_comm _ _⟩

open scoped Classical in
/-- `c_ij = 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R}` (as `MultipoleBKT.Peeling.absIndicator`). -/
noncomputable abbrev cutOn (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => (if MultipoleLinked M lam (z i) (z j) then 0 else 1) *
      (if dipoleDist (z i) (z j) ≤ 17 * ε₀ * R then 1 else 0), fun i j => by
    simp only [dipoleDist_comm (z i) (z j), propext (multipoleLinked_comm (a := z i))]⟩

open scoped Classical in
/-- The indicator `𝟙_{min(r_i, r_j) ≤ d_ij ≤ 17 ε₀ R}` of eq. (5.89). -/
noncomputable abbrev sepCutOn (ε₀ R : ℝ) (z : V → ℂ × ℂ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun i j => if min ‖(z i).1 - (z i).2‖ ‖(z j).1 - (z j).2‖ ≤ dipoleDist (z i) (z j) ∧
      dipoleDist (z i) (z j) ≤ 17 * ε₀ * R then 1 else 0, fun i j => by
    simp only [dipoleDist_comm (z i) (z j), min_comm ‖(z i).1 - (z i).2‖]⟩

theorem distOn_nonneg (z : V → ℂ × ℂ) (e : Sym2 V) : 0 ≤ distOn z e := by
  induction e using Sym2.ind with
  | h i j => exact dipoleDist_nonneg _ _

theorem cutOn_nonneg (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (e : Sym2 V) :
    0 ≤ cutOn M lam ε₀ R z e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [cutOn, Sym2.lift_mk]
    split_ifs <;> norm_num

/-- On `𝓑_ij^c` (with `M ≥ 1`), `d_ij ≥ min(r_i, r_j)`: `c_ij ≤ 𝟙_{min(r_i, r_j) ≤ d_ij ≤ 17 ε₀ R}`. -/
theorem cutOn_le_sepCutOn {M lam ε₀ R : ℝ} (hlam : 0 < lam) (hM : 1 ≤ M) (z : V → ℂ × ℂ)
    (e : Sym2 V) : cutOn M lam ε₀ R z e ≤ sepCutOn ε₀ R z e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [cutOn, sepCutOn, Sym2.lift_mk]
    by_cases hl : MultipoleLinked M lam (z i) (z j)
    · rw [ite_eq_left hl, zero_mul]
      split_ifs <;> norm_num
    · rw [ite_eq_right hl, one_mul]
      have hmin := (lt_dipoleDist_of_not_linked hlam hM hl).2
      by_cases h1 : dipoleDist (z i) (z j) ≤ 17 * ε₀ * R
      · rw [ite_eq_left h1, ite_eq_left ⟨hmin, h1⟩]
      · rw [ite_eq_right h1]
        split_ifs <;> norm_num

open scoped Classical in
/-- `a^abs_ij` at a configuration: `absWeight r d c s(i, j)` is the expression of
`MultipoleBKT.Parity.absOddWeight` (Definition 4.29). -/
theorem absWeight_on (M lam ε₀ R : ℝ) (z : V → ℂ × ℂ) (i j : V) :
    absWeight (radiiOn z) (distOn z) (cutOn M lam ε₀ R z) s(i, j) =
      ‖(z i).1 - (z i).2‖ * ‖(z j).1 - (z j).2‖ /
          (dipoleDist (z i) (z j) * max (dipoleDist (z i) (z j))
            (max ‖(z i).1 - (z i).2‖ ‖(z j).1 - (z j).2‖)) *
        (if MultipoleLinked M lam (z i) (z j) then 0 else 1) *
        (if dipoleDist (z i) (z j) ≤ 17 * ε₀ * R then 1 else 0) := by
  simp only [absWeight, radProd_mk, radMax_mk, Sym2.lift_mk, radiiOn]
  rw [max_comm (max _ _) (dipoleDist (z i) (z j))]
  ring

/-- The product over the edges of `E`, each with its endpoints in increasing order (the convention
of the activities), is the product over `E.edgeFinset` of the corresponding function of unordered
pairs. -/
theorem prod_lt_adj_eq_prod_edgeFinset [Fintype V] [LinearOrder V] (E : SimpleGraph V)
    [DecidableRel E.Adj] (f : V → V → ℝ) :
    ∏ i, ∏ j, (if i < j ∧ E.Adj i j then f i j else 1) =
      ∏ e ∈ E.edgeFinset, Sym2.lift ⟨fun i j => f (min i j) (max i j), fun i j => by
        simp only [min_comm i j, max_comm i j]⟩ e := by
  have h1 : ∏ i, ∏ j, (if i < j ∧ E.Adj i j then f i j else 1) =
      ∏ p ∈ (univ ×ˢ univ).filter (fun p : V × V => p.1 < p.2 ∧ E.Adj p.1 p.2), f p.1 p.2 := by
    rw [Finset.prod_filter, Finset.prod_product]
  rw [h1]
  refine Finset.prod_bij (fun p _ => s(p.1, p.2)) (fun p hp => ?_) (fun p hp q hq h => ?_)
    (fun e he => ?_) (fun p hp => ?_)
  · rw [mem_edgeFinset]
    exact (mem_filter.1 hp).2.2
  · have hp' := (mem_filter.1 hp).2.1
    have hq' := (mem_filter.1 hq).2.1
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · rw [h1, h2] at hp'
      exact absurd hq' (not_lt.2 hp'.le)
  · induction e using Sym2.ind with
    | h i j =>
      rw [mem_edgeFinset] at he
      rcases lt_or_gt_of_ne he.ne with h | h
      · exact ⟨(i, j), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, h, he⟩, rfl⟩
      · exact ⟨(j, i), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, h, he.symm⟩,
          Sym2.eq_swap⟩
  · have hp' := (mem_filter.1 hp).2.1
    simp only [Sym2.lift_mk, min_eq_left hp'.le, max_eq_right hp'.le]

end Weights

/-! ### Corollary 5.34 -/

section Corollary

variable {χ : ℂ → ℝ}

open scoped Classical in
/-- **Corollary 5.34, eq. (5.89)** (Corollary 5.34), in the paper's form:
there is `C ≥ 1` depending on `χ`, `p₀`, `β` and `M` such that, under the hypotheses of
the local block peeling and geometric assumptions,
`∏_{ij ∈ E} |a^{v^Z}_ij| 𝟙_{𝓑_ij^c} ∏_{i ∈ V_1^∞} |a^{v^Z}_{i∞}| ≤ C^{|V_X|} ∏_{S ∈ X} r_S²
  ∑_{T' ∈ B((x_i, y_i), T)} ∏_{ij ∈ T'} d_ij^{-2} 𝟙_{min(r_i, r_j) ≤ d_ij ≤ 17 ε₀ R̄}
  ∏_{ij ∈ F} g_ij / d_{i₀,bad}²`. -/
theorem coro_5_34 (hχ : IsMollifier χ) (p₀ : ℕ) (β M : ℝ) : ∃ C : ℝ, 1 ≤ C ∧
    ∀ {N : ℕ} (lam ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
      lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M →
    ∀ {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (ι : X.biUnion id → Fin N),
      (∀ i, ((ι i : Fin N) : ℕ) = (i : ℕ)) →
    ∀ {V₁ : Finset (X.biUnion id)} {E₀ E : SimpleGraph (X.biUnion id)},
      IsRelEulerianOffConnected X V₁ E₀ → V₁.Nonempty → IsMinimalSkeleton (blockOf hX) E₀ E →
    ∀ {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
        X.biUnion id}
      {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
        Sym2 (X.biUnion id)}
      {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
        SimpleGraph (X.biUnion id)},
      IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) (radiiOn fun i => d (ι i))
        (distOn fun i => d (ι i)) v₁ e₀ Ts Fs →
      (∀ i, ι i ∈ goodPoints p₀ β lam M ε₀ d) →
      (∀ i j, blockOf hX i = blockOf hX j →
        ι j ∈ multipoleClassOn M lam d (univ.image ι) (ι i)) →
    ∀ i₀ : X.biUnion id,
      (∏ i, ∏ j, if i < j ∧ E.Adj i j then
          |if MultipoleLinked M lam (d (ι i)) (d (ι j)) then 0 else
            if IsStableDipolePair (d (ι i)) (d (ι j)) then
              -Real.sinh (β * interactionZ χ p₀ β lam M ε₀ d (ι i) (ι j)) else 0|
        else 1) *
        ∏ i ∈ V₁, |Real.sinh (β * ∑ k ∈ badPoints p₀ β lam M ε₀ d,
          interactionZ χ p₀ β lam M ε₀ d (ι i) k)| ≤
      C ^ (X.biUnion id).card * (∏ S, blockRadius hX (radiiOn fun i => d (ι i)) S ^ 2) *
        (∑ T' ∈ longAgreeingTrees X (radiiOn fun i => d (ι i)) (distOn fun i => d (ι i))
            (plusTree (blockOf hX) E Ts),
          ∏ e ∈ T'.edgeFinset, keptWeight (distOn fun i => d (ι i))
            (sepCutOn ε₀ (truncationScale p₀ β lam) fun i => d (ι i)) e) *
        (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight (radiiOn fun i => d (ι i))
          (distOn fun i => d (ι i)) (cutOn M lam ε₀ (truncationScale p₀ β lam) fun i => d (ι i))
          (radiiOn (fun i => d (ι i)) (v₁ l)) (e₀ l) e) /
        badDist p₀ β lam M ε₀ d (ι i₀) ^ 2 := by
  obtain ⟨C₁, hC₁, hab⟩ := bornesabZ hχ β
  obtain ⟨C₂', hC₂', hinf⟩ := bornesabinfty hχ p₀ β
  set C₂ := max 1 C₂' with hC₂def
  set K := max 6 ((M + 2) ^ (pBeta p₀ β - 1)) with hKdef
  have hC₂ : 1 ≤ C₂ := le_max_left _ _
  have hK : 1 ≤ K := (by norm_num : (1 : ℝ) ≤ 6).trans (le_max_left _ _)
  refine ⟨C₁ ^ 3 * C₂ * K ^ 6, ?_, ?_⟩
  · have h1 : 1 ≤ C₁ ^ 3 := one_le_pow₀ hC₁
    have h2 : 1 ≤ K ^ 6 := one_le_pow₀ hK
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ C₁ ^ 3 * C₂ * K ^ 6 := by gcongr
  intro N lam ε₀ d hlam hlamh hM X hX ι hι V₁ E₀ E hE₀ hV₁ hE v₁ e₀ Ts Fs hP hgood hPi i₀
  set z : X.biUnion id → ℂ × ℂ := fun i => d (ι i) with hz
  set R := truncationScale p₀ β lam with hR
  -- the odd weight of an ordered pair
  set aZ : X.biUnion id → X.biUnion id → ℝ := fun i j =>
    |if MultipoleLinked M lam (d (ι i)) (d (ι j)) then 0 else
      if IsStableDipolePair (d (ι i)) (d (ι j)) then
        -Real.sinh (β * interactionZ χ p₀ β lam M ε₀ d (ι i) (ι j)) else 0| with haZ
  have hlhs := prod_lt_adj_eq_prod_edgeFinset E aZ
  simp only [haZ] at hlhs
  rw [hlhs]
  have hM1 : 1 ≤ M := (one_le_pow₀ (by norm_num)).trans hM
  -- the comparison of bad distances inside a multipole
  have hKS : ∀ i j, blockOf hX i = blockOf hX j →
      badDist p₀ β lam M ε₀ d (ι j) ≤ K * badDist p₀ β lam M ε₀ d (ι i) := by
    intro i j hij
    have hcl := hPi i j hij
    simp only [multipoleClassOn, Finset.mem_filter, Finset.mem_univ, true_and] at hcl
    have hreach : (SimpleGraph.fromRel fun a b : Fin N =>
        MultipoleLinked M lam (d a) (d b)).Reachable (ι i) (ι j) := by
      refine hcl.mono fun a b hab => ?_
      rw [fromRel_adj] at hab ⊢
      rcases hab with ⟨hne, h | h⟩
      · exact ⟨hne, Or.inl h.2.2⟩
      · exact ⟨hne, Or.inr h.2.2⟩
    have := lemma_5_9_2 hlam hlamh hM (hgood i) hreach
    have hδ0 := (lam_le_badDist hlam hlamh hM (hgood i)).trans' hlam.le
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0)
  have hmain := squares_of_bounds_sum hX hE₀ hV₁ hE hP (fun v => norm_nonneg _) (distOn_nonneg z)
    (cutOn_nonneg M lam ε₀ R z) (A := Sym2.lift ⟨fun i j => aZ (min i j) (max i j),
      fun i j => by simp only [min_comm i j, max_comm i j]⟩)
    (Ainf := fun i => |Real.sinh (β * ∑ k ∈ badPoints p₀ β lam M ε₀ d,
      interactionZ χ p₀ β lam M ε₀ d (ι i) k)|)
    (δ := fun i => badDist p₀ β lam M ε₀ d (ι i)) hC₁ hC₂ hK
    (fun e => by
      induction e using Sym2.ind with
      | h i j => exact abs_nonneg _)
    (fun e he => by
      induction e using Sym2.ind with
      | h i j =>
        rw [mem_edgeSet] at he
        -- reduce to `i < j`
        wlog hij : i < j generalizing i j
        · have := this j i he.symm (lt_of_le_of_ne (not_lt.1 hij) he.ne.symm)
          rwa [Sym2.eq_swap] at this
        simp only [Sym2.lift_mk, min_eq_left hij.le, max_eq_right hij.le, haZ]
        rw [absWeight_on]
        exact (hab p₀ lam M ε₀ d hlam hlamh hM (ι i) (hgood i) (ι j) (hgood j)).1)
    (fun i => abs_nonneg _)
    (fun i _ => by
      have h := (hinf lam M ε₀ d hlam hlamh hM (ι i) (hgood i)).1
      refine h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
      exact div_nonneg (norm_nonneg _) (badDist_nonneg (hlam.le.trans hlamh) _))
    (fun i => hlam.trans_le (lam_le_badDist hlam hlamh hM (hgood i)))
    (fun i => norm_le_badDist hlam hlamh hM (hgood i))
    (fun i j hadj hA => by
      -- a nonzero odd weight gives `v^Z_ij ≠ 0`, hence `d_{j,bad} ≤ 6 d_{i,bad}`
      have hv : interactionZ χ p₀ β lam M ε₀ d (ι i) (ι j) ≠ 0 := by
        intro h0
        apply hA
        simp only [Sym2.lift_mk, haZ]
        have h0' : interactionZ χ p₀ β lam M ε₀ d (ι (min i j)) (ι (max i j)) = 0 := by
          rcases le_total i j with h | h
          · rw [min_eq_left h, max_eq_right h]
            exact h0
          · rw [min_eq_right h, max_eq_left h, interactionZ_comm hχ]
            exact h0
        rw [h0', mul_zero, Real.sinh_zero, neg_zero]
        split_ifs <;> simp
      exact (badDist_le_six_mul hχ hlam hlamh hM (hgood i) (hgood j) hv).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (badDist_nonneg (hlam.le.trans hlamh) _)))
    hKS i₀
  have hsum : (∑ T' ∈ longAgreeingTrees X (radiiOn z) (distOn z)
      (plusTree (blockOf hX) E Ts), ∏ e ∈ T'.edgeFinset, keptWeight (distOn z) (cutOn M lam ε₀ R z) e) ≤
      ∑ T' ∈ longAgreeingTrees X (radiiOn z) (distOn z) (plusTree (blockOf hX) E Ts),
        ∏ e ∈ T'.edgeFinset, keptWeight (distOn z) (sepCutOn ε₀ R z) e := by
    apply sum_le_sum
    intro T' _
    apply prod_le_prod₀ (fun e _ => keptWeight_nonneg (cutOn_nonneg M lam ε₀ R z) e)
    intro e _
    exact div_le_div_of_nonneg_right (cutOn_le_sepCutOn hlam hM1 z e) (sq_nonneg _)
  have hrad : 0 ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ (X.biUnion id).card *
      ∏ S, blockRadius hX (radiiOn z) S ^ 2 := by positivity
  have hF : 0 ≤ ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight (radiiOn z) (distOn z)
      (cutOn M lam ε₀ R z) (radiiOn z (v₁ l)) (e₀ l) e :=
    prod_nonneg fun l _ => prod_nonneg fun e _ => peelWeight_nonneg (cutOn_nonneg M lam ε₀ R z) _ _
  have hmain' := hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hrad) hF) (sq_nonneg _))
  convert hmain' using 3

end Corollary

end Quadratic

end UpperBound

end MultipoleBKT

end
