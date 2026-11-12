/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.PairGraph
public import MultipoleBKT.UpperBound.Quadratic.Instance
public import MultipoleBKT.LowerBound.Peeling.Quadratic

/-!
# The unmarked component tail and shared tail algebra

The paper: Proposition 5.18. `euler_component_bound` is the single-tree unmarked
adapter used by the screened lower path `LowerBound.RouteBounded.ScreenTrees`.
The upper consumers use the summed estimates in `BoundedUpper.RouteRaw`.

The screened lower path uses the lexicographic skeleton of Definition 4.38,
the paper, as extended in
Definition 4.44, before the component estimate in
Proposition 4.23. The hatted path for `𝖪^0` follows the proof of
(A.30) instead (`LowerBound.RouteBounded.Component`).

This module also supplies the tail `treeTail`, its nonnegativity, maximal-radius
product algebra and the radius/bad-distance comparison used for replacement trees.
-/

@[expose] public section

open Finset SimpleGraph
open scoped NNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Peeling CoreForest Quadratic Parity

/-! ### Elementary facts -/

section Elementary

/-- If `f a = f b`, the products of `f` over `univ ∖ {a}` and `univ ∖ {b}` agree. -/
theorem prod_erase_eq_of_eq {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (f : ι → M) {a b : ι} (h : f a = f b) :
    ∏ x ∈ univ.erase a, f x = ∏ x ∈ univ.erase b, f x := by
  by_cases hab : a = b
  · rw [hab]
  · rw [← Finset.mul_prod_erase (univ.erase a) f (Finset.mem_erase.2 ⟨Ne.symm hab, mem_univ b⟩),
      ← Finset.mul_prod_erase (univ.erase b) f (Finset.mem_erase.2 ⟨hab, mem_univ a⟩), ← h,
      Finset.erase_right_comm]

variable {V : Type*} [DecidableEq V]

/-- `g_ij ≤ 1` when `0 ≤ c ≤ 1` and the radii are nonnegative. -/
theorem peelWeight_le_one {r : V → ℝ} {d c : Sym2 V → ℝ} (hr : ∀ v, 0 ≤ r v)
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (e₀ e : Sym2 V) :
    peelWeight r d c R e₀ e ≤ 1 := by
  have hrm : 0 ≤ radMax r e := by
    induction e using Sym2.ind with
    | h i j => exact (hr i).trans (le_max_left _ _)
  unfold peelWeight
  have hc0 := hc e
  have hc1' := hc1 e
  split_ifs with h1 h2
  · linarith
  · have hq : R ^ 2 / d e ^ 2 ≤ 1 := by
      rcases (hd e).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · rw [div_le_one (pow_pos h0 2)]
        have h3 := h2.2
        nlinarith
    calc c e * (R ^ 2 / d e ^ 2) ≤ 1 * 1 :=
          mul_le_mul hc1' hq (div_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one
      _ = 1 := one_mul 1
  · have hq : radMax r e ^ 2 / d e ^ 2 ≤ 1 := by
      rcases (hd e).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · rw [div_le_one (pow_pos h0 2)]
        have := not_lt.1 h1
        nlinarith
    calc c e * (radMax r e ^ 2 / d e ^ 2) ≤ 1 * 1 :=
          mul_le_mul hc1' hq (div_nonneg (sq_nonneg _) (sq_nonneg _)) zero_le_one
      _ = 1 := one_mul 1

omit [DecidableEq V] in
theorem keptWeight_nonneg' {d c : Sym2 V → ℝ} (hc : ∀ e, 0 ≤ c e) (e : Sym2 V) :
    0 ≤ keptWeight d c e :=
  div_nonneg (hc e) (sq_nonneg _)

theorem peelWeight_nonneg' {r : V → ℝ} {d c : Sym2 V → ℝ}
    (hc : ∀ e, 0 ≤ c e) (R : ℝ) (e₀ e : Sym2 V) : 0 ≤ peelWeight r d c R e₀ e := by
  unfold peelWeight
  refine mul_nonneg (hc e) ?_
  split_ifs <;> positivity

/-- The tail `(R / max(m, R))²` for `m = max_{e ∈ T} d_e`. -/
noncomputable def treeTail (d : Sym2 V → ℝ) (T : SimpleGraph V) [Fintype T.edgeSet] (R : ℝ) : ℝ :=
  (R / max ((T.edgeFinset.sup fun e => (d e).toNNReal : ℝ≥0) : ℝ) R) ^ 2

omit [DecidableEq V] in
theorem treeTail_nonneg (d : Sym2 V → ℝ) (T : SimpleGraph V) [Fintype T.edgeSet] (R : ℝ) :
    0 ≤ treeTail d T R :=
  sq_nonneg _

omit [DecidableEq V] in
/-- `min(R / d_e, 1)² ≤ (R / max(m, R))²` when `e` realizes the maximum `m` of the edge lengths. -/
theorem min_sq_le_treeTail {d : Sym2 V → ℝ} (hd : ∀ e, 0 ≤ d e) {T : SimpleGraph V}
    [Fintype T.edgeSet] {R : ℝ} (hR : 0 ≤ R) {e : Sym2 V}
    (hmax : (T.edgeFinset.sup fun e => (d e).toNNReal : ℝ≥0) = (d e).toNNReal) (hpos : 0 < d e) :
    min (R / d e) 1 ^ 2 ≤ treeTail d T R := by
  unfold treeTail
  rw [hmax, Real.coe_toNNReal _ (hd e)]
  refine pow_le_pow_left₀ (le_min (div_nonneg hR (hd e)) zero_le_one) ?_ 2
  rcases le_total (d e) R with h | h
  · rw [max_eq_right h, div_self (by linarith : R ≠ 0)]
    exact min_le_right _ _
  · rw [max_eq_left h]
    exact min_le_left _ _

end Elementary

/-! ### The component without marks: Corollary 4.47 and eq. (4.70) -/

section Euler

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)

open scoped Classical in
/-- **The quadratic estimate on a component without marks** (Corollary 4.47 with eq. (4.70)):
for `G ∈ Eulc^Y` and weights `0 ≤ A ≤ C₁ a^abs` on its edges with `a^abs ≤ 1`, there is a relative
tree `T ∈ 𝖳^Y` with
`∏_{e ∈ G} A_e ≤ C₁^{|G|} ∏_{S ≠ Ŝ} r_S² ∏_{e ∈ T} d_e^{-2} c_e (R / max(max_T d, R))²`
for every block `Ŝ` of maximal radius `R = r_Ŝ`. -/
theorem euler_component_bound {G : SimpleGraph (Y.biUnion id)} (hG : Parity.IsRelEulerianConnected Y G)
    {r : Y.biUnion id → ℝ} (hr : ∀ v, 0 ≤ r v) {d c : Sym2 (Y.biUnion id) → ℝ}
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {A : Sym2 (Y.biUnion id) → ℝ} (hA0 : ∀ e, 0 ≤ A e) {C₁ : ℝ} (hC₁ : 1 ≤ C₁)
    (hA : ∀ e ∈ G.edgeSet, A e ≤ C₁ * absWeight r d c e)
    (ha1 : ∀ e ∈ G.edgeSet, absWeight r d c e ≤ 1) {Ŝ : Y}
    (hŜ : ∀ S, blockRadius hY r S ≤ blockRadius hY r Ŝ) :
    ∃ T : SimpleGraph (Y.biUnion id), IsRelTree Y T ∧
      ∏ e ∈ G.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card *
        (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
        ((∏ e ∈ T.edgeFinset, keptWeight d c e) * treeTail d T (blockRadius hY r Ŝ)) := by
  -- Use the selected skeleton of Definition 4.44.
  -- Apply the peeling to this skeleton.
  obtain ⟨E', v₁, e₀, Qs, hselected, hP⟩ :=
    exists_isEulerPeeling_of_eulerian_eq_peeledSkeleton (hX := hY) hG r d
  subst E'
  have hstr := hP.structure hG.1.1
  set T := keptGraph (peeledSkeleton G (Parity.lemma_4_37 hY hG)) Qs
  refine ⟨T, (isRelTree₀_iff hY).1 (Or.inl hstr.1) |> fun _ => hstr.1, ?_⟩
  -- the maximal radius is that of `v₁`
  have hle := hP.2.le_radius
  have hv₁ : blockRadius hY r (blockOf hY v₁) = blockRadius hY r Ŝ := by
    refine le_antisymm (hŜ _) ?_
    have h1 : blockRadius hY r Ŝ ≤ r v₁ := by
      unfold blockRadius
      exact Finset.sup'_le _ _ fun i _ => hle i
    exact h1.trans (le_blockRadius r v₁)
  have hRv : blockRadius hY r Ŝ = r v₁ := by
    rw [← hv₁]
    refine le_antisymm ?_ (le_blockRadius r v₁)
    unfold blockRadius
    exact Finset.sup'_le _ _ fun i _ => hle i
  -- Corollary 4.47 through the skeleton
  have hq := hP.prod_absWeight_le hr hd hc ha1
  rw [prod_erase_eq_of_eq (fun S => blockRadius hY r S ^ 2) (a := blockOf hY v₁) (b := Ŝ)
    (congrArg (· ^ 2) hv₁)] at hq
  have hAle : ∏ e ∈ G.edgeFinset, A e ≤ C₁ ^ G.edgeFinset.card *
      ∏ e ∈ G.edgeFinset, absWeight r d c e := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun e _ => hA0 e) fun e he => hA e (mem_edgeFinset.1 he)
  have hP0 : 0 ≤ ∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2 :=
    prod_nonneg fun _ _ => sq_nonneg _
  have hK0 : 0 ≤ ∏ e ∈ T.edgeFinset, keptWeight d c e :=
    prod_nonneg fun e _ => keptWeight_nonneg' hc e
  have hF0 : 0 ≤ ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e :=
    prod_nonneg fun e _ => peelWeight_nonneg' hc _ _ _
  -- the tail
  have htail : (∏ e ∈ T.edgeFinset, keptWeight d c e) *
      ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e ≤
      (∏ e ∈ T.edgeFinset, keptWeight d c e) * treeTail d T (blockRadius hY r Ŝ) := by
    by_cases hK : ∏ e ∈ T.edgeFinset, keptWeight d c e = 0
    · rw [hK, zero_mul, zero_mul]
    · refine mul_le_mul_of_nonneg_left ?_ hK0
      have hTne : T.edgeFinset.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have := hstr.1.1.2.1
        obtain ⟨e, he⟩ := this
        rw [← mem_edgeFinset, hne] at he
        exact Finset.notMem_empty _ he
      obtain ⟨e, he, hemax⟩ := Finset.exists_mem_eq_sup T.edgeFinset hTne
        (fun e => (d e).toNNReal)
      have hdpos : 0 < d e := by
        rcases (hd e).eq_or_lt with h0 | h0
        · exact absurd (Finset.prod_eq_zero he (by rw [keptWeight, ← h0]; simp)) hK
        · exact h0
      have h1 := hP.prod_peelWeight_le_min_sq (c := c) hr hd hc hc1 (mem_edgeFinset.1 he) hdpos
      refine h1.trans ?_
      rw [← hRv]
      exact min_sq_le_treeTail hd ((hr _).trans (le_blockRadius r v₁) |>.trans_eq hv₁) hemax hdpos
  calc ∏ e ∈ G.edgeFinset, A e
      ≤ C₁ ^ G.edgeFinset.card * ∏ e ∈ G.edgeFinset, absWeight r d c e := hAle
    _ ≤ C₁ ^ G.edgeFinset.card * ((∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
          (∏ e ∈ T.edgeFinset, keptWeight d c e) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e) :=
        mul_le_mul_of_nonneg_left hq (pow_nonneg (zero_le_one.trans hC₁) _)
    _ = C₁ ^ G.edgeFinset.card * (∏ S ∈ univ.erase Ŝ, blockRadius hY r S ^ 2) *
          ((∏ e ∈ T.edgeFinset, keptWeight d c e) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htail
          (mul_nonneg (pow_nonneg (zero_le_one.trans hC₁) _) hP0)

end Euler

/-! ### The component with marks: Corollary 5.34 and the comparison with `d_{i_0,bad}` -/

section Marked

/-- `R² / δ² ≤ 4 K² (R / max(m, R))²` when `R ≤ δ` and `m ≤ 2 K δ` (`K ≥ 1`, `δ > 0`). -/
theorem sq_div_le_tail {R δ m K : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hRδ : R ≤ δ) (hm0 : 0 ≤ m)
    (hm : m ≤ 2 * K * δ) (hK : 1 ≤ K) :
    R ^ 2 / δ ^ 2 ≤ 4 * K ^ 2 * (R / max m R) ^ 2 := by
  have hq1 : R ^ 2 / δ ^ 2 ≤ 1 := by
    rw [div_le_one (pow_pos hδ 2)]
    exact pow_le_pow_left₀ hR hRδ 2
  rcases le_total m R with h | h
  · rw [max_eq_right h]
    rcases hR.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · rw [div_self h0.ne', one_pow, mul_one]
      nlinarith
  · rw [max_eq_left h]
    have hmpos : 0 < m ∨ m = 0 := by rcases hm0.eq_or_lt with h' | h' <;> [exact Or.inr h'.symm; exact Or.inl h']
    rcases hmpos with hmpos | hm0'
    · have hm2 : m ^ 2 ≤ (2 * K * δ) ^ 2 := pow_le_pow_left₀ hm0 hm 2
      have h1 : 1 / δ ^ 2 ≤ 4 * K ^ 2 / m ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hδ 2) (pow_pos hmpos 2)]
        nlinarith
      calc R ^ 2 / δ ^ 2 = R ^ 2 * (1 / δ ^ 2) := by ring
        _ ≤ R ^ 2 * (4 * K ^ 2 / m ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg R)
        _ = 4 * K ^ 2 * (R / m) ^ 2 := by ring
    · have hR0 : R = 0 := le_antisymm (hm0' ▸ h) hR
      rw [hR0]; simp


end Marked

end BoundedUpper

end UpperBound

end MultipoleBKT

end
