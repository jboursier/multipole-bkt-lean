/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Quadratic
public import MultipoleBKT.LowerBound.Peeling.Dipole
public import MultipoleBKT.LowerBound.Peeling.RouteDeterminant.Forest
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Counting trees that differ on short edges (Lemma 4.49(3))

We prove Lemma 4.49(3), equation (4.71). On
`{0 < r_i ≤ R} ∩ ⋂_{ij ∈ ℰ^inter(X)} 𝓑_ij^c`, the number of relative trees
agreeing on the long edges is at most
`C^{|V_X|} ∏ᵢ (1 + log_M(17 R / r_i))²`.

The proof follows the paper. Symmetry identifies the counted family with
`B(·, T₀')`. Its members are forests in the union of `T₀'` and the short edges.
The incidence-minor expansion and Cauchy–Binet bound their number by
`det(I + L_G)`. The radius bins bound `tr(D⁻¹(I + L_G))`, where
`D = diag (1 + h_i)²`. Spectral arithmetic-geometric mean, followed by the
comparison of `h_i` with `log_M(17 R / r_i)`, finishes the estimate.

The scalar product estimate `prod_le_prod_mul_exp` is used in
`LowerBound/AbsoluteLower/ClaimInt2.lean`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

/-! ### Relative trees inside a graph -/

section RelTree

variable {X : Finset (Finset ℕ)}

/-- A tree relative to `X` is acyclic as a graph on `V_X`. -/
theorem IsRelTree.isAcyclic (hX : IsSubpartition X) {T : SimpleGraph (X.biUnion id)}
    (hT : IsRelTree X T) : T.IsAcyclic := by
  obtain ⟨-, -, hF⟩ := (isRelTree₀_iff hX).mp (Or.inl hT)
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [isBridge_iff]
  exact fun hr => hF u v huv (hr.mono le_sup_right)

open scoped Classical in
/-- The forests relative to `X` contained in `G` number at most `det(I + L_G)`.
Equation (4.71) in the proof of Lemma 4.49. -/
theorem card_relTrees_le_det (hX : IsSubpartition X) (G : SimpleGraph (X.biUnion id))
    [DecidableRel G.Adj] :
    (((relTrees X).filter (· ≤ G)).card : ℝ) ≤ (1 + G.lapMatrix ℝ).det := by
  let F := (relTrees X).filter (· ≤ G)
  have hFG : ∀ T ∈ F, T ≤ G := fun T hT => (mem_filter.mp hT).2
  have hF : ∀ T ∈ F, T.IsAcyclic := by
    intro T hT
    have hrel : IsRelTree X T := mem_relTrees.mp (mem_filter.mp hT).1
    exact IsRelTree.isAcyclic hX hrel
  exact RouteDeterminant.card_forests_le_det G F hFG hF

end RelTree

/-! ### The arithmetic-geometric mean inequality -/

/-- `∏ a_i ≤ (∏ w_i) exp(∑ (a_i / w_i - 1))` for `a_i ≥ 0` and `w_i > 0`.
This scalar estimate is used in the proof of (4.105) in the proof of Lemma 4.56. -/
theorem prod_le_prod_mul_exp {ι : Type*} (s : Finset ι) (a w : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hw : ∀ i ∈ s, 0 < w i) :
    ∏ i ∈ s, a i ≤ (∏ i ∈ s, w i) * Real.exp (∑ i ∈ s, (a i / w i - 1)) := by
  rw [Real.exp_sum, ← prod_mul_distrib]
  refine prod_le_prod₀ ha fun i hi => ?_
  have h := Real.add_one_le_exp (a i / w i - 1)
  rw [sub_add_cancel] at h
  calc a i = w i * (a i / w i) := by field_simp [(hw i hi).ne']
    _ ≤ w i * Real.exp (a i / w i - 1) := mul_le_mul_of_nonneg_left h (hw i hi).le

/-! ### Dipoles -/

section Dipole

theorem dipoleDist_le {z w : ℂ × ℂ} {a b : ℂ} (ha : a = z.1 ∨ a = z.2) (hb : b = w.1 ∨ b = w.2) :
    dipoleDist z w ≤ ‖a - b‖ := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem exists_dipoleDist_eq (z w : ℂ × ℂ) :
    ∃ a b, (a = z.1 ∨ a = z.2) ∧ (b = w.1 ∨ b = w.2) ∧ dipoleDist z w = ‖a - b‖ := by
  simp only [dipoleDist]
  rcases min_choice (min ‖z.1 - w.1‖ ‖z.1 - w.2‖) (min ‖z.2 - w.1‖ ‖z.2 - w.2‖) with h | h <;>
    rw [h]
  · rcases min_choice ‖z.1 - w.1‖ ‖z.1 - w.2‖ with h' | h' <;> rw [h']
    · exact ⟨_, _, Or.inl rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, _, Or.inl rfl, Or.inr rfl, rfl⟩
  · rcases min_choice ‖z.2 - w.1‖ ‖z.2 - w.2‖ with h' | h' <;> rw [h']
    · exact ⟨_, _, Or.inr rfl, Or.inl rfl, rfl⟩
    · exact ⟨_, _, Or.inr rfl, Or.inr rfl, rfl⟩

/-- `dist(D', D'') ≤ dist(D, D') + |D| + dist(D, D'')` (equation (4.71) in the proof of Lemma 4.49). -/
theorem dipoleDist_le_add_length (z w w' : ℂ × ℂ) :
    dipoleDist w w' ≤ dipoleDist z w + dipoleLength z + dipoleDist z w' := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_dipoleDist_eq z w
  obtain ⟨a', b', ha', hb', h'⟩ := exists_dipoleDist_eq z w'
  have haa' : ‖a - a'‖ ≤ dipoleLength z := by
    rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;> simp [dipoleLength, norm_sub_rev]
  calc dipoleDist w w' ≤ ‖b - b'‖ := dipoleDist_le hb hb'
    _ = ‖(b - a) + (a - a') + (a' - b')‖ := by congr 1; ring
    _ ≤ ‖b - a‖ + ‖a - a'‖ + ‖a' - b'‖ := norm_add₃_le
    _ ≤ dipoleDist z w + dipoleLength z + dipoleDist z w' := by
        rw [norm_sub_rev b, ← h, ← h']
        linarith

end Dipole

/-! ### Dyadic levels of the radii -/

section Level

/-- The level `h = ⌊log_q(R / r)⌋` of a radius `r ≤ R` (equation (4.71) in the proof of Lemma 4.49). -/
noncomputable def level (q R r : ℝ) : ℕ := ⌊Real.logb q (R / r)⌋₊

variable {q R : ℝ}

theorem level_spec (hq : 1 < q) {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    q ^ level q R r * r ≤ R ∧ R < q ^ (level q R r + 1) * r := by
  have hRr : 1 ≤ R / r := (one_le_div hr).mpr hrR
  have hpos : 0 < R / r := zero_lt_one.trans_le hRr
  have hL := Real.logb_nonneg hq hRr
  have hq0 : 0 < q := zero_lt_one.trans hq
  have h1 : q ^ level q R r ≤ R / r := by
    rw [← Real.rpow_natCast, ← Real.rpow_logb hq0 hq.ne' hpos]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (Nat.floor_le hL)
  have h2 : R / r < q ^ (level q R r + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_logb hq0 hq.ne' hpos (x := R / r)]
    refine Real.rpow_lt_rpow_of_exponent_lt hq ?_
    push_cast
    exact Nat.lt_floor_add_one _
  exact ⟨(le_div_iff₀ hr).mp h1, (div_lt_iff₀ hr).mp h2⟩

/-- Radii at the same level differ by a factor less than `q`. -/
theorem lt_mul_of_level_eq (hq : 1 < q) {r r' : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hr' : 0 < r')
    (hr'R : r' ≤ R) (h : level q R r = level q R r') : r < q * r' := by
  obtain ⟨h1, -⟩ := level_spec hq hr hrR
  obtain ⟨-, h2⟩ := level_spec hq hr' hr'R
  rw [h] at h1
  rw [pow_succ] at h2
  have hqn : 0 < q ^ level q R r' := pow_pos (zero_lt_one.trans hq) _
  have : q ^ level q R r' * r < q ^ level q R r' * (q * r') :=
    calc q ^ level q R r' * r ≤ R := h1
      _ < q ^ level q R r' * q * r' := h2
      _ = q ^ level q R r' * (q * r') := by ring
  exact lt_of_mul_lt_mul_left this hqn.le

/-- A radius more than `M ≥ q` times larger has a smaller level. -/
theorem level_lt_of_lt (hq : 1 < q) {M r r' : ℝ} (hqM : q ≤ M) (hr : 0 < r) (hrR : r ≤ R)
    (hr' : 0 < r') (hr'R : r' ≤ R) (h : M * r < r') : level q R r' < level q R r := by
  obtain ⟨-, h2⟩ := level_spec hq hr hrR
  obtain ⟨h1, -⟩ := level_spec hq hr' hr'R
  have hq0 : 0 < q := zero_lt_one.trans hq
  rw [← pow_lt_pow_iff_right₀ hq]
  have hn : 0 < q ^ level q R r' := pow_pos hq0 _
  have key : q ^ level q R r' * (M * r) < q ^ level q R r * (M * r) := by
    calc q ^ level q R r' * (M * r) < q ^ level q R r' * r' := mul_lt_mul_of_pos_left h hn
      _ ≤ R := h1
      _ < q ^ (level q R r + 1) * r := h2
      _ = q ^ level q R r * (q * r) := by ring
      _ ≤ q ^ level q R r * (M * r) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqM hr.le)
            (pow_pos hq0 _).le
  exact lt_of_mul_lt_mul_right key (mul_pos (hq0.trans_le hqM) hr).le

/-- `1 + ⌊log_{M/3}(R / r)⌋ ≤ 2 (1 + log_M(17 R / r))` for `M ≥ 9` (equation (4.71) in the proof of Lemma 4.49). -/
theorem one_add_level_le {M r : ℝ} (hM : 9 ≤ M) (hr : 0 < r) (hrR : r ≤ R) :
    (1 + level (M / 3) R r : ℝ) ≤ 2 * (1 + Real.logb M (17 * R / r)) := by
  have hq : 1 < M / 3 := by linarith
  have hRr : 1 ≤ R / r := (one_le_div hr).mpr hrR
  have hlogRr : 0 ≤ Real.log (R / r) := Real.log_nonneg hRr
  have hlogq : 0 < Real.log (M / 3) := Real.log_pos hq
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hMq : Real.log M ≤ 2 * Real.log (M / 3) := by
    rw [← Real.log_rpow (by linarith : (0 : ℝ) < M / 3)]
    refine Real.log_le_log (by linarith) ?_
    rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hlev : (level (M / 3) R r : ℝ) ≤ Real.log (R / r) / Real.log (M / 3) :=
    Nat.floor_le (Real.logb_nonneg hq hRr)
  have h17 : Real.log (R / r) ≤ Real.log (17 * R / r) :=
    Real.log_le_log (zero_lt_one.trans_le hRr) (by
      rw [mul_div_assoc]
      linarith)
  have h1 : 1 / Real.log (M / 3) ≤ 2 / Real.log M := by
    rw [div_le_div_iff₀ hlogq hlogM]
    linarith
  have hL : Real.log (R / r) / Real.log (M / 3) ≤ 2 * Real.logb M (17 * R / r) :=
    calc Real.log (R / r) / Real.log (M / 3) = Real.log (R / r) * (1 / Real.log (M / 3)) := by
          ring
      _ ≤ Real.log (R / r) * (2 / Real.log M) := mul_le_mul_of_nonneg_left h1 hlogRr
      _ ≤ Real.log (17 * R / r) * (2 / Real.log M) :=
          mul_le_mul_of_nonneg_right h17 (div_nonneg zero_le_two hlogM.le)
      _ = 2 * Real.logb M (17 * R / r) := by rw [Real.logb]; ring
  linarith [Real.logb_nonneg (b := M) (by linarith) (le_trans hRr (by
    rw [mul_div_assoc]; linarith) : (1 : ℝ) ≤ 17 * R / r)]

end Level

/-! ### Short edges -/

section Short

variable {X : Finset (Finset ℕ)} (z : X.biUnion id → ℂ × ℂ)

/-- The short inter-block edges `ij ∈ ℰ^inter(X)` with `d_ij < max(r_i, r_j)` (equation (4.71) in the proof of Lemma 4.49). -/
def shortGraph : SimpleGraph (X.biUnion id) where
  Adj i j := (interEdges X).Adj i j ∧
    dipoleDist (z i) (z j) < max (dipoleLength (z i)) (dipoleLength (z j))
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [dipoleDist_comm, max_comm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1.ne rfl⟩

variable {z} {M lam R : ℝ}

/-- The hypotheses of Lemma 4.49(3): `9 ≤ M`, `0 < r_i ≤ R`, and `𝓑_ij^c` for inter-block pairs. -/
structure ShortHyp (X : Finset (Finset ℕ)) (z : X.biUnion id → ℂ × ℂ) (M lam R : ℝ) : Prop where
  nine_le : 9 ≤ M
  pos : ∀ i, 0 < dipoleLength (z i)
  le : ∀ i, dipoleLength (z i) ≤ R
  notLinked : ∀ i j, (interEdges X).Adj i j → ¬ MultipoleLinked M lam (z i) (z j)

theorem ShortHyp.lt_dipoleDist (h : ShortHyp X z M lam R) {i j : X.biUnion id}
    (hij : (interEdges X).Adj i j) :
    M * min (dipoleLength (z i)) (dipoleLength (z j)) < dipoleDist (z i) (z j) := by
  have := h.notLinked i j hij
  rw [multipoleLinked_iff_dipoleDist_le, not_le] at this
  refine lt_of_le_of_lt ?_ this
  exact mul_le_mul_of_nonneg_left (min_le_min (le_max_left _ _) (le_max_left _ _))
    (by linarith [h.nine_le])

/-- A short edge points to a dipole more than `M` times larger (equation (4.71) in the proof of Lemma 4.49). -/
theorem ShortHyp.mul_lt (h : ShortHyp X z M lam R) {i j : X.biUnion id}
    (hij : (shortGraph z).Adj i j) (hlt : dipoleLength (z i) < dipoleLength (z j)) :
    M * dipoleLength (z i) < dipoleLength (z j) := by
  have h1 := h.lt_dipoleDist hij.1
  have h2 := hij.2
  rw [min_eq_left hlt.le] at h1
  rw [max_eq_right hlt.le] at h2
  exact h1.trans h2

theorem ShortHyp.ne (h : ShortHyp X z M lam R) {i j : X.biUnion id}
    (hij : (shortGraph z).Adj i j) : dipoleLength (z i) ≠ dipoleLength (z j) := by
  intro heq
  have h1 := h.lt_dipoleDist hij.1
  have h2 := hij.2
  rw [heq, min_self] at h1
  rw [heq, max_self] at h2
  have := h.pos j
  have h9 := h.nine_le
  nlinarith

/-- The larger ends of the short edges at a vertex at the same level lie in the same block
(equation (4.71) in the proof of Lemma 4.49). -/
theorem ShortHyp.blockOf_eq (hX : IsSubpartition X) (h : ShortHyp X z M lam R)
    {i j j' : X.biUnion id} (hij : (shortGraph z).Adj i j) (hij' : (shortGraph z).Adj i j')
    (hlt : dipoleLength (z i) < dipoleLength (z j))
    (hlt' : dipoleLength (z i) < dipoleLength (z j'))
    (hlev : level (M / 3) R (dipoleLength (z j)) = level (M / 3) R (dipoleLength (z j'))) :
    blockOf hX j = blockOf hX j' := by
  by_contra hne
  have hq : 1 < M / 3 := by linarith [h.nine_le]
  have hjj' : (interEdges X).Adj j j' := (interEdges_adj hX).mpr hne
  have hd := h.lt_dipoleDist hjj'
  have htri := dipoleDist_le_add_length (z i) (z j) (z j')
  have hdj : dipoleDist (z i) (z j) < dipoleLength (z j) := by
    have := hij.2
    rwa [max_eq_right hlt.le] at this
  have hdj' : dipoleDist (z i) (z j') < dipoleLength (z j') := by
    have := hij'.2
    rwa [max_eq_right hlt'.le] at this
  have hMi := h.mul_lt hij hlt
  have h1 := lt_mul_of_level_eq hq (h.pos j) (h.le j) (h.pos j') (h.le j') hlev
  have h2 := lt_mul_of_level_eq hq (h.pos j') (h.le j') (h.pos j) (h.le j) hlev.symm
  have h9 := h.nine_le
  have hi := h.pos i
  rcases le_total (dipoleLength (z j)) (dipoleLength (z j')) with hle | hle
  · rw [min_eq_left hle] at hd
    have h9' : 9 * dipoleLength (z j) ≤ M * dipoleLength (z j) :=
      mul_le_mul_of_nonneg_right h9 (h.pos j).le
    have h9i : 9 * dipoleLength (z i) ≤ M * dipoleLength (z i) :=
      mul_le_mul_of_nonneg_right h9 hi.le
    linarith
  · rw [min_eq_right hle] at hd
    have h9' : 9 * dipoleLength (z j') ≤ M * dipoleLength (z j') :=
      mul_le_mul_of_nonneg_right h9 (h.pos j').le
    have h9i : 9 * dipoleLength (z i) ≤ M * dipoleLength (z i) :=
      mul_le_mul_of_nonneg_right h9 hi.le
    linarith

open scoped Classical in
/-- At most `p` larger ends of short edges at a vertex per level (equation (4.71) in the proof of Lemma 4.49). -/
theorem ShortHyp.card_level_le (hX : IsSubpartition X) (h : ShortHyp X z M lam R) {p : ℕ}
    (hp : ∀ S ∈ X, S.card ≤ p) (i : X.biUnion id) (k : ℕ) :
    (univ.filter fun j => (shortGraph z).Adj i j ∧ dipoleLength (z i) < dipoleLength (z j) ∧
      level (M / 3) R (dipoleLength (z j)) = k).card ≤ p := by
  classical
  set A := univ.filter fun j => (shortGraph z).Adj i j ∧ dipoleLength (z i) < dipoleLength (z j) ∧
    level (M / 3) R (dipoleLength (z j)) = k
  rcases A.eq_empty_or_nonempty with hA | ⟨j₀, hj₀⟩
  · rw [hA, card_empty]
    exact Nat.zero_le _
  have hsub : A ⊆ univ.filter fun j => blockOf hX j = blockOf hX j₀ := by
    intro j hj
    rw [mem_filter] at hj hj₀ ⊢
    refine ⟨mem_univ _, h.blockOf_eq hX hj.2.1 hj₀.2.1 hj.2.2.1 hj₀.2.2.1 ?_⟩
    rw [hj.2.2.2, hj₀.2.2.2]
  have hcard : (univ.filter fun j => blockOf hX j = blockOf hX j₀).card ≤ p := by
    refine (card_le_card_of_injOn (s := univ.filter fun j => blockOf hX j = blockOf hX j₀)
      (t := ((blockOf hX j₀ : X) : Finset ℕ)) (fun j : X.biUnion id => (j : ℕ))
      ?_ ?_).trans (hp _ (blockOf hX j₀).2)
    · intro j hj
      rw [coe_filter] at hj
      exact hj.2 ▸ mem_blockOf hX j
    · exact fun j _ j' _ hjj' => Subtype.ext hjj'
  exact (card_le_card hsub).trans hcard

/-- The larger ends of the short edges at `i` have a smaller level. -/
theorem ShortHyp.level_lt (h : ShortHyp X z M lam R) {i j : X.biUnion id}
    (hij : (shortGraph z).Adj i j) (hlt : dipoleLength (z i) < dipoleLength (z j)) :
    level (M / 3) R (dipoleLength (z j)) < level (M / 3) R (dipoleLength (z i)) :=
  level_lt_of_lt (by linarith [h.nine_le]) (by linarith [h.nine_le]) (h.pos i) (h.le i)
    (h.pos j) (h.le j) (h.mul_lt hij hlt)

open scoped Classical in
/-- `∑_{j ↑ i} f(h_j) ≤ p ∑_{k < h_i} f(k)` over the larger ends `j` of the short edges at `i`. -/
theorem ShortHyp.sum_up_le (hX : IsSubpartition X) (h : ShortHyp X z M lam R) {p : ℕ}
    (hp : ∀ S ∈ X, S.card ≤ p) (i : X.biUnion id) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ j ∈ univ.filter (fun j => (shortGraph z).Adj i j ∧
        dipoleLength (z i) < dipoleLength (z j)), f (level (M / 3) R (dipoleLength (z j))) ≤
      p * ∑ k ∈ range (level (M / 3) R (dipoleLength (z i))), f k := by
  set B := univ.filter (fun j => (shortGraph z).Adj i j ∧ dipoleLength (z i) < dipoleLength (z j))
  have hmaps : ∀ j ∈ B, level (M / 3) R (dipoleLength (z j)) ∈
      range (level (M / 3) R (dipoleLength (z i))) := fun j hj => by
    rw [mem_filter] at hj
    exact mem_range.mpr (h.level_lt hj.2.1 hj.2.2)
  rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
  refine sum_le_sum fun k _ => ?_
  have hc : (B.filter fun j => level (M / 3) R (dipoleLength (z j)) = k).card ≤ p := by
    have := h.card_level_le hX hp i k
    rw [filter_filter]
    convert this using 3
    exact and_assoc
  calc ∑ j ∈ B.filter (fun j => level (M / 3) R (dipoleLength (z j)) = k),
        f (level (M / 3) R (dipoleLength (z j)))
      = ∑ j ∈ B.filter (fun j => level (M / 3) R (dipoleLength (z j)) = k), f k :=
        sum_congr rfl fun j hj => by rw [(mem_filter.mp hj).2]
    _ = (B.filter fun j => level (M / 3) R (dipoleLength (z j)) = k).card * f k := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ p * f k := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf k)

end Short

/-! ### Elementary sums -/

theorem sum_range_inv_sq_le_two (H : ℕ) : ∑ k ∈ range H, 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 := by
  have key : ∀ H : ℕ, ∑ k ∈ range (H + 1), 1 / ((k : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((H : ℝ) + 1) := by
    intro H
    induction H with
    | zero => norm_num
    | succ H ih =>
      rw [sum_range_succ]
      have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
      have step : 1 / ((((H + 1 : ℕ) : ℝ)) + 1) ^ 2 ≤
          1 / ((H : ℝ) + 1) - 1 / (((H + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      push_cast at step ⊢
      linarith
  rcases H with _ | H
  · simp
  · exact (key H).trans (by linarith [show (0 : ℝ) < 1 / ((H : ℝ) + 1) by positivity])

/-! ### The weighted degree sum -/

section Count

variable {X : Finset (Finset ℕ)} {z : X.biUnion id → ℂ × ℂ} {M lam R : ℝ}

open scoped Classical in
/-- `deg_{T ∪ short}(i) ≤ deg_T(i) + #{larger short neighbours} + #{smaller short neighbours}`. -/
theorem ShortHyp.degree_le (h : ShortHyp X z M lam R) (T : SimpleGraph (X.biUnion id))
    (i : X.biUnion id) :
    (T ⊔ shortGraph z).degree i ≤ T.degree i +
      (univ.filter fun j => (shortGraph z).Adj i j ∧
        dipoleLength (z i) < dipoleLength (z j)).card +
      (univ.filter fun j => (shortGraph z).Adj i j ∧
        dipoleLength (z j) < dipoleLength (z i)).card := by
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, neighborFinset_sup,
    add_assoc]
  refine (card_union_le _ _).trans (Nat.add_le_add_left ((card_le_card fun j hj => ?_).trans
    (card_union_le _ _)) _)
  rw [mem_neighborFinset] at hj
  rw [mem_union, mem_filter, mem_filter]
  rcases lt_or_gt_of_ne (h.ne hj) with hlt | hlt
  exacts [Or.inl ⟨mem_univ _, hj, hlt⟩, Or.inr ⟨mem_univ _, hj, hlt⟩]

open scoped Classical in
/-- The weighted degree sum, equation (4.71) in the proof of Lemma 4.49:
`∑_i (1 + deg_G(i)) / (1 + h_i)² ≤ (3 + 3p) |V_X|` for `G = T ∪ short edges`, `T ∈ 𝖳^X`. -/
theorem ShortHyp.sum_degree_div_le (hX : IsSubpartition X) (h : ShortHyp X z M lam R) {p : ℕ}
    (hp : ∀ S ∈ X, S.card ≤ p) {T : SimpleGraph (X.biUnion id)} (hT : IsRelTree X T) :
    ∑ i, (1 + ((T ⊔ shortGraph z).degree i : ℝ)) /
        (1 + (level (M / 3) R (dipoleLength (z i)) : ℝ)) ^ 2 ≤
      (3 + 3 * p) * (Fintype.card (X.biUnion id) : ℝ) := by
  set n := Fintype.card (X.biUnion id)
  set hl : X.biUnion id → ℝ := fun i => (level (M / 3) R (dipoleLength (z i)) : ℝ)
  set w : X.biUnion id → ℝ := fun i => (1 + hl i) ^ 2
  set out : X.biUnion id → Finset (X.biUnion id) := fun i =>
    univ.filter fun j => (shortGraph z).Adj i j ∧ dipoleLength (z i) < dipoleLength (z j)
  set inn : X.biUnion id → Finset (X.biUnion id) := fun i =>
    univ.filter fun j => (shortGraph z).Adj i j ∧ dipoleLength (z j) < dipoleLength (z i)
  have hl0 : ∀ i, 0 ≤ hl i := fun i => Nat.cast_nonneg _
  have hw1 : ∀ i, 1 ≤ w i := fun i => by
    have := hl0 i
    simp only [w]
    nlinarith
  have hw0 : ∀ i, 0 < w i := fun i => zero_lt_one.trans_le (hw1 i)
  -- (a) the constant term
  have ha : ∑ i, 1 / w i ≤ n := by
    calc ∑ i, 1 / w i ≤ ∑ _i : X.biUnion id, (1 : ℝ) :=
          sum_le_sum fun i _ => (div_le_one (hw0 i)).mpr (hw1 i)
      _ = n := by simp [n]
  -- (b) the tree
  have hb : ∑ i, (T.degree i : ℝ) / w i ≤ 2 * n := by
    have hcard : T.edgeFinset.card + 1 = X.card := IsRelTree₀.card_edgeFinset hX (Or.inl hT)
    have hXn : X.card ≤ n := by
      rw [show n = (X.biUnion id).card from Fintype.card_coe _]
      exact card_le_card_biUnion (fun S hS S' hS' hne => hX.2 hS hS' hne) hX.1
    calc ∑ i, (T.degree i : ℝ) / w i ≤ ∑ i, (T.degree i : ℝ) :=
          sum_le_sum fun i _ => div_le_self (Nat.cast_nonneg _) (hw1 i)
      _ = 2 * T.edgeFinset.card := by exact_mod_cast sum_degrees_eq_twice_card_edges T
      _ ≤ 2 * n := by
          have : (T.edgeFinset.card : ℝ) ≤ n := by exact_mod_cast (by omega : T.edgeFinset.card ≤ n)
          linarith
  -- (c) the larger short neighbours
  have hc : ∑ i, ((out i).card : ℝ) / w i ≤ p * n := by
    have hout : ∀ i, ((out i).card : ℝ) ≤ p * hl i := by
      intro i
      have := h.sum_up_le hX hp i (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
      simp only [sum_const, nsmul_eq_mul, mul_one, card_range] at this
      exact this
    calc ∑ i, ((out i).card : ℝ) / w i ≤ ∑ _i : X.biUnion id, (p : ℝ) := by
          refine sum_le_sum fun i _ => ?_
          rw [div_le_iff₀ (hw0 i)]
          refine (hout i).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
          have := hl0 i
          simp only [w]
          nlinarith
      _ = p * n := by simp [n, mul_comm]
  -- (d) the smaller short neighbours, counted from the other end
  have hd : ∑ i, ((inn i).card : ℝ) / w i ≤ 2 * p * n := by
    have hswap : ∑ i, ((inn i).card : ℝ) / w i = ∑ j, ∑ i ∈ out j, 1 / w i := by
      have h1 : ∀ i, ((inn i).card : ℝ) / w i = ∑ j, if (shortGraph z).Adj i j ∧
          dipoleLength (z j) < dipoleLength (z i) then 1 / w i else 0 := by
        intro i
        rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_one_div]
      have h2 : ∀ j, ∑ i ∈ out j, 1 / w i = ∑ i, if (shortGraph z).Adj i j ∧
          dipoleLength (z j) < dipoleLength (z i) then 1 / w i else 0 := by
        intro j
        rw [← sum_filter]
        refine sum_congr ?_ fun _ _ => rfl
        ext i
        simp only [out, mem_filter, mem_univ, true_and]
        exact and_congr_left' ⟨fun h' => h'.symm, fun h' => h'.symm⟩
      simp only [h1, h2]
      exact sum_comm
    rw [hswap]
    calc ∑ j, ∑ i ∈ out j, 1 / w i
        ≤ ∑ j, (p : ℝ) * ∑ k ∈ range (level (M / 3) R (dipoleLength (z j))),
            1 / ((k : ℝ) + 1) ^ 2 := by
          refine sum_le_sum fun j _ => ?_
          have := h.sum_up_le hX hp j (fun k => 1 / ((k : ℝ) + 1) ^ 2)
            (fun k => by positivity)
          refine le_of_eq_of_le ?_ this
          refine sum_congr rfl fun i _ => ?_
          simp only [w, hl]
          ring
      _ ≤ ∑ _j : X.biUnion id, (p : ℝ) * 2 :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (sum_range_inv_sq_le_two _)
            (Nat.cast_nonneg _)
      _ = 2 * p * n := by simp [n]; ring
  calc ∑ i, (1 + ((T ⊔ shortGraph z).degree i : ℝ)) / w i
      ≤ ∑ i, (1 / w i + (T.degree i : ℝ) / w i + ((out i).card : ℝ) / w i +
          ((inn i).card : ℝ) / w i) := by
        refine sum_le_sum fun i _ => ?_
        rw [← add_div, ← add_div, ← add_div, div_le_div_iff_of_pos_right (hw0 i)]
        have := h.degree_le T i
        have : ((T ⊔ shortGraph z).degree i : ℝ) ≤ T.degree i + (out i).card + (inn i).card := by
          exact_mod_cast this
        linarith
    _ = ∑ i, 1 / w i + ∑ i, (T.degree i : ℝ) / w i + ∑ i, ((out i).card : ℝ) / w i +
          ∑ i, ((inn i).card : ℝ) / w i := by
        rw [sum_add_distrib, sum_add_distrib, sum_add_distrib]
    _ ≤ n + 2 * n + p * n + 2 * p * n := by linarith
    _ = (3 + 3 * p) * n := by ring

open scoped Classical in
/-- The radius-bin trace bound, equation (4.71) in the proof of Lemma 4.49. -/
theorem ShortHyp.weighted_trace_le (hX : IsSubpartition X) (h : ShortHyp X z M lam R)
    {p : ℕ} (hp : ∀ S ∈ X, S.card ≤ p) {T : SimpleGraph (X.biUnion id)}
    (hT : IsRelTree X T) :
    (Matrix.diagonal (fun i => ((1 +
        (level (M / 3) R (dipoleLength (z i)) : ℝ)) ^ 2)⁻¹) *
      (1 + (T ⊔ shortGraph z).lapMatrix ℝ)).trace ≤
        (3 + 3 * p) * (Fintype.card (X.biUnion id) : ℝ) := by
  rw [RouteDeterminant.weighted_trace_laplacian]
  exact h.sum_degree_div_le hX hp hT

end Count

/-! ### Lemma 4.49(3) -/

open scoped Classical in
/-- **Lemma 4.49(3)**, equation (4.71). For blocks of size at most `p` and `M ≥ 9`, the
number of relative trees agreeing on long edges is at most
`C^{|V_X|} ∏ᵢ (1 + log_M(17 R / r_i))²`, with `C = 4 (3 + 3p)`.
In the paper, `R = ε₀ R̄`. -/
theorem lemma_4_49_three (p : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ {X : Finset (Finset ℕ)}, IsSubpartition X → (∀ S ∈ X, S.card ≤ p) →
      ∀ {M lam R : ℝ} (z : X.biUnion id → ℂ × ℂ), 9 ≤ M →
      (∀ i, 0 < dipoleLength (z i) ∧ dipoleLength (z i) ≤ R) →
      (∀ i j, (interEdges X).Adj i j → ¬ MultipoleLinked M lam (z i) (z j)) →
      ∀ T₀' ∈ relTrees X,
        ((((relTrees X).filter fun T₀ =>
            T₀' ∈ longAgreeingTrees X (fun i => dipoleLength (z i)) (dipoleDistOn z) T₀).card :
            ℝ)) ≤
          C ^ (X.biUnion id).card *
            ∏ i, (1 + Real.logb M (17 * R / dipoleLength (z i))) ^ 2 := by
  refine ⟨4 * (3 + 3 * p), by positivity, ?_⟩
  intro X hX hp M lam R z hM hr hB T₀' hT₀'
  have h : ShortHyp X z M lam R := ⟨hM, fun i => (hr i).1, fun i => (hr i).2, hB⟩
  rw [mem_relTrees] at hT₀'
  set r : X.biUnion id → ℝ := fun i => dipoleLength (z i)
  set G := T₀' ⊔ shortGraph z
  set n := (X.biUnion id).card
  have hn : Fintype.card (X.biUnion id) = n := Fintype.card_coe _
  -- Symmetry identifies the counted family with `B(·, T₀')`, proof of Lemma 4.49.
  have hsym : ((relTrees X).filter fun T₀ =>
      T₀' ∈ longAgreeingTrees X r (dipoleDistOn z) T₀) =
      longAgreeingTrees X r (dipoleDistOn z) T₀' := by
    ext T₀
    simp only [longAgreeingTrees, mem_filter]
    constructor
    · rintro ⟨hT, _, hagree⟩
      exact ⟨hT, fun e => (hagree e).symm⟩
    · rintro ⟨hT, hagree⟩
      exact ⟨hT, mem_relTrees.mpr hT₀', fun e => (hagree e).symm⟩
  rw [hsym]
  -- Every member is a forest in `G`, proof of Lemma 4.49.
  have hsub : longAgreeingTrees X r (dipoleDistOn z) T₀' ⊆
      (relTrees X).filter (· ≤ G) := by
    intro T₀ hT₀
    rw [longAgreeingTrees, mem_filter] at hT₀
    refine mem_filter.mpr ⟨hT₀.1, fun u v huv => ?_⟩
    by_cases hlong : radMax r s(u, v) ≤ dipoleDistOn z s(u, v)
    · exact Or.inl ((hT₀.2 s(u, v)).mp ⟨huv, hlong⟩).1
    · exact Or.inr ⟨(mem_relTrees.mp hT₀.1).1.1 huv, not_le.mp hlong⟩
  have hcount := (Nat.cast_le.mpr (card_le_card hsub)).trans (card_relTrees_le_det hX G)
  set w : X.biUnion id → ℝ := fun i => (1 + (level (M / 3) R (r i) : ℝ)) ^ 2
  have hw0 : ∀ i, 0 < w i := fun i => by positivity
  -- The radius-bin estimate bounds `tr(D⁻¹(I + L_G))`, proof of Lemma 4.49.
  have htrace := h.weighted_trace_le hX hp hT₀'
  rw [hn] at htrace
  -- Spectral AM–GM after conjugating by `D⁻¹ᐟ²`, proof of Lemma 4.49.
  have hdet : (1 + G.lapMatrix ℝ).det ≤ (∏ i, w i) * (3 + 3 * p) ^ n := by
    cases isEmpty_or_nonempty (X.biUnion id) with
    | inl hV =>
      have := hV
      have hn0 : n = 0 := by rw [← hn]; exact Fintype.card_eq_zero
      simp [Matrix.det_isEmpty, hn0]
    | inr hV =>
      have := hV
      have hnpos : (0 : ℝ) < n := by rw [← hn]; exact_mod_cast Fintype.card_pos
      have hamgm := RouteDeterminant.det_one_add_laplacian_le G w hw0
      rw [← RouteDeterminant.weighted_trace_laplacian G w, hn] at hamgm
      refine hamgm.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      apply pow_le_pow_left₀
      · apply div_nonneg _ hnpos.le
        rw [RouteDeterminant.weighted_trace_laplacian]
        exact sum_nonneg fun i _ => div_nonneg (by positivity) (hw0 i).le
      · exact (div_le_iff₀ hnpos).mpr htrace
  have hw : ∏ i, w i ≤ 4 ^ n * ∏ i, (1 + Real.logb M (17 * R / r i)) ^ 2 := by
    rw [← hn, ← card_univ, ← prod_const, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun i _ => (hw0 i).le) fun i _ => ?_
    have h1 := one_add_level_le hM (hr i).1 (hr i).2
    have h0 : (0 : ℝ) ≤ 1 + (level (M / 3) R (r i) : ℝ) := by positivity
    calc w i = (1 + (level (M / 3) R (r i) : ℝ)) ^ 2 := rfl
      _ ≤ (2 * (1 + Real.logb M (17 * R / r i))) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * (1 + Real.logb M (17 * R / r i)) ^ 2 := by ring
  calc _ ≤ (1 + G.lapMatrix ℝ).det := hcount
    _ ≤ (∏ i, w i) * (3 + 3 * p) ^ n := hdet
    _ ≤ (4 ^ n * ∏ i, (1 + Real.logb M (17 * R / r i)) ^ 2) * (3 + 3 * p) ^ n :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (4 * (3 + 3 * p)) ^ n * ∏ i, (1 + Real.logb M (17 * R / r i)) ^ 2 := by
      rw [mul_pow]
      ring

end Peeling

end MultipoleBKT

end
