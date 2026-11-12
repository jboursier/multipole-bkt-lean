/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Ear
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-!
# Edge weights of the peeling (Definition 4.29, eq. (4.66))

The peeling estimates of Section 4.11 are inequalities between
products of edge weights built from the dipole sizes `r_i ≥ 0`, the distances `d_ij ≥ 0` and the
indicator factors `1_{𝓑_ij^c} 1_{d_ij ≤ 17 ε₀ R̄}`. We keep these as abstract data: radii
`r : V → ℝ`, and distances and indicator factors `d c : Sym2 V → ℝ` on unordered pairs
(so that `d_ij = d_ji` and `c_ij = c_ji` hold by construction).

* `MultipoleBKT.Peeling.absWeight r d c ij = r_i r_j / (d_ij max(r_i, r_j, d_ij)) c_ij`: the weight
  `a^abs_ij` of Definition 4.29 (eq. (4.57)) when `c_ij` is the indicator
  `1_{𝓑_ij^c} 1_{d_ij ≤ 17 ε₀ R̄}`;
* `MultipoleBKT.Peeling.keptWeight d c ij = c_ij / d_ij²`: the factor
  `d_ij^{-2} 1_{d_ij ≤ 17 ε₀ R̄} 1_{𝓑_ij^c}` of a kept edge (eqs. (4.65), (4.67));
* `MultipoleBKT.Peeling.peelWeight r d c R e₀ ij`: the weight `g_ij` of equation (4.66), with `R = max_{v ∈ V_X} r_v` and `e₀` the longest edge of the peeling;
* `MultipoleBKT.Peeling.peelScore r d ij = min(d_ij, max(r_i, r_j))`: the score maximized by the
  deletion rule (2) of Definition 4.43;
* `MultipoleBKT.Peeling.innerProd r`: for the oriented edges `(a₁, b₁), …, (a_m, b_m)` of an ear,
  `∏_{k=1}^{m-1} r_{b_k} r_{a_{k+1}}`, the factor `∏_{i=2}^{n-1} r_{v_i} r_{v_i'}` of (4.65).

The scalar inequalities behind the proof of Lemma 4.45 are
`MultipoleBKT.Peeling.mul_kappa_le` (an end edge absorbs the radius of its outer endpoint) and
`MultipoleBKT.Peeling.end_pair_le` (the two end edges of an ear).
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset

variable {V : Type*}

/-- `r_i r_j` for the pair `ij`. -/
def radProd (r : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun i j => r i * r j, fun _ _ => mul_comm _ _⟩ e

/-- `max(r_i, r_j)` for the pair `ij`. -/
def radMax (r : V → ℝ) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun i j => max (r i) (r j), fun _ _ => max_comm _ _⟩ e

theorem radProd_mk (r : V → ℝ) (i j : V) : radProd r s(i, j) = r i * r j := rfl

theorem radMax_mk (r : V → ℝ) (i j : V) : radMax r s(i, j) = max (r i) (r j) := rfl

/-- The weight `a^abs_ij = r_i r_j / (d_ij max(r_i, r_j, d_ij)) c_ij` (Definition 4.29, eq.
(4.57), with `c_ij = 1_{𝓑_ij^c} 1_{d_ij ≤ 17 ε₀ R̄}`). -/
noncomputable def absWeight (r : V → ℝ) (d c : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  radProd r e / (d e * max (radMax r e) (d e)) * c e

/-- The weight `d_ij^{-2} c_ij` of a kept edge. -/
noncomputable def keptWeight (d c : Sym2 V → ℝ) (e : Sym2 V) : ℝ := c e / d e ^ 2

/-- The weight `g_ij` of eq. (4.66) (Lemma 4.45), for the longest edge `e₀`
and `R = max_{v ∈ V_X} r_v`:
`c_ij` if `d_ij < max(r_i, r_j)`; `c_ij R² / d_ij²` if `d_ij ≥ R` and `ij = e₀`;
`c_ij max(r_i, r_j)² / d_ij²` otherwise. -/
noncomputable def peelWeight [DecidableEq V] (r : V → ℝ) (d c : Sym2 V → ℝ) (R : ℝ)
    (e₀ e : Sym2 V) : ℝ :=
  c e * if d e < radMax r e then 1
    else if e = e₀ ∧ R ≤ d e then R ^ 2 / d e ^ 2 else radMax r e ^ 2 / d e ^ 2

/-- The score `min(d_ij, max(r_i, r_j))` of the deletion rule (2) of Definition 4.43. -/
noncomputable def peelScore (r : V → ℝ) (d : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  min (d e) (radMax r e)

/-- `c_ij / (d_ij max(r_i, r_j, d_ij))`: the weight `a^abs_ij` without the radii. -/
noncomputable def kappa (r : V → ℝ) (d c : Sym2 V → ℝ) (e : Sym2 V) : ℝ :=
  c e / (d e * max (radMax r e) (d e))

/-- For the oriented edges `(a₁, b₁), …, (a_m, b_m)` of an ear, `∏_{k<m} r_{b_k} r_{a_{k+1}}`. -/
def innerProd (r : V → ℝ) : List (V × V) → ℝ
  | [] => 1
  | [_] => 1
  | p :: q :: L => r p.2 * r q.1 * innerProd r (q :: L)

/-! ### Scalar facts -/

section Scalar

variable {r : V → ℝ} {d c : Sym2 V → ℝ}

theorem absWeight_edge (p : V × V) :
    absWeight r d c (edge p) = r p.1 * r p.2 * kappa r d c (edge p) := by
  simp only [absWeight, kappa, edge_apply, radProd_mk]
  ring

theorem radMax_nonneg (hr : ∀ v, 0 ≤ r v) (e : Sym2 V) : 0 ≤ radMax r e := by
  induction e using Sym2.ind with
  | h i j => exact (hr i).trans (le_max_left _ _)

theorem le_radMax_left (p : V × V) : r p.1 ≤ radMax r (edge p) := le_max_left _ _

theorem le_radMax_right (p : V × V) : r p.2 ≤ radMax r (edge p) := le_max_right _ _

theorem kappa_nonneg (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (e : Sym2 V) :
    0 ≤ kappa r d c e :=
  div_nonneg (hc e) (mul_nonneg (hd e) ((radMax_nonneg hr e).trans (le_max_left _ _)))

theorem keptWeight_nonneg (hc : ∀ e, 0 ≤ c e) (e : Sym2 V) : 0 ≤ keptWeight d c e :=
  div_nonneg (hc e) (sq_nonneg _)

theorem absWeight_nonneg (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e)
    (e : Sym2 V) : 0 ≤ absWeight r d c e := by
  induction e using Sym2.ind with
  | h i j =>
    rw [show s(i, j) = edge (i, j) from rfl, absWeight_edge]
    exact mul_nonneg (mul_nonneg (hr i) (hr j)) (kappa_nonneg hr hd hc _)

theorem peelScore_nonneg (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (e : Sym2 V) :
    0 ≤ peelScore r d e := le_min (hd e) (radMax_nonneg hr e)

/-- `a^abs_ij ≤ r_i r_j d_ij^{-2} c_ij`: `kappa ≤ keptWeight`. -/
theorem kappa_le_keptWeight (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e)
    (e : Sym2 V) : kappa r d c e ≤ keptWeight d c e := by
  rcases (hd e).eq_or_lt with h0 | hpos
  · simp [kappa, keptWeight, ← h0]
  · refine div_le_div_of_nonneg_left (hc e) (pow_pos hpos 2) ?_
    rw [sq]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (hd e)

/-- The real inequality behind `MultipoleBKT.Peeling.mul_kappa_le`. -/
theorem mul_div_mul_max_le {ρ μ δ C : ℝ} (hρμ : ρ ≤ μ) (hδ : 0 < δ) (hC : 0 ≤ C) :
    ρ * (C / (δ * max μ δ)) ≤ C * min δ μ / δ ^ 2 := by
  rcases le_total μ δ with h | h
  · rw [max_eq_right h, min_eq_right h, show C * μ / δ ^ 2 = μ * (C / (δ * δ)) by ring]
    exact mul_le_mul_of_nonneg_right hρμ (div_nonneg hC (mul_nonneg hδ.le hδ.le))
  · have hμ : 0 < μ := hδ.trans_le h
    rw [max_eq_left h, min_eq_left h]
    calc ρ * (C / (δ * μ)) = ρ / μ * (C / δ) := by field_simp
      _ ≤ 1 * (C / δ) :=
          mul_le_mul_of_nonneg_right (div_le_one_of_le₀ hρμ hμ.le) (div_nonneg hC hδ.le)
      _ = C * δ / δ ^ 2 := by field_simp

/-- An end edge absorbs the radius of its outer endpoint (proof of Lemma 4.45):
`ρ c / (d max(μ, d)) ≤ c min(d, μ) / d²` for `0 ≤ ρ ≤ μ = max(r_i, r_j)`. -/
theorem mul_kappa_le (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) {e : Sym2 V}
    {ρ : ℝ} (hρμ : ρ ≤ radMax r e) :
    ρ * kappa r d c e ≤ c e * peelScore r d e / d e ^ 2 := by
  rcases (hd e).eq_or_lt with h0 | hpos
  · simp [kappa, ← h0]
  exact mul_div_mul_max_le hρμ hpos (hc e)

/-- The square of the score of a non-exceptional edge is controlled by `g`: if `ij ≠ e₀` or
`d_ij < R`, then `c_ij min(d_ij, max(r_i, r_j))² / d_ij² ≤ g_ij`. -/
theorem peelScore_sq_le_peelWeight [DecidableEq V] (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e)
    {R : ℝ} {e₀ e : Sym2 V} (he : ¬ (e = e₀ ∧ R ≤ d e)) :
    c e * peelScore r d e ^ 2 / d e ^ 2 ≤ peelWeight r d c R e₀ e := by
  rw [peelWeight, ite_eq_right he, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hc e)
  split_ifs with h
  · rw [peelScore, min_eq_left h.le]
    rcases (hd e).eq_or_lt with h0 | hpos
    · simp [← h0]
    · rw [div_self (pow_pos hpos 2).ne']
  · rw [peelScore, min_eq_right (not_lt.mp h)]

/-- The weight `g_{e₀}` of the longest edge in the exceptional case: `R² d^{-2} c ≤ g_{e₀}` when
`max(r_i, r_j) ≤ R ≤ d_{e₀}`. -/
theorem sq_mul_keptWeight_le [DecidableEq V] {R : ℝ} {e₀ : Sym2 V}
    (hR : radMax r e₀ ≤ R) (hRd : R ≤ d e₀) :
    R ^ 2 * keptWeight d c e₀ ≤ peelWeight r d c R e₀ e₀ := by
  rw [peelWeight, ite_eq_right (not_lt.mpr (hR.trans hRd)), ite_eq_left ⟨rfl, hRd⟩, keptWeight]
  ring_nf
  exact le_rfl

/-- `0 ≤ g_ij ≤ 1` when `0 ≤ c_ij ≤ 1`. -/
theorem peelWeight_nonneg [DecidableEq V] (hc : ∀ e, 0 ≤ c e) {R : ℝ} (e₀ e : Sym2 V) :
    0 ≤ peelWeight r d c R e₀ e := by
  rw [peelWeight]
  refine mul_nonneg (hc e) ?_
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem peelWeight_le_one [DecidableEq V] (hr : ∀ v, 0 ≤ r v) (hc1 : ∀ e, c e ≤ 1) {R : ℝ}
    (hR : 0 ≤ R) (e₀ e : Sym2 V) : peelWeight r d c R e₀ e ≤ 1 := by
  rw [peelWeight]
  have h0 : 0 ≤ if d e < radMax r e then (1 : ℝ)
      else if e = e₀ ∧ R ≤ d e then R ^ 2 / d e ^ 2 else radMax r e ^ 2 / d e ^ 2 := by
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  refine (mul_le_mul (hc1 e) ?_ h0 zero_le_one).trans_eq (one_mul 1)
  · split_ifs with h1 h2
    · exact le_rfl
    · exact div_le_one_of_le₀ (pow_le_pow_left₀ hR h2.2 2) (sq_nonneg _)
    · exact div_le_one_of_le₀ (pow_le_pow_left₀ (radMax_nonneg hr e) (not_lt.mp h1) 2)
        (sq_nonneg _)

/-- The two end edges of an ear (proof of Lemma 4.45): if `e` has score at
least that of `f`, then `ρ κ_e ρ' κ_f ≤ c_e min(d_e, μ_e)² / d_e² · c_f / d_f²` for radii
`ρ ≤ μ_e`, `0 ≤ ρ' ≤ μ_f`. -/
theorem end_pair_le (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e)
    {e f : Sym2 V} {ρ ρ' : ℝ} (hρμ : ρ ≤ radMax r e) (hρ' : 0 ≤ ρ')
    (hρμ' : ρ' ≤ radMax r f) (hs : peelScore r d f ≤ peelScore r d e) :
    ρ * kappa r d c e * (ρ' * kappa r d c f) ≤
      c e * peelScore r d e ^ 2 / d e ^ 2 * keptWeight d c f := by
  have h1 := mul_kappa_le hd hc hρμ
  have h2 := mul_kappa_le (e := f) hd hc hρμ'
  have hse := peelScore_nonneg hr hd e
  have hsf := peelScore_nonneg hr hd f
  calc ρ * kappa r d c e * (ρ' * kappa r d c f)
      ≤ c e * peelScore r d e / d e ^ 2 * (c f * peelScore r d f / d f ^ 2) :=
        mul_le_mul h1 h2 (mul_nonneg hρ' (kappa_nonneg hr hd hc f))
          (div_nonneg (mul_nonneg (hc e) hse) (sq_nonneg _))
    _ ≤ c e * peelScore r d e / d e ^ 2 * (c f * peelScore r d e / d f ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (mul_nonneg (hc e) hse) (sq_nonneg _))
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (hc f)) (sq_nonneg _)
    _ = c e * peelScore r d e ^ 2 / d e ^ 2 * keptWeight d c f := by
        rw [keptWeight]
        ring

end Scalar

/-! ### The radii along an ear -/

section Radii

variable {r : V → ℝ}

theorem innerProd_nonneg (hr : ∀ v, 0 ≤ r v) : ∀ L : List (V × V), 0 ≤ innerProd r L
  | [] => zero_le_one
  | [_] => zero_le_one
  | _ :: q :: L => mul_nonneg (mul_nonneg (hr _) (hr _)) (innerProd_nonneg hr (q :: L))

/-- `∏_{k=1}^m r_{a_k} r_{b_k} = r_{a₁} (∏_{k<m} r_{b_k} r_{a_{k+1}}) r_{b_m}`. -/
theorem prod_radii_eq (r : V → ℝ) : ∀ (p : V × V) (L : List (V × V)) (l : V × V),
    ((p :: (L ++ [l])).map fun q => r q.1 * r q.2).prod =
      r p.1 * innerProd r (p :: (L ++ [l])) * r l.2
  | p, [], l => by
    simp only [List.nil_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      innerProd]
    ring
  | p, q :: L, l => by
    simp only [List.cons_append]
    rw [List.map_cons, List.prod_cons, prod_radii_eq r q L l, innerProd]
    ring

/-- Grouping the radii of an ear by interior blocks (proof of Corollary 4.47): along a chain,
`∏_{k<m} r_{b_k} r_{a_{k+1}} ≤ ∏_{k<m} ρ([b_k])²` when `0 ≤ r_v ≤ ρ([v])`. -/
theorem innerProd_le {β : Type*} {b : V → β} (ρ : β → ℝ) (hr : ∀ v, 0 ≤ r v)
    (hrρ : ∀ v, r v ≤ ρ (b v)) : ∀ (p : V × V) (L : List (V × V)),
    (p :: L).IsChain (ChainRel b) →
      innerProd r (p :: L) ≤ ((p :: L).dropLast.map fun q => ρ (b q.2) ^ 2).prod
  | p, [], _ => by simp [innerProd]
  | p, q :: L, h => by
    rw [List.isChain_cons_cons] at h
    rw [innerProd, List.dropLast_cons_cons, List.map_cons, List.prod_cons]
    have hpq : r p.2 * r q.1 ≤ ρ (b p.2) ^ 2 := by
      rw [sq]
      refine mul_le_mul (hrρ _) ((hrρ _).trans_eq (congrArg ρ h.1.symm)) (hr _)
        ((hr _).trans (hrρ _))
    exact mul_le_mul hpq (innerProd_le ρ hr hrρ q L h.2) (innerProd_nonneg hr _)
      (sq_nonneg _)

end Radii

/-! ### One exceptional edge in a product -/

/-- If `x` occurs once among the edges of `L`, `F ≤ G` on the other edges and `C · F(x) ≤ G(x)`,
then `C ∏ F ≤ ∏ G` (all nonnegative). -/
theorem mul_prod_le_prod_of_mem {F G : Sym2 V → ℝ} {C : ℝ} (hC : 0 ≤ C) {x : Sym2 V}
    (hF : ∀ e, 0 ≤ F e) (hFG : ∀ e, e ≠ x → F e ≤ G e) (hx : C * F x ≤ G x) :
    ∀ {L : List (Sym2 V)}, L.Nodup → x ∈ L → C * (L.map F).prod ≤ (L.map G).prod
  | [], _, h => absurd h List.not_mem_nil
  | e :: L, hnd, hmem => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.prod_cons]
    have hFG' : ∀ e' ∈ L, e' ≠ x → F e' ≤ G e' := fun e' _ => hFG e'
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rw [← mul_assoc]
      refine mul_le_mul hx (List.prod_map_le_prod_map₀ F G (fun e' _ => hF e') ?_)
        (List.prod_nonneg fun a ha => ?_) ((mul_nonneg hC (hF _)).trans hx)
      · exact fun e' he' => hFG e' fun h => hnd.1 (h ▸ he')
      · obtain ⟨e', _, rfl⟩ := List.mem_map.mp ha
        exact hF e'
    · have hne : e ≠ x := fun h => hnd.1 (h ▸ hmem)
      rw [mul_left_comm]
      exact mul_le_mul (hFG e hne) (mul_prod_le_prod_of_mem hC hF hFG hx hnd.2 hmem)
        (mul_nonneg hC (List.prod_nonneg fun a ha => by
          obtain ⟨e', _, rfl⟩ := List.mem_map.mp ha
          exact hF e')) ((hF e).trans (hFG e hne))

end Peeling

end MultipoleBKT

end
