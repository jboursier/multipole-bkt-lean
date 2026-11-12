/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Peeling.Peel

/-!
# The quadratic estimate (Lemma 4.45, Corollary 4.47, Lemma 4.49(1)–(2))

We prove the estimates of Section 4.11 on the peeling of
Definition 4.43:

* `MultipoleBKT.Peeling.ear_estimate`: **Lemma 4.45** (eq. (4.65)), with constant `C = 1`: for an ear `P = (a₁, b₁), …, (a_m, b_m)` and its deleted
  edge `uv`,
  `∏_{ij ∈ P} a^abs_ij ≤ (∏_{k<m} r_{b_k} r_{a_{k+1}}) ∏_{ij ∈ P ∖ {uv}} d_ij^{-2} c_ij · g_uv`.
* `MultipoleBKT.Peeling.quadratic_estimate`: **Corollary 4.47** (eq. (4.67)), with constant `C = 1`:
  `∏_{ij ∈ E} a^abs_ij ≤ ∏_{S ≠ [v₁]} r_S² ∏_{ij ∈ 𝒯} d_ij^{-2} c_ij ∏_{ij ∈ 𝓕} g_ij`, and the
  paper's form with the sum over `B(·, 𝒯)` (`MultipoleBKT.Peeling.quadratic_estimate_sum`).
* `MultipoleBKT.Peeling.IsStrictEarDecomp.natCard_edgeSet_le`: `|E| ≤ 2(|V_X| - 1)`
  (proof of Corollary 4.47).
* `MultipoleBKT.Peeling.IsPeelingOn.prod_peelWeight_mul_sq_le`,
  `MultipoleBKT.Peeling.IsPeelingOn.prod_peelWeight_le_min_sq`: **Lemma 4.49(2)** (eq. (4.70),
  Lemma 4.49 and proof of Lemma 4.49).
* `MultipoleBKT.Peeling.lemma_4_49_one`: **Lemma 4.49(1)** (`𝓕 ∈ PF(V_X)` and (4.69)).
* `MultipoleBKT.Peeling.IsEulerPeeling`: Definition 4.44,
  the peeling of a graph 2-edge-connected relative to `X` (e.g. `E ∈ 𝖤𝗎𝗅_c^X`, by Lemma 4.37)
  through a minimal skeleton. The existence theorem
  `MultipoleBKT.Peeling.exists_isEulerPeeling_eq_peeledSkeleton` records the specified
  lexicographic skeleton. The API also gives its structure
  (`MultipoleBKT.Peeling.IsEulerPeeling.structure`: `𝒯 ∈ 𝖳^X`, `𝒯 ∪ 𝓕 = Peeled_X(E)` minimally
  2-edge-connected with at most `2(|V_X| - 1)` edges), Lemma 4.49(1)–(2) in that setting
  (`MultipoleBKT.Peeling.IsEulerPeeling.lemma_4_49`,
  `MultipoleBKT.Peeling.IsEulerPeeling.prod_peelWeight_le_min_sq`) and Corollary 4.47 through the
  skeleton (`MultipoleBKT.Peeling.IsEulerPeeling.prod_absWeight_le`).

Corollary 4.47 holds with the single tree `𝒯` in place of the sum over `B(·, 𝒯)`: the sum over
`B(·, 𝒯)` in the paper is a weakening (its proof uses `𝒯 ∈ B(·, 𝒯)`, proof of Corollary 4.47). Consumers that use
`MultipoleBKT.Peeling.quadratic_estimate` do not need Lemma 4.49(3).

The weights are abstract (`MultipoleBKT.Peeling.absWeight` etc.): with `c_ij = 1_{𝓑_ij^c}
1_{d_ij ≤ 17 ε₀ R̄}`, `absWeight r d c` is `a^abs` of Definition 4.29. The paper's constant `C` in
Lemma 4.45 and Corollary 4.47 can be taken equal to `1`.

The block radius `r_S = max_{i ∈ S} r_i` (Definition 4.42) is
`MultipoleBKT.Peeling.blockRadius`, and the set `B((x_i, y_i), T)` of Definition 4.46 is `MultipoleBKT.Peeling.longAgreeingTrees`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Peeling

open Finset SimpleGraph

variable {V β : Type*} {b : V → β}

/-! ### Lemma 4.45: one ear -/

section Ear

variable [DecidableEq V] {r : V → ℝ} {d c : Sym2 V → ℝ} {R : ℝ} {e₀ : Sym2 V}

/-- The weights on the edges of an ear with deleted oriented edge `t`: `g` on `t`, `d^{-2} c` on
the other edges. -/
noncomputable def earWeight (r : V → ℝ) (d c : Sym2 V → ℝ) (R : ℝ) (e₀ : Sym2 V) (t : V × V)
    (e : Sym2 V) : ℝ :=
  if e = edge t then peelWeight r d c R e₀ e else keptWeight d c e

omit [DecidableEq V] in
theorem Ear.prod_map_toList (P : Ear V) (f : V × V → ℝ) :
    (P.toList.map f).prod = f P.first * (P.mid.map f).prod * f P.last := by
  simp only [Ear.toList, List.map_cons, List.map_append, List.map_nil, List.prod_cons,
    List.prod_append, List.prod_nil, mul_one]
  ring

omit [DecidableEq V] in
theorem Ear.prod_map_edges (P : Ear V) (f : Sym2 V → ℝ) :
    (P.edges.map f).prod = (P.toList.map fun p => f (edge p)).prod := by
  rw [Ear.edges, List.map_map]
  rfl

omit [DecidableEq V] in
theorem radMax_le_of_le (hR : ∀ v, r v ≤ R) (e : Sym2 V) : radMax r e ≤ R := by
  induction e using Sym2.ind with
  | h i j => exact max_le (hR i) (hR j)

/-- The algebra of the generic case of Lemma 4.45. -/
theorem ear_alg {inner r₁ r₂ κ₁ κ₂ Mκ Mk W₁ W₂ : ℝ} (hinner : 0 ≤ inner) (hMκ : 0 ≤ Mκ)
    (hM : Mκ ≤ Mk) (hend : r₁ * κ₁ * (r₂ * κ₂) ≤ W₁ * W₂) (hW : 0 ≤ W₁ * W₂) :
    r₁ * inner * r₂ * (κ₁ * Mκ * κ₂) ≤ inner * (W₁ * Mk * W₂) := by
  calc r₁ * inner * r₂ * (κ₁ * Mκ * κ₂) = inner * (r₁ * κ₁ * (r₂ * κ₂)) * Mκ := by ring
    _ ≤ inner * (W₁ * W₂) * Mk :=
        mul_le_mul (mul_le_mul_of_nonneg_left hend hinner) hM hMκ (mul_nonneg hinner hW)
    _ = inner * (W₁ * Mk * W₂) := by ring

omit [DecidableEq V] in
/-- The product of `a^abs` over an ear: `r_{a₁} (∏_{k<m} r_{b_k} r_{a_{k+1}}) r_{b_m} ∏ κ`. -/
theorem Ear.prod_absWeight (P : Ear V) :
    (P.edges.map (absWeight r d c)).prod =
      r P.first.1 * innerProd r P.toList * r P.last.2 *
        (kappa r d c (edge P.first) * (P.mid.map fun p => kappa r d c (edge p)).prod *
          kappa r d c (edge P.last)) := by
  have h1 : (P.edges.map (absWeight r d c)).prod =
      (P.toList.map fun p => r p.1 * r p.2).prod *
        (P.toList.map fun p => kappa r d c (edge p)).prod := by
    rw [Ear.prod_map_edges, ← List.prod_map_mul]
    exact congrArg List.prod (List.map_congr_left fun p _ => absWeight_edge p)
  rw [h1, Ear.prod_map_toList P fun p => kappa r d c (edge p)]
  congr 1
  exact prod_radii_eq r P.first P.mid P.last

omit [DecidableEq V] in
/-- Splitting the edges of an ear with distinct edges. -/
theorem Ear.nodup_edges_iff (P : Ear V) :
    P.edges.Nodup ↔ edge P.first ∉ P.mid.map edge ++ [edge P.last] ∧
      (P.mid.map edge).Nodup ∧ edge P.last ∉ P.mid.map edge := by
  have : P.edges = edge P.first :: (P.mid.map edge ++ [edge P.last]) := by
    simp [Ear.edges, Ear.toList]
  rw [this, List.nodup_cons, List.nodup_append]
  constructor
  · rintro ⟨h1, h2, -, h3⟩
    exact ⟨h1, h2, fun h => h3 _ h _ (List.mem_singleton_self _) rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, List.nodup_singleton _, fun a ha c hc hac => h3 ?_⟩
    rw [List.mem_singleton] at hc
    rwa [hac, hc] at ha

/-- **Lemma 4.45** (eq. (4.65)), with `C = 1`:
for an ear `P = (a₁, b₁), …, (a_m, b_m)` of the peeling whose deleted oriented edge is `t`,
`∏_{ij ∈ P} a^abs_ij ≤ (∏_{k<m} r_{b_k} r_{a_{k+1}}) ∏_{ij ∈ P ∖ {t}} d_ij^{-2} c_ij · g_t`.
Here `R ≥ r_v` for all `v` (the paper's `R = max_v r_v`). -/
theorem ear_estimate {β : Type*} {b : V → β} {U : Finset β} (hr : ∀ v, 0 ≤ r v)
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hR : ∀ v, r v ≤ R) {P : Ear V} {t : V × V}
    (hnd : P.edges.Nodup) (ht : IsEarRemoval b r d R e₀ U P t) :
    (P.edges.map (absWeight r d c)).prod ≤
      innerProd r P.toList * (P.edges.map (earWeight r d c R e₀ t)).prod := by
  obtain ⟨hnd1, -, hnd3⟩ := P.nodup_edges_iff.mp hnd
  have hinner := innerProd_nonneg hr P.toList
  have hκ0 : 0 ≤ (P.mid.map fun p => kappa r d c (edge p)).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
      exact kappa_nonneg hr hd hc _
  have hκk : (P.mid.map fun p => kappa r d c (edge p)).prod ≤
      (P.mid.map fun p => keptWeight d c (edge p)).prod :=
    List.prod_map_le_prod_map₀ _ _ (fun p _ => kappa_nonneg hr hd hc _)
      (fun p _ => kappa_le_keptWeight hd hc _)
  rw [P.prod_absWeight]
  rcases ht with ⟨he₀, hRd, hte, -⟩ | ⟨hne, ⟨rfl, hs⟩ | ⟨rfl, hs⟩⟩
  · -- rule (1): the longest edge `e₀` is deleted
    have hR0 : 0 ≤ R := (hr P.first.1).trans (hR _)
    have hends : r P.first.1 * r P.last.2 ≤ R ^ 2 := by
      rw [sq]
      exact mul_le_mul (hR _) (hR _) (hr _) hR0
    have hκP : (P.toList.map fun p => kappa r d c (edge p)).prod =
        kappa r d c (edge P.first) * (P.mid.map fun p => kappa r d c (edge p)).prod *
          kappa r d c (edge P.last) := Ear.prod_map_toList _ _
    have hmain : R ^ 2 * (P.edges.map (kappa r d c)).prod ≤
        (P.edges.map (earWeight r d c R e₀ t)).prod := by
      refine mul_prod_le_prod_of_mem (sq_nonneg R) (kappa_nonneg hr hd hc) (fun e he => ?_) ?_
        hnd he₀
      · rw [earWeight, ite_eq_right (fun h => he (h.trans hte))]
        exact kappa_le_keptWeight hd hc e
      · rw [earWeight, ite_eq_left hte.symm]
        exact (mul_le_mul_of_nonneg_left (kappa_le_keptWeight hd hc e₀) (sq_nonneg R)).trans
          (sq_mul_keptWeight_le (radMax_le_of_le hR e₀) hRd)
    rw [Ear.prod_map_edges (f := kappa r d c), hκP] at hmain
    calc r P.first.1 * innerProd r P.toList * r P.last.2 *
          (kappa r d c (edge P.first) * (P.mid.map fun p => kappa r d c (edge p)).prod *
            kappa r d c (edge P.last))
        = innerProd r P.toList * (r P.first.1 * r P.last.2) *
            (kappa r d c (edge P.first) * (P.mid.map fun p => kappa r d c (edge p)).prod *
              kappa r d c (edge P.last)) := by ring
      _ ≤ innerProd r P.toList * R ^ 2 *
            (kappa r d c (edge P.first) * (P.mid.map fun p => kappa r d c (edge p)).prod *
              kappa r d c (edge P.last)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hends hinner)
            (mul_nonneg (mul_nonneg (kappa_nonneg hr hd hc _) hκ0) (kappa_nonneg hr hd hc _))
      _ = innerProd r P.toList * (R ^ 2 *
            (kappa r d c (edge P.first) * (P.mid.map fun p => kappa r d c (edge p)).prod *
              kappa r d c (edge P.last))) := by ring
      _ ≤ innerProd r P.toList * (P.edges.map (earWeight r d c R e₀ t)).prod :=
          mul_le_mul_of_nonneg_left hmain hinner
  · -- rule (2), the first edge is deleted
    have hmid : (P.mid.map fun p => earWeight r d c R e₀ P.first.swap (edge p)).prod =
        (P.mid.map fun p => keptWeight d c (edge p)).prod := by
      refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
      rw [earWeight, edge_swap, ite_eq_right (show ¬ edge p = edge P.first from fun h =>
        hnd1 (List.mem_append_left _ (h ▸ List.mem_map_of_mem hp)))]
    have hlast : earWeight r d c R e₀ P.first.swap (edge P.last) =
        keptWeight d c (edge P.last) := by
      rw [earWeight, edge_swap, ite_eq_right (show ¬ edge P.last = edge P.first from fun h =>
        hnd1 (List.mem_append_right _ (h ▸ List.mem_singleton_self _)))]
    have hfirst : earWeight r d c R e₀ P.first.swap (edge P.first) =
        peelWeight r d c R e₀ (edge P.first) := by
      rw [earWeight, edge_swap, ite_eq_left rfl]
    rw [Ear.prod_map_edges, Ear.prod_map_toList, hfirst, hlast, hmid]
    have hne' : ¬ (edge P.first = e₀ ∧ R ≤ d (edge P.first)) := fun h =>
      hne ⟨h.1 ▸ List.mem_map_of_mem P.first_mem_toList, h.1 ▸ h.2⟩
    have hg := peelScore_sq_le_peelWeight (r := r) hd hc hne'
    have hkl := keptWeight_nonneg (d := d) hc (edge P.last)
    refine ear_alg hinner hκ0 hκk ?_ (mul_nonneg (peelWeight_nonneg hc _ _) hkl)
    exact (end_pair_le hr hd hc (le_radMax_left P.first) (hr P.last.2) (le_radMax_right P.last)
      hs).trans (mul_le_mul_of_nonneg_right hg hkl)
  · -- rule (2), the last edge is deleted
    have hmid : (P.mid.map fun p => earWeight r d c R e₀ P.last (edge p)).prod =
        (P.mid.map fun p => keptWeight d c (edge p)).prod := by
      refine congrArg List.prod (List.map_congr_left fun p hp => ?_)
      rw [earWeight, ite_eq_right (show ¬ edge p = edge P.last from fun h =>
        hnd3 (h ▸ List.mem_map_of_mem hp))]
    have hfirst : earWeight r d c R e₀ P.last (edge P.first) =
        keptWeight d c (edge P.first) := by
      rw [earWeight, ite_eq_right (show ¬ edge P.first = edge P.last from fun h =>
        hnd1 (List.mem_append_right _ (h ▸ List.mem_singleton_self _)))]
    have hlast : earWeight r d c R e₀ P.last (edge P.last) =
        peelWeight r d c R e₀ (edge P.last) := by
      rw [earWeight, ite_eq_left rfl]
    rw [Ear.prod_map_edges, Ear.prod_map_toList, hfirst, hlast, hmid]
    have hne' : ¬ (edge P.last = e₀ ∧ R ≤ d (edge P.last)) := fun h =>
      hne ⟨h.1 ▸ List.mem_map_of_mem P.last_mem_toList, h.1 ▸ h.2⟩
    have hg := peelScore_sq_le_peelWeight (r := r) hd hc hne'
    have hkf := keptWeight_nonneg (d := d) hc (edge P.first)
    refine ear_alg hinner hκ0 hκk ?_ (mul_nonneg hkf (peelWeight_nonneg hc _ _))
    have := (end_pair_le hr hd hc (le_radMax_right P.last) (hr P.first.1)
      (le_radMax_left P.first) hs).trans (mul_le_mul_of_nonneg_right hg hkf)
    linarith [mul_comm (r P.first.1 * kappa r d c (edge P.first))
      (r P.last.2 * kappa r d c (edge P.last)),
      mul_comm (peelWeight r d c R e₀ (edge P.last)) (keptWeight d c (edge P.first))]

end Ear

/-! ### Corollary 4.47 -/

section Quadratic

variable [DecidableEq β] {E : SimpleGraph V}

/-- The interior blocks of an ear sequence relative to `U` are distinct, outside `U`, and together
with `U` they are the covered blocks. -/
theorem IsEarSeq.interiors : ∀ {U : Finset β} {Ps : List (Ear V)}, IsEarSeq b E U Ps →
    (Ps.flatMap (Ear.interior b)).Nodup ∧ (∀ B ∈ Ps.flatMap (Ear.interior b), B ∉ U) ∧
      covered b U Ps = U ∪ (Ps.flatMap (Ear.interior b)).toFinset
  | _, [], _ => by simp [covered_nil]
  | U, P :: Ps, ⟨hP, hPs⟩ => by
    obtain ⟨h1, h2, h3⟩ := IsEarSeq.interiors hPs
    rw [List.flatMap_cons, List.nodup_append, covered_cons, h3, hP.union_blocks,
      List.toFinset_append, union_assoc]
    refine ⟨⟨hP.nodup_interior, h1, fun a ha c hc hac => ?_⟩, fun B hB => ?_, rfl⟩
    · refine h2 c hc (mem_union_right _ ?_)
      rw [← hac]
      simp only [Ear.blocks, mem_insert, List.mem_toFinset]
      exact Or.inr (Or.inr ha)
    · rcases List.mem_append.mp hB with hB | hB
      · exact hP.interior_notMem B hB
      · exact fun h => h2 B hB (mem_union_left _ h)

variable [DecidableEq V] {r : V → ℝ} {d c : Sym2 V → ℝ} {R : ℝ} {e₀ : Sym2 V}

/-- The ear-by-ear estimate behind Corollary 4.47 (eq. (4.68)), for a
weight `W` that agrees on each ear with `g` on its deleted edge and with `d^{-2} c` elsewhere. -/
theorem prod_absWeight_le_aux (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e)
    (hR : ∀ v, r v ≤ R) (ρ : β → ℝ) (hrρ : ∀ v, r v ≤ ρ (b v)) (W : Sym2 V → ℝ) :
    ∀ {U U' : Finset β} {Qs : List (Ear V × (V × V))}, IsEarSeq b E U' (Qs.map Prod.fst) →
      IsPeelingSeq b r d R e₀ U Qs →
      (∀ Q ∈ Qs, ∀ e ∈ Q.1.edges, W e = earWeight r d c R e₀ Q.2 e) →
      (((Qs.map Prod.fst).flatMap Ear.edges).map (absWeight r d c)).prod ≤
        (((Qs.map Prod.fst).flatMap (Ear.interior b)).map fun S => ρ S ^ 2).prod *
          (((Qs.map Prod.fst).flatMap Ear.edges).map W).prod
  | _, _, [], _, _, _ => by simp
  | U, U', Q :: Qs, ⟨hP, hPs⟩, ⟨hQ, hQs⟩, hW => by
    have ih := prod_absWeight_le_aux hr hd hc hR ρ hrρ W hPs hQs
      (fun Q' hQ' => hW Q' (List.mem_cons_of_mem _ hQ'))
    simp only [List.map_cons, List.flatMap_cons, List.map_append, List.prod_append]
    have hWQ : (Q.1.edges.map W).prod = (Q.1.edges.map (earWeight r d c R e₀ Q.2)).prod :=
      congrArg List.prod (List.map_congr_left fun e he => hW Q List.mem_cons_self e he)
    have hWQ0 : 0 ≤ (Q.1.edges.map W).prod := by
      rw [hWQ]
      refine List.prod_nonneg fun x hx => ?_
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      rw [earWeight]
      split_ifs
      · exact peelWeight_nonneg hc _ _
      · exact keptWeight_nonneg hc _
    have hear := ear_estimate (c := c) hr hd hc hR hP.nodup_edges hQ
    have hinner : innerProd r Q.1.toList ≤ ((Q.1.interior b).map fun S => ρ S ^ 2).prod := by
      have := innerProd_le ρ hr hrρ Q.1.first (Q.1.mid ++ [Q.1.last]) hP.isChain
      rw [← List.cons_append, List.dropLast_concat] at this
      rw [Ear.interior_eq, List.map_map]
      exact this
    have hI0 : 0 ≤ ((Q.1.interior b).map fun S => ρ S ^ 2).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨S, -, rfl⟩ := List.mem_map.mp hx
        exact sq_nonneg _
    have hA0 : 0 ≤ (((Qs.map Prod.fst).flatMap Ear.edges).map (absWeight r d c)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
        exact absWeight_nonneg hr hd hc _
    have hQe : (Q.1.edges.map (absWeight r d c)).prod ≤
        ((Q.1.interior b).map fun S => ρ S ^ 2).prod * (Q.1.edges.map W).prod := by
      rw [hWQ]
      exact hear.trans (mul_le_mul_of_nonneg_right hinner (by rw [← hWQ]; exact hWQ0))
    calc (Q.1.edges.map (absWeight r d c)).prod *
          (((Qs.map Prod.fst).flatMap Ear.edges).map (absWeight r d c)).prod
        ≤ (((Q.1.interior b).map fun S => ρ S ^ 2).prod * (Q.1.edges.map W).prod) *
          ((((Qs.map Prod.fst).flatMap (Ear.interior b)).map fun S => ρ S ^ 2).prod *
            (((Qs.map Prod.fst).flatMap Ear.edges).map W).prod) :=
          mul_le_mul hQe ih hA0 (mul_nonneg hI0 hWQ0)
      _ = _ := by ring

variable [Fintype β] {v₁ : V} {Qs : List (Ear V × (V × V))}

theorem IsPeelingOn.edgeFinset_eq [Fintype E.edgeSet] (h : IsPeelingOn b E r d v₁ e₀ Qs) :
    E.edgeFinset = ((Qs.map Prod.fst).flatMap Ear.edges).toFinset := by
  ext e
  rw [mem_edgeFinset, List.mem_toFinset, h.decomp.mem_iff]

open scoped Classical in
/-- **Corollary 4.47** (generic form, `C = 1`): for an admissible peeling and any bound
`r_v ≤ ρ([v])` by block radii,
`∏_{ij ∈ E} a^abs_ij ≤ ∏_{S ≠ [v₁]} ρ_S² ∏_{ij ∈ 𝒯} d_ij^{-2} c_ij ∏_{ij ∈ 𝓕} g_ij`. -/
theorem IsPeelingOn.prod_absWeight_le [Fintype V] (h : IsPeelingOn b E r d v₁ e₀ Qs)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (ρ : β → ℝ)
    (hrρ : ∀ v, r v ≤ ρ (b v)) :
    ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
      (∏ S ∈ univ.erase (b v₁), ρ S ^ 2) *
        (∏ e ∈ (keptGraph E Qs).edgeFinset, keptWeight d c e) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e := by
  set L := (Qs.map Prod.fst).flatMap Ear.edges
  set W : Sym2 V → ℝ := fun e =>
    if e ∈ removedEdges Qs then peelWeight r d c (r v₁) e₀ e else keptWeight d c e
  have hW : ∀ Q ∈ Qs, ∀ e ∈ Q.1.edges, W e = earWeight r d c (r v₁) e₀ Q.2 e := by
    intro Q hQ e he
    simp only [W, earWeight, h.isRemoval.mem_removedEdges_iff h.decomp.nodup Q hQ e he]
  have haux := prod_absWeight_le_aux hr hd hc h.le_radius ρ hrρ W h.decomp.isEarSeq h.rule hW
  obtain ⟨hInd, hInot, hcov⟩ := h.decomp.isEarSeq.interiors
  rw [h.decomp.covered_eq] at hcov
  have hIfin : ((Qs.map Prod.fst).flatMap (Ear.interior b)).toFinset = univ.erase (b v₁) := by
    ext B
    rw [mem_erase]
    constructor
    · intro hB
      exact ⟨fun h' => hInot B (List.mem_toFinset.mp hB) (mem_singleton.mpr h'), mem_univ _⟩
    · rintro ⟨hne, -⟩
      have : B ∈ ({b v₁} : Finset β) ∪ _ := hcov ▸ mem_univ B
      rcases mem_union.mp this with h' | h'
      · exact absurd (mem_singleton.mp h') hne
      · exact h'
  have hE : E.edgeFinset = L.toFinset := h.edgeFinset_eq
  rw [hE, List.prod_toFinset _ h.decomp.nodup, ← hIfin, List.prod_toFinset _ hInd]
  refine haux.trans (le_of_eq ?_)
  rw [mul_assoc]
  congr 1
  rw [← List.prod_toFinset _ h.decomp.nodup, ← hE, prod_ite, mul_comm]
  have hrem : E.edgeFinset.filter (· ∈ removedEdges Qs) = (removedGraph Qs).edgeFinset := by
    ext e
    rw [mem_filter, mem_edgeFinset, mem_edgeFinset, removedGraph, edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨he, hmem⟩
      exact ⟨hmem, fun hd' => (SimpleGraph.not_isDiag_of_mem_edgeSet _ he) hd'⟩
    · rintro ⟨hmem, -⟩
      exact ⟨h.removedEdges_mem hmem, hmem⟩
  have hkept : E.edgeFinset.filter (fun e => ¬ e ∈ removedEdges Qs) =
      (keptGraph E Qs).edgeFinset := by
    ext e
    rw [mem_filter, mem_edgeFinset, mem_edgeFinset, keptGraph, edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_ofPred_eq]
  rw [hrem, hkept]

end Quadratic

/-! ### Lemma 4.49(2): the discarded weights -/

section HateF

variable [DecidableEq β] [Fintype β] [DecidableEq V] {E : SimpleGraph V} {r : V → ℝ}
  {d c : Sym2 V → ℝ} {v₁ : V} {e₀ : Sym2 V} {Qs : List (Ear V × (V × V))}

open scoped Classical in
/-- `∏_{ij ∈ 𝓕} g_ij ≤ 1` when `0 ≤ c ≤ 1`. -/
theorem IsPeelingOn.prod_peelWeight_le_one [Fintype V] (h : IsPeelingOn b E r d v₁ e₀ Qs)
    (hr : ∀ v, 0 ≤ r v) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) :
    ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e ≤ 1 :=
  prod_le_one₀ (fun _ _ => peelWeight_nonneg hc _ _)
    (fun _ _ => peelWeight_le_one hr hc1 ((hr _).trans (h.le_radius v₁)) _ _)

open scoped Classical in
/-- **Lemma 4.49(2)** (eq. (4.70) in the proof of Lemma 4.49), multiplicative
form: for every kept edge `e ∈ 𝒯`, `(∏_{ij ∈ 𝓕} g_ij) d_e² ≤ (max_i r_i)²`, when `0 ≤ c ≤ 1`. -/
theorem IsPeelingOn.prod_peelWeight_mul_sq_le [Fintype V] (h : IsPeelingOn b E r d v₁ e₀ Qs)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {e : Sym2 V} (he : e ∈ (keptGraph E Qs).edgeSet) :
    (∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f) * d e ^ 2 ≤ r v₁ ^ 2 := by
  have hP1 := h.prod_peelWeight_le_one hr hc hc1
  have hP0 : 0 ≤ ∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f :=
    prod_nonneg fun f _ => peelWeight_nonneg hc _ _
  have heE : e ∈ E.edgeSet := (edgeSet_mono (deleteEdges_le _)) he
  rcases le_or_gt (d e) (r v₁) with hle | hlt
  · calc (∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f) * d e ^ 2
        ≤ 1 * d e ^ 2 := mul_le_mul_of_nonneg_right hP1 (sq_nonneg _)
      _ ≤ r v₁ ^ 2 := by rw [one_mul]; exact pow_le_pow_left₀ (hd e) hle 2
  · -- the longest edge is long, so it is discarded with weight `R² / d_{e₀}²`
    have hd₀ : d e ≤ d e₀ := h.le_longest e heE
    have hRd : r v₁ ≤ d e₀ := hlt.le.trans hd₀
    have hpos : 0 < d e₀ := ((hr v₁).trans_lt hlt).trans_le hd₀
    have hmem : e₀ ∈ (removedGraph Qs).edgeFinset := by
      rw [mem_edgeFinset, removedGraph, edgeSet_fromEdgeSet, Set.mem_sdiff]
      exact ⟨h.longest_mem_removedEdges hRd, SimpleGraph.not_isDiag_of_mem_edgeSet _
        h.longest_mem⟩
    have hrad : radMax r e₀ ≤ r v₁ := radMax_le_of_le h.le_radius e₀
    have hg : peelWeight r d c (r v₁) e₀ e₀ ≤ r v₁ ^ 2 / d e₀ ^ 2 := by
      rw [peelWeight, ite_eq_right (not_lt.mpr (hrad.trans hRd)), ite_eq_left ⟨rfl, hRd⟩]
      exact mul_le_of_le_one_left (div_nonneg (sq_nonneg _) (sq_nonneg _)) (hc1 _)
    have hprod : ∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f ≤
        r v₁ ^ 2 / d e₀ ^ 2 := by
      rw [← mul_prod_erase _ _ hmem]
      refine (mul_le_of_le_one_right (peelWeight_nonneg hc _ _) ?_).trans hg
      exact prod_le_one₀ (fun f _ => peelWeight_nonneg hc _ _)
        (fun f _ => peelWeight_le_one hr hc1 ((hr _).trans (h.le_radius v₁)) _ _)
    calc (∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f) * d e ^ 2
        ≤ r v₁ ^ 2 / d e₀ ^ 2 * d e₀ ^ 2 :=
          mul_le_mul hprod (pow_le_pow_left₀ (hd e) hd₀ 2) (sq_nonneg _)
            (div_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = r v₁ ^ 2 := div_mul_cancel₀ _ (pow_pos hpos 2).ne'

open scoped Classical in
/-- **Lemma 4.49(2)** (eq. (4.70)) in the paper's form: if `e` is a longest kept edge and
`d_e > 0`, then `∏_{ij ∈ 𝓕} g_ij ≤ min(max_i r_i / max_{e ∈ 𝒯} d_e, 1)²`. -/
theorem IsPeelingOn.prod_peelWeight_le_min_sq [Fintype V] (h : IsPeelingOn b E r d v₁ e₀ Qs)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    {e : Sym2 V} (he : e ∈ (keptGraph E Qs).edgeSet) (hpos : 0 < d e) :
    ∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f ≤ min (r v₁ / d e) 1 ^ 2 := by
  have h1 := h.prod_peelWeight_le_one hr hc hc1
  have h2 := h.prod_peelWeight_mul_sq_le hr hd hc hc1 he
  rcases le_total (r v₁ / d e) 1 with hle | hle
  · rw [min_eq_left hle, div_pow, le_div_iff₀ (pow_pos hpos 2)]
    exact h2
  · rw [min_eq_right hle, one_pow]
    exact h1

end HateF

/-! ### Relative to a subpartition -/

section Subpartition

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

/-- The block radius `r_S = max_{i ∈ S} r_i` (Definition 4.42). -/
noncomputable def blockRadius (r : X.biUnion id → ℝ) (S : X) : ℝ :=
  (univ.filter fun i => blockOf hX i = S).sup'
    (by
      obtain ⟨i, hi⟩ := blockOf_surjective hX S
      exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩) r

variable {hX}

theorem le_blockRadius (r : X.biUnion id → ℝ) (i : X.biUnion id) :
    r i ≤ blockRadius hX r (blockOf hX i) := by
  unfold blockRadius
  apply le_sup'
  simp

open scoped Classical in
/-- The set `B((x_i, y_i), T)` of Definition 4.46: the trees
`T' ∈ 𝖳^X` that coincide with `T` on the edges with `d_ij ≥ max(r_i, r_j)`. -/
noncomputable def longAgreeingTrees (X : Finset (Finset ℕ)) (r : X.biUnion id → ℝ)
    (d : Sym2 (X.biUnion id) → ℝ) (T : SimpleGraph (X.biUnion id)) :
    Finset (SimpleGraph (X.biUnion id)) :=
  (relTrees X).filter fun T' =>
    ∀ e, (e ∈ T'.edgeSet ∧ radMax r e ≤ d e) ↔ (e ∈ T.edgeSet ∧ radMax r e ≤ d e)

theorem self_mem_longAgreeingTrees {r : X.biUnion id → ℝ} {d : Sym2 (X.biUnion id) → ℝ}
    {T : SimpleGraph (X.biUnion id)} (hT : IsRelTree X T) : T ∈ longAgreeingTrees X r d T := by
  classical
  rw [longAgreeingTrees, mem_filter, mem_relTrees]
  exact ⟨hT, fun _ => Iff.rfl⟩

variable {E : SimpleGraph (X.biUnion id)} {r : X.biUnion id → ℝ} {d c : Sym2 (X.biUnion id) → ℝ}
  {v₁ : X.biUnion id} {e₀ : Sym2 (X.biUnion id)}
  {Qs : List (Ear (X.biUnion id) × (X.biUnion id × X.biUnion id))}

/-- The edge count in the proof of Corollary 4.47: a graph with a strict ear
decomposition relative to `X`, e.g. a minimally 2-edge-connected one, has at most `2(|V_X| - 1)`
edges. -/
theorem IsStrictEarDecomp.natCard_edgeSet_le {S₁ : X} {Ps : List (Ear (X.biUnion id))}
    (hD : IsStrictEarDecomp hX E S₁ Ps) : Nat.card E.edgeSet ≤ 2 * ((X.biUnion id).card - 1) := by
  have h1 := IsStrictEarDecompOn.natCard_edgeSet_le hD
  rw [Fintype.card_coe] at h1
  have h2 : X.card ≤ (X.biUnion id).card :=
    card_le_card_biUnion (fun S hS S' hS' hne => hX.2 hS hS' hne) hX.1
  omega

open scoped Classical in
/-- **Corollary 4.47** (eq. (4.67)), with `C = 1`: for the
peeling of Definition 4.43 of `E` (minimally 2-edge-connected relative to `X`), with `T = 𝒯^X` and
`F = 𝓕^X`, `∏_{ij ∈ E} a^abs_ij ≤ ∏_{S ∈ X, S ≠ [v₁]} r_S² ∏_{ij ∈ T} d_ij^{-2} c_ij
∏_{ij ∈ F} g_ij`. -/
theorem quadratic_estimate (h : IsPeeling hX E r d v₁ e₀ Qs) (hr : ∀ v, 0 ≤ r v)
    (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) :
    ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
      (∏ S ∈ univ.erase (blockOf hX v₁), blockRadius hX r S ^ 2) *
        (∏ e ∈ (keptGraph E Qs).edgeFinset, keptWeight d c e) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e :=
  IsPeelingOn.prod_absWeight_le h hr hd hc _ (le_blockRadius r)

open scoped Classical in
/-- **Corollary 4.47** in the paper's form (eq. (4.67)): there is `C > 0` such that for every
peeling, `∏_{ij ∈ E} a^abs_ij ≤ C^{|V_X|} ∏_{S ≠ [v₁]} r_S² ∑_{T' ∈ B(·, T)} ∏_{ij ∈ T'}
d_ij^{-2} c_ij ∏_{ij ∈ F} g_ij` (with `C = 1`). -/
theorem quadratic_estimate_sum : ∃ C : ℝ, 0 < C ∧
    ∀ {X : Finset (Finset ℕ)} {hX : IsSubpartition X} {E : SimpleGraph (X.biUnion id)}
      {r : X.biUnion id → ℝ} {d c : Sym2 (X.biUnion id) → ℝ} {v₁ : X.biUnion id}
      {e₀ : Sym2 (X.biUnion id)} {Qs : List (Ear (X.biUnion id) × (X.biUnion id × X.biUnion id))},
      E ≤ interEdges X → IsPeeling hX E r d v₁ e₀ Qs → (∀ v, 0 ≤ r v) → (∀ e, 0 ≤ d e) →
      (∀ e, 0 ≤ c e) →
      ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
        C ^ (X.biUnion id).card * (∏ S ∈ univ.erase (blockOf hX v₁), blockRadius hX r S ^ 2) *
          (∑ T' ∈ longAgreeingTrees X r d (keptGraph E Qs),
            ∏ e ∈ T'.edgeFinset, keptWeight d c e) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e := by
  refine ⟨1, one_pos, fun {X hX E r d c v₁ e₀ Qs} hE h hr hd hc => ?_⟩
  refine (quadratic_estimate h hr hd hc).trans ?_
  rw [one_pow, one_mul]
  have hrS : 0 ≤ ∏ S ∈ univ.erase (blockOf hX v₁), blockRadius hX r S ^ 2 :=
    prod_nonneg fun S _ => sq_nonneg _
  have hg : 0 ≤ ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e :=
    prod_nonneg fun e _ => peelWeight_nonneg hc _ _
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hrS) hg
  have hT := self_mem_longAgreeingTrees (r := r) (d := d) (h.isRelTree hE)
  have key := single_le_sum (f := fun T' : SimpleGraph (X.biUnion id) =>
    ∏ e ∈ T'.edgeFinset, keptWeight d c e)
    (fun _ _ => prod_nonneg fun e _ => keptWeight_nonneg hc e) hT
  convert key using 1

open scoped Classical in
/-- **Lemma 4.49(1)**: for the peeling of
Definition 4.43, `𝓕^X ∈ PF(V_X)`; and for nonnegative weights `g`,
`∑_{F ∈ PF(V_X)} ∏_{ij ∈ F} g_ij ≤ ∏_{i ∈ V_X} (1 + ∑_{j ≠ i} g_ij)`. -/
theorem lemma_4_49_one (h : IsPeeling hX E r d v₁ e₀ Qs) (g : Sym2 (X.biUnion id) → ℝ)
    (hg : ∀ e, 0 ≤ g e) :
    removedGraph Qs ∈ pseudoforests ∧
      ∑ F ∈ pseudoforests, ∏ e ∈ F.edgeFinset, g e ≤
        ∏ i, (1 + ∑ j ∈ univ.erase i, g s(i, j)) :=
  ⟨mem_pseudoforests.mpr (IsPeelingOn.isPseudoforest h), sum_pseudoforests_le g hg⟩

/-! ### The peeling of a 2-edge-connected graph -/

/-- The admissible peeling data of Definition 4.44, for a graph
`E` 2-edge-connected relative to `X` (by Lemma 4.37 this covers `E ∈ 𝖤𝗎𝗅_c^X`): `E'` is a
minimal skeleton and `Qs` an admissible peeling of `E'`. Then `𝒯^X(·, E) = 𝒯^X(·, E')` is
`keptGraph E' Qs` and `𝓕^X(·, E)` is `removedGraph Qs`. -/
def IsEulerPeeling (hX : IsSubpartition X) (E E' : SimpleGraph (X.biUnion id))
    (r : X.biUnion id → ℝ) (d : Sym2 (X.biUnion id) → ℝ) (v₁ : X.biUnion id)
    (e₀ : Sym2 (X.biUnion id)) (Qs : List (Ear (X.biUnion id) × (X.biUnion id × X.biUnion id))) :
    Prop :=
  IsPeeledSkeleton X E E' ∧ IsPeeling hX E' r d v₁ e₀ Qs

/-- The peeling uses the lexicographically first minimal skeleton of
Definition 4.38.
The ear peeling of this skeleton is the extension in Definition 4.44. -/
theorem exists_isEulerPeeling_eq_peeledSkeleton (hE : Parity.IsRelTwoEdgeConnected X E)
    (r : X.biUnion id → ℝ) (d : Sym2 (X.biUnion id) → ℝ) :
    ∃ E' v₁ e₀ Qs, E' = peeledSkeleton E hE ∧ IsEulerPeeling hX E E' r d v₁ e₀ Qs := by
  have hs := peeledSkeleton_spec E hE
  obtain ⟨v₁, e₀, Qs, hP⟩ := exists_isPeeling (hX := hX) (hs.isRelMinTwoEdgeConnected hX) r d
  exact ⟨peeledSkeleton E hE, v₁, e₀, Qs, rfl, hs, hP⟩

/-- The peeling of Definition 4.44 exists for every graph 2-edge-connected relative to `X`. -/
theorem exists_isEulerPeeling (hE : Parity.IsRelTwoEdgeConnected X E) (r : X.biUnion id → ℝ)
    (d : Sym2 (X.biUnion id) → ℝ) : ∃ E' v₁ e₀ Qs, IsEulerPeeling hX E E' r d v₁ e₀ Qs := by
  obtain ⟨E', v₁, e₀, Qs, _, hP⟩ := exists_isEulerPeeling_eq_peeledSkeleton (hX := hX) hE r d
  exact ⟨E', v₁, e₀, Qs, hP⟩

/-- Definition 4.44,
with the selected skeleton recorded for an Eulerian connected graph.
Lemma 4.37 supplies its two-edge-connectivity. -/
theorem exists_isEulerPeeling_of_eulerian_eq_peeledSkeleton
    (hE : Parity.IsRelEulerianConnected X E) (r : X.biUnion id → ℝ)
    (d : Sym2 (X.biUnion id) → ℝ) :
    ∃ E' v₁ e₀ Qs, E' = peeledSkeleton E (Parity.lemma_4_37 hX hE) ∧
      IsEulerPeeling hX E E' r d v₁ e₀ Qs :=
  exists_isEulerPeeling_eq_peeledSkeleton (Parity.lemma_4_37 hX hE) r d

/-- The peeling of Definition 4.44 exists for every `E ∈ 𝖤𝗎𝗅_c^X` (by Lemma 4.37,
`MultipoleBKT.Parity.lemma_4_37`). -/
theorem exists_isEulerPeeling_of_eulerian (hE : Parity.IsRelEulerianConnected X E)
    (r : X.biUnion id → ℝ) (d : Sym2 (X.biUnion id) → ℝ) :
    ∃ E' v₁ e₀ Qs, IsEulerPeeling hX E E' r d v₁ e₀ Qs :=
  exists_isEulerPeeling (Parity.lemma_4_37 hX hE) r d

/-- The structure of the peeling of Definition 4.44: `𝒯 ∈ 𝖳^X`, `𝒯 ∪ 𝓕 = Peeled_X(E) ⊆ E` is
minimally 2-edge-connected relative to `X` (the fact used in the proof of Lemma 4.55), and it has at most
`2(|V_X| - 1)` edges. -/
theorem IsEulerPeeling.structure {E' : SimpleGraph (X.biUnion id)} (hE : E ≤ interEdges X)
    (h : IsEulerPeeling hX E E' r d v₁ e₀ Qs) :
    IsRelTree X (keptGraph E' Qs) ∧ keptGraph E' Qs ⊔ removedGraph Qs = E' ∧ E' ≤ E ∧
      Parity.IsRelMinTwoEdgeConnected X E' ∧ Nat.card E'.edgeSet ≤ 2 * ((X.biUnion id).card - 1) :=
  ⟨h.2.isRelTree (h.1.1.trans hE), IsPeelingOn.keptGraph_sup_removedGraph h.2, h.1.1,
    h.1.isRelMinTwoEdgeConnected hX, IsStrictEarDecomp.natCard_edgeSet_le h.2.decomp⟩

open scoped Classical in
/-- **Lemma 4.49(1)–(2)** for the peeling of Definition 4.44, with `T = 𝒯^X(·, E)`, `F = 𝓕^X(·, E)`, `0 ≤ c ≤ 1`: `F ∈ PF(V_X)`,
`∏_{ij ∈ F} g_ij ≤ 1`, and `(∏_{ij ∈ F} g_ij) d_e² ≤ (max_i r_i)²` for every `e ∈ T`. -/
theorem IsEulerPeeling.lemma_4_49 {E' : SimpleGraph (X.biUnion id)}
    (h : IsEulerPeeling hX E E' r d v₁ e₀ Qs) (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e)
    (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) :
    removedGraph Qs ∈ pseudoforests ∧
      ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e ≤ 1 ∧
      ∀ e ∈ (keptGraph E' Qs).edgeSet,
        (∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f) * d e ^ 2 ≤
          r v₁ ^ 2 :=
  ⟨mem_pseudoforests.mpr (IsPeelingOn.isPseudoforest h.2),
    IsPeelingOn.prod_peelWeight_le_one h.2 hr hc hc1,
    fun _ he => IsPeelingOn.prod_peelWeight_mul_sq_le h.2 hr hd hc hc1 he⟩

open scoped Classical in
/-- (4.70) for the peeling of Definition 4.44, in the paper's form: if `e` is a longest edge
of `T = 𝒯^X(·, E)` and `d_e > 0`, then `∏_{ij ∈ F} g_ij ≤ min(max_i r_i / d_e, 1)²`. -/
theorem IsEulerPeeling.prod_peelWeight_le_min_sq {E' : SimpleGraph (X.biUnion id)}
    (h : IsEulerPeeling hX E E' r d v₁ e₀ Qs) (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e)
    (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1) {e : Sym2 (X.biUnion id)}
    (he : e ∈ (keptGraph E' Qs).edgeSet) (hpos : 0 < d e) :
    ∏ f ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ f ≤ min (r v₁ / d e) 1 ^ 2 :=
  IsPeelingOn.prod_peelWeight_le_min_sq h.2 hr hd hc hc1 he hpos

open scoped Classical in
/-- Corollary 4.47 for a graph `E` 2-edge-connected relative to `X` (e.g. `E ∈ 𝖤𝗎𝗅_c^X`) through
its skeleton `E' = Peeled_X(E)` (as used in the proof of Proposition 4.23): if the
weights of the edges of `E` are at most `1` (as `a^abs_ij ≤ 1/M` on `𝓑_ij^c`), then
`∏_{ij ∈ E} a^abs_ij ≤ ∏_{S ≠ [v₁]} r_S² ∏_{ij ∈ 𝒯} d_ij^{-2} c_ij ∏_{ij ∈ 𝓕} g_ij`. -/
theorem IsEulerPeeling.prod_absWeight_le {E' : SimpleGraph (X.biUnion id)}
    (h : IsEulerPeeling hX E E' r d v₁ e₀ Qs) (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e)
    (hc : ∀ e, 0 ≤ c e) (ha1 : ∀ e ∈ E.edgeSet, absWeight r d c e ≤ 1) :
    ∏ e ∈ E.edgeFinset, absWeight r d c e ≤
      (∏ S ∈ univ.erase (blockOf hX v₁), blockRadius hX r S ^ 2) *
        (∏ e ∈ (keptGraph E' Qs).edgeFinset, keptWeight d c e) *
          ∏ e ∈ (removedGraph Qs).edgeFinset, peelWeight r d c (r v₁) e₀ e := by
  have hsub : E'.edgeFinset ⊆ E.edgeFinset := edgeFinset_mono h.1.1
  rw [← prod_sdiff hsub]
  refine le_trans ?_ (quadratic_estimate h.2 hr hd hc)
  refine mul_le_of_le_one_left (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e) ?_
  exact prod_le_one₀ (fun e _ => absWeight_nonneg hr hd hc e)
    (fun e he => ha1 e (mem_edgeFinset.mp (mem_sdiff.mp he).1))

end Subpartition

end Peeling

end MultipoleBKT

end
