/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.RouteTypeTwoIntegral.CutWeight
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.API

/-!
# Leaf deletion down to the retained type-two core

The paper: Lemma 5.41. Each step deletes a degree-one vertex from the current
tree. The terminal tree is thus the remaining tree of the deletion process.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes

open MeasureTheory Finset SimpleGraph MultipoleIntegral
open scoped ENNReal Classical

universe u
variable {V : Type u} [Fintype V]

/-- A sequence of leaf deletions. Its terminal graph is the retained core. -/
inductive LeafPruning : {V : Type u} → [Fintype V] → SimpleGraph V →
    {W : Type u} → [Fintype W] → SimpleGraph W → Prop
  | stop {V : Type u} [Fintype V] (T : SimpleGraph V) : LeafPruning T T
  | remove {V W : Type u} [Fintype V] [Fintype W] {T : SimpleGraph V}
      (v : V) (hv : Cayley.deg T v = 1) {U : SimpleGraph W}
      (next : LeafPruning (T.comap (Subtype.val : {i // i ≠ v} → V)) U) :
      LeafPruning T U

/-- The radial tree integral with an arbitrary nonnegative vertex weight. -/
noncomputable def radialTreeIntegral (T : SimpleGraph V) (lam : ℝ) (w : ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x : V → ℂ, ENNReal.ofReal (∏ e ∈ T.edgeFinset,
    edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) * ∏ i, w (x i)

/-- Removing a leaf separates its single edge from the product on the smaller tree. -/
theorem prod_edgeMin_remove_leaf [DecidableEq V] {T : SimpleGraph V}
    [DecidableRel T.Adj]
    {v : V} (hv : Cayley.deg T v = 1) (p : {i // i ≠ v}) (hp : T.Adj v p.1)
    (f : ℝ → ℝ) (r : V → ℝ) :
    ∏ e ∈ T.edgeFinset, edgeMin f r e = f (min (r v) (r p.1)) *
      ∏ e ∈ (T.comap (Subtype.val : {i // i ≠ v} → V)).edgeFinset,
        edgeMin f (fun i => r i.1) e := by
  classical
  let T' := T.comap (Subtype.val : {i // i ≠ v} → V)
  have hsplit := Cayley.addLeaf_comap hv hp
  have hn : ¬ (T'.map (Function.Embedding.subtype _)).Adj v p.1 := by
    rw [Cayley.map_subtype_adj]
    rintro ⟨h, -⟩
    exact h rfl
  have heq : T.edgeFinset = (Cayley.addLeaf v p T').edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [hsplit]
  rw [heq]
  have hedges : (Cayley.addLeaf v p T').edgeFinset =
      insert s(v, p.1) (T'.edgeFinset.map (Function.Embedding.subtype _).sym2Map) := by
    ext e
    simp only [Finset.mem_insert, SimpleGraph.mem_edgeFinset, Finset.mem_map]
    induction e using Sym2.inductionOn with
    | _ a b =>
      simp only [Cayley.addLeaf, SimpleGraph.mem_edgeSet, SimpleGraph.sup_adj,
        SimpleGraph.map_adj, SimpleGraph.edge_adj, Sym2.eq_iff]
      constructor
      · rintro (⟨x, y, h, rfl, rfl⟩ | ⟨h, hne⟩)
        · exact Or.inr ⟨s(x, y), by simpa using h, rfl⟩
        · exact Or.inl (by rcases h with h | h <;> tauto)
      · rintro (h | ⟨e, he, hab⟩)
        · rcases h with h | h
          · exact Or.inr ⟨Or.inl h, by simpa [h.1, h.2] using p.2.symm⟩
          · exact Or.inr ⟨Or.inr h, by simpa [h.1, h.2] using p.2⟩
        · induction e using Sym2.inductionOn with
          | _ x y =>
            change T'.Adj x y at he
            change s(x.1, y.1) = s(a, b) at hab
            rcases Sym2.eq_iff.mp hab with h | h
            · exact Or.inl ⟨x, y, he, h.1, h.2⟩
            · exact Or.inl ⟨y, x, he.symm, h.2, h.1⟩
  have hnot : s(v, p.1) ∉ T'.edgeFinset.map (Function.Embedding.subtype _).sym2Map := by
    rw [← SimpleGraph.edgeFinset_map]
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hn
  rw [hedges, Finset.prod_insert hnot, Finset.prod_map, edgeMin_mk]
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | _ i j => rfl

/-- Separate one coordinate from all remaining coordinates by Tonelli. -/
theorem lintegral_vertex_mul (v : V) (w : ℂ → ℝ≥0∞)
    (hw : Measurable w) (G : ({i // i ≠ v} → ℂ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ x : V → ℂ, w (x v) * G (fun i => x i.1)) =
      (∫⁻ z : ℂ, w z) * ∫⁻ y : {i // i ≠ v} → ℂ, G y := by
  let : Unique {i : V // i = v} :=
    ⟨⟨⟨v, rfl⟩⟩, fun i => Subtype.ext i.2⟩
  let : Fintype {i : V // i = v} := Subtype.fintype (fun i => i = v)
  let a : {i : V // i = v} := ⟨v, rfl⟩
  have hsplit := (volume_preserving_piEquivPiSubtypeProd (fun _ : V => ℂ)
    (fun i => i = v)).lintegral_map_equiv
      (fun z => w (z.1 a) * G z.2)
  change (∫⁻ z : ({i : V // i = v} → ℂ) × ({i : V // i ≠ v} → ℂ),
      w (z.1 a) * G z.2) = _ at hsplit
  change (∫⁻ z : ({i : V // i = v} → ℂ) × ({i : V // i ≠ v} → ℂ),
      w (z.1 a) * G z.2) = ∫⁻ x : V → ℂ, w (x v) * G (fun i => x i.1) at hsplit
  rw [← hsplit]
  have hm : Measurable (fun z : ({i : V // i = v} → ℂ) × ({i : V // i ≠ v} → ℂ) =>
      w (z.1 a) * G z.2) :=
    by
      apply Measurable.mul
      · exact hw.comp (by fun_prop)
      · exact hG.comp measurable_snd
  change (∫⁻ z : ({i : V // i = v} → ℂ) × ({i : V // i ≠ v} → ℂ),
    w (z.1 a) * G z.2 ∂(volume : Measure ({i : V // i = v} → ℂ)).prod volume) = _
  rw [lintegral_prod (μ := (volume : Measure ({i : V // i = v} → ℂ)))
    (ν := (volume : Measure ({i : V // i ≠ v} → ℂ))) _ hm.aemeasurable]
  simp_rw [lintegral_const_mul _ hG]
  have hwa : Measurable (fun x : {i : V // i = v} → ℂ => w (x a)) :=
    hw.comp (by fun_prop)
  rw [lintegral_mul_const _ hwa]
  congr 1
  exact ((volume_preserving_piUnique (fun _ : {i : V // i = v} => ℂ)).lintegral_map_equiv w).symm

/-- Measurability of the weighted radial tree integrand. -/
theorem measurable_radialTreeIntegrand (T : SimpleGraph V) {lam : ℝ} (_hlam : 0 < lam)
    {w : ℂ → ℝ≥0∞} (hw : Measurable w) :
    Measurable fun x : V → ℂ => ENNReal.ofReal (∏ e ∈ T.edgeFinset,
      edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) * ∏ i, w (x i) := by
  refine (ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun e _ => ?_)).mul ?_
  · induction e using Sym2.inductionOn with
    | _ i j => exact (((measurable_pi_apply i : Measurable (fun x : V → ℂ => x i)).norm.min
        (measurable_pi_apply j).norm).max measurable_const).pow_const 2
  · exact Finset.measurable_prod _ fun i _ => hw.comp (measurable_pi_apply i)

/-- Integrating a leaf costs one truncated second radial moment.
The remaining factor is the integral on the tree with that leaf deleted. -/
theorem radialTreeIntegral_remove_leaf {T : SimpleGraph V} (v : V)
    (hv : Cayley.deg T v = 1) {lam : ℝ} (hlam : 0 < lam)
    {w : ℂ → ℝ≥0∞} (hw : Measurable w) :
    radialTreeIntegral T lam w ≤
      (∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * w z) *
        radialTreeIntegral (T.comap (Subtype.val : {i // i ≠ v} → V)) lam w := by
  obtain ⟨p, hp, -⟩ := (Cayley.deg_eq_one_iff T v).mp hv
  let p' : {i // i ≠ v} := ⟨p, hp.ne'⟩
  let T' := T.comap (Subtype.val : {i // i ≠ v} → V)
  let G (y : {i // i ≠ v} → ℂ) : ℝ≥0∞ := ENNReal.ofReal
    (∏ e ∈ T'.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖y i‖) e) *
      ∏ i, w (y i)
  have hpt (x : V → ℂ) : ENNReal.ofReal (∏ e ∈ T.edgeFinset,
      edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i‖) e) * ∏ i, w (x i) ≤
      (ENNReal.ofReal (max ‖x v‖ lam ^ 2) * w (x v)) * G (fun i => x i.1) := by
    rw [prod_edgeMin_remove_leaf hv p' hp,
      ENNReal.ofReal_mul (by positivity : 0 ≤ max (min ‖x v‖ ‖x p'.1‖) lam ^ 2),
      Fintype.prod_eq_mul_prod_subtype_ne (fun i => w (x i)) v]
    have hpow : max (min ‖x v‖ ‖x p'.1‖) lam ^ 2 ≤ max ‖x v‖ lam ^ 2 :=
      pow_le_pow_left₀ (by positivity) (max_le_max (min_le_left _ _) le_rfl) 2
    calc
      _ ≤ (ENNReal.ofReal (max ‖x v‖ lam ^ 2) * ENNReal.ofReal
          (∏ e ∈ T'.edgeFinset, edgeMin (fun t => max t lam ^ 2) (fun i => ‖x i.1‖) e)) *
            (w (x v) * ∏ i : {i // i ≠ v}, w (x i.1)) := by
        exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl) le_rfl
      _ = _ := by dsimp only [G]; ring
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  have hleaf : Measurable (fun z : ℂ => ENNReal.ofReal (max ‖z‖ lam ^ 2) * w z) :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hw
  exact lintegral_vertex_mul v _ hleaf G
    (measurable_radialTreeIntegrand T' hlam hw)

/-- Remove leaves until exactly `k` vertices remain. The witness includes the
actual deletion sequence and the integral of its terminal tree. -/
theorem exists_pruned_core {T : SimpleGraph V} (hT : T.IsTree) {k : ℕ}
    (hk : 1 ≤ k) (hkV : k ≤ Fintype.card V) {lam : ℝ} (hlam : 0 < lam)
    {w : ℂ → ℝ≥0∞} (hw : Measurable w) :
    ∃ (W : Type u) (_ : Fintype W) (U : SimpleGraph W),
      LeafPruning T U ∧ Fintype.card W = k ∧ U.IsTree ∧
        radialTreeIntegral T lam w ≤
          (∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * w z) ^ (Fintype.card V - k) *
            radialTreeIntegral U lam w := by
  have main : ∀ n, ∀ (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ (G : SimpleGraph W), G.IsTree → k ≤ Fintype.card W →
      ∃ (C : Type u) (_ : Fintype C) (U : SimpleGraph C),
        LeafPruning G U ∧ Fintype.card C = k ∧ U.IsTree ∧
          radialTreeIntegral G lam w ≤
            (∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * w z) ^ (Fintype.card W - k) *
              radialTreeIntegral U lam w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ hcard G hG hsize
      by_cases heq : Fintype.card W = k
      · refine ⟨W, inferInstance, G, LeafPruning.stop G, heq, hG, ?_⟩
        rw [heq, Nat.sub_self, pow_zero, one_mul]
      · have : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨v, hv⟩ := hG.exists_vert_degree_one_of_nontrivial
        have hv' : Cayley.deg G v = 1 := by rw [Cayley.deg_eq_degree, hv]
        let W' := {i : W // i ≠ v}
        let G' : SimpleGraph W' := G.comap Subtype.val
        have hs : Fintype.card W' + 1 = Fintype.card W :=
          by convert Cayley.card_subtype_ne_add_one v
        obtain ⟨C, hC, U, hchain, hCsize, hU, hb⟩ :=
          ih (Fintype.card W') (by omega) W' rfl G' (Cayley.isTree_comap hG hv') (by omega)
        refine ⟨C, hC, U, LeafPruning.remove v hv' hchain, hCsize, hU, ?_⟩
        refine (radialTreeIntegral_remove_leaf v hv' hlam hw).trans ?_
        calc
          _ ≤ (∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * w z) *
              ((∫⁻ z : ℂ, ENNReal.ofReal (max ‖z‖ lam ^ 2) * w z) ^ (Fintype.card W' - k) *
                radialTreeIntegral U lam w) := mul_le_mul' le_rfl hb
          _ = _ := by
            rw [← mul_assoc, ← pow_succ']
            congr 2
            omega
  exact main _ V rfl T hT hkV

end MultipoleBKT.BadPointTypes

end
