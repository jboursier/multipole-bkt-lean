/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Nat.Choose.Bounds
import MultipoleBKT.Appendix.Cayley

/-!
# Counting labeled trees, and sums over tree-compatible tuples

The exact count `n^(n-2)` is supplied by the Prüfer bijection in
`MultipoleBKT.Appendix.Cayley`, with the singleton case handled separately.
`card_isTree_fin_eq` is used before any estimate of the numerical coefficient.
`cayley_pow_le_exp_mul_factorial` absorbs that coefficient only at the end.

The second input is summation leaf by leaf, `sum_ite_forall_adj_le`.
For a tree on `n + 1` vertices, summing a leaf costs `c` and leaves the
root factor `∑ w`. This is the argument of Lemma 4.53.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

section TreeCount

variable {V : Type*} [Fintype V]

/-- Cayley's count without a chosen enumeration of the graph type. -/
theorem natCard_isTree_eq_pow (hV : 2 ≤ Fintype.card V) :
    Nat.card {T : SimpleGraph V // T.IsTree} =
      Fintype.card V ^ (Fintype.card V - 2) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_isTree_eq_pow hV

open scoped Classical in
/-- Cayley's count, including the one-vertex tree, as used in
Lemma 4.53. -/
theorem card_isTree_fin_eq (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (SimpleGraph (Fin n))).filter fun T => T.IsTree).card =
      n ^ (n - 2) := by
  by_cases h : 2 ≤ n
  · rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    have hc : 2 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; exact h
    have hh := natCard_isTree_eq_pow hc
    simpa only [Fintype.card_fin] using hh
  · have heq : n = 1 := by omega
    subst n
    have ht : (⊥ : SimpleGraph (Fin 1)).IsTree :=
      SimpleGraph.IsTree.of_subsingleton
    have hall : ∀ T : SimpleGraph (Fin 1), T = ⊥ := fun T => Subsingleton.elim _ _
    have hset : (univ : Finset (SimpleGraph (Fin 1))).filter (fun T => T.IsTree) = {⊥} := by
      ext T
      rw [hall T]
      simp [ht]
    rw [hset]
    simp

/-- Rooting Cayley's trees at one of the `n` vertices gives `n^(n-1)` choices,
as in Step 2 of the proof of Proposition 4.62. -/
theorem mul_cayley_pow (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (n : ℝ) ^ (n - 2) = (n : ℝ) ^ (n - 1) := by
  by_cases h : 2 ≤ n
  · rw [← pow_succ']
    congr 1
    omega
  · have : n = 1 := by omega
    subst n
    norm_num

/-- Only after the exact Cayley count do we absorb its normalized coefficient into an
exponential. This keeps the constants of the existing cluster estimates. -/
theorem cayley_pow_le_exp_mul_factorial (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (n - 2) ≤ Real.exp 2 ^ n * n.factorial := by
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc (n : ℝ) ^ (n - 2) ≤ (n : ℝ) ^ n :=
        pow_le_pow_right₀ h1 (Nat.sub_le n 2)
    _ ≤ Real.exp n * n.factorial := by
        have h := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mp h
    _ ≤ Real.exp 2 ^ n * n.factorial := by
        gcongr
        rw [← Real.exp_nat_mul]
        gcongr
        nlinarith [Nat.cast_nonneg (α := ℝ) n]

end TreeCount

section TreeSum

variable {β : Type*} [Fintype β]

open scoped Classical in
/-- **Summation leaf by leaf.** Let `w ≥ 0` be weights on a finite type `β` and `r` a relation
on `β` such that `w z · ∑_{y, r y z} w y ≤ c · w z` for every `z`. For every tree `T` on `n + 1`
vertices, the weighted number of tuples `x : ι → β` with `r (x i) (x j)` along every edge of `T`
is at most `(∑ w) cⁿ`. -/
theorem sum_ite_forall_adj_le (w : β → ℝ) (hw : ∀ b, 0 ≤ w b) (r : β → β → Prop)
    [DecidableRel r] {c : ℝ}
    (hc : 0 ≤ c) (hrc : ∀ z, w z * ∑ y, (if r y z then w y else 0) ≤ c * w z) (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (T : SimpleGraph ι), Fintype.card ι = n + 1 →
      T.IsTree →
      ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w (x i) else 0) ≤
        (∑ y, w y) * c ^ n := by
  induction n with
  | zero =>
    intro ι _ _ T hcard _
    calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w (x i) else 0)
        ≤ ∑ x : ι → β, ∏ i, w (x i) := by
          refine sum_le_sum fun x _ => ?_
          split_ifs
          · exact le_rfl
          · exact prod_nonneg fun i _ => hw _
      _ = ∏ _i : ι, ∑ y, w y := (Fintype.prod_sum fun _ y => w y).symm
      _ = (∑ y, w y) * c ^ 0 := by
          rw [prod_const, card_univ, hcard, pow_zero, pow_one, mul_one]
  | succ n ih =>
    intro ι _ _ T hcard hT
    have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
    obtain ⟨u, hvu, -⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    let T' : SimpleGraph {i // i ≠ v} := T.comap Subtype.val
    have hT' : T'.IsTree :=
      ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
        hT.isAcyclic.comap ⟨Subtype.val, fun h => h⟩ Subtype.val_injective⟩
    have hcard' : Fintype.card {i // i ≠ v} = n + 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    let u' : {i // i ≠ v} := ⟨u, hvu.ne.symm⟩
    let F' : ({i // i ≠ v} → β) → ℝ := fun x' =>
      if ∀ i j, T'.Adj i j → r (x' i) (x' j) then ∏ i, w (x' i) else 0
    have hF' : ∀ x', 0 ≤ F' x' := fun x' => by
      simp only [F']
      split_ifs
      · exact prod_nonneg fun i _ => hw _
      · exact le_rfl
    have hpt : ∀ x : ι → β,
        (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w (x i) else 0) ≤
          (if r (x v) (x u) then w (x v) else 0) * F' (fun i => x i.1) := by
      intro x
      by_cases h1 : ∀ i j, T.Adj i j → r (x i) (x j)
      · simp only [F']
        have h2 : ∀ i j : {i // i ≠ v}, T'.Adj i j → r (x i.1) (x j.1) := fun i j h => h1 i j h
        rw [ite_eq_left h1, ite_eq_left (h1 v u hvu), ite_eq_left h2,
          Fintype.prod_eq_mul_prod_subtype_ne _ v]
      · rw [ite_eq_right h1]
        refine mul_nonneg ?_ (hF' _)
        split_ifs
        · exact hw _
        · exact le_rfl
    have hsplit : ∀ G : β → ({i // i ≠ v} → β) → ℝ,
        ∑ x : ι → β, G (x v) (fun i => x i.1) = ∑ y, ∑ x' : {i // i ≠ v} → β, G y x' := by
      intro G
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv (Equiv.funSplitAt v β) _ _ (fun x => rfl)
    have key : ∀ x', (∑ y, (if r y (x' u') then w y else 0)) * F' x' ≤ c * F' x' := by
      intro x'
      simp only [F']
      split_ifs
      · rw [Fintype.prod_eq_mul_prod_subtype_ne _ u']
        have hP : 0 ≤ ∏ i : {i // i ≠ u'}, w (x' i.1) := prod_nonneg fun i _ => hw _
        calc (∑ y, (if r y (x' u') then w y else 0)) * (w (x' u') * ∏ i : {i // i ≠ u'}, w (x' i.1))
            = (w (x' u') * ∑ y, (if r y (x' u') then w y else 0)) *
                ∏ i : {i // i ≠ u'}, w (x' i.1) := by ring
          _ ≤ (c * w (x' u')) * ∏ i : {i // i ≠ u'}, w (x' i.1) :=
              mul_le_mul_of_nonneg_right (hrc _) hP
          _ = c * (w (x' u') * ∏ i : {i // i ≠ u'}, w (x' i.1)) := by ring
      · simp
    calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w (x i) else 0)
        ≤ ∑ x : ι → β, (if r (x v) (x u) then w (x v) else 0) * F' (fun i => x i.1) :=
          sum_le_sum fun x _ => hpt x
      _ = ∑ y, ∑ x' : {i // i ≠ v} → β, (if r y (x' u') then w y else 0) * F' x' :=
          hsplit fun y x' => (if r y (x' u') then w y else 0) * F' x'
      _ = ∑ x' : {i // i ≠ v} → β, (∑ y, (if r y (x' u') then w y else 0)) * F' x' := by
          rw [sum_comm]
          simp_rw [sum_mul]
      _ ≤ ∑ x' : {i // i ≠ v} → β, c * F' x' := sum_le_sum fun x' _ => key x'
      _ = c * ∑ x' : {i // i ≠ v} → β, F' x' := (mul_sum _ _ _).symm
      _ ≤ c * ((∑ y, w y) * c ^ n) := mul_le_mul_of_nonneg_left (by convert ih T' hcard' hT') hc
      _ = (∑ y, w y) * c ^ (n + 1) := by ring

end TreeSum

end MultipoleBKT

end
