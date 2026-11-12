/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Tail
public import MultipoleBKT.Appendix.Cayley
public import MultipoleBKT.LowerBound.AbsoluteLower.Dyadic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The anchored-norm tree bound (proof of Proposition 4.27, eq. (4.56))

The proof of Proposition 4.27: the Kotecký–Preiss anchored-norm argument, for an arbitrary activity `K` on the
subsets of a finite set `A` of polymers' elements (in Section 4, `A = π` and the polymers are the
subpartitions `X ⊆ π`).

* `exists_leaf_ne`: a tree with at least two vertices has a leaf other than a given root.
* `sum_forall_adj_le_root` (the leaf removal, proof of Proposition 4.27): for a tree `T` rooted at `ρ`,
  per-vertex weights `wᵢ ≥ 0` and a relation `r` with
  `∑_{y, r y z} wᵢ(y) ≤ fᵢ hⱼ` whenever `wⱼ(z) ≠ 0` (`i ≠ ρ`, `j ≠ i`, `hⱼ ≥ 1`),
  `∑_x 𝟙_{r along T} ∏ᵢ wᵢ(xᵢ) ≤ (∑ w_ρ) ∏_{i ≠ ρ} fᵢ ∏ⱼ hⱼ^{deg_T(j)}`.
  The paper removes leaves one at a time with the polymer sizes `kᵢ` fixed; here `hⱼ = kⱼ`.
* `sum_abs_ursell_mul_le_sum_isTree'`: Rota's bound (4.87) in a cluster sum with per-vertex
  weights.
* `cluster_tree_bound` (eq. (4.137)): with `𝒜 = sup_{a ∈ A} ∑_{Y ∋ a} |K(Y)| 20^{|Y|}` and
  `B = ∑_{Q(Y)} |K(Y)| 20^{|Y|}`, for `n ≥ 1`,
  `(1/n!) ∑_{Y₁, …, Yₙ connected, ∃ i, Q(Yᵢ)} |∏ K(Yᵢ) I(G(Y))| ≤ B (𝒜/5)^{n-1}`.
  The paper's weight is `20^{|V_X|}`; since `|V_X| ≥ |X|`, its hypotheses imply these.
  The constant: `∑_{k ≥ 1} k (e/20)^k ≤ 1/5` replaces the paper's `1/(20e^{-2} - 1)`.
* `tsum_cluster_le`, `summable_cluster`: the series over `n` is at most `2B` for `𝒜 ≤ 1`, and
  converges absolutely.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset SimpleGraph

/-! ### Leaves -/

section Leaf

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- A tree with at least two vertices has a leaf other than any given vertex. -/
theorem exists_leaf_ne [Nontrivial ι] {T : SimpleGraph ι} (hT : T.IsTree) (ρ : ι) :
    ∃ v, v ≠ ρ ∧ Cayley.deg T v = 1 := by
  obtain ⟨u, v, huv, hu, hv⟩ := hT.exists_ne_and_degree_eq_one
  by_cases hu' : u = ρ
  · refine ⟨v, fun h => huv (hu'.trans h.symm), ?_⟩
    rw [Cayley.deg_eq_degree]
    convert hv
  · refine ⟨u, hu', ?_⟩
    rw [Cayley.deg_eq_degree]
    convert hu

end Leaf

/-! ### Leaf removal with a root and per-vertex weights -/

section LeafRemoval

variable {β : Type*} [Fintype β]

open scoped Classical in
/-- **Leaf removal** (proof of Proposition 4.27). For a tree `T` on `ι` rooted at
`ρ`, weights `w i ≥ 0`, `f i ≥ 0`, `h j ≥ 1` and a relation `r` such that, for `i ≠ ρ`, `j ≠ i`
and every `z` with `w j z ≠ 0`, `∑_{y, r y z} w i y ≤ f i * h j`:
`∑_x 𝟙_{∀ ij ∈ T, r (x i) (x j)} ∏ᵢ w i (x i) ≤ (∑_y w ρ y) ∏_{i ≠ ρ} f i ∏_j h j ^ deg_T(j)`. -/
theorem sum_forall_adj_le_root (r : β → β → Prop) (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (T : SimpleGraph ι), Fintype.card ι = n + 1 →
      T.IsTree → ∀ (ρ : ι) (w : ι → β → ℝ) (f h : ι → ℝ), (∀ i b, 0 ≤ w i b) → (∀ i, 0 ≤ f i) →
        (∀ i, 1 ≤ h i) →
        (∀ i, i ≠ ρ → ∀ j, j ≠ i → ∀ z, w j z ≠ 0 →
          ∑ y, (if r y z then w i y else 0) ≤ f i * h j) →
        ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w i (x i) else 0) ≤
          (∑ y, w ρ y) * ((∏ i ∈ univ.erase ρ, f i) * ∏ j, h j ^ Cayley.deg T j) := by
  induction n with
  | zero =>
    intro ι _ _ T hcard hT ρ w f h hw hf hh hleaf
    have hsub : ∀ a b : ι, a = b := fun a b => by
      have := Fintype.card_le_one_iff.mp (le_of_eq hcard) a b
      exact this
    have huniv : (univ : Finset ι) = {ρ} := by
      ext a
      simp [hsub a ρ]
    have hadj : ∀ x : ι → β, ∀ i j, T.Adj i j → r (x i) (x j) := fun x i j hij =>
      absurd (hsub i j) hij.ne
    have hdeg : ∀ j, Cayley.deg T j = 0 := by
      intro j
      rw [Cayley.deg, Nat.card_eq_zero]
      left
      refine ⟨fun ⟨k, hk⟩ => ?_⟩
      exact (T.ne_of_adj hk) (hsub j k)
    refine le_of_eq ?_
    calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w i (x i) else 0)
        = ∑ x : ι → β, ∏ i, w i (x i) := sum_congr rfl fun x _ => ite_eq_left (hadj x)
      _ = ∏ i, ∑ y, w i y := (Fintype.prod_sum fun i y => w i y).symm
      _ = ∑ y, w ρ y := by rw [huniv, prod_singleton]
      _ = (∑ y, w ρ y) * ((∏ i ∈ univ.erase ρ, f i) * ∏ j, h j ^ Cayley.deg T j) := by
          simp only [hdeg, pow_zero, prod_const_one, mul_one]
          rw [huniv, erase_singleton, prod_empty, mul_one]
  | succ n ih =>
    intro ι _ _ T hcard hT ρ w f h hw hf hh hleaf
    have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hvρ, hv⟩ := exists_leaf_ne hT ρ
    obtain ⟨u, hvu, hu⟩ := (Cayley.deg_eq_one_iff T v).mp hv
    let ι' := {i // i ≠ v}
    let T' : SimpleGraph ι' := T.comap Subtype.val
    have hT' : T'.IsTree := Cayley.isTree_comap hT hv
    have hcard' : Fintype.card ι' = n + 1 := by
      have h1 : Fintype.card ι' + 1 = Fintype.card ι := by
        convert Cayley.card_subtype_ne_add_one v
      omega
    let u' : ι' := ⟨u, hvu.ne.symm⟩
    let ρ' : ι' := ⟨ρ, hvρ.symm⟩
    let w' : ι' → β → ℝ := fun i => w i.1
    have hleaf' : ∀ i : ι', i ≠ ρ' → ∀ j : ι', j ≠ i → ∀ z, w' j z ≠ 0 →
        ∑ y, (if r y z then w' i y else 0) ≤ f i.1 * h j.1 := by
      intro i hi j hj z hz
      exact hleaf i.1 (fun h' => hi (Subtype.ext h')) j.1 (fun h' => hj (Subtype.ext h')) z hz
    have hIH := ih T' hcard' hT' ρ' w' (fun i => f i.1) (fun i => h i.1) (fun i b => hw i.1 b)
      (fun i => hf i.1) (fun i => hh i.1) hleaf'
    -- the restricted sum
    let F' : (ι' → β) → ℝ := fun x' =>
      if ∀ i j, T'.Adj i j → r (x' i) (x' j) then ∏ i, w' i (x' i) else 0
    have hF' : ∀ x', 0 ≤ F' x' := fun x' => by
      simp only [F']
      split_ifs
      · exact prod_nonneg fun i _ => hw _ _
      · exact le_rfl
    have hpt : ∀ x : ι → β,
        (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w i (x i) else 0) ≤
          (if r (x v) (x u) then w v (x v) else 0) * F' (fun i => x i.1) := by
      intro x
      by_cases h1 : ∀ i j, T.Adj i j → r (x i) (x j)
      · simp only [F']
        have h2 : ∀ i j : ι', T'.Adj i j → r (x i.1) (x j.1) := fun i j h => h1 i j h
        rw [ite_eq_left h1, ite_eq_left (h1 v u hvu), ite_eq_left h2,
          Fintype.prod_eq_mul_prod_subtype_ne _ v]
      · rw [ite_eq_right h1]
        refine mul_nonneg ?_ (hF' _)
        split_ifs
        · exact hw _ _
        · exact le_rfl
    have hsplit : ∀ G : β → (ι' → β) → ℝ,
        ∑ x : ι → β, G (x v) (fun i => x i.1) = ∑ y, ∑ x' : ι' → β, G y x' := by
      intro G
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv (Equiv.funSplitAt v β) _ _ (fun x => rfl)
    have key : ∀ x', (∑ y, (if r y (x' u') then w v y else 0)) * F' x' ≤
        (f v * h u) * F' x' := by
      intro x'
      by_cases hz : F' x' = 0
      · rw [hz, mul_zero, mul_zero]
      · refine mul_le_mul_of_nonneg_right ?_ (hF' x')
        have hwu : w' u' (x' u') ≠ 0 := by
          intro h0
          apply hz
          simp only [F']
          split_ifs
          · exact prod_eq_zero (mem_univ u') h0
          · rfl
        exact hleaf v hvρ u hvu.ne.symm (x' u') hwu
    have hsum : ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w i (x i) else 0) ≤
        (f v * h u) * ∑ x' : ι' → β, F' x' := by
      calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w i (x i) else 0)
          ≤ ∑ x : ι → β, (if r (x v) (x u) then w v (x v) else 0) * F' (fun i => x i.1) :=
            sum_le_sum fun x _ => hpt x
        _ = ∑ y, ∑ x' : ι' → β, (if r y (x' u') then w v y else 0) * F' x' :=
            hsplit fun y x' => (if r y (x' u') then w v y else 0) * F' x'
        _ = ∑ x' : ι' → β, (∑ y, (if r y (x' u') then w v y else 0)) * F' x' := by
            rw [sum_comm]
            simp_rw [sum_mul]
        _ ≤ ∑ x' : ι' → β, (f v * h u) * F' x' := sum_le_sum fun x' _ => key x'
        _ = (f v * h u) * ∑ x' : ι' → β, F' x' := (mul_sum _ _ _).symm
    -- the products over `ι` and over `ι'`
    have hprodf : ∏ i ∈ univ.erase ρ, f i = f v * ∏ i ∈ (univ : Finset ι').erase ρ', f i.1 := by
      rw [← mul_prod_erase _ _ (mem_erase.2 ⟨hvρ, mem_univ v⟩)]
      congr 1
      refine prod_bij (fun i hi => (⟨i, (mem_erase.1 hi).1⟩ : ι')) (fun i hi => ?_)
        (fun a ha b hb hab => ?_) (fun b hb => ?_) (fun i hi => rfl)
      · simp only [mem_erase, ne_eq, mem_univ, and_true] at hi ⊢
        exact fun h' => hi.2 (congrArg Subtype.val h')
      · exact congrArg Subtype.val hab
      · refine ⟨b.1, ?_, rfl⟩
        simp only [mem_erase, ne_eq, mem_univ, and_true] at hb ⊢
        exact ⟨b.2, fun h' => hb (Subtype.ext h')⟩
    have hdegT : ∀ j : ι', Cayley.deg T j.1 = Cayley.deg T' j + if j = u' then 1 else 0 := by
      intro j
      rw [Cayley.deg_eq_comap_add T v j]
      congr 1
      by_cases hj : j = u'
      · rw [ite_eq_left hj, ite_eq_left]
        rw [hj]
        exact hvu.symm
      · rw [ite_eq_right hj, ite_eq_right]
        intro hjv
        exact hj (Subtype.ext (hu j.1 hjv.symm))
    have hprodh : ∏ j, h j ^ Cayley.deg T j =
        h v * (h u * ∏ j : ι', h j.1 ^ Cayley.deg T' j) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ v, hv, pow_one]
      congr 1
      simp_rw [hdegT]
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ u']
      have hrest : ∏ j : {j : ι' // j ≠ u'}, h j.1.1 ^ (Cayley.deg T' j.1 +
          if (j : ι') = u' then 1 else 0) =
          ∏ j : {j : ι' // j ≠ u'}, h j.1.1 ^ Cayley.deg T' j.1 :=
        prod_congr rfl fun j _ => by rw [ite_eq_right j.2, add_zero]
      rw [hrest, ite_eq_left rfl, pow_add, pow_one, Fintype.prod_eq_mul_prod_subtype_ne
        (fun j : ι' => h j.1 ^ Cayley.deg T' j) u']
      ring
    have hfprod : 0 ≤ ∏ i ∈ (univ : Finset ι').erase ρ', f i.1 := prod_nonneg fun i _ => hf _
    have hhprod : 0 ≤ ∏ j : ι', h j.1 ^ Cayley.deg T' j :=
      prod_nonneg fun j _ => pow_nonneg (zero_le_one.trans (hh _)) _
    have hwρ : 0 ≤ ∑ y, w ρ y := sum_nonneg fun y _ => hw _ _
    have hfv := hf v
    have hhu : 0 ≤ h u := zero_le_one.trans (hh u)
    calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, w i (x i) else 0)
        ≤ (f v * h u) * ∑ x' : ι' → β, F' x' := hsum
      _ ≤ (f v * h u) * ((∑ y, w' ρ' y) * ((∏ i ∈ (univ : Finset ι').erase ρ', f i.1) *
            ∏ j : ι', h j.1 ^ Cayley.deg T' j)) :=
          mul_le_mul_of_nonneg_left hIH (mul_nonneg hfv hhu)
      _ = (∑ y, w ρ y) * ((f v * ∏ i ∈ (univ : Finset ι').erase ρ', f i.1) *
            (1 * (h u * ∏ j : ι', h j.1 ^ Cayley.deg T' j))) := by
          simp only [w']
          ring
      _ ≤ (∑ y, w ρ y) * ((f v * ∏ i ∈ (univ : Finset ι').erase ρ', f i.1) *
            (h v * (h u * ∏ j : ι', h j.1 ^ Cayley.deg T' j))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hfv hfprod)) hwρ
          exact mul_le_mul_of_nonneg_right (hh v) (mul_nonneg hhu hhprod)
      _ = (∑ y, w ρ y) * ((∏ i ∈ univ.erase ρ, f i) * ∏ j, h j ^ Cayley.deg T j) := by
          rw [hprodf, hprodh]

end LeafRemoval

/-! ### Tree sums -/

section TreeSums

open scoped Classical in
/-- `∑_{T tree on Fin n} ∏ⱼ hⱼ^{deg_T(j)} ≤ (n-1)! ∏ⱼ hⱼ e^{hⱼ}` for `n ≥ 1` and `hⱼ ≥ 1`
(Cayley's formula (Lemma A.9) and `xᵐ/m! ≤ eˣ`; the paper's bound in the proof of Proposition 4.27). -/
theorem sum_isTree_prod_pow_le {n : ℕ} (hn : 1 ≤ n) (h : Fin n → ℝ) (hh : ∀ j, 1 ≤ h j) :
    ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
        ∏ j, h j ^ Cayley.deg T j ≤
      ((n - 1).factorial : ℝ) * ∏ j, (h j * Real.exp (h j)) := by
  have hh0 : ∀ j, 0 ≤ h j := fun j => zero_le_one.trans (hh j)
  have hexp : ∀ j, 1 ≤ h j * Real.exp (h j) := fun j =>
    one_le_mul_of_one_le_of_one_le (hh j) (Real.one_le_exp (hh0 j))
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- `n = 1`: the only graph is `⊥`
    have hn1 : n = 1 := by omega
    subst hn1
    have hsub : ∀ G H : SimpleGraph (Fin 1), G = H := fun G H => by
      ext a b
      have : a = b := Subsingleton.elim a b
      subst this
      simp
    have hdeg : ∀ (T : SimpleGraph (Fin 1)) j, Cayley.deg T j = 0 := by
      intro T j
      rw [Cayley.deg, Nat.card_eq_zero]
      left
      exact ⟨fun ⟨k, hk⟩ => (T.ne_of_adj hk) (Subsingleton.elim j k)⟩
    simp only [hdeg, pow_zero, prod_const_one, sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((univ : Finset (SimpleGraph (Fin 1))).filter (fun T => T.IsTree)).card ≤ 1 :=
      (card_le_card (filter_subset _ _)).trans
        (card_le_one.mpr fun G _ H _ => hsub G H)
    refine le_trans (by exact_mod_cast hcard : _ ≤ (1 : ℝ)) ?_
    simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, Fin.prod_univ_one]
    exact hexp 0
  · have hcay := sum_isTree_prod_pow_degree (V := Fin n) (R := ℝ) (by simpa using h2) h
    simp only [Fintype.card_fin] at hcay
    simp only [← Cayley.deg_eq_degree] at hcay
    have key : ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
        ∏ j, h j ^ Cayley.deg T j = (∏ j, h j) * (∑ j, h j) ^ (n - 2) := by
      convert hcay
    rw [key]
    have hS : 0 ≤ ∑ j, h j := sum_nonneg fun j _ => hh0 j
    have hpow : (∑ j, h j) ^ (n - 2) ≤ ((n - 2).factorial : ℝ) * Real.exp (∑ j, h j) := by
      have := Real.pow_div_factorial_le_exp (∑ j, h j) hS (n - 2)
      have hf : (0 : ℝ) < (n - 2).factorial := by exact_mod_cast Nat.factorial_pos _
      rw [div_le_iff₀ hf] at this
      linarith
    have hfac : ((n - 2).factorial : ℝ) ≤ (n - 1).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hP : 0 ≤ ∏ j, h j := prod_nonneg fun j _ => hh0 j
    calc (∏ j, h j) * (∑ j, h j) ^ (n - 2)
        ≤ (∏ j, h j) * (((n - 2).factorial : ℝ) * Real.exp (∑ j, h j)) :=
          mul_le_mul_of_nonneg_left hpow hP
      _ ≤ (∏ j, h j) * (((n - 1).factorial : ℝ) * Real.exp (∑ j, h j)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hfac (Real.exp_pos _).le) hP
      _ = ((n - 1).factorial : ℝ) * ∏ j, (h j * Real.exp (h j)) := by
          rw [Real.exp_sum, prod_mul_distrib]
          ring

/-- `k e^k ≤ 20^k`. -/
theorem natCast_mul_exp_le_pow (k : ℕ) : (k : ℝ) * Real.exp k ≤ 20 ^ k := by
  have h1 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2 : Real.exp k ≤ 3 ^ k := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le k
  calc (k : ℝ) * Real.exp k ≤ 2 ^ k * 3 ^ k :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = 6 ^ k := by rw [← mul_pow]; norm_num
    _ ≤ 20 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k

/-- `∑_{1 ≤ k ≤ K} k e^k 20^{-k} ≤ 1/4`. -/
theorem sum_mul_exp_div_le (K : ℕ) :
    ∑ k ∈ range (K + 1), (if 1 ≤ k then (k : ℝ) * Real.exp k * (1 / 20) ^ k else 0) ≤ 1 / 4 := by
  set x : ℝ := Real.exp 1 / 20 with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 3 / 20 := by
    rw [hx]
    linarith [Real.exp_one_lt_three]
  have hterm : ∀ k ∈ range (K + 1),
      (if 1 ≤ k then (k : ℝ) * Real.exp k * (1 / 20) ^ k else 0) ≤ (k : ℝ) * x ^ k := by
    intro k _
    have : (k : ℝ) * Real.exp k * (1 / 20) ^ k = (k : ℝ) * x ^ k := by
      rw [show (1 / 20 : ℝ) = 20⁻¹ by norm_num, hx, div_pow, ← Real.exp_one_pow, div_eq_mul_inv,
        inv_pow]
      ring
    split_ifs
    · exact this.le
    · positivity
  refine (sum_le_sum hterm).trans ((sum_mul_pow_le _ hx0 (by linarith)).trans ?_)
  have h1 : (17 / 20 : ℝ) ^ 2 ≤ (1 - x) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith

end TreeSums

/-! ### The anchored-norm bound -/

section Cluster

variable {α : Type*} [DecidableEq α]

open scoped Classical in
/-- Rota's bound (4.87) in a cluster sum, with per-vertex weights. -/
theorem sum_abs_ursell_mul_le_sum_isTree' {n : ℕ} (S : Finset (Fin n → Finset α))
    (w : Fin n → Finset α → ℝ) (hw : ∀ i Y, 0 ≤ w i Y) :
    ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, w i (X i) ≤
      ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
        ∑ X ∈ S, (if T ≤ connectionGraph X then ∏ i, w i (X i) else 0) := by
  have hP : ∀ X : Fin n → Finset α, 0 ≤ ∏ i, w i (X i) := fun X => prod_nonneg fun i _ => hw _ _
  calc ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, w i (X i)
      ≤ ∑ X ∈ S, |(ursell (connectionGraph X) : ℝ)| * ∏ i, w i (X i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun X _ _ => mul_nonneg (abs_nonneg _) (hP X)
    _ ≤ ∑ X ∈ S, (((univ : Finset (SimpleGraph (Fin n))).filter
          (fun T => T ≤ connectionGraph X ∧ T.IsTree)).card : ℝ) * ∏ i, w i (X i) := by
        refine sum_le_sum fun X _ => mul_le_mul_of_nonneg_right ?_ (hP X)
        have h := abs_ursell_le_natCard_isTree (connectionGraph X)
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
        rw [← Int.cast_abs, ← Int.cast_natCast]
        exact Int.cast_le.mpr h
    _ = ∑ X ∈ S, ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
          (if T ≤ connectionGraph X then ∏ i, w i (X i) else 0) := by
        refine sum_congr rfl fun X _ => ?_
        rw [← sum_filter, filter_filter, sum_const, nsmul_eq_mul]
        congr 3
        ext T
        simp only [mem_filter, mem_univ, true_and]
        exact and_comm
    _ = _ := sum_comm

omit [DecidableEq α] in
/-- Decomposition of a product of weights according to the sizes of the polymers. -/
theorem prod_eq_sum_sizes {n : ℕ} (A : Finset α) (W : Fin n → Finset α → ℝ)
    (x : Fin n → A.powerset) :
    ∏ i, W i (x i) = ∑ k ∈ Fintype.piFinset (fun _ : Fin n => range (A.card + 1)),
      ∏ i, (if ((x i : Finset α)).card = k i then W i (x i) else 0) := by
  rw [← prod_univ_sum (fun _ : Fin n => range (A.card + 1))
    (fun i κ => if ((x i : Finset α)).card = κ then W i (x i) else 0)]
  refine prod_congr rfl fun i _ => ?_
  rw [sum_ite_eq (range (A.card + 1))]
  have : ((x i : Finset α)).card ∈ range (A.card + 1) :=
    mem_range.2 (Nat.lt_succ_of_le (card_le_card (mem_powerset.1 (x i).2)))
  rw [ite_eq_left this]

/-- The leaf condition: the polymers of size `κ ≥ 1` meeting `z` carry at most
`|z| 𝒜 20^{-κ}`. -/
theorem sum_inter_card_le (A : Finset α) (K : Finset α → ℝ) {𝒜 : ℝ} (hK0 : K ∅ = 0)
    (h𝒜 : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) ≤ 𝒜)
    (κ : ℕ) (z : A.powerset) :
    ∑ y : A.powerset, (if ((y : Finset α) ∩ z).Nonempty then
        (if (y : Finset α).card = κ then |K y| else 0) else 0) ≤
      (if 1 ≤ κ then 𝒜 * (1 / 20) ^ κ else 0) * (z : Finset α).card := by
  have hnn : ∀ Y : Finset α, 0 ≤ (if Y.card = κ then |K Y| else 0) := fun Y => by
    split_ifs <;> positivity
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · -- only `∅` has size `0`
    rw [ite_eq_right (by omega), zero_mul]
    refine le_of_eq (sum_eq_zero fun y _ => ?_)
    split_ifs with h1 h2
    · rw [card_eq_zero] at h2
      rw [h2, hK0, abs_zero]
    · rfl
    · rfl
  · rw [ite_eq_left (show 1 ≤ κ by omega)]
    set K' : Finset α → ℝ := fun Y => if Y.card = κ then K Y else 0 with hK'
    have habs : ∀ Y, |K' Y| = if Y.card = κ then |K Y| else 0 := fun Y => by
      simp only [hK']
      split_ifs <;> simp
    have hq : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K' Y| else 0) ≤ 𝒜 * (1 / 20) ^ κ := by
      intro a ha
      have hpt : ∀ Y ∈ A.powerset, (if a ∈ Y then |K' Y| else 0) ≤
          (1 / 20) ^ κ * (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) := by
        intro Y _
        rw [habs]
        by_cases haY : a ∈ Y
        · rw [ite_eq_left haY, ite_eq_left haY]
          by_cases hY : Y.card = κ
          · rw [ite_eq_left hY, hY, ← mul_assoc, mul_comm ((1 / 20 : ℝ) ^ κ), mul_assoc, ← mul_pow]
            norm_num
          · rw [ite_eq_right hY]
            positivity
        · rw [ite_eq_right haY, ite_eq_right haY, mul_zero]
      calc ∑ Y ∈ A.powerset, (if a ∈ Y then |K' Y| else 0)
          ≤ ∑ Y ∈ A.powerset, (1 / 20) ^ κ * (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) :=
            sum_le_sum hpt
        _ = (1 / 20) ^ κ * ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) :=
            (mul_sum _ _ _).symm
        _ ≤ (1 / 20) ^ κ * 𝒜 := mul_le_mul_of_nonneg_left (h𝒜 a ha) (by positivity)
        _ = 𝒜 * (1 / 20) ^ κ := mul_comm _ _
    have hmain := sum_powerset_ite_inter_nonempty_le (mem_powerset.1 z.2) hq
    have hconv : ∑ y : A.powerset, (if ((y : Finset α) ∩ z).Nonempty then
        (if (y : Finset α).card = κ then |K y| else 0) else 0) =
        ∑ Y ∈ A.powerset, (if (Y ∩ z).Nonempty then |K' Y| else 0) := by
      rw [← sum_coe_sort A.powerset]
      refine sum_congr rfl fun y _ => ?_
      rw [habs]
    rw [hconv]
    linarith [hmain]

open scoped Classical in
/-- **One tree** (proof of Proposition 4.27): for a tree `T` on `Fin n` rooted at `i₀`, the tuples whose
polymers intersect along `T`, with the root polymer satisfying `Q`, decomposed by the sizes `k`
of the polymers. -/
theorem sum_tree_tuples_le (A : Finset α) (K : Finset α → ℝ) (Q : Finset α → Prop)
    {𝒜 : ℝ} (h𝒜0 : 0 ≤ 𝒜) (hK0 : K ∅ = 0)
    (h𝒜 : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) ≤ 𝒜)
    {n : ℕ} (T : SimpleGraph (Fin n)) (hT : T.IsTree) (i₀ : Fin n) :
    ∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset),
        (if T ≤ connectionGraph X then
          ∏ i, (if i = i₀ then (if Q (X i) then |K (X i)| else 0) else |K (X i)|) else 0) ≤
      ∑ k ∈ Fintype.piFinset (fun _ : Fin n => range (A.card + 1)),
        (∑ y : A.powerset, (if ((y : Finset α)).card = k i₀ then
            (if Q y then |K y| else 0) else 0)) *
          ((∏ i ∈ univ.erase i₀, (if 1 ≤ k i then 𝒜 * (1 / 20) ^ k i else 0)) *
            ∏ j, (max (k j : ℝ) 1) ^ Cayley.deg T j) := by
  set W : Fin n → Finset α → ℝ :=
    fun i Y => if i = i₀ then (if Q Y then |K Y| else 0) else |K Y| with hWdef
  have hW0 : ∀ i Y, 0 ≤ W i Y := fun i Y => by
    simp only [hWdef]
    split_ifs <;> positivity
  have hWK : ∀ i Y, W i Y ≠ 0 → K Y ≠ 0 := fun i Y hY hK => by
    apply hY
    simp only [hWdef, hK, abs_zero]
    split_ifs <;> rfl
  set r : A.powerset → A.powerset → Prop :=
    fun y z => ((y : Finset α) ∩ z).Nonempty with hr
  have hn : Fintype.card (Fin n) = (n - 1) + 1 := by
    rw [Fintype.card_fin]
    have := i₀.pos
    omega
  rw [sum_piFinset_const_eq_sum_subtype]
  -- the condition along `T`
  have hpt : ∀ x : Fin n → A.powerset,
      (if T ≤ connectionGraph (fun i => (x i : Finset α)) then ∏ i, W i (x i) else 0) ≤
        ∑ k ∈ Fintype.piFinset (fun _ : Fin n => range (A.card + 1)),
          (if ∀ i j, T.Adj i j → r (x i) (x j) then
            ∏ i, (if ((x i : Finset α)).card = k i then W i (x i) else 0) else 0) := by
    intro x
    by_cases hTx : T ≤ connectionGraph (fun i => (x i : Finset α))
    · have hc : ∀ i j, T.Adj i j → r (x i) (x j) := fun i j h =>
        inter_nonempty_of_connectionGraph_adj (hTx h)
      rw [ite_eq_left hTx, prod_eq_sum_sizes A W x]
      exact le_of_eq (sum_congr rfl fun k _ => (ite_eq_left hc).symm)
    · rw [ite_eq_right hTx]
      refine sum_nonneg fun k _ => ?_
      split_ifs
      · exact prod_nonneg fun i _ => by split_ifs <;> simp [hW0]
      · exact le_rfl
  refine (sum_le_sum fun x _ => hpt x).trans ?_
  rw [sum_comm]
  refine sum_le_sum fun k _ => ?_
  -- the leaf removal for fixed sizes
  have hleaf := sum_forall_adj_le_root r (n - 1) T hn hT i₀
    (fun i y => if ((y : Finset α)).card = k i then W i y else 0)
    (fun i => if 1 ≤ k i then 𝒜 * (1 / 20) ^ k i else 0) (fun j => max (k j : ℝ) 1)
    (fun i y => by split_ifs <;> simp [hW0]) (fun i => by split_ifs <;> positivity)
    (fun j => le_max_right _ _) ?_
  · refine le_trans (le_of_eq (sum_congr rfl fun x _ => by congr)) (hleaf.trans (le_of_eq ?_))
    congr 1
    refine sum_congr rfl fun y _ => ?_
    simp only [hWdef, ite_true]
  · intro i hi j hji z hz
    have hzk : ((z : Finset α)).card = k j := by
      by_contra hc
      exact hz (by simp only [ite_eq_right hc])
    have hzK : K z ≠ 0 := hWK j z (by
      intro h0
      exact hz (by simp only [hzk, ite_true, h0]))
    have hz1 : 1 ≤ ((z : Finset α)).card := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [card_eq_zero] at h0
      exact hzK (by rw [h0, hK0])
    have hmax : max (k j : ℝ) 1 = ((z : Finset α)).card := by
      rw [← hzk]
      exact max_eq_left (by exact_mod_cast hz1)
    rw [hmax]
    have hWi : ∀ y, W i y = |K y| := fun y => by
      simp only [hWdef, ite_eq_right hi]
    simp only [hWi]
    exact sum_inter_card_le A K hK0 h𝒜 (k i) z

open scoped Classical in
/-- **The anchored-norm tree bound** (proof of Proposition 4.27, eqs. (4.135)–(4.137),
proof of Proposition 4.27): for `n ≥ 1`,
`∑_{Y₁, …, Yₙ ⊆ A, G(Y) connected, ∃ i, Q(Yᵢ)} |∏ᵢ K(Yᵢ) I(G(Y))| ≤ n! B (𝒜/4)^{n-1}`, where
`𝒜 ≥ ∑_{Y ∋ a} |K(Y)| 20^{|Y|}` for every `a ∈ A`, `B ≥ ∑_{Q(Y)} |K(Y)| 20^{|Y|}` and
`K(∅) = 0`. -/
theorem cluster_tree_bound (A : Finset α) (K : Finset α → ℝ) (Q : Finset α → Prop)
    {𝒜 B : ℝ} (h𝒜0 : 0 ≤ 𝒜) (hK0 : K ∅ = 0)
    (h𝒜 : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| * 20 ^ Y.card else 0) ≤ 𝒜)
    (hB : ∑ Y ∈ A.powerset.filter Q, |K Y| * 20 ^ Y.card ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
        (fun X => (connectionGraph X).Connected ∧ ∃ i, Q (X i)),
      |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| ≤
      (n.factorial : ℝ) * (B * (𝒜 / 4) ^ (n - 1)) := by
  set S := Fintype.piFinset fun _ : Fin n => A.powerset with hS
  set W : Fin n → Fin n → Finset α → ℝ :=
    fun i₀ i Y => if i = i₀ then (if Q Y then |K Y| else 0) else |K Y| with hWdef
  have hW0 : ∀ i₀ i Y, 0 ≤ W i₀ i Y := fun i₀ i Y => by
    simp only [hWdef]
    split_ifs <;> positivity
  -- Step 1: choose the vertex carrying `Q`
  have hstep1 : ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected ∧ ∃ i, Q (X i)),
      |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| ≤
      ∑ i₀, ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, W i₀ i (X i) := by
    rw [sum_comm]
    calc ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected ∧ ∃ i, Q (X i)),
          |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)|
        ≤ ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected ∧ ∃ i, Q (X i)),
          ∑ i₀, |(ursell (connectionGraph X) : ℝ)| * ∏ i, W i₀ i (X i) := by
          refine sum_le_sum fun X hX => ?_
          obtain ⟨i₁, hi₁⟩ := (mem_filter.1 hX).2.2
          have heq : |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| =
              |(ursell (connectionGraph X) : ℝ)| * ∏ i, W i₁ i (X i) := by
            rw [abs_mul, abs_prod, mul_comm]
            congr 1
            refine prod_congr rfl fun i _ => ?_
            simp only [hWdef]
            by_cases hi : i = i₁
            · subst hi
              rw [ite_eq_left rfl, ite_eq_left hi₁]
            · rw [ite_eq_right hi]
          rw [heq]
          exact single_le_sum (f := fun i₀ => |(ursell (connectionGraph X) : ℝ)| *
            ∏ i, W i₀ i (X i)) (fun i₀ _ => mul_nonneg (abs_nonneg _)
              (prod_nonneg fun i _ => hW0 _ _ _)) (mem_univ i₁)
      _ ≤ ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
          ∑ i₀, |(ursell (connectionGraph X) : ℝ)| * ∏ i, W i₀ i (X i) := by
          refine sum_le_sum_of_subset_of_nonneg (fun X hX => ?_) fun X _ _ =>
            sum_nonneg fun i₀ _ => mul_nonneg (abs_nonneg _) (prod_nonneg fun i _ => hW0 _ _ _)
          rw [mem_filter] at hX ⊢
          exact ⟨hX.1, hX.2.1⟩
  refine hstep1.trans ?_
  have hn' : (n : ℝ) * (n - 1).factorial = n.factorial := by
    have : n = (n - 1) + 1 := by omega
    conv_rhs => rw [this, Nat.factorial_succ]
    rw [← this]
    push_cast
    ring
  rw [← hn', mul_assoc]
  have hconst : ∑ _i₀ : Fin n, ((n - 1).factorial : ℝ) * (B * (𝒜 / 4) ^ (n - 1)) =
      (n : ℝ) * (((n - 1).factorial : ℝ) * (B * (𝒜 / 4) ^ (n - 1))) := by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← hconst]
  refine sum_le_sum fun i₀ _ => ?_
  -- Step 2: Rota's bound
  refine (sum_abs_ursell_mul_le_sum_isTree' S (W i₀) (hW0 i₀)).trans ?_
  -- Step 3: one tree at a time
  set f : ℕ → ℝ := fun κ => if 1 ≤ κ then 𝒜 * (1 / 20) ^ κ else 0 with hf
  set hh : ℕ → ℝ := fun κ => max (κ : ℝ) 1 with hhdef
  set root : ℕ → ℝ := fun κ => ∑ y : A.powerset, (if ((y : Finset α)).card = κ then
    (if Q y then |K y| else 0) else 0) with hroot
  have hroot0 : ∀ κ, 0 ≤ root κ := fun κ => sum_nonneg fun y _ => by split_ifs <;> positivity
  have hf0 : ∀ κ, 0 ≤ f κ := fun κ => by simp only [hf]; split_ifs <;> positivity
  have hh1 : ∀ κ, 1 ≤ hh κ := fun κ => le_max_right _ _
  have hstep3 : ∀ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
      ∑ X ∈ S, (if T ≤ connectionGraph X then ∏ i, W i₀ i (X i) else 0) ≤
      ∑ k ∈ Fintype.piFinset (fun _ : Fin n => range (A.card + 1)),
        root (k i₀) * ((∏ i ∈ univ.erase i₀, f (k i)) * ∏ j, hh (k j) ^ Cayley.deg T j) :=
    fun T hT => sum_tree_tuples_le A K Q h𝒜0 hK0 h𝒜 T (mem_filter.1 hT).2 i₀
  refine (sum_le_sum hstep3).trans ?_
  rw [sum_comm]
  -- Step 4: Cayley
  set g : Fin n → ℕ → ℝ := fun i κ =>
    if i = i₀ then root κ * (hh κ * Real.exp (hh κ)) else f κ * (hh κ * Real.exp (hh κ))
    with hg
  have hstep4 : ∀ k ∈ Fintype.piFinset (fun _ : Fin n => range (A.card + 1)),
      ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
        root (k i₀) * ((∏ i ∈ univ.erase i₀, f (k i)) * ∏ j, hh (k j) ^ Cayley.deg T j) ≤
      ((n - 1).factorial : ℝ) * ∏ i, g i (k i) := by
    intro k _
    rw [← mul_sum, ← mul_sum]
    have hc := sum_isTree_prod_pow_le hn (fun j => hh (k j)) (fun j => hh1 (k j))
    have hfp : 0 ≤ ∏ i ∈ univ.erase i₀, f (k i) := prod_nonneg fun i _ => hf0 _
    calc root (k i₀) * ((∏ i ∈ univ.erase i₀, f (k i)) *
          ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
            ∏ j, hh (k j) ^ Cayley.deg T j)
        ≤ root (k i₀) * ((∏ i ∈ univ.erase i₀, f (k i)) *
          (((n - 1).factorial : ℝ) * ∏ j, (hh (k j) * Real.exp (hh (k j))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hfp) (hroot0 _)
      _ = ((n - 1).factorial : ℝ) * ∏ i, g i (k i) := by
          rw [← mul_prod_erase univ (fun i => g i (k i)) (mem_univ i₀),
            ← mul_prod_erase univ (fun j => hh (k j) * Real.exp (hh (k j))) (mem_univ i₀)]
          have : ∏ i ∈ univ.erase i₀, g i (k i) =
              ∏ i ∈ univ.erase i₀, (f (k i) * (hh (k i) * Real.exp (hh (k i)))) :=
            prod_congr rfl fun i hi => by
              simp only [hg, ite_eq_right (mem_erase.1 hi).1]
          rw [this]
          simp only [hg, ite_true, prod_mul_distrib]
          ring
  refine (sum_le_sum hstep4).trans ?_
  rw [← mul_sum, ← prod_univ_sum (fun _ : Fin n => range (A.card + 1)) g]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- Step 5: the factors
  have hroot_le : ∑ κ ∈ range (A.card + 1), g i₀ κ ≤ B := by
    simp only [hg, ite_true]
    have hcol : ∑ κ ∈ range (A.card + 1), root κ * (hh κ * Real.exp (hh κ)) =
        ∑ y : A.powerset, (if Q y then |K y| else 0) *
          (hh ((y : Finset α)).card * Real.exp (hh ((y : Finset α)).card)) := by
      simp only [hroot, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun y _ => ?_
      have hy : ((y : Finset α)).card ∈ range (A.card + 1) :=
        mem_range.2 (Nat.lt_succ_of_le (card_le_card (mem_powerset.1 y.2)))
      have : ∀ x ∈ range (A.card + 1), (if ((y : Finset α)).card = x then
          (if Q y then |K y| else 0) else 0) * (hh x * Real.exp (hh x)) =
          if ((y : Finset α)).card = x then
            (if Q y then |K y| else 0) * (hh x * Real.exp (hh x)) else 0 :=
        fun x _ => by split_ifs <;> simp
      rw [sum_congr rfl this, sum_ite_eq (range (A.card + 1)), ite_eq_left hy]
    rw [hcol]
    refine le_trans ?_ hB
    rw [← sum_coe_sort (A.powerset.filter Q)]
    have hfil : ∑ y : A.powerset, (if Q y then |K y| else 0) *
          (hh ((y : Finset α)).card * Real.exp (hh ((y : Finset α)).card)) ≤
        ∑ y : A.powerset, (if Q y then |K y| * 20 ^ ((y : Finset α)).card else 0) := by
      refine sum_le_sum fun y _ => ?_
      by_cases hQ : Q y
      · rw [ite_eq_left hQ, ite_eq_left hQ]
        by_cases hy0 : ((y : Finset α)).card = 0
        · rw [card_eq_zero] at hy0
          rw [hy0, hK0, abs_zero, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have : hh ((y : Finset α)).card = ((y : Finset α)).card :=
            max_eq_left (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hy0)
          rw [this]
          exact natCast_mul_exp_le_pow _
      · rw [ite_eq_right hQ, ite_eq_right hQ, zero_mul]
    refine hfil.trans (le_of_eq ?_)
    rw [← sum_filter]
    refine sum_bij' (fun y hy => ⟨y, mem_filter.2 ⟨y.2, (mem_filter.1 hy).2⟩⟩)
      (fun y _ => ⟨y, (mem_filter.1 y.2).1⟩) (fun _ _ => mem_univ _)
      (fun y _ => mem_filter.2 ⟨mem_univ _, (mem_filter.1 y.2).2⟩)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hleaf_le : ∀ i ≠ i₀, ∑ κ ∈ range (A.card + 1), g i κ ≤ 𝒜 / 4 := by
    intro i hi
    simp only [hg, ite_eq_right hi]
    have h4 := sum_mul_exp_div_le A.card
    have hterm : ∀ κ ∈ range (A.card + 1), f κ * (hh κ * Real.exp (hh κ)) =
        𝒜 * (if 1 ≤ κ then (κ : ℝ) * Real.exp κ * (1 / 20) ^ κ else 0) := by
      intro κ _
      simp only [hf, hhdef]
      split_ifs with hκ
      · rw [max_eq_left (by exact_mod_cast hκ)]
        ring
      · ring
    rw [sum_congr rfl hterm, ← mul_sum]
    calc 𝒜 * ∑ κ ∈ range (A.card + 1), (if 1 ≤ κ then (κ : ℝ) * Real.exp κ * (1 / 20) ^ κ
          else 0) ≤ 𝒜 * (1 / 4) := mul_le_mul_of_nonneg_left h4 h𝒜0
      _ = 𝒜 / 4 := by ring
  have hg0 : ∀ i κ, 0 ≤ g i κ := fun i κ => by
    simp only [hg]
    split_ifs
    · exact mul_nonneg (hroot0 _) (mul_nonneg (zero_le_one.trans (hh1 _)) (Real.exp_pos _).le)
    · exact mul_nonneg (hf0 _) (mul_nonneg (zero_le_one.trans (hh1 _)) (Real.exp_pos _).le)
  rw [← mul_prod_erase univ (fun i => ∑ κ ∈ range (A.card + 1), g i κ) (mem_univ i₀)]
  have hcard : (univ.erase i₀).card = n - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  calc (∑ κ ∈ range (A.card + 1), g i₀ κ) *
        ∏ i ∈ univ.erase i₀, ∑ κ ∈ range (A.card + 1), g i κ
      ≤ B * ∏ i ∈ univ.erase i₀, (𝒜 / 4) := by
        refine mul_le_mul hroot_le (prod_le_prod₀ (fun i _ => sum_nonneg fun κ _ => hg0 _ _)
          fun i hi => hleaf_le i (mem_erase.1 hi).1) (prod_nonneg fun i _ =>
            sum_nonneg fun κ _ => hg0 _ _) ?_
        exact (sum_nonneg fun κ _ => hg0 _ _).trans hroot_le
    _ = B * (𝒜 / 4) ^ (n - 1) := by rw [prod_const, hcard]

end Cluster

end AbsoluteLower

end MultipoleBKT

end
