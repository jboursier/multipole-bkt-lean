/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Tail

/-!
# Telescoping two connected cluster series (proof of Proposition 4.62, Step 2)

The comparison of two retained connected cluster series in the proof of Proposition 4.62, Step 2: for activities `K₁`, `K₂` on the subsets of a
finite set `A`, with `|K₁|, |K₂| ≤ w` and `|K₁ - K₂| ≤ d`, where the weights `w`, `d` vanish on
sets with more than `p` elements and `q = max_{a ∈ A} ∑_{Y ∋ a} w(Y)`,

  `|∑_{n ≥ 1} (1/n!) ∑_{X₁, …, Xₙ ⊂ A connected} (∏ᵢ K₁(Xᵢ) - ∏ᵢ K₂(Xᵢ)) I(G(X))|
    ≤ 4 e² ∑_{Y ⊂ A} d(Y)`

as soon as `e² p q ≤ 1/2`. The paper's argument: telescope the products
(`abs_prod_sub_prod_le_sum_erase`), bound `|I(G)|` by the number of spanning trees (Rota's bound,
`sum_abs_ursell_mul_le_sum_isTree'`), and sum the tree leaf by leaf, rooted at the changed factor
(`sum_ite_forall_adj_le_rooted`). Cayley's exact count and the `n` choices of the root
give `n^(n-1)` rooted trees (`mul_cayley_pow`). The normalized coefficient
`n^(n-1)/n!` is kept until the final summable majorant.

Results:

* `abs_prod_sub_prod_le_sum_erase`: `|∏ a - ∏ b| ≤ ∑_j d_j ∏_{i ≠ j} w_i`;
* `sum_ite_forall_adj_le_rooted`: the leaf-by-leaf summation of
  `MultipoleBKT.sum_ite_forall_adj_le` with a distinguished root carrying the weight `d`;
* `abs_sum_connected_prod_sub_le`: the `n`-th term,
  `|∑_{X connected} (∏ K₁ - ∏ K₂) I(G(X))| ≤ n^(n-1) D cⁿ⁻¹`, with `D = ∑_{Y ⊂ A} d(Y)`
  and `c` the cost of a leaf;
* `abs_tsum_connected_sub_le`: the series, `≤ 4 e² D` when `e² c ≤ 1/2`.
-/

@[expose] public section

namespace MultipoleBKT

namespace LowerBoundLDP

open Finset SimpleGraph

/-! ### Telescoping a product -/

/-- **Telescoping a product**: if `|a_i|, |b_i| ≤ w_i` and `|a_i - b_i| ≤ d_i`, then
`|∏_{i ∈ s} a_i - ∏_{i ∈ s} b_i| ≤ ∑_{j ∈ s} d_j ∏_{i ∈ s, i ≠ j} w_i`. -/
theorem abs_prod_sub_prod_le_sum_erase {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {a b w d : ι → ℝ} (ha : ∀ i ∈ s, |a i| ≤ w i) (hb : ∀ i ∈ s, |b i| ≤ w i)
    (hab : ∀ i ∈ s, |a i - b i| ≤ d i) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ j ∈ s, d j * ∏ i ∈ s.erase j, w i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have ha' : ∀ i ∈ s, |a i| ≤ w i := fun i hi => ha i (mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ w i := fun i hi => hb i (mem_insert_of_mem hi)
    have hab' : ∀ i ∈ s, |a i - b i| ≤ d i := fun i hi => hab i (mem_insert_of_mem hi)
    have hw0 : ∀ i ∈ s, 0 ≤ w i := fun i hi => (abs_nonneg _).trans (ha' i hi)
    have hwx : 0 ≤ w x := (abs_nonneg _).trans (ha x (mem_insert_self x s))
    have hPb : |∏ i ∈ s, b i| ≤ ∏ i ∈ s, w i := by
      rw [abs_prod]
      exact prod_le_prod₀ (fun i _ => abs_nonneg _) hb'
    rw [prod_insert hx, prod_insert hx, sum_insert hx, erase_insert hx]
    have hsplit : a x * ∏ i ∈ s, a i - b x * ∏ i ∈ s, b i =
        a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i := by ring
    have hsum : ∑ j ∈ s, d j * ∏ i ∈ (insert x s).erase j, w i =
        w x * ∑ j ∈ s, d j * ∏ i ∈ s.erase j, w i := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hjx : j ≠ x := fun h => hx (h ▸ hj)
      rw [erase_insert_of_ne hjx.symm, prod_insert fun h => hx (mem_of_mem_erase h)]
      ring
    rw [hsplit, hsum]
    calc |a x * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a x - b x) * ∏ i ∈ s, b i|
        ≤ |a x| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| + |a x - b x| * |∏ i ∈ s, b i| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
      _ ≤ w x * ∑ j ∈ s, d j * ∏ i ∈ s.erase j, w i + d x * ∏ i ∈ s, w i := by
          gcongr
          · exact ha x (mem_insert_self x s)
          · exact ih ha' hb' hab'
          · exact (abs_nonneg _).trans (hab x (mem_insert_self x s))
          · exact hab x (mem_insert_self x s)
      _ = d x * ∏ i ∈ s, w i + w x * ∑ j ∈ s, d j * ∏ i ∈ s.erase j, w i := by ring

/-! ### Summation leaf by leaf, with a root -/

section TreeSum

variable {β : Type*} [Fintype β]

/-- The weights of a rooted sum: `d` at the root `ρ`, `w` elsewhere. -/
def rootWeight {ι : Type*} [DecidableEq ι] (w d : β → ℝ) (ρ i : ι) (y : β) : ℝ :=
  if i = ρ then d y else w y

omit [Fintype β] in
theorem rootWeight_nonneg {ι : Type*} [DecidableEq ι] {w d : β → ℝ} (hw : ∀ b, 0 ≤ w b)
    (hd : ∀ b, 0 ≤ d b) (ρ i : ι) (y : β) : 0 ≤ rootWeight w d ρ i y := by
  unfold rootWeight
  split_ifs
  · exact hd y
  · exact hw y

open scoped Classical in
/-- **Summation leaf by leaf, with a root.** Let `w, d ≥ 0` be weights on a finite type `β` and
`r` a relation on `β` such that `w z · ∑_{y, r y z} w y ≤ c · w z` and
`d z · ∑_{y, r y z} w y ≤ c · d z` for every `z`. For every tree `T` on `n + 1` vertices with a
root `ρ`, `∑_{x : ι → β, r (x i) (x j) for ij ∈ T} d(x_ρ) ∏_{i ≠ ρ} w(x_i) ≤ (∑ d) cⁿ`. -/
theorem sum_ite_forall_adj_le_rooted (w d : β → ℝ) (hw : ∀ b, 0 ≤ w b) (hd : ∀ b, 0 ≤ d b)
    (r : β → β → Prop) {c : ℝ} (hc : 0 ≤ c)
    (hrw : ∀ z, w z * ∑ y, (if r y z then w y else 0) ≤ c * w z)
    (hrd : ∀ z, d z * ∑ y, (if r y z then w y else 0) ≤ c * d z) (n : ℕ) :
    ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (T : SimpleGraph ι) (ρ : ι),
      Fintype.card ι = n + 1 → T.IsTree →
      ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then
          ∏ i, rootWeight w d ρ i (x i) else 0) ≤ (∑ y, d y) * c ^ n := by
  induction n with
  | zero =>
    intro ι _ _ T ρ hcard _
    have hsub : ∀ i : ι, i = ρ := fun i =>
      Fintype.card_le_one_iff.mp (by omega) i ρ
    calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then
          ∏ i, rootWeight w d ρ i (x i) else 0)
        ≤ ∑ x : ι → β, ∏ i, rootWeight w d ρ i (x i) := by
          refine sum_le_sum fun x _ => ?_
          split_ifs
          · exact le_rfl
          · exact prod_nonneg fun i _ => rootWeight_nonneg hw hd ρ i _
      _ = ∏ i : ι, ∑ y, rootWeight w d ρ i y := (Fintype.prod_sum fun i y => rootWeight w d ρ i y).symm
      _ = ∑ y, d y := by
          rw [Fintype.prod_eq_single ρ fun i hi => absurd (hsub i) hi]
          simp only [rootWeight, ↓reduceIte]
      _ = (∑ y, d y) * c ^ 0 := by rw [pow_zero, mul_one]
  | succ n ih =>
    intro ι _ _ T ρ hcard hT
    have : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hv, hvρ⟩ : ∃ v, T.degree v = 1 ∧ v ≠ ρ := by
      obtain ⟨u₁, u₂, hne, h₁, h₂⟩ := hT.exists_ne_and_degree_eq_one
      by_cases h : u₁ = ρ
      · exact ⟨u₂, h₂, fun h' => hne (h.trans h'.symm)⟩
      · exact ⟨u₁, h₁, h⟩
    obtain ⟨u, hvu, -⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
    let T' : SimpleGraph {i // i ≠ v} := T.comap Subtype.val
    have hT' : T'.IsTree :=
      ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
        hT.isAcyclic.comap ⟨Subtype.val, fun h => h⟩ Subtype.val_injective⟩
    have hcard' : Fintype.card {i // i ≠ v} = n + 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
      omega
    let ρ' : {i // i ≠ v} := ⟨ρ, hvρ.symm⟩
    let u' : {i // i ≠ v} := ⟨u, hvu.ne.symm⟩
    have hW : ∀ (i : {i // i ≠ v}) (y : β), rootWeight w d ρ' i y = rootWeight w d ρ i.1 y := by
      intro i y
      unfold rootWeight
      congr 1
      exact propext Subtype.ext_iff
    let F' : ({i // i ≠ v} → β) → ℝ := fun x' =>
      if ∀ i j, T'.Adj i j → r (x' i) (x' j) then ∏ i, rootWeight w d ρ' i (x' i) else 0
    have hF' : ∀ x', 0 ≤ F' x' := fun x' => by
      simp only [F']
      split_ifs
      · exact prod_nonneg fun i _ => rootWeight_nonneg hw hd ρ' i _
      · exact le_rfl
    have hpt : ∀ x : ι → β,
        (if ∀ i j, T.Adj i j → r (x i) (x j) then ∏ i, rootWeight w d ρ i (x i) else 0) ≤
          (if r (x v) (x u) then w (x v) else 0) * F' (fun i => x i.1) := by
      intro x
      by_cases h1 : ∀ i j, T.Adj i j → r (x i) (x j)
      · simp only [F']
        have h2 : ∀ i j : {i // i ≠ v}, T'.Adj i j → r (x i.1) (x j.1) := fun i j h => h1 i j h
        rw [ite_eq_left h1, ite_eq_left (h1 v u hvu), ite_eq_left h2,
          Fintype.prod_eq_mul_prod_subtype_ne _ v]
        have hv' : rootWeight w d ρ v (x v) = w (x v) := by
          unfold rootWeight
          rw [ite_eq_right hvρ]
        rw [hv']
        exact le_of_eq (congrArg _ (prod_congr rfl fun i _ => (hW i (x i.1)).symm))
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
        have hP : 0 ≤ ∏ i : {i // i ≠ u'}, rootWeight w d ρ' i.1 (x' i.1) :=
          prod_nonneg fun i _ => rootWeight_nonneg hw hd ρ' _ _
        have hu : rootWeight w d ρ' u' (x' u') * ∑ y, (if r y (x' u') then w y else 0) ≤
            c * rootWeight w d ρ' u' (x' u') := by
          unfold rootWeight
          split_ifs
          · exact hrd _
          · exact hrw _
        calc (∑ y, (if r y (x' u') then w y else 0)) *
              (rootWeight w d ρ' u' (x' u') * ∏ i : {i // i ≠ u'}, rootWeight w d ρ' i.1 (x' i.1))
            = (rootWeight w d ρ' u' (x' u') * ∑ y, (if r y (x' u') then w y else 0)) *
                ∏ i : {i // i ≠ u'}, rootWeight w d ρ' i.1 (x' i.1) := by ring
          _ ≤ (c * rootWeight w d ρ' u' (x' u')) *
                ∏ i : {i // i ≠ u'}, rootWeight w d ρ' i.1 (x' i.1) :=
              mul_le_mul_of_nonneg_right hu hP
          _ = c * (rootWeight w d ρ' u' (x' u') *
                ∏ i : {i // i ≠ u'}, rootWeight w d ρ' i.1 (x' i.1)) := by ring
      · simp
    calc ∑ x : ι → β, (if ∀ i j, T.Adj i j → r (x i) (x j) then
          ∏ i, rootWeight w d ρ i (x i) else 0)
        ≤ ∑ x : ι → β, (if r (x v) (x u) then w (x v) else 0) * F' (fun i => x i.1) :=
          sum_le_sum fun x _ => hpt x
      _ = ∑ y, ∑ x' : {i // i ≠ v} → β, (if r y (x' u') then w y else 0) * F' x' :=
          hsplit fun y x' => (if r y (x' u') then w y else 0) * F' x'
      _ = ∑ x' : {i // i ≠ v} → β, (∑ y, (if r y (x' u') then w y else 0)) * F' x' := by
          rw [sum_comm]
          simp_rw [sum_mul]
      _ ≤ ∑ x' : {i // i ≠ v} → β, c * F' x' := sum_le_sum fun x' _ => key x'
      _ = c * ∑ x' : {i // i ≠ v} → β, F' x' := (mul_sum _ _ _).symm
      _ ≤ c * ((∑ y, d y) * c ^ n) := mul_le_mul_of_nonneg_left (by convert ih T' ρ' hcard' hT') hc
      _ = (∑ y, d y) * c ^ (n + 1) := by ring

end TreeSum

/-! ### The `n`-th term -/

section Term

variable {α : Type*} [DecidableEq α]

open scoped Classical in
/-- Rota's bound (4.86) in a cluster sum with an arbitrary nonnegative weight `f` of the tuple:
`∑_{X connected} |I(G(X))| f(X) ≤ ∑_{T tree} ∑_X 𝟙_{T ≤ G(X)} f(X)`. -/
theorem sum_abs_ursell_mul_le_sum_isTree' {n : ℕ} (S : Finset (Fin n → Finset α))
    (f : (Fin n → Finset α) → ℝ) (hf : ∀ X, 0 ≤ f X) :
    ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * f X ≤
      ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
        ∑ X ∈ S, (if T ≤ connectionGraph X then f X else 0) := by
  calc ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * f X
      ≤ ∑ X ∈ S, |(ursell (connectionGraph X) : ℝ)| * f X :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun X _ _ => mul_nonneg (abs_nonneg _) (hf X)
    _ ≤ ∑ X ∈ S, (((univ : Finset (SimpleGraph (Fin n))).filter
          (fun T => T ≤ connectionGraph X ∧ T.IsTree)).card : ℝ) * f X := by
        refine sum_le_sum fun X _ => mul_le_mul_of_nonneg_right ?_ (hf X)
        have h := abs_ursell_le_natCard_isTree (connectionGraph X)
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
        rw [← Int.cast_abs, ← Int.cast_natCast]
        exact Int.cast_le.mpr h
    _ = ∑ X ∈ S, ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
          (if T ≤ connectionGraph X then f X else 0) := by
        refine sum_congr rfl fun X _ => ?_
        rw [← sum_filter, filter_filter, sum_const, nsmul_eq_mul]
        congr 3
        ext T
        simp only [mem_filter, mem_univ, true_and]
        exact and_comm
    _ = _ := sum_comm

omit [DecidableEq α] in
theorem prod_rootWeight_eq {n : ℕ} (w d : Finset α → ℝ) (X : Fin n → Finset α) (j : Fin n) :
    ∏ i, rootWeight w d j i (X i) = d (X j) * ∏ i ∈ univ.erase j, w (X i) := by
  rw [← mul_prod_erase univ _ (mem_univ j)]
  unfold rootWeight
  rw [ite_eq_left rfl]
  congr 1
  exact prod_congr rfl fun i hi => ite_eq_right (ne_of_mem_erase hi)

open scoped Classical in
/-- The rooted tree sum of a fixed tree `T`: summing leaf by leaf from the root `j`,
`∑_{X ⊂ A, T ≤ G(X)} d(X_j) ∏_{i ≠ j} w(X_i) ≤ D cⁿ⁻¹`. -/
theorem sum_ite_le_connectionGraph_le {A : Finset α} {w d : Finset α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hw : ∀ Y, 0 ≤ w Y) (hd : ∀ Y, 0 ≤ d Y)
    (hcw : ∀ Z ⊆ A, w Z * ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ c * w Z)
    (hcd : ∀ Z ⊆ A, d Z * ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ c * d Z)
    {n : ℕ} (hn : 1 ≤ n) (T : SimpleGraph (Fin n)) (hT : T.IsTree) (j : Fin n) :
    ∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset),
        (if T ≤ connectionGraph X then ∏ i, rootWeight w d j i (X i) else 0) ≤
      (∑ Y ∈ A.powerset, d Y) * c ^ (n - 1) := by
  obtain ⟨r, hr⟩ : ∃ r : A.powerset → A.powerset → Prop,
      ∀ y z, r y z ↔ ((y : Finset α) ∩ z).Nonempty := ⟨_, fun _ _ => Iff.rfl⟩
  set w' : A.powerset → ℝ := fun y => w y
  set d' : A.powerset → ℝ := fun y => d y
  have hsumr : ∀ z : A.powerset, ∑ y : A.powerset, (if r y z then w' y else 0) =
      ∑ Y ∈ A.powerset, (if (Y ∩ z).Nonempty then w Y else 0) := by
    intro z
    rw [← sum_coe_sort A.powerset]
    refine sum_congr rfl fun y _ => ?_
    by_cases h : r y z
    · rw [ite_eq_left h, ite_eq_left ((hr y z).mp h)]
    · rw [ite_eq_right h, ite_eq_right fun h' => h ((hr y z).mpr h')]
  have hrw : ∀ z, w' z * ∑ y, (if r y z then w' y else 0) ≤ c * w' z := fun z => by
    rw [hsumr]
    exact hcw z (mem_powerset.mp z.2)
  have hrd : ∀ z, d' z * ∑ y, (if r y z then w' y else 0) ≤ c * d' z := fun z => by
    rw [hsumr]
    exact hcd z (mem_powerset.mp z.2)
  have hroot := sum_ite_forall_adj_le_rooted w' d' (fun y => hw _) (fun y => hd _) r hc hrw hrd
    (n - 1) T j (by rw [Fintype.card_fin]; omega) hT
  rw [sum_piFinset_const_eq_sum_subtype]
  have hD : ∑ y : A.powerset, d' y = ∑ Y ∈ A.powerset, d Y := sum_coe_sort A.powerset d
  rw [← hD]
  refine le_trans (sum_le_sum fun x _ => ?_) hroot
  have hW : ∀ i, rootWeight w d j i (x i : Finset α) = rootWeight w' d' j i (x i) := fun i => rfl
  simp only [hW]
  by_cases hTx : T ≤ connectionGraph (fun i => (x i : Finset α))
  · have hcx : ∀ i k, T.Adj i k → r (x i) (x k) := fun i k h =>
      (hr _ _).mpr (inter_nonempty_of_connectionGraph_adj (hTx h))
    rw [ite_eq_left hTx, ite_eq_left hcx]
  · rw [ite_eq_right hTx]
    split_ifs
    · exact prod_nonneg fun i _ => rootWeight_nonneg (fun y => hw _) (fun y => hd _) j i _
    · exact le_rfl

open scoped Classical in
/-- **The `n`-th term of the telescoping estimate**: with `|K₁|, |K₂| ≤ w`, `|K₁ - K₂| ≤ d` on
the subsets of `A` and the leaf costs `c` for `w` and `d`,
`|∑_{X ⊂ A connected} (∏ᵢ K₁(Xᵢ) - ∏ᵢ K₂(Xᵢ)) I(G(X))| ≤ n^(n-1) (∑_{Y ⊂ A} d(Y)) cⁿ⁻¹`. -/
theorem abs_sum_connected_prod_sub_le {A : Finset α} {K₁ K₂ w d : Finset α → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hw : ∀ Y, 0 ≤ w Y) (hd : ∀ Y, 0 ≤ d Y)
    (h₁ : ∀ Y ⊆ A, |K₁ Y| ≤ w Y) (h₂ : ∀ Y ⊆ A, |K₂ Y| ≤ w Y)
    (h₁₂ : ∀ Y ⊆ A, |K₁ Y - K₂ Y| ≤ d Y)
    (hcw : ∀ Z ⊆ A, w Z * ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ c * w Z)
    (hcd : ∀ Z ⊆ A, d Z * ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ c * d Z)
    {n : ℕ} (hn : 1 ≤ n) :
    |∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₁ (X i) - ∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)| ≤
      (n : ℝ) ^ (n - 1) * (∑ Y ∈ A.powerset, d Y) * c ^ (n - 1) := by
  set S := Fintype.piFinset fun _ : Fin n => A.powerset
  set D := ∑ Y ∈ A.powerset, d Y
  have hD : 0 ≤ D := sum_nonneg fun Y _ => hd Y
  set 𝒯 := (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree)
  have hsub : ∀ X ∈ S, ∀ i, X i ⊆ A := fun X hX i =>
    mem_powerset.mp (Fintype.mem_piFinset.mp hX i)
  -- telescoping each product
  have htel : ∀ X ∈ S, |∏ i, K₁ (X i) - ∏ i, K₂ (X i)| ≤
      ∑ j, ∏ i, rootWeight w d j i (X i) := by
    intro X hX
    refine (abs_prod_sub_prod_le_sum_erase univ (fun i _ => h₁ _ (hsub X hX i))
      (fun i _ => h₂ _ (hsub X hX i)) (fun i _ => h₁₂ _ (hsub X hX i))).trans (le_of_eq ?_)
    exact sum_congr rfl fun j _ => (prod_rootWeight_eq w d X j).symm
  have hP : ∀ (j : Fin n) (X : Fin n → Finset α), 0 ≤ ∏ i, rootWeight w d j i (X i) := fun j X =>
    prod_nonneg fun i _ => rootWeight_nonneg hw hd j i _
  calc |∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        (∏ i, K₁ (X i) - ∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)|
      ≤ ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
          |(ursell (connectionGraph X) : ℝ)| * ∑ j, ∏ i, rootWeight w d j i (X i) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun X hX => ?_)
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (htel X (mem_filter.mp hX).1) (abs_nonneg _)
    _ = ∑ j, ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
          |(ursell (connectionGraph X) : ℝ)| * ∏ i, rootWeight w d j i (X i) := by
        rw [sum_comm]
        exact sum_congr rfl fun X _ => mul_sum _ _ _
    _ ≤ ∑ j : Fin n, ∑ T ∈ 𝒯, ∑ X ∈ S,
          (if T ≤ connectionGraph X then ∏ i, rootWeight w d j i (X i) else 0) :=
        sum_le_sum fun j _ => sum_abs_ursell_mul_le_sum_isTree' S _ (hP j)
    _ ≤ ∑ _j : Fin n, ∑ _T ∈ 𝒯, D * c ^ (n - 1) := by
        refine sum_le_sum fun j _ => sum_le_sum fun T hT => ?_
        exact sum_ite_le_connectionGraph_le hc hw hd hcw hcd hn T (by simpa [𝒯] using hT) j
    _ = n * ((𝒯.card : ℝ) * (D * c ^ (n - 1))) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    _ = n * ((n : ℝ) ^ (n - 2) * (D * c ^ (n - 1))) := by
        rw [card_isTree_fin_eq n hn, Nat.cast_pow]
    _ = (n : ℝ) ^ (n - 1) * D * c ^ (n - 1) := by
        rw [← mul_assoc, mul_cayley_pow n hn]
        ring

/-- `e^{2n} cⁿ⁻¹ ≤ 2 e² (1/2)ⁿ` when `e² c ≤ 1/2`, `c ≥ 0`, `n ≥ 1`. -/
theorem exp_two_pow_mul_pow_le {c : ℝ} (hc : 0 ≤ c) (hsmall : Real.exp 2 * c ≤ 1 / 2) {n : ℕ}
    (hn : 1 ≤ n) : Real.exp 2 ^ n * c ^ (n - 1) ≤ 2 * Real.exp 2 * (1 / 2) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, pow_succ]
  have h1 : Real.exp 2 ^ m * c ^ m ≤ (1 / 2) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsmall m
  have he : 0 < Real.exp 2 := Real.exp_pos 2
  calc Real.exp 2 ^ m * Real.exp 2 * c ^ m = Real.exp 2 * (Real.exp 2 ^ m * c ^ m) := by ring
    _ ≤ Real.exp 2 * (1 / 2) ^ m := mul_le_mul_of_nonneg_left h1 he.le
    _ = 2 * Real.exp 2 * ((1 / 2) ^ m * (1 / 2)) := by ring

/-- `∑_{n ≥ 1} n (1/2)ⁿ ≤ 2`. -/
theorem tsum_pnat_mul_half_pow_le :
    ∑' n : ℕ+, ((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ) ≤ 2 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
  have hs : Summable fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  calc ∑' n : ℕ+, ((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ)
      ≤ ∑' n : ℕ, (n : ℝ) * (1 / 2 : ℝ) ^ n :=
        tsum_comp_le_tsum_of_inj (f := fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) hs
          (fun _ => by positivity) PNat.coe_injective
    _ = 2 := by
        rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
        norm_num

open scoped Classical in
/-- **The telescoping estimate for two connected cluster series** (proof of Proposition 4.62): under the hypotheses of `abs_sum_connected_prod_sub_le` and
`e² c ≤ 1/2`, if both series converge,
`|∑_{n ≥ 1} (1/n!) ∑_{X conn} ∏ K₁(Xᵢ) I(G(X)) - ∑_{n ≥ 1} (1/n!) ∑_{X conn} ∏ K₂(Xᵢ) I(G(X))|
≤ 4 e² ∑_{Y ⊂ A} d(Y)`. -/
theorem abs_tsum_connected_sub_le {A : Finset α} {K₁ K₂ w d : Finset α → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hw : ∀ Y, 0 ≤ w Y) (hd : ∀ Y, 0 ≤ d Y)
    (h₁ : ∀ Y ⊆ A, |K₁ Y| ≤ w Y) (h₂ : ∀ Y ⊆ A, |K₂ Y| ≤ w Y)
    (h₁₂ : ∀ Y ⊆ A, |K₁ Y - K₂ Y| ≤ d Y)
    (hcw : ∀ Z ⊆ A, w Z * ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ c * w Z)
    (hcd : ∀ Z ⊆ A, d Z * ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ c * d Z)
    (hsmall : Real.exp 2 * c ≤ 1 / 2)
    (hs₁ : Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ))
    (hs₂ : Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)) :
    |(∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
            (fun X => (connectionGraph X).Connected),
          (∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)) -
      ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
            (fun X => (connectionGraph X).Connected),
          (∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)| ≤
      4 * Real.exp 2 * ∑ Y ∈ A.powerset, d Y := by
  set D := ∑ Y ∈ A.powerset, d Y
  have hD : 0 ≤ D := sum_nonneg fun Y _ => hd Y
  rw [← hs₁.tsum_sub hs₂]
  set g : ℕ+ → ℝ := fun n => 2 * Real.exp 2 * D * (((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ))
  have hterm : ∀ n : ℕ+, ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ) -
      1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)‖ ≤ g n := by
    intro n
    have hn : 1 ≤ (n : ℕ) := n.pos
    have hf : (0 : ℝ) < ((n : ℕ).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [← mul_sub, ← sum_sub_distrib, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℕ).factorial : ℝ))]
    have e : ∀ X : Fin n → Finset α, (∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ) -
        (∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ) =
        (∏ i, K₁ (X i) - ∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ) := fun X => by ring
    simp only [e]
    have hb := abs_sum_connected_prod_sub_le hc hw hd h₁ h₂ h₁₂ hcw hcd hn
    have hpow := exp_two_pow_mul_pow_le hc hsmall hn
    calc 1 / ((n : ℕ).factorial : ℝ) * |∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
          (∏ i, K₁ (X i) - ∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)|
        ≤ 1 / ((n : ℕ).factorial : ℝ) *
            ((((n : ℕ) : ℝ) ^ ((n : ℕ) - 1)) * D * c ^ ((n : ℕ) - 1)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (((n : ℕ) : ℝ) ^ ((n : ℕ) - 1) / (n : ℕ).factorial) *
          D * c ^ ((n : ℕ) - 1) := by ring
      _ ≤ ((n : ℕ) : ℝ) * D * (Real.exp 2 ^ (n : ℕ) * c ^ ((n : ℕ) - 1)) := by
          have hcount : (((n : ℕ) : ℝ) ^ ((n : ℕ) - 1) / (n : ℕ).factorial) ≤
              ((n : ℕ) : ℝ) * Real.exp 2 ^ (n : ℕ) := by
            rw [← mul_cayley_pow (n : ℕ) hn, mul_div_assoc]
            exact mul_le_mul_of_nonneg_left
              ((div_le_iff₀ hf).mpr (cayley_pow_le_exp_mul_factorial (n : ℕ) hn))
              (Nat.cast_nonneg _)
          calc _ ≤ (((n : ℕ) : ℝ) * Real.exp 2 ^ (n : ℕ)) * D * c ^ ((n : ℕ) - 1) := by
                     gcongr
               _ = _ := by ring
      _ ≤ ((n : ℕ) : ℝ) * D * (2 * Real.exp 2 * (1 / 2) ^ (n : ℕ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = g n := by simp only [g]; ring
  have hg : Summable g := by
    have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by norm_num)]; norm_num
    have hs : Summable fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
    exact (hs.comp_injective PNat.coe_injective).mul_left (2 * Real.exp 2 * D)
  have hnorm : Summable fun n : ℕ+ => ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ) -
      1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, K₂ (X i)) * (ursell (connectionGraph X) : ℝ)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hg
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hnorm).trans ((hnorm.tsum_le_tsum hterm hg).trans ?_)
  rw [show g = fun n : ℕ+ => 2 * Real.exp 2 * D * (((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ)) from rfl,
    tsum_mul_left]
  calc 2 * Real.exp 2 * D * ∑' n : ℕ+, ((n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ)
      ≤ 2 * Real.exp 2 * D * 2 :=
        mul_le_mul_of_nonneg_left tsum_pnat_mul_half_pow_le (by positivity)
    _ = 4 * Real.exp 2 * D := by ring

end Term

end LowerBoundLDP

end MultipoleBKT

end
