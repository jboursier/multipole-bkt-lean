/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Rota
public import MultipoleBKT.Cluster.TreeCount
public import MultipoleBKT.Frozen.ConnectionGraph

/-!
# The bounded cluster tail (Lemma 4.53)

We prove Lemma 4.53 (equation (4.88)): let `A` be a nonempty finite set with
`|A| ≤ N`, `p ≥ 2`, and `K : 𝒫(A) → ℝ` vanishing unless `2 ≤ |X| ≤ p`, with
`|K(X)| ≤ C₀ (λ²/N)^(|X|-1)` on this range. There is `C = C(C₀, p)` such that for
`0 < λ ≤ 1` and `n ≥ 1`,

  `(1 / (N n!)) ∑_{X_1, …, X_n ⊂ A connected} |I(G(X_1, …, X_n))| ∏ᵢ |K(X_i)| ≤ (C λ²)ⁿ`

(`MultipoleBKT.bounded_cluster_tail`). The specialization to `A = {0, …, N-1}` with labels in
`ℕ`, in the form of the cluster sums of Theorem 1, is
`MultipoleBKT.bounded_cluster_tail_range`; the bound `|cluster n| ≤ N (C λ²)ⁿ` on the cluster
terms of Theorem 1 (2.38) and (2.40) is `MultipoleBKT.abs_cluster_le` and
`MultipoleBKT.abs_cluster_le'`.

The proof follows the paper. With `q = max_{a ∈ A} ∑_{X ∋ a} |K(X)| ≤ p C₀ λ²`
(`MultipoleBKT.sum_powerset_ite_mem_le`), Rota's bound (4.87)
(`MultipoleBKT.abs_ursell_le_card_isTree`) bounds `|I(G(X))|` by the number of spanning trees of
`G(X)`. For a fixed tree on `[n]`, summing leaf by leaf (`MultipoleBKT.sum_ite_forall_adj_le`)
costs at most `p q` per leaf and `N q` at the root. Cayley's formula gives exactly
`n^(n-2)` trees, including the singleton case.
`bounded_cluster_tail_cayley` retains the exact coefficient `n^(n-2)/n!`.
Only at the last step is it bounded by `e^(2n)`, preserving the numerical constant
`C = e² p² (max C₀ 0 + 1)`.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

section Tail

variable {α : Type*} [DecidableEq α]

/-- `M.choose m (x/N)^m ≤ x` for `M ≤ N`, `m ≥ 1` and `0 ≤ x ≤ 1`. -/
theorem choose_mul_div_pow_le {M N m : ℕ} (hMN : M ≤ N) (hN : 0 < N) (hm : 1 ≤ m) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (M.choose m : ℝ) * (x / N) ^ m ≤ x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  calc (M.choose m : ℝ) * (x / N) ^ m ≤ (N : ℝ) ^ m * (x / N) ^ m := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast (Nat.choose_le_pow M m).trans (Nat.pow_le_pow_left hMN m)
    _ = x ^ m := by rw [← mul_pow, mul_div_cancel₀ _ hN'.ne']
    _ ≤ x := pow_le_of_le_one hx0 hx1 (by omega)

/-- The bound `q ≤ p C₀ λ²` (proof of Lemma 4.53): for `a ∈ A`, `∑_{X ⊂ A, X ∋ a} |K(X)|` is
at most `p C₀ λ²`. -/
theorem sum_powerset_ite_mem_le {N p : ℕ} {A : Finset α} {K : Finset α → ℝ} {C₀ lam : ℝ}
    (hAN : A.card ≤ N) (hC₀ : 0 ≤ C₀) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hK0 : ∀ X ⊆ A, ¬ (2 ≤ X.card ∧ X.card ≤ p) → K X = 0)
    (hK : ∀ X ⊆ A, 2 ≤ X.card → X.card ≤ p → |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1))
    {a : α} (ha : a ∈ A) :
    ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| else 0) ≤ p * C₀ * lam ^ 2 := by
  have hN : 0 < N := (card_pos.mpr ⟨a, ha⟩).trans_le hAN
  have haA : a ∉ A.erase a := notMem_erase a A
  have hlam2 : 0 ≤ lam ^ 2 := sq_nonneg lam
  have hlam21 : lam ^ 2 ≤ 1 := pow_le_one₀ hlam hlam1
  let g : ℕ → ℝ := fun m => if 1 ≤ m ∧ m + 1 ≤ p then C₀ * (lam ^ 2 / N) ^ m else 0
  rw [← insert_erase ha, sum_powerset_insert haA]
  have h1 : ∑ t ∈ (A.erase a).powerset, (if a ∈ t then |K t| else 0) = 0 :=
    sum_eq_zero fun t ht => ite_eq_right fun hat => haA (mem_powerset.mp ht hat)
  have h2 : ∀ t ∈ (A.erase a).powerset,
      (if a ∈ insert a t then |K (insert a t)| else 0) ≤ g t.card := by
    intro t ht
    have hta : a ∉ t := fun h => haA (mem_powerset.mp ht h)
    have hsub : insert a t ⊆ A :=
      insert_subset ha ((mem_powerset.mp ht).trans (erase_subset a A))
    have hcard : (insert a t).card = t.card + 1 := card_insert_of_notMem hta
    rw [ite_eq_left (mem_insert_self a t)]
    by_cases hr : 1 ≤ t.card ∧ t.card + 1 ≤ p
    · have h := hK _ hsub (by omega) (by omega)
      rw [hcard, Nat.add_sub_cancel] at h
      simpa only [g, ite_eq_left hr] using h
    · rw [hK0 _ hsub (by omega), abs_zero]
      simp only [g, ite_eq_right hr, le_refl]
  have h3 : ∀ m ∈ range ((A.erase a).card + 1),
      ((A.erase a).card.choose m) • g m ≤ (if m < p then C₀ * lam ^ 2 else 0) := by
    intro m _
    rw [nsmul_eq_mul]
    by_cases hr : 1 ≤ m ∧ m + 1 ≤ p
    · simp only [g, ite_eq_left hr, ite_eq_left (show m < p by omega)]
      have hAe : (A.erase a).card ≤ N := (card_erase_le).trans hAN
      calc ((A.erase a).card.choose m : ℝ) * (C₀ * (lam ^ 2 / N) ^ m)
          = C₀ * (((A.erase a).card.choose m : ℝ) * (lam ^ 2 / N) ^ m) := by ring
        _ ≤ C₀ * lam ^ 2 :=
            mul_le_mul_of_nonneg_left (choose_mul_div_pow_le hAe hN hr.1 hlam2 hlam21) hC₀
    · simp only [g, ite_eq_right hr, mul_zero]
      split_ifs <;> positivity
  calc ∑ t ∈ (A.erase a).powerset, (if a ∈ t then |K t| else 0) +
        ∑ t ∈ (A.erase a).powerset, (if a ∈ insert a t then |K (insert a t)| else 0)
      ≤ 0 + ∑ t ∈ (A.erase a).powerset, g t.card := by
        rw [h1]
        exact add_le_add le_rfl (sum_le_sum h2)
    _ = ∑ m ∈ range ((A.erase a).card + 1), ((A.erase a).card.choose m) • g m := by
        rw [zero_add, sum_powerset_apply_card g]
    _ ≤ ∑ m ∈ range ((A.erase a).card + 1), (if m < p then C₀ * lam ^ 2 else 0) :=
        sum_le_sum h3
    _ = ∑ m ∈ (range ((A.erase a).card + 1)).filter (· < p), C₀ * lam ^ 2 := by
        rw [sum_filter]
    _ ≤ ∑ m ∈ range p, C₀ * lam ^ 2 := by
        refine sum_le_sum_of_subset_of_nonneg (fun m hm => ?_) fun _ _ _ => by positivity
        rw [mem_filter] at hm
        exact mem_range.mpr hm.2
    _ = p * C₀ * lam ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul, mul_assoc]

/-- Union bound: for `Z ⊆ A`, `∑_{X ⊂ A, X ∩ Z ≠ ∅} |K(X)| ≤ |Z| q`, where `q` bounds
`∑_{X ⊂ A, X ∋ a} |K(X)|` for every `a ∈ A`. -/
theorem sum_powerset_ite_inter_nonempty_le {A Z : Finset α} {K : Finset α → ℝ} {q : ℝ}
    (hZ : Z ⊆ A) (hq : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| else 0) ≤ q) :
    ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then |K Y| else 0) ≤ Z.card * q := by
  have hnn : ∀ (b : α) (Y : Finset α), 0 ≤ (if b ∈ Y then |K Y| else 0) := fun b Y => by
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  calc ∑ Y ∈ A.powerset, (if (Y ∩ Z).Nonempty then |K Y| else 0)
      ≤ ∑ Y ∈ A.powerset, ∑ a ∈ Z, (if a ∈ Y then |K Y| else 0) := by
        refine sum_le_sum fun Y _ => ?_
        split_ifs with h
        · obtain ⟨a, ha⟩ := h
          rw [mem_inter] at ha
          calc |K Y| = (if a ∈ Y then |K Y| else 0) := (ite_eq_left ha.1).symm
            _ ≤ ∑ b ∈ Z, (if b ∈ Y then |K Y| else 0) :=
                single_le_sum (fun b _ => hnn b Y) ha.2
        · exact sum_nonneg fun b _ => hnn b Y
    _ = ∑ a ∈ Z, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| else 0) := sum_comm
    _ ≤ ∑ _a ∈ Z, q := sum_le_sum fun a ha => hq a (hZ ha)
    _ = Z.card * q := by rw [sum_const, nsmul_eq_mul]

/-- The root bound: `∑_{X ⊂ A} |K(X)| ≤ |A| q` when `K(∅) = 0`. -/
theorem sum_powerset_abs_le {A : Finset α} {K : Finset α → ℝ} {q : ℝ} (hK : K ∅ = 0)
    (hq : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| else 0) ≤ q) :
    ∑ Y ∈ A.powerset, |K Y| ≤ A.card * q := by
  calc ∑ Y ∈ A.powerset, |K Y|
      = ∑ Y ∈ A.powerset, (if (Y ∩ A).Nonempty then |K Y| else 0) := by
        refine sum_congr rfl fun Y hY => ?_
        rw [inter_eq_left.mpr (mem_powerset.mp hY)]
        split_ifs with h
        · rfl
        · rw [not_nonempty_iff_eq_empty.mp h, hK, abs_zero]
    _ ≤ A.card * q := sum_powerset_ite_inter_nonempty_le subset_rfl hq

/-- Sums over `piFinset (fun _ => s)` are sums over functions into the subtype `s`. -/
theorem sum_piFinset_const_eq_sum_subtype {ι γ : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset γ) (f : (ι → γ) → ℝ) :
    ∑ X ∈ Fintype.piFinset (fun _ : ι => s), f X = ∑ x : ι → s, f (fun i => (x i : γ)) :=
  sum_bij' (fun X hX i => ⟨X i, Fintype.mem_piFinset.mp hX i⟩) (fun x _ i => (x i : γ))
    (fun _ _ => mem_univ _) (fun x _ => Fintype.mem_piFinset.mpr fun i => (x i).2)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- Adjacent vertices of the connection graph `G(X)` index intersecting sets. -/
theorem inter_nonempty_of_connectionGraph_adj {n : ℕ} {X : Fin n → Finset α} {i j : Fin n}
    (h : (connectionGraph X).Adj i j) : (X i ∩ X j).Nonempty := by
  rw [connectionGraph, fromRel_adj] at h
  rcases h.2 with h | h
  · exact h
  · rwa [inter_comm]

open scoped Classical in
/-- Rota's bound (4.87) in the cluster sum: `|I(G(X))|` is at most the number of trees `T ≤ G(X)`,
and the resulting sum is regrouped over the trees on `[n]`. -/
theorem sum_abs_ursell_mul_le_sum_isTree {n : ℕ} (S : Finset (Fin n → Finset α))
    (w : Finset α → ℝ) (hw : ∀ Y, 0 ≤ w Y) :
    ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, w (X i) ≤
      ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
        ∑ X ∈ S, (if T ≤ connectionGraph X then ∏ i, w (X i) else 0) := by
  have hP : ∀ X : Fin n → Finset α, 0 ≤ ∏ i, w (X i) := fun X => prod_nonneg fun i _ => hw _
  calc ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, w (X i)
      ≤ ∑ X ∈ S, |(ursell (connectionGraph X) : ℝ)| * ∏ i, w (X i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun X _ _ => mul_nonneg (abs_nonneg _) (hP X)
    _ ≤ ∑ X ∈ S, (((univ : Finset (SimpleGraph (Fin n))).filter
          (fun T => T ≤ connectionGraph X ∧ T.IsTree)).card : ℝ) * ∏ i, w (X i) := by
        refine sum_le_sum fun X _ => mul_le_mul_of_nonneg_right ?_ (hP X)
        have h := abs_ursell_le_natCard_isTree (connectionGraph X)
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
        rw [← Int.cast_abs, ← Int.cast_natCast]
        exact Int.cast_le.mpr h
    _ = ∑ X ∈ S, ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
          (if T ≤ connectionGraph X then ∏ i, w (X i) else 0) := by
        refine sum_congr rfl fun X _ => ?_
        rw [← sum_filter, filter_filter, sum_const, nsmul_eq_mul]
        congr 3
        ext T
        simp only [mem_filter, mem_univ, true_and]
        exact and_comm
    _ = _ := sum_comm

open scoped Classical in
/-- **The exact Cayley estimate** in Lemma 4.53. The root costs `Nq`,
each leaf costs `pq`, and there are `n^(n-2)` trees, including the singleton case. -/
theorem bounded_cluster_tail_cayley {N p n : ℕ} {A : Finset α} {K : Finset α → ℝ}
    {C₀ lam : ℝ} (hA : A.Nonempty) (hAN : A.card ≤ N) (hC₀ : 0 ≤ C₀)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hn : 1 ≤ n)
    (hK0 : ∀ X ⊆ A, ¬ (2 ≤ X.card ∧ X.card ≤ p) → K X = 0)
    (hK : ∀ X ⊆ A, 2 ≤ X.card → X.card ≤ p → |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) :
    1 / (N * n.factorial) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
            (fun X => (connectionGraph X).Connected),
          |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K (X i)| ≤
      (n : ℝ) ^ (n - 2) / n.factorial *
        (p * C₀ * lam ^ 2) * (p * (p * C₀ * lam ^ 2)) ^ (n - 1) := by
  have hN : 0 < N := (card_pos.mpr hA).trans_le hAN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  set q : ℝ := p * C₀ * lam ^ 2 with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq : ∀ a ∈ A, ∑ Y ∈ A.powerset, (if a ∈ Y then |K Y| else 0) ≤ q := fun a ha =>
    sum_powerset_ite_mem_le hAN hC₀ hlam.le hlam1 hK0 hK ha
  have hKe : K ∅ = 0 := hK0 ∅ (empty_subset A) (by simp)
  -- the polymers are the elements of `𝒫(A)`, with weights `|K|` and incompatibility
  -- `X ∩ Y ≠ ∅`
  obtain ⟨r, hr⟩ : ∃ r : A.powerset → A.powerset → Prop,
      ∀ y z, r y z ↔ ((y : Finset α) ∩ z).Nonempty := ⟨_, fun _ _ => Iff.rfl⟩
  have hroot : ∑ y : A.powerset, |K y| ≤ N * q := by
    calc ∑ y : A.powerset, |K y| = ∑ Y ∈ A.powerset, |K Y| :=
          sum_coe_sort A.powerset (fun Y => |K Y|)
      _ ≤ A.card * q := sum_powerset_abs_le hKe hq
      _ ≤ N * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hAN) hq0
  have hleaf : ∀ z : A.powerset,
      |K z| * ∑ y : A.powerset, (if r y z then |K y| else 0) ≤ (p * q) * |K z| := by
    intro z
    have hz : (z : Finset α) ⊆ A := mem_powerset.mp z.2
    have hsum : ∑ y : A.powerset, (if r y z then |K y| else 0) =
        ∑ Y ∈ A.powerset, (if (Y ∩ z).Nonempty then |K Y| else 0) := by
      rw [← sum_coe_sort A.powerset]
      refine sum_congr rfl fun y _ => ?_
      by_cases h : r y z
      · rw [ite_eq_left h, ite_eq_left ((hr y z).mp h)]
      · rw [ite_eq_right h, ite_eq_right fun h' => h ((hr y z).mpr h')]
    by_cases hKz : K z = 0
    · rw [hKz, abs_zero, zero_mul, mul_zero]
    · have hzp : (z : Finset α).card ≤ p := by
        by_contra h
        exact hKz (hK0 _ hz fun h' => h h'.2)
      rw [hsum, mul_comm (p * q)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc ∑ Y ∈ A.powerset, (if (Y ∩ z).Nonempty then |K Y| else 0)
          ≤ (z : Finset α).card * q := sum_powerset_ite_inter_nonempty_le hz hq
        _ ≤ p * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hzp) hq0
  -- the bound for a fixed tree
  have htree : ∀ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
      ∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset),
          (if T ≤ connectionGraph X then ∏ i, |K (X i)| else 0) ≤
        (N * q) * (p * q) ^ (n - 1) := by
    intro T hT
    have hT' : T.IsTree := by simpa using hT
    rw [sum_piFinset_const_eq_sum_subtype]
    refine le_trans (sum_le_sum fun x _ => ?_)
      ((sum_ite_forall_adj_le (fun y : A.powerset => |K y|) (fun _ => abs_nonneg _) r
        (by positivity) hleaf (n - 1) T (by rw [Fintype.card_fin]; omega) hT').trans
        (mul_le_mul_of_nonneg_right hroot (by positivity)))
    by_cases hTx : T ≤ connectionGraph (fun i => (x i : Finset α))
    · have hc : ∀ i j, T.Adj i j → r (x i) (x j) := fun i j h =>
        (hr _ _).mpr (inter_nonempty_of_connectionGraph_adj (hTx h))
      rw [ite_eq_left hTx, ite_eq_left hc]
    · rw [ite_eq_right hTx]
      split_ifs
      · exact prod_nonneg fun i _ => abs_nonneg _
      · exact le_rfl
  have hsum : ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
        (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K (X i)| ≤
      (n : ℝ) ^ (n - 2) * ((N * q) * (p * q) ^ (n - 1)) := by
    calc _ ≤ ∑ T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
          ∑ X ∈ Fintype.piFinset (fun _ : Fin n => A.powerset),
            (if T ≤ connectionGraph X then ∏ i, |K (X i)| else 0) :=
          sum_abs_ursell_mul_le_sum_isTree _ (fun Y => |K Y|) fun Y => abs_nonneg _
      _ ≤ ∑ _T ∈ (univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree),
          (N * q) * (p * q) ^ (n - 1) := sum_le_sum htree
      _ = (((univ : Finset (SimpleGraph (Fin n))).filter (fun T => T.IsTree)).card : ℝ) *
          ((N * q) * (p * q) ^ (n - 1)) := by rw [sum_const, nsmul_eq_mul]
      _ = (n : ℝ) ^ (n - 2) * ((N * q) * (p * q) ^ (n - 1)) := by
          rw [card_isTree_fin_eq n hn, Nat.cast_pow]
  calc 1 / (N * n.factorial) * _
      ≤ 1 / (N * n.factorial) *
          ((n : ℝ) ^ (n - 2) * ((N * q) * (p * q) ^ (n - 1))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (n : ℝ) ^ (n - 2) / n.factorial * q * (p * q) ^ (n - 1) := by
        field_simp

open scoped Classical in
/-- **Lemma 4.53 with explicit constant** (internal form): under the hypotheses of Lemma 4.53 with `C₀ ≥ 0` and `p ≥ 1`, the left side of (4.88) is at most
`(e² p (p C₀ λ²))ⁿ`. -/
theorem bounded_cluster_tail_of_nonneg {N p n : ℕ} {A : Finset α} {K : Finset α → ℝ}
    {C₀ lam : ℝ} (hA : A.Nonempty) (hAN : A.card ≤ N) (hp : 1 ≤ p) (hC₀ : 0 ≤ C₀)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hn : 1 ≤ n)
    (hK0 : ∀ X ⊆ A, ¬ (2 ≤ X.card ∧ X.card ≤ p) → K X = 0)
    (hK : ∀ X ⊆ A, 2 ≤ X.card → X.card ≤ p → |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) :
    1 / (N * n.factorial) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
            (fun X => (connectionGraph X).Connected),
          |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K (X i)| ≤
      (Real.exp 2 * (p * (p * C₀ * lam ^ 2))) ^ n := by
  have h := bounded_cluster_tail_cayley hA hAN hC₀ hlam hlam1 hn hK0 hK
  set q : ℝ := p * C₀ * lam ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hcount : (n : ℝ) ^ (n - 2) / n.factorial ≤ Real.exp 2 ^ n :=
    (div_le_iff₀ hf).mpr (cayley_pow_le_exp_mul_factorial n hn)
  have hpow : (p * q) ^ n = (p * q) * (p * q) ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
  calc _ ≤ (n : ℝ) ^ (n - 2) / n.factorial * q * (p * q) ^ (n - 1) := h
    _ ≤ Real.exp 2 ^ n * (q * (p * q) ^ (n - 1)) := by
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hcount (show 0 ≤ q * (p * q) ^ (n - 1) by positivity)
    _ ≤ Real.exp 2 ^ n * ((p * q) * (p * q) ^ (n - 1)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        exact le_mul_of_one_le_left hq0 hp'
    _ = (Real.exp 2 * (p * q)) ^ n := by rw [mul_pow (Real.exp 2), hpow]

open scoped Classical in
/-- **Lemma 4.53** (equation (4.88)). Let `C₀ ∈ ℝ` and `p ≥ 2`. There is `C > 0` (depending only on
`C₀` and `p`) such that: for every nonempty finite set `A` with `|A| ≤ N` and every
`K : 𝒫(A) → ℝ` that vanishes unless `2 ≤ |X| ≤ p` and satisfies
`|K(X)| ≤ C₀ (λ²/N)^(|X|-1)` on this range, for `0 < λ ≤ 1` and every `n ≥ 1`,

  `(1 / (N n!)) ∑_{X_1, …, X_n ⊂ A, G(X) connected} |I(G(X_1, …, X_n))| ∏ᵢ |K(X_i)| ≤ (C λ²)ⁿ`.

Tuples `X_1, …, X_n ⊂ A` are functions `Fin n → Finset α` with values in `A.powerset`; the
values of `K` off `𝒫(A)` play no role. -/
theorem bounded_cluster_tail (C₀ : ℝ) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (N : ℕ) (A : Finset α) (K : Finset α → ℝ) (lam : ℝ)
        (n : ℕ),
        A.Nonempty → A.card ≤ N →
        (∀ X ⊆ A, ¬ (2 ≤ X.card ∧ X.card ≤ p) → K X = 0) →
        (∀ X ⊆ A, 2 ≤ X.card → X.card ≤ p → |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
        0 < lam → lam ≤ 1 → 1 ≤ n →
        1 / (N * n.factorial) *
            ∑ X ∈ (Fintype.piFinset fun _ : Fin n => A.powerset).filter
                (fun X => (connectionGraph X).Connected),
              |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K (X i)| ≤
          (C * lam ^ 2) ^ n := by
  refine ⟨Real.exp 2 * p ^ 2 * (max C₀ 0 + 1), by positivity, ?_⟩
  intro α _ N A K lam n hA hAN hK0 hK hlam hlam1 hn
  have hK' : ∀ X ⊆ A, 2 ≤ X.card → X.card ≤ p →
      |K X| ≤ max C₀ 0 * (lam ^ 2 / N) ^ (X.card - 1) := fun X hX h2 hp' =>
    (hK X hX h2 hp').trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine (bounded_cluster_tail_of_nonneg hA hAN (by omega) (le_max_right _ _) hlam hlam1 hn
    hK0 hK').trans (pow_le_pow_left₀ (by positivity) ?_ n)
  have hC : (p : ℝ) * (p * max C₀ 0) ≤ p ^ 2 * (max C₀ 0 + 1) := by
    rw [← mul_assoc, ← sq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc Real.exp 2 * (p * (p * max C₀ 0 * lam ^ 2))
      = Real.exp 2 * (p * (p * max C₀ 0)) * lam ^ 2 := by ring
    _ ≤ Real.exp 2 * (p ^ 2 * (max C₀ 0 + 1)) * lam ^ 2 := by gcongr
    _ = Real.exp 2 * p ^ 2 * (max C₀ 0 + 1) * lam ^ 2 := by ring

open scoped Classical in
/-- Comparison of a filtered cluster sum with the connected cluster sum of Lemma 4.53: if the
filter `P` only keeps tuples with connected `G(X)`, on which `|∏ K(X_i)| ≤ ∏ |K'(X_i)|`, then
`∑_{X ∈ S, P X} |∏ K(X_i) · I(G(X))| ≤ ∑_{X ∈ S, G(X) connected} |I(G(X))| ∏ |K'(X_i)|`. -/
theorem sum_filter_abs_prod_mul_ursell_le {n : ℕ} (S : Finset (Fin n → Finset α))
    (P : (Fin n → Finset α) → Prop) [DecidablePred P] (K K' : Finset α → ℝ)
    (hP : ∀ X ∈ S, P X → (connectionGraph X).Connected)
    (hK : ∀ X ∈ S, P X → |∏ i, K (X i)| ≤ ∏ i, |K' (X i)|) :
    ∑ X ∈ S.filter P, |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| ≤
      ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
        |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K' (X i)| := by
  calc ∑ X ∈ S.filter P, |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)|
      ≤ ∑ X ∈ S.filter P, |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K' (X i)| := by
        refine sum_le_sum fun X hX => ?_
        rw [mem_filter] at hX
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hK X hX.1 hX.2) (abs_nonneg _)
    _ ≤ ∑ X ∈ S.filter (fun X => (connectionGraph X).Connected),
          |(ursell (connectionGraph X) : ℝ)| * ∏ i, |K' (X i)| := by
        refine sum_le_sum_of_subset_of_nonneg (fun X hX => ?_) fun X _ _ =>
          mul_nonneg (abs_nonneg _) (prod_nonneg fun i _ => abs_nonneg _)
        rw [mem_filter] at hX ⊢
        exact ⟨hX.1, hP X hX.1 hX.2⟩

end Tail

section Range

open scoped Classical in
/-- **Lemma 4.53 for `A = {0, …, N-1}`** (labels in `ℕ`, as in the cluster sums of Theorem 1). -/
theorem bounded_cluster_tail_range (C₀ : ℝ) (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (K : Finset ℕ → ℝ) (lam : ℝ) (n : ℕ), 1 ≤ N →
        (∀ X ⊆ Finset.range N, ¬ (2 ≤ X.card ∧ X.card ≤ p) → K X = 0) →
        (∀ X ⊆ Finset.range N, 2 ≤ X.card → X.card ≤ p →
          |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
        0 < lam → lam ≤ 1 → 1 ≤ n →
        1 / (N * n.factorial) *
            ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                (fun V => (connectionGraph V).Connected),
              |(ursell (connectionGraph V) : ℝ)| * ∏ i, |K (V i)| ≤
          (C * lam ^ 2) ^ n := by
  obtain ⟨C, hC, h⟩ := bounded_cluster_tail C₀ p hp
  refine ⟨C, hC, fun N K lam n hN hK0 hK hlam hlam1 hn => ?_⟩
  exact h N (Finset.range N) K lam n (nonempty_range_iff.mpr (by omega)) (card_range N).le hK0
    hK hlam hlam1 hn

open scoped Classical in
/-- The `n`-th cluster term of Theorem 1 (2.38), `(1/n!) ∑_{X connected, 2 ≤ |X_i| ≤ p}
∏ K(X_i) I(G(X))`, is at most `N (C λ²)ⁿ` in absolute value, for any `K` with
`|K(X)| ≤ C₀ (λ²/N)^(|X|-1)` when `2 ≤ |X| ≤ p` (Lemma 4.53; no condition on `p`). -/
theorem abs_cluster_le (C₀ : ℝ) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (K : Finset ℕ → ℝ) (lam : ℝ) (n : ℕ), 1 ≤ N →
        (∀ X ⊆ Finset.range N, 2 ≤ X.card → X.card ≤ p →
          |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
        0 < lam → lam ≤ 1 → 1 ≤ n →
        |1 / (n.factorial : ℝ) *
            ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                (fun V => (connectionGraph V).Connected ∧
                  ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
              (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)| ≤
          N * (C * lam ^ 2) ^ n := by
  obtain ⟨C, hC, h⟩ := bounded_cluster_tail_range (max C₀ 0) (max p 2) (le_max_right _ _)
  refine ⟨C, hC, fun N K lam n hN hK hlam hlam1 hn => ?_⟩
  obtain ⟨K', hK'_def⟩ : ∃ K' : Finset ℕ → ℝ,
      ∀ X, K' X = if 2 ≤ X.card ∧ X.card ≤ p then K X else 0 := ⟨_, fun _ => rfl⟩
  have hK'0 : ∀ X ⊆ Finset.range N, ¬ (2 ≤ X.card ∧ X.card ≤ max p 2) → K' X = 0 :=
    fun X _ hX => by
      rw [hK'_def]
      exact ite_eq_right fun h' => hX ⟨h'.1, h'.2.trans (le_max_left _ _)⟩
  have hK' : ∀ X ⊆ Finset.range N, 2 ≤ X.card → X.card ≤ max p 2 →
      |K' X| ≤ max C₀ 0 * (lam ^ 2 / N) ^ (X.card - 1) := by
    intro X hX h2 _
    by_cases hXp : X.card ≤ p
    · rw [hK'_def, ite_eq_left ⟨h2, hXp⟩]
      exact (hK X hX h2 hXp).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · rw [hK'_def, ite_eq_right fun h' => hXp h'.2, abs_zero]
      positivity
  have hmain := h N K' lam n hN hK'0 hK' hlam hlam1 hn
  have hcmp := sum_filter_abs_prod_mul_ursell_le
    (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset)
    (fun V => (connectionGraph V).Connected ∧ ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p) K K'
    (fun _ _ hX => hX.1) (fun X _ hX => by
      rw [abs_prod]
      refine le_of_eq (prod_congr rfl fun i _ => ?_)
      rw [hK'_def, ite_eq_left (hX.2 i)])
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n.factorial)]
  calc 1 / (n.factorial : ℝ) * |∑ V ∈ (Fintype.piFinset fun _ : Fin n =>
          (Finset.range N).powerset).filter (fun V => (connectionGraph V).Connected ∧
            ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
          (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)|
      ≤ 1 / (n.factorial : ℝ) *
          ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
            (fun V => (connectionGraph V).Connected),
            |(ursell (connectionGraph V) : ℝ)| * ∏ i, |K' (V i)| :=
        mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans hcmp) (by positivity)
    _ = N * (1 / (N * n.factorial) *
          ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
            (fun V => (connectionGraph V).Connected),
            |(ursell (connectionGraph V) : ℝ)| * ∏ i, |K' (V i)|) := by
        field_simp
    _ ≤ N * (C * lam ^ 2) ^ n := mul_le_mul_of_nonneg_left hmain hN'.le

open scoped Classical in
/-- The `n`-th cluster term of Theorem 1 (2.40), `(1/n!) ∑_{X connected, |X_i| ≤ p}
∏ K(X_i) I(G(X))`, is at most `N (C λ²)ⁿ` in absolute value, for any `K` vanishing on sets with
fewer than two elements and with `|K(X)| ≤ C₀ (λ²/N)^(|X|-1)` when `2 ≤ |X| ≤ p`
(Lemma 4.53). -/
theorem abs_cluster_le' (C₀ : ℝ) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (K : Finset ℕ → ℝ) (lam : ℝ) (n : ℕ), 1 ≤ N →
        (∀ X ⊆ Finset.range N, X.card < 2 → K X = 0) →
        (∀ X ⊆ Finset.range N, 2 ≤ X.card → X.card ≤ p →
          |K X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
        0 < lam → lam ≤ 1 → 1 ≤ n →
        |1 / (n.factorial : ℝ) *
            ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                (fun V => (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p),
              (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)| ≤
          N * (C * lam ^ 2) ^ n := by
  obtain ⟨C, hC, h⟩ := abs_cluster_le C₀ p
  refine ⟨C, hC, fun N K lam n hN hK1 hK hlam hlam1 hn => ?_⟩
  have heq : ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
        (fun V => (connectionGraph V).Connected ∧ ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ p),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ) =
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
        (fun V => (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ) := by
    refine sum_subset (fun V hV => ?_) (fun V hV3 hV1 => ?_)
    · rw [mem_filter] at hV ⊢
      exact ⟨hV.1, hV.2.1, fun i => (hV.2.2 i).2⟩
    · rw [mem_filter] at hV3 hV1
      have hi : ∃ i, (V i).card < 2 := by
        by_contra hcon
        push Not at hcon
        exact hV1 ⟨hV3.1, hV3.2.1, fun i => ⟨hcon i, hV3.2.2 i⟩⟩
      obtain ⟨i, hi⟩ := hi
      have hsub : V i ⊆ Finset.range N := mem_powerset.mp (Fintype.mem_piFinset.mp hV3.1 i)
      rw [prod_eq_zero (mem_univ i) (hK1 _ hsub hi), zero_mul]
  rw [← heq]
  exact h N K lam n hN hK hlam hlam1 hn

end Range

end MultipoleBKT

end
