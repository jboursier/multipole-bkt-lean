/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.StableMatching

/-!
# The greedy stable matching

API for the frozen `greedyMatching` and `stableMatching` (Definition 2.1;
Definition 4.1 and Remark 4.2). Configurations are `c : Fin N → ℂ × ℂ`
with `c i = (x_i, y_i)`; the pair matched at each iteration is the
lexicographic minimiser of the key `(|x_i - y_j|, i, j)`.

* `matchKey c (i, j) = (|x_i - y_j|, i, j)` (in `ℝ ×ₗ (Fin N ×ₗ Fin N)`): the key the procedure
  minimises. It is injective, so it is a strict preference order on the pairs.
* `greedyMatching_succ_apply_fst`, `greedyMatching_succ_apply_of_ne`: one iteration of the procedure
  matches the key minimiser `(i, j)` and then runs on the remaining labels.
* `greedyMatching_not_blocking`, `greedyMatching_eq_of_bijOn`: the greedy matching has no
  blocking pair for the key order, and it is the only bijection with this property.
* `IsLexStable c σ`: `σ` has no blocking pair for the key order;
  `stableMatching_eq_iff : stableMatching c = σ ↔ IsLexStable c σ`.
* `stableMatching_apply_of_isMin`, `stableMatching_apply_of_forall_lt`,
  `stableMatching_apply_of_ne`: the first matched pair is the key minimiser, and the rest of the
  matching is the greedy matching of the remaining labels.
* `stableMatching_not_blocking`, `stableMatching_eq_iff_of_injective` (Remark 4.2): the stable
  matching has no blocking pair for the distance preferences, and when the distances
  `|x_i - y_j|` are pairwise distinct it is the unique matching with this property.
-/

@[expose] public section

namespace MultipoleBKT

variable {N : ℕ}

/-! ### The key `(|x_i - y_j|, i, j)` -/

section Key

/-- The key `(|x_i - y_j|, i, j)` of the pair `p = (i, j)`, ordered lexicographically: the
procedure of Definition 4.1 matches the pair of smallest key first (first
contact, simultaneous contacts broken by the lexicographically smallest `(i, j)`). -/
noncomputable def matchKey (c : Fin N → ℂ × ℂ) (p : Fin N × Fin N) : ℝ ×ₗ (Fin N ×ₗ Fin N) :=
  toLex (‖(c p.1).1 - (c p.2).2‖, toLex p)

theorem matchKey_injective (c : Fin N → ℂ × ℂ) : Function.Injective (matchKey c) := by
  intro p q h
  simpa [matchKey] using congrArg (fun z => ofLex (ofLex z).2) h

theorem matchKey_lt_matchKey_iff (c : Fin N → ℂ × ℂ) (p q : Fin N × Fin N) :
    matchKey c p < matchKey c q ↔
      ‖(c p.1).1 - (c p.2).2‖ < ‖(c q.1).1 - (c q.2).2‖ ∨
        ‖(c p.1).1 - (c p.2).2‖ = ‖(c q.1).1 - (c q.2).2‖ ∧ toLex p < toLex q := by
  simp only [matchKey, Prod.Lex.toLex_lt_toLex]

theorem norm_sub_le_of_matchKey_le {c : Fin N → ℂ × ℂ} {p q : Fin N × Fin N}
    (h : matchKey c p ≤ matchKey c q) : ‖(c p.1).1 - (c p.2).2‖ ≤ ‖(c q.1).1 - (c q.2).2‖ := by
  rcases h.lt_or_eq with h | h
  · rcases (matchKey_lt_matchKey_iff c p q).1 h with h | h
    · exact h.le
    · exact h.1.le
  · rw [matchKey_injective c h]

theorem matchKey_lt_of_norm_sub_lt {c : Fin N → ℂ × ℂ} {p q : Fin N × Fin N}
    (h : ‖(c p.1).1 - (c p.2).2‖ < ‖(c q.1).1 - (c q.2).2‖) : matchKey c p < matchKey c q :=
  (matchKey_lt_matchKey_iff c p q).2 (Or.inl h)

/-- When the distances `|x_i - y_j|` are pairwise distinct, the key order is the distance
order. -/
theorem matchKey_lt_matchKey_iff_of_injective {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (p q : Fin N × Fin N) :
    matchKey c p < matchKey c q ↔ ‖(c p.1).1 - (c p.2).2‖ < ‖(c q.1).1 - (c q.2).2‖ := by
  refine ⟨fun h => ?_, matchKey_lt_of_norm_sub_lt⟩
  refine (norm_sub_le_of_matchKey_le h.le).lt_of_ne fun heq => h.ne ?_
  rw [hc heq]

/-- Every nonempty finite set of pairs has a key minimiser. -/
theorem exists_isMin_matchKey (c : Fin N → ℂ × ℂ) {s : Finset (Fin N × Fin N)}
    (hs : s.Nonempty) : ∃ p ∈ s, ∀ q ∈ s, matchKey c p ≤ matchKey c q :=
  s.exists_min_image (matchKey c) hs

theorem min'_image_matchKey (c : Fin N → ℂ × ℂ) {s : Finset (Fin N × Fin N)}
    (hs : (s.image (matchKey c)).Nonempty) {p : Fin N × Fin N} (hp : p ∈ s)
    (hmin : ∀ q ∈ s, matchKey c p ≤ matchKey c q) :
    (s.image (matchKey c)).min' hs = matchKey c p := by
  refine le_antisymm (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hp)) ?_
  refine Finset.le_min' _ _ _ fun y hy => ?_
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
  exact hmin q hq

end Key

/-! ### One iteration of the greedy procedure -/

section Greedy

/-- The pair chosen in the body of `greedyMatching` is the key minimiser (stated with the literal
key of the frozen body). -/
theorem ofLex_min'_image_eq (c : Fin N → ℂ × ℂ) {s : Finset (Fin N × Fin N)}
    (hs : (s.image fun ij : Fin N × Fin N =>
      toLex (‖(c ij.1).1 - (c ij.2).2‖, toLex ij)).Nonempty)
    {p : Fin N × Fin N} (hp : p ∈ s) (hmin : ∀ q ∈ s, matchKey c p ≤ matchKey c q) :
    ofLex (ofLex ((s.image fun ij : Fin N × Fin N =>
      toLex (‖(c ij.1).1 - (c ij.2).2‖, toLex ij)).min' hs)).2 = p :=
  congrArg (fun z => ofLex (ofLex z).2) (min'_image_matchKey c hs hp hmin)

/-- `greedyMatching` only depends on its label sets (not on the cardinality proofs). -/
theorem greedyMatching_congr (c : Fin N → ℂ × ℂ) {k k' : ℕ} {A A' B B' : Finset (Fin N)}
    (hk : k = k') (hAA : A = A') (hBB : B = B') (hA : A.card = k) (hB : B.card = k)
    (hA' : A'.card = k') (hB' : B'.card = k') {a : Fin N} (ha : a ∈ A) (ha' : a ∈ A') :
    (greedyMatching c k A B hA hB ⟨a, ha⟩ : Fin N) =
      greedyMatching c k' A' B' hA' hB' ⟨a, ha'⟩ := by
  subst hk hAA hBB
  rfl

theorem nonempty_product_of_card_eq_succ {k : ℕ} {A B : Finset (Fin N)} (hA : A.card = k + 1)
    (hB : B.card = k + 1) : (A ×ˢ B).Nonempty :=
  (Finset.card_pos.1 (by omega)).product (Finset.card_pos.1 (by omega))

/-- The first iteration of the procedure matches the key minimiser `p = (i, j)`: `σ(i) = j`. -/
theorem greedyMatching_succ_apply_fst (c : Fin N → ℂ × ℂ) {k : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = k + 1) (hB : B.card = k + 1) {p : Fin N × Fin N} (hp : p ∈ A ×ˢ B)
    (hmin : ∀ q ∈ A ×ˢ B, matchKey c p ≤ matchKey c q) :
    (greedyMatching c (k + 1) A B hA hB ⟨p.1, (Finset.mem_product.1 hp).1⟩ : Fin N) = p.2 := by
  rw [greedyMatching]
  simp only [Equiv.coe_fn_mk]
  split_ifs with h
  · exact congrArg Prod.snd (ofLex_min'_image_eq c _ hp hmin)
  · rw [ofLex_min'_image_eq c _ hp hmin] at h
    exact absurd rfl h

/-- After the first iteration (which matches the key minimiser `p`), the procedure is the greedy
matching of the remaining labels `A ∖ {p.1}`, `B ∖ {p.2}`. -/
theorem greedyMatching_succ_apply_of_ne (c : Fin N → ℂ × ℂ) {k : ℕ} {A B : Finset (Fin N)}
    (hA : A.card = k + 1) (hB : B.card = k + 1) {p : Fin N × Fin N} (hp : p ∈ A ×ˢ B)
    (hmin : ∀ q ∈ A ×ˢ B, matchKey c p ≤ matchKey c q) (hA' : (A.erase p.1).card = k)
    (hB' : (B.erase p.2).card = k) (a : A) (ha : (a : Fin N) ≠ p.1) :
    (greedyMatching c (k + 1) A B hA hB a : Fin N) =
      greedyMatching c k (A.erase p.1) (B.erase p.2) hA' hB'
        ⟨a, Finset.mem_erase.2 ⟨ha, a.2⟩⟩ := by
  rw [greedyMatching]
  simp only [Equiv.coe_fn_mk]
  split_ifs with h
  · rw [ofLex_min'_image_eq c _ hp hmin] at h
    exact absurd h ha
  · exact greedyMatching_congr c rfl (by rw [ofLex_min'_image_eq c _ hp hmin])
      (by rw [ofLex_min'_image_eq c _ hp hmin]) _ _ _ _ _ _

theorem card_erase_fst_of_mem {k : ℕ} {A B : Finset (Fin N)} (hA : A.card = k + 1)
    {p : Fin N × Fin N} (hp : p ∈ A ×ˢ B) : (A.erase p.1).card = k := by
  rw [Finset.card_erase_of_mem (Finset.mem_product.1 hp).1, hA, Nat.add_sub_cancel]

theorem card_erase_snd_of_mem {k : ℕ} {A B : Finset (Fin N)} (hB : B.card = k + 1)
    {p : Fin N × Fin N} (hp : p ∈ A ×ˢ B) : (B.erase p.2).card = k := by
  rw [Finset.card_erase_of_mem (Finset.mem_product.1 hp).2, hB, Nat.add_sub_cancel]

/-- **Stability.** The greedy matching `e : A ≃ B` has no blocking pair for the key order: there
are no `a, a' ∈ A` such that `x_a` prefers `y_{e(a')}` to its own partner `y_{e(a)}` while
`y_{e(a')}` prefers `x_a` to its own partner `x_{a'}`. -/
theorem greedyMatching_not_blocking (c : Fin N → ℂ × ℂ) (k : ℕ) :
    ∀ (A B : Finset (Fin N)) (hA : A.card = k) (hB : B.card = k) (a a' : A),
      ¬ (matchKey c (a, greedyMatching c k A B hA hB a') <
            matchKey c (a, greedyMatching c k A B hA hB a) ∧
          matchKey c (a, greedyMatching c k A B hA hB a') <
            matchKey c (a', greedyMatching c k A B hA hB a')) := by
  induction k with
  | zero =>
    intro A B hA hB a
    exact absurd a.2 (by simp [Finset.card_eq_zero.1 hA])
  | succ k ih =>
    intro A B hA hB a a' ⟨h1, h2⟩
    obtain ⟨p, hp, hmin⟩ := exists_isMin_matchKey c (nonempty_product_of_card_eq_succ hA hB)
    have hp1 := (Finset.mem_product.1 hp).1
    have hmem : ∀ x y : A, ((x : Fin N), (greedyMatching c (k + 1) A B hA hB y : Fin N)) ∈
        A ×ˢ B := fun x y => Finset.mem_product.2 ⟨x.2, (greedyMatching c (k + 1) A B hA hB y).2⟩
    have hfst : ∀ x : A, (x : Fin N) = p.1 →
        ((x : Fin N), (greedyMatching c (k + 1) A B hA hB x : Fin N)) = p := by
      intro x hx
      obtain ⟨x, hxA⟩ := x
      simp only at hx
      subst hx
      exact Prod.ext rfl (greedyMatching_succ_apply_fst c hA hB hp hmin)
    by_cases ha : (a : Fin N) = p.1
    · rw [hfst a ha] at h1
      exact absurd h1 (not_lt.2 (hmin _ (hmem a a')))
    by_cases ha' : (a' : Fin N) = p.1
    · rw [hfst a' ha'] at h2
      exact absurd h2 (not_lt.2 (hmin _ (hmem a a')))
    have hA' := card_erase_fst_of_mem hA hp
    have hB' := card_erase_snd_of_mem hB hp
    have e1 := greedyMatching_succ_apply_of_ne c hA hB hp hmin hA' hB' a ha
    have e2 := greedyMatching_succ_apply_of_ne c hA hB hp hmin hA' hB' a' ha'
    rw [e1, e2] at h1
    rw [e2] at h2
    exact ih _ _ hA' hB' ⟨a, _⟩ ⟨a', _⟩ ⟨h1, h2⟩

/-- **Uniqueness.** A bijection `f : A → B` without blocking pair for the key order is the greedy
matching. -/
theorem greedyMatching_eq_of_bijOn (c : Fin N → ℂ × ℂ) (f : Fin N → Fin N) (k : ℕ) :
    ∀ (A B : Finset (Fin N)) (hA : A.card = k) (hB : B.card = k),
      Set.BijOn f A B →
      (∀ a ∈ A, ∀ a' ∈ A, ¬ (matchKey c (a, f a') < matchKey c (a, f a) ∧
          matchKey c (a, f a') < matchKey c (a', f a'))) →
      ∀ a : A, (greedyMatching c k A B hA hB a : Fin N) = f a := by
  induction k with
  | zero =>
    intro A B hA hB _ _ a
    exact absurd a.2 (by simp [Finset.card_eq_zero.1 hA])
  | succ k ih =>
    intro A B hA hB hf hst a
    obtain ⟨p, hp, hmin⟩ := exists_isMin_matchKey c (nonempty_product_of_card_eq_succ hA hB)
    have hp1 := (Finset.mem_product.1 hp).1
    have hp2 := (Finset.mem_product.1 hp).2
    -- the key minimiser is a pair of `f`
    have hfp : f p.1 = p.2 := by
      obtain ⟨a', ha'A, ha'⟩ := hf.surjOn (Finset.mem_coe.2 hp2)
      by_contra hne
      have hne' : a' ≠ p.1 := fun h => hne (h ▸ ha')
      have hfA : ∀ x ∈ A, ∀ y ∈ A, (x, f y) ∈ A ×ˢ B := fun x hx y hy =>
        Finset.mem_product.2 ⟨hx, Finset.mem_coe.1 (hf.mapsTo (Finset.mem_coe.2 hy))⟩
      refine hst p.1 hp1 a' (Finset.mem_coe.1 ha'A) ⟨?_, ?_⟩
      · rw [ha']
        refine (hmin _ (hfA _ hp1 _ hp1)).lt_of_ne fun h => hne ?_
        exact (congrArg Prod.snd (matchKey_injective c h)).symm
      · rw [ha']
        have hmem' : ((a' : Fin N), p.2) ∈ A ×ˢ B :=
          Finset.mem_product.2 ⟨Finset.mem_coe.1 ha'A, hp2⟩
        refine (hmin _ hmem').lt_of_ne fun h => hne' ?_
        exact (congrArg Prod.fst (matchKey_injective c h)).symm
    by_cases ha : (a : Fin N) = p.1
    · obtain ⟨a, haA⟩ := a
      simp only at ha
      subst ha
      rw [greedyMatching_succ_apply_fst c hA hB hp hmin, hfp]
    have hA' := card_erase_fst_of_mem hA hp
    have hB' := card_erase_snd_of_mem hB hp
    rw [greedyMatching_succ_apply_of_ne c hA hB hp hmin hA' hB' a ha]
    refine ih _ _ hA' hB' ⟨?_, hf.injOn.mono ?_, ?_⟩ ?_ _
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_erase] at hx ⊢
      refine ⟨fun h => hx.1 (hf.injOn (Finset.mem_coe.2 hx.2) (Finset.mem_coe.2 hp1) ?_),
        Finset.mem_coe.1 (hf.mapsTo (Finset.mem_coe.2 hx.2))⟩
      rw [h, hfp]
    · intro x hx
      exact Finset.mem_coe.2 (Finset.mem_of_mem_erase (Finset.mem_coe.1 hx))
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_erase] at hy
      obtain ⟨x, hxA, rfl⟩ := hf.surjOn (Finset.mem_coe.2 hy.2)
      refine ⟨x, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun h => hy.1 ?_, hxA⟩), rfl⟩
      rw [h, hfp]
    · intro x hx y hy
      exact hst x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)

end Greedy

/-! ### The stable matching `σ_N` -/

section Stable

theorem stableMatching_apply (c : Fin N → ℂ × ℂ) (i : Fin N) :
    stableMatching c i = (greedyMatching c N Finset.univ Finset.univ (by simp) (by simp)
      ⟨i, Finset.mem_univ i⟩ : Fin N) :=
  rfl

/-- `σ` has no blocking pair for the key order `matchKey c` (lexicographic preferences): there
are no `i, j` such that `x_i` prefers `y_{σ(j)}` to `y_{σ(i)}` while `y_{σ(j)}` prefers `x_i` to
`x_j`. This is the stability of Remark 4.2 for the strict
preferences given by the keys `(|x_i - y_j|, i, j)`. -/
def IsLexStable (c : Fin N → ℂ × ℂ) (σ : Equiv.Perm (Fin N)) : Prop :=
  ∀ i j : Fin N, ¬ (matchKey c (i, σ j) < matchKey c (i, σ i) ∧
    matchKey c (i, σ j) < matchKey c (j, σ j))

theorem isLexStable_stableMatching (c : Fin N → ℂ × ℂ) : IsLexStable c (stableMatching c) :=
  fun i j => greedyMatching_not_blocking c N Finset.univ Finset.univ (by simp) (by simp)
    ⟨i, Finset.mem_univ i⟩ ⟨j, Finset.mem_univ j⟩

theorem IsLexStable.stableMatching_eq {c : Fin N → ℂ × ℂ} {σ : Equiv.Perm (Fin N)}
    (h : IsLexStable c σ) : stableMatching c = σ := by
  ext i
  rw [stableMatching_apply]
  refine congrArg Fin.val (greedyMatching_eq_of_bijOn c σ N Finset.univ Finset.univ (by simp)
    (by simp) ?_ (fun a _ a' _ => h a a') ⟨i, Finset.mem_univ i⟩)
  simpa only [Finset.coe_univ] using σ.bijective.bijOn_univ

/-- The stable matching is the unique permutation without blocking pair for the key order
(Remark 4.2, with the lexicographic tie rule). -/
theorem stableMatching_eq_iff (c : Fin N → ℂ × ℂ) (σ : Equiv.Perm (Fin N)) :
    stableMatching c = σ ↔ IsLexStable c σ :=
  ⟨fun h => h ▸ isLexStable_stableMatching c, IsLexStable.stableMatching_eq⟩

/-- The first matched pair: if `p = (i, j)` minimises the key `(|x_i - y_j|, i, j)` over all
pairs, then `σ_N(i) = j`. -/
theorem stableMatching_apply_of_isMin (c : Fin N → ℂ × ℂ) {p : Fin N × Fin N}
    (hmin : ∀ q, matchKey c p ≤ matchKey c q) : stableMatching c p.1 = p.2 := by
  by_contra hne
  set σ := stableMatching c
  have hj : σ.symm p.2 ≠ p.1 := fun h => hne (by rw [← h, Equiv.apply_symm_apply])
  refine isLexStable_stableMatching c p.1 (σ.symm p.2) ⟨?_, ?_⟩
  · rw [Equiv.apply_symm_apply]
    refine (hmin _).lt_of_ne fun h => hne ?_
    exact (congrArg Prod.snd (matchKey_injective c h)).symm
  · rw [Equiv.apply_symm_apply]
    refine (hmin _).lt_of_ne fun h => hj ?_
    exact (congrArg Prod.fst (matchKey_injective c h)).symm

/-- The first matched pair, distance form: if `|x_i - y_j|` is strictly smaller than every other
opposite-sign distance, then `σ_N(i) = j`. -/
theorem stableMatching_apply_of_forall_lt (c : Fin N → ℂ × ℂ) {p : Fin N × Fin N}
    (h : ∀ q, q ≠ p → ‖(c p.1).1 - (c p.2).2‖ < ‖(c q.1).1 - (c q.2).2‖) :
    stableMatching c p.1 = p.2 := by
  refine stableMatching_apply_of_isMin c fun q => ?_
  rcases eq_or_ne q p with rfl | hq
  · exact le_rfl
  · exact (matchKey_lt_of_norm_sub_lt (h q hq)).le

/-- The rest of the stable matching: once the key minimiser `p = (i, j)` is matched, `σ_N` is
the greedy matching of the remaining labels `[N] ∖ {i}` and `[N] ∖ {j}`. -/
theorem stableMatching_apply_of_ne {n : ℕ} (c : Fin (n + 1) → ℂ × ℂ) {p : Fin (n + 1) × Fin (n + 1)}
    (hmin : ∀ q, matchKey c p ≤ matchKey c q) (hA' : (Finset.univ.erase p.1).card = n)
    (hB' : (Finset.univ.erase p.2).card = n) (i : Fin (n + 1)) (hi : i ≠ p.1) :
    stableMatching c i = (greedyMatching c n (Finset.univ.erase p.1) (Finset.univ.erase p.2)
      hA' hB' ⟨i, Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩⟩ : Fin (n + 1)) := by
  rw [stableMatching_apply]
  exact greedyMatching_succ_apply_of_ne c _ _ (Finset.mem_univ p) (fun q _ => hmin q) hA' hB'
    ⟨i, Finset.mem_univ i⟩ hi

/-- **Stability for the distance preferences** (Remark 4.2): no `x_i` and
`y_{σ_N(j)}` both strictly prefer each other to their partners under `σ_N`. -/
theorem stableMatching_not_blocking (c : Fin N → ℂ × ℂ) (i j : Fin N) :
    ¬ (‖(c i).1 - (c (stableMatching c j)).2‖ < ‖(c i).1 - (c (stableMatching c i)).2‖ ∧
      ‖(c i).1 - (c (stableMatching c j)).2‖ < ‖(c j).1 - (c (stableMatching c j)).2‖) :=
  fun h => isLexStable_stableMatching c i j
    ⟨matchKey_lt_of_norm_sub_lt h.1, matchKey_lt_of_norm_sub_lt h.2⟩

/-- **Uniqueness of the stable matching** (Remark 4.2): when the distances
`|x_i - y_j|` are pairwise distinct (strict preferences), `σ_N` is the unique permutation without
blocking pair for the distance preferences. -/
theorem stableMatching_eq_iff_of_injective {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (σ : Equiv.Perm (Fin N)) :
    stableMatching c = σ ↔ ∀ i j : Fin N,
      ¬ (‖(c i).1 - (c (σ j)).2‖ < ‖(c i).1 - (c (σ i)).2‖ ∧
        ‖(c i).1 - (c (σ j)).2‖ < ‖(c j).1 - (c (σ j)).2‖) := by
  rw [stableMatching_eq_iff]
  simp only [IsLexStable, matchKey_lt_matchKey_iff_of_injective hc]

end Stable

end MultipoleBKT

end
