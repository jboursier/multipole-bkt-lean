/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Matching.Greedy
public import MultipoleBKT.Frozen.IsStableDipolePair
public import MultipoleBKT.Frozen.MultipoleLinked

/-!
# The pair events `𝒜_ij`: Lemmas 4.3 and 4.5, Remark 4.6

For two dipoles `d = (x_i, y_i)` and
`e = (x_j, y_j)` with `i < j`, the event `𝒜_ij` is `IsStableDipolePair d e`: the stable matching
of `x_i, x_j` with `y_i, y_j` alone is the identity. Write
`r_i = |x_i - y_i|`.

* `isStableDipolePair_iff_not_blocking`, `isStableDipolePair_iff`, `isStableDipolePair_iff'`:
  exact characterizations of `IsStableDipolePair d e` by the four opposite-sign distances, with
  the lexicographic tie rule (no hypothesis).
* `isStableDipolePair_iff_of_le`, `isStableDipolePair_swap_iff_of_lt`: the tie-free cores of
  Lemma 4.5.
* `lemma_4_5`, `lemma_4_5_swap`: Lemma 4.5 (proof omitted in the paper), for the
  dipole of smaller radius carrying the lower, resp. the higher, label.
* `isStableDipolePair_comm_of_nodup`: `𝒜_ij` does not depend on the order of the labels when the
  four distances are distinct.
* `stableMatching_eq_refl_iff`: `σ_N = Id ⟺ ∀ i < j, 𝒜_ij`, for every configuration (the
  lexicographic tie rule makes the distinctness hypothesis unnecessary).
* `lemma_4_3`, `lemma_4_3'`: Lemma 4.3 as stated in the paper,
  with the distinctness hypothesis, for `i < j` and for `i ≠ j`.
* `isStableDipolePair_of_lt`, `remark_4_6`: if the smaller matched distance is below both cross
  distances, the pair is stable; hence `𝓑_ij^c ⊆ 𝒜_ij` (Remark 4.6).
-/

@[expose] public section

namespace MultipoleBKT

variable {N : ℕ}

/-! ### Relabelling -/

section Relabel

/-- The key order is invariant under an order-preserving relabelling of the dipoles. -/
theorem matchKey_comp_lt_iff {M : ℕ} (c : Fin N → ℂ × ℂ) {ι : Fin M → Fin N}
    (hι : StrictMono ι) (p q : Fin M × Fin M) :
    matchKey (c ∘ ι) p < matchKey (c ∘ ι) q ↔
      matchKey c (ι p.1, ι p.2) < matchKey c (ι q.1, ι q.2) := by
  simp only [matchKey_lt_matchKey_iff, Function.comp_apply, Prod.Lex.toLex_lt_toLex,
    hι.lt_iff_lt, hι.injective.eq_iff]

theorem isLexStable_refl_iff (c : Fin N → ℂ × ℂ) :
    IsLexStable c (Equiv.refl _) ↔ ∀ i j : Fin N,
      ¬ (matchKey c (i, j) < matchKey c (i, i) ∧ matchKey c (i, j) < matchKey c (j, j)) :=
  Iff.rfl

theorem isStableDipolePair_iff_isLexStable (d e : ℂ × ℂ) :
    IsStableDipolePair d e ↔ IsLexStable ![d, e] (Equiv.refl _) :=
  stableMatching_eq_iff _ _

/-- `𝒜_ij` in terms of the keys of the full configuration: neither `(i, j)` nor `(j, i)` blocks
the identity. -/
theorem isStableDipolePair_apply_iff (c : Fin N → ℂ × ℂ) {i j : Fin N} (hij : i < j) :
    IsStableDipolePair (c i) (c j) ↔
      ¬ (matchKey c (i, j) < matchKey c (i, i) ∧ matchKey c (i, j) < matchKey c (j, j)) ∧
      ¬ (matchKey c (j, i) < matchKey c (j, j) ∧ matchKey c (j, i) < matchKey c (i, i)) := by
  have hι : StrictMono ![i, j] := Fin.strictMono_iff_lt_succ.2 fun a => by
    fin_cases a
    simpa using hij
  have hc : ![c i, c j] = c ∘ ![i, j] := by
    funext a
    fin_cases a <;> rfl
  rw [isStableDipolePair_iff_isLexStable, hc, isLexStable_refl_iff]
  simp only [matchKey_comp_lt_iff c hι, Fin.forall_fin_two, lt_irrefl, and_false,
    not_false_eq_true, true_and, and_true]
  simp

end Relabel

/-! ### Lemma 4.3 -/

section Lemma43

/-- `σ_N = Id` if and only if `𝒜_ij` holds for every `i < j`, for every configuration (with the
lexicographic tie rule, no distinctness is needed). -/
theorem stableMatching_eq_refl_iff (c : Fin N → ℂ × ℂ) :
    stableMatching c = Equiv.refl _ ↔ ∀ i j : Fin N, i < j → IsStableDipolePair (c i) (c j) := by
  rw [stableMatching_eq_iff, isLexStable_refl_iff]
  constructor
  · intro h i j hij
    exact (isStableDipolePair_apply_iff c hij).2 ⟨h i j, h j i⟩
  · intro h i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact ((isStableDipolePair_apply_iff c hij).1 (h i j hij)).1
    · exact fun h' => lt_irrefl _ h'.1
    · exact ((isStableDipolePair_apply_iff c hji).1 (h j i hji)).2

/-- **Lemma 4.3**: if the distances `|x_i - y_j|`,
`1 ≤ i, j ≤ N`, are all distinct, then `σ_N = Id` if and only if `𝒜_ij` holds for every pair of
labels (taken with the lower label first). The hypothesis is not needed in Lean (see
`stableMatching_eq_refl_iff`); it is kept to state the paper's lemma. -/
theorem lemma_4_3 {c : Fin N → ℂ × ℂ}
    (_hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) :
    stableMatching c = Equiv.refl _ ↔ ∀ i j : Fin N, i < j → IsStableDipolePair (c i) (c j) :=
  stableMatching_eq_refl_iff c

end Lemma43

/-! ### Two dipoles -/

section TwoDipoles

/-- The four opposite-sign distances of two dipoles `i ≠ j` of a configuration whose distances
`|x_k - y_l|` are all distinct are distinct (the hypothesis of Lemma 4.5). -/
theorem nodup_norm_sub_of_injective {ι : Type*} {c : ι → ℂ × ℂ}
    (hc : Function.Injective fun p : ι × ι => ‖(c p.1).1 - (c p.2).2‖) {i j : ι} (hij : i ≠ j) :
    [‖(c i).1 - (c i).2‖, ‖(c i).1 - (c j).2‖, ‖(c j).1 - (c i).2‖,
      ‖(c j).1 - (c j).2‖].Nodup := by
  have h : ∀ p q : ι × ι, p ≠ q →
      ‖(c p.1).1 - (c p.2).2‖ ≠ ‖(c q.1).1 - (c q.2).2‖ := fun p q hpq h => hpq (hc h)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  refine ⟨⟨h (i, i) (i, j) ?_, h (i, i) (j, i) ?_, h (i, i) (j, j) ?_⟩,
    ⟨h (i, j) (j, i) ?_, h (i, j) (j, j) ?_⟩, h (j, i) (j, j) ?_⟩ <;>
    simp [Prod.ext_iff, hij, hij.symm]

/-- `𝒜_ij` without blocking pair: `𝒜_ij` fails exactly when `x_i` and `y_j` prefer each other to
their own partners, or `x_j` and `y_i` do, with the lexicographic tie rule (a tie is won by the
pair with the lexicographically smaller labels). -/
theorem isStableDipolePair_iff_not_blocking (d e : ℂ × ℂ) :
    IsStableDipolePair d e ↔
      ¬ (‖d.1 - e.2‖ < ‖d.1 - d.2‖ ∧ ‖d.1 - e.2‖ ≤ ‖e.1 - e.2‖) ∧
      ¬ (‖e.1 - d.2‖ ≤ ‖e.1 - e.2‖ ∧ ‖e.1 - d.2‖ < ‖d.1 - d.2‖) := by
  have h1 : matchKey ![d, e] (0, 1) < matchKey ![d, e] (0, 0) ↔ ‖d.1 - e.2‖ < ‖d.1 - d.2‖ := by
    rw [matchKey_lt_matchKey_iff]
    simp [Prod.Lex.toLex_lt_toLex]
  have h2 : matchKey ![d, e] (0, 1) < matchKey ![d, e] (1, 1) ↔ ‖d.1 - e.2‖ ≤ ‖e.1 - e.2‖ := by
    rw [matchKey_lt_matchKey_iff, le_iff_lt_or_eq]
    simp [Prod.Lex.toLex_lt_toLex]
  have h3 : matchKey ![d, e] (1, 0) < matchKey ![d, e] (1, 1) ↔ ‖e.1 - d.2‖ ≤ ‖e.1 - e.2‖ := by
    rw [matchKey_lt_matchKey_iff, le_iff_lt_or_eq]
    simp [Prod.Lex.toLex_lt_toLex]
  have h4 : matchKey ![d, e] (1, 0) < matchKey ![d, e] (0, 0) ↔ ‖e.1 - d.2‖ < ‖d.1 - d.2‖ := by
    rw [matchKey_lt_matchKey_iff]
    simp [Prod.Lex.toLex_lt_toLex]
  rw [isStableDipolePair_iff_isLexStable, isLexStable_refl_iff]
  simp only [Fin.forall_fin_two, lt_irrefl, and_false, not_false_eq_true, true_and, and_true,
    h1, h2, h3, h4]

/-- An elementary equivalence behind `isStableDipolePair_iff`. -/
theorem not_blocking_iff_aux (r₀ a₀₁ a₁₀ r₁ : ℝ) :
    (¬ (a₀₁ < r₀ ∧ a₀₁ ≤ r₁) ∧ ¬ (a₁₀ ≤ r₁ ∧ a₁₀ < r₀)) ↔
      (r₀ ≤ a₀₁ ∧ r₀ ≤ a₁₀ ∧ r₀ ≤ r₁) ∨ (r₁ < r₀ ∧ r₁ < a₀₁ ∧ r₁ < a₁₀) := by
  constructor
  · rintro ⟨h01, h10⟩
    rcases le_or_gt r₀ r₁ with h | h
    · refine Or.inl ⟨?_, ?_, h⟩
      · exact not_lt.1 fun h' => h01 ⟨h', h'.le.trans h⟩
      · exact not_lt.1 fun h' => h10 ⟨h'.le.trans h, h'⟩
    · refine Or.inr ⟨h, ?_, ?_⟩
      · exact not_le.1 fun h' => h01 ⟨h'.trans_lt h, h'⟩
      · exact not_le.1 fun h' => h10 ⟨h', h'.trans_lt h⟩
  · rintro (⟨h01, h10, -⟩ | ⟨-, h01, h10⟩)
    · exact ⟨fun h => (not_lt.2 h01) h.1, fun h => (not_lt.2 h10) h.2⟩
    · exact ⟨fun h => (not_le.2 h01) h.2, fun h => (not_le.2 h10) h.1⟩

/-- **Exact characterization of `𝒜_ij`** (Definition 4.4): the first
contact (the pair of smallest key `(|x_a - y_b|, a, b)`) is `(i, i)`, which wins every tie, or it
is `(j, j)`, which loses every tie. -/
theorem isStableDipolePair_iff (d e : ℂ × ℂ) :
    IsStableDipolePair d e ↔
      (‖d.1 - d.2‖ ≤ ‖d.1 - e.2‖ ∧ ‖d.1 - d.2‖ ≤ ‖e.1 - d.2‖ ∧ ‖d.1 - d.2‖ ≤ ‖e.1 - e.2‖) ∨
      (‖e.1 - e.2‖ < ‖d.1 - d.2‖ ∧ ‖e.1 - e.2‖ < ‖d.1 - e.2‖ ∧ ‖e.1 - e.2‖ < ‖e.1 - d.2‖) := by
  rw [isStableDipolePair_iff_not_blocking, not_blocking_iff_aux]

/-- A shorter form of `isStableDipolePair_iff`: both cross distances are at least `r_i`, or both
exceed `r_j`. -/
theorem isStableDipolePair_iff' (d e : ℂ × ℂ) :
    IsStableDipolePair d e ↔
      (‖d.1 - d.2‖ ≤ ‖d.1 - e.2‖ ∧ ‖d.1 - d.2‖ ≤ ‖e.1 - d.2‖) ∨
      (‖e.1 - e.2‖ < ‖d.1 - e.2‖ ∧ ‖e.1 - e.2‖ < ‖e.1 - d.2‖) := by
  rw [isStableDipolePair_iff]
  constructor
  · rintro (⟨h1, h2, -⟩ | ⟨-, h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rcases le_or_gt ‖d.1 - d.2‖ ‖e.1 - e.2‖ with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h, h.trans_le h1, h.trans_le h2⟩
    · rcases le_or_gt ‖d.1 - d.2‖ ‖e.1 - e.2‖ with h | h
      · exact Or.inl ⟨h.trans h1.le, h.trans h2.le, h⟩
      · exact Or.inr ⟨h, h1, h2⟩

/-- If the smaller matched distance `min(r_i, r_j)` is below both cross distances, then `𝒜_ij`
holds ("the shortest opposite-sign distance is a matched-pair distance", Remark 4.6). -/
theorem isStableDipolePair_of_lt {d e : ℂ × ℂ}
    (h₁ : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ < ‖d.1 - e.2‖)
    (h₂ : min ‖d.1 - d.2‖ ‖e.1 - e.2‖ < ‖e.1 - d.2‖) : IsStableDipolePair d e := by
  rw [isStableDipolePair_iff']
  rcases le_total ‖d.1 - d.2‖ ‖e.1 - e.2‖ with h | h
  · rw [min_eq_left h] at h₁ h₂
    exact Or.inl ⟨h₁.le, h₂.le⟩
  · rw [min_eq_right h] at h₁ h₂
    exact Or.inr ⟨h₁, h₂⟩

/-- The core of Lemma 4.5 when the dipole of smaller radius carries the lower label: no
distinctness is needed. -/
theorem isStableDipolePair_iff_of_le {d e : ℂ × ℂ} (hr : ‖d.1 - d.2‖ ≤ ‖e.1 - e.2‖) :
    IsStableDipolePair d e ↔ ‖d.1 - d.2‖ ≤ ‖d.1 - e.2‖ ∧ ‖d.1 - d.2‖ ≤ ‖e.1 - d.2‖ := by
  rw [isStableDipolePair_iff']
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · exact h
    · exact ⟨hr.trans h1.le, hr.trans h2.le⟩
  · exact Or.inl

/-- The core of Lemma 4.5 when the dipole `d` of strictly smaller radius carries the higher
label. -/
theorem isStableDipolePair_swap_iff_of_lt {d e : ℂ × ℂ} (hr : ‖d.1 - d.2‖ < ‖e.1 - e.2‖) :
    IsStableDipolePair e d ↔ ‖d.1 - d.2‖ < ‖e.1 - d.2‖ ∧ ‖d.1 - d.2‖ < ‖d.1 - e.2‖ := by
  rw [isStableDipolePair_iff']
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · exact ⟨hr.trans_le h1, hr.trans_le h2⟩
    · exact h
  · exact Or.inr

/-- **Lemma 4.5** (the proof is omitted in the paper), for
dipoles `d = (x_i, y_i)`, `e = (x_j, y_j)` with `i < j`: if `r_i ≤ r_j` and the four
opposite-sign distances are distinct, then `𝒜_ij` holds if and only if `|y_j - x_i| ≥ r_i` and
`|y_i - x_j| ≥ r_i`. (For `i > j`, see `lemma_4_5_swap`.) -/
theorem lemma_4_5 {d e : ℂ × ℂ} (hr : ‖d.1 - d.2‖ ≤ ‖e.1 - e.2‖)
    (_hdist : [‖d.1 - d.2‖, ‖d.1 - e.2‖, ‖e.1 - d.2‖, ‖e.1 - e.2‖].Nodup) :
    IsStableDipolePair d e ↔ ‖e.2 - d.1‖ ≥ ‖d.1 - d.2‖ ∧ ‖d.2 - e.1‖ ≥ ‖d.1 - d.2‖ := by
  rw [isStableDipolePair_iff_of_le hr, norm_sub_rev e.2, norm_sub_rev d.2]

/-- **Lemma 4.5** for dipoles `d = (x_i, y_i)`,
`e = (x_j, y_j)` with `i > j`, so that `𝒜_ij` is `IsStableDipolePair e d` (lower label first): if `r_i ≤ r_j` and the four opposite-sign distances are distinct, then `𝒜_ij` holds
if and only if `|y_j - x_i| ≥ r_i` and `|y_i - x_j| ≥ r_i`. -/
theorem lemma_4_5_swap {d e : ℂ × ℂ} (hr : ‖d.1 - d.2‖ ≤ ‖e.1 - e.2‖)
    (hdist : [‖d.1 - d.2‖, ‖d.1 - e.2‖, ‖e.1 - d.2‖, ‖e.1 - e.2‖].Nodup) :
    IsStableDipolePair e d ↔ ‖e.2 - d.1‖ ≥ ‖d.1 - d.2‖ ∧ ‖d.2 - e.1‖ ≥ ‖d.1 - d.2‖ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hdist
  obtain ⟨⟨h01, h10, hrr⟩, -⟩ := hdist
  rw [isStableDipolePair_swap_iff_of_lt (hr.lt_of_ne hrr), norm_sub_rev e.2, norm_sub_rev d.2]
  exact ⟨fun h => ⟨h.2.le, h.1.le⟩, fun h => ⟨h.2.lt_of_ne h10, h.1.lt_of_ne h01⟩⟩

/-- When the four opposite-sign distances are distinct, `IsStableDipolePair` does not depend on
the order of the two dipoles. -/
theorem isStableDipolePair_comm_of_nodup {d e : ℂ × ℂ}
    (hdist : [‖d.1 - d.2‖, ‖d.1 - e.2‖, ‖e.1 - d.2‖, ‖e.1 - e.2‖].Nodup) :
    IsStableDipolePair d e ↔ IsStableDipolePair e d := by
  rcases le_total ‖d.1 - d.2‖ ‖e.1 - e.2‖ with h | h
  · rw [lemma_4_5 h hdist, lemma_4_5_swap h hdist]
  · have hdist' : [‖e.1 - e.2‖, ‖e.1 - d.2‖, ‖d.1 - e.2‖, ‖d.1 - d.2‖].Nodup := by
      simpa using List.nodup_reverse.2 hdist
    rw [lemma_4_5 h hdist', lemma_4_5_swap h hdist']

/-- **Lemma 4.3** with the paper's quantifier
"for every `1 ≤ i ≠ j ≤ N`": if the distances `|x_i - y_j|` are all distinct, then `σ_N = Id` if
and only if `σ₂[(x_i, x_j), (y_i, y_j)] = Id` for all `i ≠ j` (in either order of the two
dipoles). -/
theorem lemma_4_3' {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) :
    stableMatching c = Equiv.refl _ ↔ ∀ i j : Fin N, i ≠ j → IsStableDipolePair (c i) (c j) := by
  rw [stableMatching_eq_refl_iff]
  refine ⟨fun h i j hij => ?_, fun h i j hij => h i j hij.ne⟩
  rcases hij.lt_or_gt with hij | hji
  · exact h i j hij
  · exact (isStableDipolePair_comm_of_nodup (nodup_norm_sub_of_injective hc hji.ne)).1 (h j i hji)

/-- **Remark 4.6**: `𝓑_ij^c ⊆ 𝒜_ij`. If two
dipoles are not linked by the multipole relation with a constant `M ≥ 1` (the paper has
`M > 20`), then they form a stable pair. -/
theorem remark_4_6 {M lam : ℝ} (hM : 1 ≤ M) {d e : ℂ × ℂ} (h : ¬ MultipoleLinked M lam d e) :
    IsStableDipolePair d e := by
  rw [MultipoleLinked, not_le] at h
  set m := min ‖d.1 - d.2‖ ‖e.1 - e.2‖
  have hm0 : 0 ≤ m := le_min (norm_nonneg _) (norm_nonneg _)
  have hX : m ≤ min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) :=
    min_le_min (le_max_left _ _) (le_max_left _ _)
  have hMX : m < min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) := by
    refine lt_of_le_of_lt ?_ h
    calc m ≤ min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) := hX
      _ ≤ M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) :=
        le_mul_of_one_le_left (hm0.trans hX) hM
  refine isStableDipolePair_of_lt ?_ ?_
  · exact hMX.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  · rw [norm_sub_rev e.1 d.2]
    exact hMX.trans_le ((min_le_right _ _).trans (min_le_left _ _))

end TwoDipoles

end MultipoleBKT

end
