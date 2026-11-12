/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.Grouping
public import MultipoleBKT.UpperBound.BoundedUpper.ParityReduction

/-!
# The expansion of one term of `𝖪^{+,Z}` in odd and even parts

The paper: Definition 5.15,
Corollary 5.24 and the start of the proof of Lemma 5.35
( "The proof follows Lemma 4.54, starting from Corollary 5.24").

For a pair interaction `w` (odd in each dipole), the external sum `s` (odd) of the dipoles with the
frozen bad points (`f_{i∞} = e^{-β s_i} - 1`), a family of disjoint outer groups `X₁, …, Xₙ ⊆ X` and
a set `U` of labels carrying an external bond, the terms of Definition 5.15 summed over the edge
sets `Eₗ ∈ 𝖤^{Xₗ}` and `F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}` are expanded with
`f_ij 𝟙_{𝓑_ij^c} = a_ij 𝟙_{𝓑^c} + b_ij 𝟙_{𝓑^c}` and `f_{i∞} = -sinh(β s_i) + (cosh(β s_i) - 1)`:

* `evenSum Y E₁ = (∑_{E₂ : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^Y} ∏_{E₂} b 𝟙_{𝓑^c}) ∏_{ℰ^inter(Y)} 𝟙_{𝓑^c}`,
  `groupTerm Y E₁ = ∏_{E₁} a 𝟙_{𝓑^c} · evenSum Y E₁` (the summand of `𝒰(Y)` in Step 1 of the
  proof of Lemma 4.54), `treeF` the sum over `F` of `∏_F (-𝟙_𝓑)`;
* `expTerm U U₁ E₁s = ∏ₗ groupTerm Xₗ E₁ₗ · treeF · ∏_{U₁} (-sinh) ∏_{U ∖ U₁} (cosh - 1)`;
* `sum_clusterTerm_eq_sum_expTerm`: the identity
  `∑_{Eₗ} ∑_F clusterTerm · ∏_{i ∈ U} f_{i∞} = ∑_{U₁ ⊆ U} ∑_{E₁ₗ ⊆ ℰ^inter(Xₗ)} expTerm U U₁ E₁s`;
* `expTerm_flipOn`: the reversal of the dipoles of a block `S₀` multiplies `expTerm` by
  `(-1)^{∑ₗ deg_{E₁ₗ}(S₀) + |S₀ ∩ U₁|}` (Lemma 4.32 with marks, Corollary 5.24).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Finset Multipole Hierarchical SetPartition AbsoluteLower Parity

/-! ### Reindexing -/

section Reindex

open scoped Classical

/-- `∑_{E ∈ 𝒮} ∑_{E₁ ⊆ E} φ(E₁, E ∖ E₁)
= ∑_{E₁ ⊆ I} ∑_{E₂ ⊆ I : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝒮} φ(E₁, E₂)`
for `𝒮 ⊆ 𝒫(I)`. -/
theorem sum_sum_powerset_eq {I : Finset (ℕ × ℕ)} {𝒮 : Finset (Finset (ℕ × ℕ))}
    (h𝒮 : ∀ E ∈ 𝒮, E ⊆ I) (φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) → ℝ) :
    ∑ E ∈ 𝒮, ∑ E₁ ∈ E.powerset, φ E₁ (E \ E₁) =
      ∑ E₁ ∈ I.powerset, ∑ E₂ ∈ I.powerset.filter (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ 𝒮),
        φ E₁ E₂ := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun x _ => ⟨x.2, x.1 \ x.2⟩) (fun y _ => ⟨y.1 ∪ y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hE, hE₁⟩ := mem_sigma.1 hx
    rw [mem_powerset] at hE₁
    refine mem_sigma.2 ⟨mem_powerset.2 (hE₁.trans (h𝒮 _ hE)), mem_filter.2 ⟨mem_powerset.2
      (sdiff_subset.trans (h𝒮 _ hE)), disjoint_sdiff, ?_⟩⟩
    rw [union_sdiff_of_subset hE₁]
    exact hE
  · intro y hy
    obtain ⟨-, hy2⟩ := mem_sigma.1 hy
    obtain ⟨-, -, hy3⟩ := mem_filter.1 hy2
    exact mem_sigma.2 ⟨hy3, mem_powerset.2 subset_union_left⟩
  · intro x hx
    obtain ⟨-, hE₁⟩ := mem_sigma.1 hx
    simp only [union_sdiff_of_subset (mem_powerset.1 hE₁)]
  · intro y hy
    obtain ⟨-, hy2⟩ := mem_sigma.1 hy
    obtain ⟨-, hd, -⟩ := mem_filter.1 hy2
    simp only [union_sdiff_cancel_left hd]
  · intro x _
    rfl

end Reindex

/-! ### The objects of the expansion -/

section Defs

open scoped Classical

variable (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (s : ℂ × ℂ → ℝ)

/-- `(∑_{E₂ : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^Y} ∏_{E₂} b^w 𝟙_{𝓑^c}) ∏_{ℰ^inter(Y)} 𝟙_{𝓑^c}`. -/
noncomputable def evenSum (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∑ E₂ ∈ (interPairs Y).powerset.filter (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets Y),
      ∏ q ∈ E₂, evenBondUnlinked β w M lam (c q.1) (c q.2)) *
    ∏ q ∈ interPairs Y, (if MultipoleLinked M lam (c q.1) (c q.2) then (0 : ℝ) else 1)

/-- `∏_{E₁} a^w 𝟙_{𝓑^c} · evenSum Y E₁`. -/
noncomputable def groupTerm (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ q ∈ E₁, oddBondUnlinked β w M lam (c q.1) (c q.2)) * evenSum β w M lam Y E₁ c

/-- `∑_{F ∈ 𝖤_0^Y} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})`. -/
noncomputable def treeF (Y : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∑ F ∈ relEdgeSets₀ Y, ∏ q ∈ F, -(if MultipoleLinked M lam (c q.1) (c q.2) then (1 : ℝ) else 0)

/-- The expanded term
`∏ₗ groupTerm Xₗ E₁ₗ · treeF · ∏_{U₁} (-sinh(β s)) ∏_{U ∖ U₁} (cosh(β s) - 1)`. -/
noncomputable def expTerm (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (U U₁ : Finset ℕ) (E₁s : Fin n → Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ l, groupTerm β w M lam (Xs l) (E₁s l) c) * treeF M lam (coarsen X (univ.image Xs)) c *
    (∏ i ∈ U₁, -Real.sinh (β * s (c i))) * ∏ i ∈ U \ U₁, (Real.cosh (β * s (c i)) - 1)

end Defs

/-! ### The expansion identity -/

section Identity

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}

/-- **The expansion of one group** (Step 1 of Lemma 4.54): for a group `Y`,
`∑_{E ∈ 𝖤^Y} ∏_E f^w ∏_{ℰ^inter(Y)} 𝟙_{𝓑^c} = ∑_{E₁ ⊆ ℰ^inter(Y)} groupTerm Y E₁`. -/
theorem sum_relEdgeSets_eq_sum_groupTerm (Y : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    (∑ E ∈ relEdgeSets Y, ∏ q ∈ E, mayerBondOf β w (c q.1) (c q.2)) *
        ∏ q ∈ interPairs Y, (if MultipoleLinked M lam (c q.1) (c q.2) then (0 : ℝ) else 1) =
      ∑ E₁ ∈ (interPairs Y).powerset, groupTerm β w M lam Y E₁ c := by
  set I := interPairs Y
  set L : ℕ × ℕ → ℝ := fun q => if MultipoleLinked M lam (c q.1) (c q.2) then (0 : ℝ) else 1
  have hEI : ∀ E ∈ relEdgeSets Y, E ⊆ I := fun E hE => (mem_relEdgeSets.1 hE).1
  have hstep : ∀ E ∈ relEdgeSets Y, (∏ q ∈ E, mayerBondOf β w (c q.1) (c q.2)) * ∏ q ∈ I, L q =
      ∑ E₁ ∈ E.powerset, ((∏ q ∈ E₁, oddBondUnlinked β w M lam (c q.1) (c q.2)) *
        ∏ q ∈ E \ E₁, evenBondUnlinked β w M lam (c q.1) (c q.2)) * ∏ q ∈ I, L q := by
    intro E hE
    rw [prod_mul_prod_of_idem (hEI E hE) (fun q _ => unlinkedIndicator_mul_self _ _)]
    simp only [L, mayerBondOf_mul_unlinked]
    rw [prod_add, sum_mul]
  rw [sum_mul, sum_congr rfl hstep, sum_sum_powerset_eq hEI
    (fun E₁ E₂ => ((∏ q ∈ E₁, oddBondUnlinked β w M lam (c q.1) (c q.2)) *
      ∏ q ∈ E₂, evenBondUnlinked β w M lam (c q.1) (c q.2)) * ∏ q ∈ I, L q)]
  refine sum_congr rfl fun E₁ _ => ?_
  rw [groupTerm, evenSum, ← sum_mul, ← mul_sum]
  ring

/-- **The expansion identity** (Definition 5.15 with Corollary 5.24): for disjoint groups
`Xₗ ⊆ X` and a set `U` of external bonds,
`∑_{Eₗ ∈ 𝖤^{Xₗ}} ∑_{F} clusterTerm · ∏_{i ∈ U} (e^{-β s_i} - 1)
= ∑_{U₁ ⊆ U} ∑_{E₁ₗ ⊆ ℰ^inter(Xₗ)} expTerm U U₁ E₁s`. -/
theorem sum_clusterTerm_eq_sum_expTerm {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (U : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)),
          clusterTerm β w M lam Xs Es F c * ∏ i ∈ U, (Real.exp (-β * s (c i)) - 1) =
      ∑ U₁ ∈ U.powerset, ∑ E₁s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset),
        expTerm β w M lam s X Xs U U₁ E₁s c := by
  set L : ℕ × ℕ → ℝ := fun q => if MultipoleLinked M lam (c q.1) (c q.2) then (0 : ℝ) else 1
  set G := treeF M lam (coarsen X (univ.image Xs)) c with hG
  set Fac := ∏ i ∈ U, (Real.exp (-β * s (c i)) - 1) with hFac
  have hInter : ∏ q ∈ univ.biUnion fun l => interPairs (Xs l), L q =
      ∏ l, ∏ q ∈ interPairs (Xs l), L q :=
    prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX hXs hdisj fun _ => le_rfl)
  -- the clusterTerm summed over `F`
  have hF : ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∑ F ∈ relEdgeSets₀ (coarsen X (univ.image Xs)), clusterTerm β w M lam Xs Es F c * Fac =
        (∏ l, (∏ q ∈ Es l, mayerBondOf β w (c q.1) (c q.2)) * ∏ q ∈ interPairs (Xs l), L q) *
          G * Fac := by
    intro Es hEs
    have hE : ∏ q ∈ univ.biUnion Es, mayerBondOf β w (c q.1) (c q.2) =
        ∏ l, ∏ q ∈ Es l, mayerBondOf β w (c q.1) (c q.2) :=
      prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX hXs hdisj fun l =>
        (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1)
    simp only [clusterTerm]
    rw [← sum_mul, ← mul_sum, hE, hInter, hG, treeF, prod_mul_distrib]
  rw [sum_congr rfl hF, ← sum_mul, ← sum_mul]
  -- the sum over the `Eₗ` factorizes
  have hfac : ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∏ l, (∏ q ∈ Es l, mayerBondOf β w (c q.1) (c q.2)) * ∏ q ∈ interPairs (Xs l), L q =
      ∏ l, ∑ E₁ ∈ (interPairs (Xs l)).powerset, groupTerm β w M lam (Xs l) E₁ c := by
    have h : ∀ l, ∑ E₁ ∈ (interPairs (Xs l)).powerset, groupTerm β w M lam (Xs l) E₁ c =
        ∑ E ∈ relEdgeSets (Xs l),
          (∏ q ∈ E, mayerBondOf β w (c q.1) (c q.2)) * ∏ q ∈ interPairs (Xs l), L q := fun l => by
      rw [← sum_relEdgeSets_eq_sum_groupTerm (Xs l) c, sum_mul]
    rw [prod_congr rfl fun l _ => h l]
    exact (prod_univ_sum (fun l => relEdgeSets (Xs l)) fun l E =>
      (∏ q ∈ E, mayerBondOf β w (c q.1) (c q.2)) * ∏ q ∈ interPairs (Xs l), L q).symm
  rw [hfac, prod_univ_sum]
  -- the external factor
  have hext : Fac = ∑ U₁ ∈ U.powerset,
      (∏ i ∈ U₁, -Real.sinh (β * s (c i))) * ∏ i ∈ U \ U₁, (Real.cosh (β * s (c i)) - 1) := by
    have h : ∀ i, Real.exp (-β * s (c i)) - 1 =
        -Real.sinh (β * s (c i)) + (Real.cosh (β * s (c i)) - 1) := by
      intro i
      rw [neg_mul, Real.sinh_eq, Real.cosh_eq]
      ring
    rw [hFac]
    simp_rw [h]
    rw [prod_add]
  rw [hext, mul_sum]
  refine sum_congr rfl fun U₁ _ => ?_
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun E₁s _ => ?_
  rw [expTerm, hG]
  ring

end Identity

/-! ### The reversal of a block -/

section Flip

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}
  (hM : 1 ≤ M) (hw₁ : ∀ d e, w d.swap e = -w d e) (hw₂ : ∀ d e, w d e.swap = -w d e)
  (hs : ∀ d, s d.swap = -s d)
include hM hw₁ hw₂

omit hM hw₁ hw₂ in
theorem prod_linked_flipOn (S₀ : Finset ℕ) (c : ℕ → ℂ × ℂ) (E : Finset (ℕ × ℕ)) (a b : ℝ) :
    ∏ q ∈ E, (if MultipoleLinked M lam (flipOn Prod.swap S₀ c q.1) (flipOn Prod.swap S₀ c q.2)
      then a else b) =
      ∏ q ∈ E, (if MultipoleLinked M lam (c q.1) (c q.2) then a else b) :=
  prod_congr rfl fun q _ => if_congr (linkedIndicator_flipOn S₀ c q) rfl rfl

theorem evenSum_flipOn (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) (S₀ : Finset ℕ)
    (c : ℕ → ℂ × ℂ) :
    evenSum β w M lam Y E₁ (flipOn Prod.swap S₀ c) = evenSum β w M lam Y E₁ c := by
  unfold evenSum
  rw [prod_linked_flipOn]
  congr 1
  refine sum_congr rfl fun E₂ _ => ?_
  exact prod_flipOn_of_even' (evenBondUnlinked_swap_left hM hw₁)
    (evenBondUnlinked_swap_right hM hw₂) E₂ S₀ c

theorem groupTerm_flipOn (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) (S₀ : Finset ℕ)
    (c : ℕ → ℂ × ℂ) : groupTerm β w M lam Y E₁ (flipOn Prod.swap S₀ c) =
      (-1) ^ blockDeg E₁ S₀ * groupTerm β w M lam Y E₁ c := by
  unfold groupTerm
  rw [evenSum_flipOn hM hw₁ hw₂, prod_flipOn_of_odd' (oddBondUnlinked_swap_left hM hw₁)
    (oddBondUnlinked_swap_right hM hw₂) E₁ S₀ c]
  ring

omit hM hw₁ hw₂ in
theorem treeF_flipOn (Y : Finset (Finset ℕ)) (S₀ : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    treeF M lam Y (flipOn Prod.swap S₀ c) = treeF M lam Y c := by
  unfold treeF
  refine sum_congr rfl fun F _ => prod_congr rfl fun q _ => ?_
  rw [if_congr (linkedIndicator_flipOn S₀ c q) rfl rfl]

include hs in
/-- **The reversal of a block** (Lemma 4.32 with marks, Corollary 5.24): reversing the dipoles of
`S₀` multiplies `expTerm` by `(-1)^{∑ₗ deg_{E₁ₗ}(S₀) + |S₀ ∩ U₁|}`. -/
theorem expTerm_flipOn (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (U U₁ : Finset ℕ) (E₁s : Fin n → Finset (ℕ × ℕ)) (S₀ : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    expTerm β w M lam s X Xs U U₁ E₁s (flipOn Prod.swap S₀ c) =
      (-1) ^ (∑ l, blockDeg (E₁s l) S₀ + (S₀ ∩ U₁).card) *
        expTerm β w M lam s X Xs U U₁ E₁s c := by
  unfold expTerm
  have h1 : ∏ l, groupTerm β w M lam (Xs l) (E₁s l) (flipOn Prod.swap S₀ c) =
      (-1) ^ (∑ l, blockDeg (E₁s l) S₀) * ∏ l, groupTerm β w M lam (Xs l) (E₁s l) c := by
    rw [prod_congr rfl fun l _ => groupTerm_flipOn hM hw₁ hw₂ (Xs l) (E₁s l) S₀ c,
      prod_mul_distrib, prod_pow_eq_pow_sum]
  rw [h1, treeF_flipOn,
    BoundedUpper.prod_flipOn_vertex_odd (u := fun d => -Real.sinh (β * s d))
      (fun d => by simp only [hs, mul_neg, Real.sinh_neg, neg_neg]) U₁ S₀ c,
    BoundedUpper.prod_flipOn_vertex_even (v := fun d => Real.cosh (β * s d) - 1)
      (fun d => by simp only [hs, mul_neg, Real.cosh_neg]) (U \ U₁) S₀ c, pow_add]
  ring

end Flip

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
