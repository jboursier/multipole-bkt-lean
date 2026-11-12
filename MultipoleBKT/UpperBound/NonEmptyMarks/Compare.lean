/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.NonEmptyMarks.Parity

/-!
# The three marked comparisons before applying family bounds

The paper: (5.106).

With `E = ∪ E_l ∪ F`, the marked term is compared with a reduced term
and a factor carrying the gain. `abs_markedTerm_le_even` keeps one even
external factor. `abs_markedTerm_le_two` keeps two odd external factors
and removes their marks. `abs_markedTerm_le_odd` keeps all odd marks
in the reduced term.

These elementary comparisons are multiplied by full odd-component
separation in `PointwiseMarked`, before the paper family estimates.
The graph helpers identify `E ∈ 𝖤₀^X` and prove that `F` is disjoint
from the internal Mayer edges.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace NonEmptyMarks

open Hierarchical Multipole Parity BoundedUpper SetPartition

open scoped Classical

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-! ### The edge set `E = ∪ Eₗ ∪ F` -/

section EdgeSet

variable {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}

/-- Reachability transfers along a map of the adjacencies to reachabilities. -/
theorem reachable_of_adj_reachable {G G' : SimpleGraph ℕ} (h : ∀ u v, G.Adj u v → G'.Reachable u v)
    {a b : ℕ} (hab : G.Reachable a b) : G'.Reachable a b := by
  obtain ⟨w⟩ := hab
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

/-- The pairs of `𝖤^{Xₗ}` are pairs of a block of the coarsening, so `F` is disjoint from them. -/
theorem disjoint_biUnion_F {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) {F : Finset (ℕ × ℕ)}
    (hF : F ⊆ interPairs (coarsen X (univ.image Xs))) : Disjoint (univ.biUnion Es) F := by
  rw [Finset.disjoint_left]
  intro p hp hpF
  obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
  have hpp := mem_pairsOn.1 (interPairs_subset_pairsOn (hEs l hpl))
  have hC : (Xs l).biUnion id ∈ coarsen X (univ.image Xs) :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (mem_univ l)))
  have hintra : p ∈ intraPairs (coarsen X (univ.image Xs)) :=
    mem_intraPairs.2 ⟨_, hC, mem_pairsOn.2 hpp⟩
  exact Finset.disjoint_left.1 disjoint_interPairs_intraPairs (hF hpF) hintra

/-- **`E = ∪ Eₗ ∪ F ∈ 𝖤_0^X`** for the data of Definition 5.15. -/
theorem union_mem_relEdgeSets₀ (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l)) {F : Finset (ℕ × ℕ)}
    (hF : F ∈ relEdgeSets₀ (coarsen X (univ.image Xs))) :
    univ.biUnion Es ∪ F ∈ relEdgeSets₀ X := by
  have hGX : ∀ Y ∈ univ.image Xs, Y ⊆ X := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
    exact hXs l
  have hVC : (coarsen X (univ.image Xs)).biUnion id = X.biUnion id := biUnion_coarsen hGX
  obtain ⟨hFi, hFc⟩ := mem_relEdgeSets₀.1 hF
  have hEsi : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs l)).1
  refine mem_relEdgeSets₀.2 ⟨Finset.union_subset (Finset.biUnion_subset.2 fun l _ =>
    (hEsi l).trans (interPairs_subset_of_subset hX (hXs l))) ?_, ?_⟩
  · -- `F ⊆ ℰ^inter(X)`: a pair inside a block of `X` is inside a block of the coarsening
    intro p hp
    have hpI := hFi hp
    rw [mem_interPairs] at hpI ⊢
    refine ⟨hVC ▸ hpI.1, ?_⟩
    rintro ⟨B, hB, hpB⟩
    obtain ⟨C, hC, hBC⟩ := SmallIntegral.exists_coarsen_superset (univ.image Xs) hB
    exact hpI.2 ⟨C, hC, pairsOn_mono hBC hpB⟩
  · -- connectivity
    refine ⟨hVC ▸ hFc.1, fun i hi j hj => ?_⟩
    have hr := hFc.2 i (hVC ▸ hi) j (hVC ▸ hj)
    refine reachable_of_adj_reachable (fun u v huv => ?_) hr
    have key : ∀ p ∈ F ∪ intraPairs (coarsen X (univ.image Xs)),
        (edgeGraph (univ.biUnion Es ∪ F ∪ intraPairs X)).Reachable p.1 p.2 := by
      intro p hp
      have hlt := (mem_pairsOn.1 (Finset.union_subset (hFi.trans interPairs_subset_pairsOn)
        intraPairs_subset_pairsOn hp)).2.2
      rcases Finset.mem_union.1 hp with hpF | hpC
      · refine SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨hlt.ne, Or.inl ?_⟩)
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hpF)
      · obtain ⟨C, hC, hpC⟩ := mem_intraPairs.1 hpC
        rcases Finset.mem_union.1 hC with hC | hC
        · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hC
          obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
          have hconn := (mem_relEdgeSets.1 (hEs l)).2.2
          have hpp := mem_pairsOn.1 hpC
          have hr' := hconn.2 p.1 hpp.1 p.2 hpp.2.1
          refine (hr'.mono (edgeGraph_mono ?_))
          refine Finset.union_subset (fun q hq => ?_) (fun q hq => ?_)
          · exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_biUnion.2 ⟨l, mem_univ _, hq⟩))
          · obtain ⟨B, hB, hqB⟩ := mem_intraPairs.1 hq
            exact Finset.mem_union_right _ (mem_intraPairs.2 ⟨B, hXs l hB, hqB⟩)
        · refine SimpleGraph.Adj.reachable (edgeGraph_adj.2 ⟨hlt.ne, Or.inl ?_⟩)
          exact Finset.mem_union_right _ (mem_intraPairs.2 ⟨C, (Finset.mem_filter.1 hC).1, hpC⟩)
    rcases exists_mem_of_edgeGraph_adj huv with h | h
    · exact key _ h
    · exact (key _ h).symm

end EdgeSet

/-! ### The comparison with the reduced terms -/

section Compare

variable {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} {Es : Fin n → Finset (ℕ × ℕ)}
  {F : Finset (ℕ × ℕ)}

theorem one_le_cosh' (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have h := Real.add_one_le_exp x
  have h' := Real.add_one_le_exp (-x)
  linarith

theorem abs_evenBondUnlinked_le_evenBondMult (d e : ℂ × ℂ) :
    |evenBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| ≤
      |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| := by
  unfold evenBondMult
  by_cases h : MultipoleLinked M lam d e
  · rw [evenBondUnlinked_of_linked h, abs_zero]
    exact abs_nonneg _
  · rw [ite_eq_right h, sub_zero]

theorem linked_le_abs_evenBondMult (d e : ℂ × ℂ) :
    (if MultipoleLinked M lam d e then (1 : ℝ) else 0) ≤
      |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| := by
  unfold evenBondMult
  by_cases h : MultipoleLinked M lam d e
  · rw [evenBondUnlinked_of_linked h, ite_eq_left h, zero_sub, abs_neg, abs_one]
  · rw [ite_eq_right h]
    exact abs_nonneg _

/-- **The core comparison**: with `E = ∪ Eₗ ∪ F` (`F` disjoint from `∪ Eₗ`) and `E₁ ⊆ ∪ Eₗ`,
`|markedTerm U U₁ E₁| ≤ ∏_{E₁} |a| ∏_{E ∖ E₁} |b 𝟙_{𝓑^c} - 𝟙_𝓑| ∏_{U₁} |sinh| ∏_{U ∖ U₁} (cosh - 1)`. -/
theorem abs_markedTerm_le_core (hdisj : Disjoint (univ.biUnion Es) F) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ⊆ univ.biUnion Es) (U U₁ : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| ≤
      (∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
        (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
          |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
        (∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
        ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1) := by
  set w := interactionGoodZ χ p₀ β lam ε₀ V Z
  have hsplit : (univ.biUnion Es ∪ F) \ E₁ = (univ.biUnion Es \ E₁) ∪ F := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, fun h => Finset.disjoint_left.1 hdisj (hE₁ h) h1⟩
  have hdisj' : Disjoint (univ.biUnion Es \ E₁) F :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
  have hcosh : ∀ i ∈ U \ U₁, 0 ≤ Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1 :=
    fun i _ => by linarith [one_le_cosh' (β * extSumZ χ p₀ β lam ε₀ V Z (c i))]
  have hsep : |sepFactor M lam Xs F c| ≤
      ∏ p ∈ F, (if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0) := by
    unfold sepFactor
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    have h1 : ∏ p ∈ univ.biUnion fun l => interPairs (Xs l),
        |if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1| ≤ 1 :=
      Finset.prod_le_one₀ (fun p _ => abs_nonneg _) fun p _ => by split_ifs <;> simp
    have h2 : ∏ p ∈ F, |-(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)| =
        ∏ p ∈ F, (if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0) :=
      Finset.prod_congr rfl fun p _ => by split_ifs <;> simp
    rw [h2]
    calc (∏ p ∈ univ.biUnion fun l => interPairs (Xs l),
          |if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1|) *
          ∏ p ∈ F, (if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)
        ≤ 1 * ∏ p ∈ F, (if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0) :=
          mul_le_mul_of_nonneg_right h1 (Finset.prod_nonneg fun p _ => by split_ifs <;> norm_num)
      _ = _ := one_mul _
  have heven : (∏ p ∈ univ.biUnion Es \ E₁, |evenBondUnlinked β w M lam (c p.1) (c p.2)|) *
      ∏ p ∈ F, (if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0) ≤
      ∏ p ∈ (univ.biUnion Es ∪ F) \ E₁, |evenBondMult β w M lam (c p.1) (c p.2)| := by
    rw [hsplit, Finset.prod_union hdisj']
    exact mul_le_mul (Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) fun p _ =>
      abs_evenBondUnlinked_le_evenBondMult _ _) (Finset.prod_le_prod₀ (fun p _ => by
        split_ifs <;> norm_num) fun p _ => linked_le_abs_evenBondMult _ _)
      (Finset.prod_nonneg fun p _ => by split_ifs <;> norm_num)
      (Finset.prod_nonneg fun p _ => abs_nonneg _)
  unfold markedTerm
  rw [abs_mul, abs_mul, abs_mul, abs_mul, Finset.abs_prod, Finset.abs_prod, Finset.abs_prod,
    Finset.abs_prod, Finset.prod_congr rfl fun i hi => abs_of_nonneg (hcosh i hi)]
  have hsinh : ∏ i ∈ U₁, |-Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| =
      ∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
    Finset.prod_congr rfl fun i _ => abs_neg _
  rw [hsinh]
  have hO : 0 ≤ ∏ p ∈ E₁, |oddBondUnlinked β w M lam (c p.1) (c p.2)| :=
    Finset.prod_nonneg fun p _ => abs_nonneg _
  have hS : 0 ≤ ∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
    Finset.prod_nonneg fun i _ => abs_nonneg _
  have hC : 0 ≤ ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1) :=
    Finset.prod_nonneg hcosh
  have hEu : 0 ≤ ∏ p ∈ univ.biUnion Es \ E₁, |evenBondUnlinked β w M lam (c p.1) (c p.2)| :=
    Finset.prod_nonneg fun p _ => abs_nonneg _
  calc (∏ p ∈ E₁, |oddBondUnlinked β w M lam (c p.1) (c p.2)|) *
        (∏ p ∈ univ.biUnion Es \ E₁, |evenBondUnlinked β w M lam (c p.1) (c p.2)|) *
        |sepFactor M lam Xs F c| *
        (∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
        ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1)
      = (∏ p ∈ E₁, |oddBondUnlinked β w M lam (c p.1) (c p.2)|) *
          ((∏ p ∈ univ.biUnion Es \ E₁, |evenBondUnlinked β w M lam (c p.1) (c p.2)|) *
            |sepFactor M lam Xs F c|) *
          ((∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
            ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1)) := by ring
    _ ≤ (∏ p ∈ E₁, |oddBondUnlinked β w M lam (c p.1) (c p.2)|) *
          (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁, |evenBondMult β w M lam (c p.1) (c p.2)|) *
          ((∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
            ∏ i ∈ U \ U₁, (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) - 1)) := by
        gcongr
        exact (mul_le_mul_of_nonneg_left hsep hEu).trans heven
    _ = _ := by ring

theorem one_le_prod_cosh (s : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    1 ≤ ∏ i ∈ s, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) :=
  Finset.one_le_prod₀ fun _ _ => one_le_cosh' _

theorem prod_cosh_le_prod_cosh {s t : Finset ℕ} (h : s ⊆ t) (c : ℕ → ℂ × ℂ) :
    ∏ i ∈ s, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) ≤
      ∏ i ∈ t, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) :=
  Finset.prod_le_prod_of_subset_of_one_le₀ h (fun _ _ => (Real.cosh_pos _).le)
    fun _ _ _ => one_le_cosh' _

variable {X : Finset (Finset ℕ)}

/-- **An even mark** `i₁ ∈ U ∖ U₁` ("an external even bond supplies the same gain"):
`|markedTerm U U₁ E₁| ≤ (cosh(β S_{i₁}) - 1) |reducedTerm X E E₁ U₁|`, `E = ∪ Eₗ ∪ F`. -/
theorem abs_markedTerm_le_even (hdisj : Disjoint (univ.biUnion Es) F) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ⊆ univ.biUnion Es) {U U₁ : Finset ℕ} (hU : U ⊆ X.biUnion id) {i₁ : ℕ}
    (hi₁ : i₁ ∈ U \ U₁) (c : ℕ → ℂ × ℂ) :
    |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U₁ E₁ c| ≤
      (Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₁)) - 1) *
        |reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ U₁ c| := by
  set ch : ℕ → ℝ := fun i => Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) with hch
  have hcosh : ∀ i, 0 ≤ ch i - 1 := fun i => by
    linarith [one_le_cosh' (β * extSumZ χ p₀ β lam ε₀ V Z (c i))]
  refine (abs_markedTerm_le_core hdisj hE₁ U U₁ c).trans ?_
  rw [abs_reducedTerm_eq]
  have hprod : ∏ i ∈ U \ U₁, (ch i - 1) ≤ (ch i₁ - 1) * ∏ i ∈ X.biUnion id \ U₁, ch i := by
    rw [← Finset.mul_prod_erase _ _ hi₁]
    refine mul_le_mul_of_nonneg_left ?_ (hcosh i₁)
    calc ∏ i ∈ (U \ U₁).erase i₁, (ch i - 1) ≤ ∏ i ∈ (U \ U₁).erase i₁, ch i :=
          Finset.prod_le_prod₀ (fun i _ => hcosh i) fun i _ => by linarith
      _ ≤ ∏ i ∈ X.biUnion id \ U₁, ch i :=
          prod_cosh_le_prod_cosh ((Finset.erase_subset _ _).trans
            (Finset.sdiff_subset_sdiff hU le_rfl)) c
  have hA : 0 ≤ (∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (c p.1) (c p.2)|) * (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
        |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
      ∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p _ => abs_nonneg _)
      (Finset.prod_nonneg fun p _ => abs_nonneg _)) (Finset.prod_nonneg fun i _ => abs_nonneg _)
  calc _ ≤ ((∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
          (c p.1) (c p.2)|) * (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
            |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
          ∏ i ∈ U₁, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
          ((ch i₁ - 1) * ∏ i ∈ X.biUnion id \ U₁, ch i) := mul_le_mul_of_nonneg_left hprod hA
    _ = _ := by ring

/-- **Two odd marks** `i₁ ≠ i₂` (all marks odd): `|markedTerm U U E₁| ≤
|sinh(β S_{i₁})| |sinh(β S_{i₂})| |reducedTerm X E E₁ (U ∖ {i₁, i₂})|`. -/
theorem abs_markedTerm_le_two (hdisj : Disjoint (univ.biUnion Es) F) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ⊆ univ.biUnion Es) {U : Finset ℕ} {i₁ i₂ : ℕ} (hi₁ : i₁ ∈ U) (hi₂ : i₂ ∈ U)
    (h12 : i₁ ≠ i₂) (c : ℕ → ℂ × ℂ) :
    |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U E₁ c| ≤
      |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₁))| *
        |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i₂))| *
        |reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ ((U.erase i₁).erase i₂) c| := by
  set sh : ℕ → ℝ := fun i => |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| with hsh
  refine (abs_markedTerm_le_core hdisj hE₁ U U c).trans ?_
  rw [abs_reducedTerm_eq, Finset.sdiff_self, Finset.prod_empty, mul_one]
  have hU : ∏ i ∈ U, sh i = sh i₁ * sh i₂ * ∏ i ∈ (U.erase i₁).erase i₂, sh i := by
    rw [← Finset.mul_prod_erase U sh hi₁, ← Finset.mul_prod_erase (U.erase i₁) sh
      (Finset.mem_erase.2 ⟨Ne.symm h12, hi₂⟩)]
    ring
  rw [hU]
  have hC := one_le_prod_cosh (χ := χ) (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V)
    (Z := Z) (X.biUnion id \ (U.erase i₁).erase i₂) c
  have hA : 0 ≤ (∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (c p.1) (c p.2)|) * (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
        |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
      (sh i₁ * sh i₂ * ∏ i ∈ (U.erase i₁).erase i₂, sh i) :=
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p _ => abs_nonneg _)
      (Finset.prod_nonneg fun p _ => abs_nonneg _))
      (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.prod_nonneg fun i _ => abs_nonneg _))
  calc _ ≤ ((∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
          (c p.1) (c p.2)|) * (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
            |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
          (sh i₁ * sh i₂ * ∏ i ∈ (U.erase i₁).erase i₂, sh i)) *
          ∏ i ∈ X.biUnion id \ (U.erase i₁).erase i₂,
            Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) := le_mul_of_one_le_right hA hC
    _ = _ := by ring

/-- **All marks odd**: `|markedTerm U U E₁| ≤ |reducedTerm X E E₁ U|`. -/
theorem abs_markedTerm_le_odd (hdisj : Disjoint (univ.biUnion Es) F) {E₁ : Finset (ℕ × ℕ)}
    (hE₁ : E₁ ⊆ univ.biUnion Es) (U : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    |markedTerm χ p₀ β lam M ε₀ V Z Xs Es F U U E₁ c| ≤
      |reducedTerm χ p₀ β lam M ε₀ V Z X (univ.biUnion Es ∪ F) E₁ U c| := by
  refine (abs_markedTerm_le_core hdisj hE₁ U U c).trans ?_
  rw [abs_reducedTerm_eq, Finset.sdiff_self, Finset.prod_empty, mul_one]
  have hC := one_le_prod_cosh (χ := χ) (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V)
    (Z := Z) (X.biUnion id \ U) c
  have hA : 0 ≤ (∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
      (c p.1) (c p.2)|) * (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
        |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
      ∏ i ∈ U, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| :=
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p _ => abs_nonneg _)
      (Finset.prod_nonneg fun p _ => abs_nonneg _)) (Finset.prod_nonneg fun i _ => abs_nonneg _)
  calc _ ≤ ((∏ p ∈ E₁, |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam
          (c p.1) (c p.2)|) * (∏ p ∈ (univ.biUnion Es ∪ F) \ E₁,
            |evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)|) *
          ∏ i ∈ U, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))|) *
          ∏ i ∈ X.biUnion id \ U, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) :=
        le_mul_of_one_le_right hA hC
    _ = _ := by ring

end Compare

end NonEmptyMarks

end UpperBound

end MultipoleBKT

end
