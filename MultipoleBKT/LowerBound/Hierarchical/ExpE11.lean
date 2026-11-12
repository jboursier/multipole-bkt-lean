/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Hierarchical.Euler

/-!
# Corollary 4.34: the reduction (4.61) of `𝖪^-_{ε₀}` to Eulerian graphs

Corollary 4.34 (eq. (4.61),
Corollary 4.34). For a model `(ρ, w, ψ)` with `ρ` reversal-invariant, `w` odd and bounded and `ψ`
reversal-invariant, and `M ≥ 1` (so that `𝓑_ij^c ⊂ 𝒜_ij`, Remark 4.6), every term of the
activity series of Definition 4.15 is expanded with `f^w_ij = a^w_ij + b^w_ij` (Definition 4.28)
over the edges of `E = E₁ ∪ ⋯ ∪ Eₙ`, and the terms in which the edges carrying `a` are not
Eulerian relative to `X` vanish (`integral_prod_add_mul_eq_sum_relEulerian`):

* `ModelHyp.integral_clusterTerm_eq_sum_relEulerian`: for one term,
  `𝔼_{𝖯_X}[∏_{E} f ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)]
  = ∑_{E₁ ⊆ E, E₁ ∈ Eul^X} 𝔼_{𝖯_X}[∏_{E₁} a ∏_{E ∖ E₁} b ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)]`.

The factors `𝟙_{𝓑_ij^c}`, `ij ∈ ℰ^inter(Xₗ) ⊇ Eₗ`, make the bonds odd/even in each dipole
(`MultipoleBKT.Parity.oddBondUnlinked_swap_left`, …); they are idempotent, so they can be moved
on and off the bonds (`prod_mul_prod_of_idem`).
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace Hierarchical

open Multipole SetPartition Parity

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

/-! ### Idempotent factors -/

/-- For `E ⊆ I` and an idempotent weight `L` on `I`, `(∏_E u)(∏_I L) = (∏_E u L)(∏_I L)`. -/
theorem prod_mul_prod_of_idem {E I : Finset (ℕ × ℕ)} (hEI : E ⊆ I) {L : ℕ × ℕ → ℝ}
    (hL : ∀ p ∈ I, L p * L p = L p) (u : ℕ × ℕ → ℝ) :
    (∏ p ∈ E, u p) * ∏ p ∈ I, L p = (∏ p ∈ E, (u p * L p)) * ∏ p ∈ I, L p := by
  have hsq : (∏ p ∈ E, L p) * (∏ p ∈ E, L p) = ∏ p ∈ E, L p := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp => hL p (hEI hp)
  rw [Finset.prod_mul_distrib, ← Finset.prod_sdiff hEI]
  calc (∏ p ∈ E, u p) * ((∏ p ∈ I \ E, L p) * ∏ p ∈ E, L p)
      = (∏ p ∈ E, u p) * (∏ p ∈ I \ E, L p) * ((∏ p ∈ E, L p) * ∏ p ∈ E, L p) := by
        rw [hsq]; ring
    _ = (∏ p ∈ E, u p) * (∏ p ∈ E, L p) * ((∏ p ∈ I \ E, L p) * ∏ p ∈ E, L p) := by ring

open scoped Classical in
/-- `𝟙_{𝓑^c}` is idempotent. -/
theorem unlinkedIndicator_mul_self (d e : ℂ × ℂ) :
    (if MultipoleLinked M lam d e then (0 : ℝ) else 1) *
      (if MultipoleLinked M lam d e then 0 else 1) =
      if MultipoleLinked M lam d e then 0 else 1 := by
  split_ifs <;> norm_num

open scoped Classical in
theorem mayerBondOf_mul_unlinked (d e : ℂ × ℂ) :
    mayerBondOf β w d e * (if MultipoleLinked M lam d e then 0 else 1) =
      oddBondUnlinked β w M lam d e + evenBondUnlinked β w M lam d e := by
  rw [← mayerBondOf_unlinked_eq_add]
  split_ifs <;> ring

open scoped Classical in
theorem oddBond_mul_unlinked (d e : ℂ × ℂ) :
    oddBond β w d e * (if MultipoleLinked M lam d e then 0 else 1) =
      oddBondUnlinked β w M lam d e := by
  unfold oddBondUnlinked
  split_ifs <;> ring

open scoped Classical in
theorem evenBond_mul_unlinked (d e : ℂ × ℂ) :
    evenBond β w d e * (if MultipoleLinked M lam d e then 0 else 1) =
      evenBondUnlinked β w M lam d e := by
  unfold evenBondUnlinked
  split_ifs <;> ring

/-! ### Measurability, bounds and locality -/

section Bounds

open scoped Classical

theorem measurable_oddBondUnlinked (hw : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (β M lam : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => oddBondUnlinked β w M lam q.1 q.2 := by
  unfold oddBondUnlinked oddBond
  exact Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const
    (Measurable.ite measurableSet_isStableDipolePair
      ((Real.continuous_sinh.measurable.comp (measurable_const.mul hw)).neg) measurable_const)

theorem measurable_evenBondUnlinked (hw : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => w q.1 q.2)
    (β M lam : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => evenBondUnlinked β w M lam q.1 q.2 := by
  unfold evenBondUnlinked evenBond
  exact Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const
    (Measurable.ite measurableSet_isStableDipolePair
      ((Real.continuous_cosh.measurable.comp (measurable_const.mul hw)).sub_const 1)
      measurable_const)

theorem abs_le_exp_abs (t : ℝ) : |t| ≤ Real.exp |t| := by
  linarith [Real.add_one_le_exp |t|]

theorem exists_abs_oddBondUnlinked_le (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (β M lam : ℝ) :
    ∃ C, ∀ d ∈ K, ∀ e ∈ K, |oddBondUnlinked β w M lam d e| ≤ C := by
  obtain ⟨C, hC⟩ := hwb
  refine ⟨Real.exp (2 * (|β| * C)), fun d hd e he => ?_⟩
  have hb : |β * w d e| ≤ |β| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC d hd e he) (abs_nonneg β)
  unfold oddBondUnlinked oddBond
  split_ifs
  · simp [(Real.exp_pos _).le]
  · rw [abs_neg]
    calc |Real.sinh (β * w d e)| ≤ |β * w d e| * Real.exp |β * w d e| := abs_sinh_le _
      _ ≤ Real.exp |β * w d e| * Real.exp |β * w d e| := by
          gcongr
          exact abs_le_exp_abs _
      _ = Real.exp (2 * |β * w d e|) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (2 * (|β| * C)) := Real.exp_le_exp.2 (by linarith)
  · simp [(Real.exp_pos _).le]

theorem exists_abs_evenBondUnlinked_le (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (β M lam : ℝ) :
    ∃ C, ∀ d ∈ K, ∀ e ∈ K, |evenBondUnlinked β w M lam d e| ≤ C := by
  obtain ⟨C, hC⟩ := hwb
  refine ⟨Real.exp (3 * (|β| * C)), fun d hd e he => ?_⟩
  have hb : |β * w d e| ≤ |β| * C := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC d hd e he) (abs_nonneg β)
  have h0 : 0 ≤ |β| * C := (abs_nonneg _).trans hb
  have h1 : 1 ≤ Real.exp (3 * (|β| * C)) := Real.one_le_exp (by linarith)
  unfold evenBondUnlinked evenBond
  split_ifs
  · simp [(Real.exp_pos _).le]
  · calc |Real.cosh (β * w d e) - 1| ≤ (β * w d e) ^ 2 * Real.exp |β * w d e| :=
          abs_cosh_sub_one_le _
      _ = |β * w d e| * |β * w d e| * Real.exp |β * w d e| := by
          rw [abs_mul_abs_self, sq]
      _ ≤ Real.exp |β * w d e| * Real.exp |β * w d e| * Real.exp |β * w d e| := by
          gcongr <;> exact abs_le_exp_abs _
      _ = Real.exp (3 * |β * w d e|) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * (|β| * C)) := Real.exp_le_exp.2 (by linarith)
  · simpa using h1

end Bounds

/-! ### The reduction of one term of the series -/

section Term

variable (β w M lam)

open scoped Classical in
/-- The term of (4.61) for the groups `X₁, …, Xₙ`, the edge sets `E₁` (carrying the odd parts
`a^w`) and `E₂` (carrying the even parts `b^w`), and `F`:
`∏_{ij ∈ E₁} a^w_ij ∏_{ij ∈ E₂} b^w_ij ∏_{ij ∈ ∪ ℰ^inter(Xₗ)} 𝟙_{𝓑_ij^c} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})`. -/
noncomputable def eulerTerm {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (E₁ E₂ F : Finset (ℕ × ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ E₁, oddBond β w (c p.1) (c p.2)) * (∏ p ∈ E₂, evenBond β w (c p.1) (c p.2)) *
    (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
      if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1) *
    ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)

end Term

section TermReduction

open scoped Classical

/-- The pairs of a term of the series lie in `V_X`. -/
theorem mem_biUnion_of_mem_interPairs {X Y : Finset (Finset ℕ)} (hY : Y ⊆ X) {p : ℕ × ℕ}
    (hp : p ∈ interPairs Y) : p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id :=
  ⟨Finset.biUnion_subset_biUnion_of_subset_left id hY (interPairs_subset_pairsOn_biUnion _ hp).1,
    Finset.biUnion_subset_biUnion_of_subset_left id hY (interPairs_subset_pairsOn_biUnion _ hp).2⟩

theorem prod_pair_congr {V : Finset ℕ} {s : Finset (ℕ × ℕ)}
    (hs : ∀ p ∈ s, p.1 ∈ V ∧ p.2 ∈ V) (g : ℂ × ℂ → ℂ × ℂ → ℝ) {c c' : ℕ → ℂ × ℂ}
    (hcc' : ∀ i ∈ (V : Set ℕ), c i = c' i) :
    ∏ p ∈ s, g (c p.1) (c p.2) = ∏ p ∈ s, g (c' p.1) (c' p.2) := by
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [hcc' _ (Finset.mem_coe.2 (hs p hp).1), hcc' _ (Finset.mem_coe.2 (hs p hp).2)]

theorem measurable_prod_pair {s : Finset (ℕ × ℕ)} {g : ℂ × ℂ → ℂ × ℂ → ℝ}
    (hg : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => g q.1 q.2) :
    Measurable fun c : ℕ → ℂ × ℂ => ∏ p ∈ s, g (c p.1) (c p.2) :=
  Finset.measurable_prod _ fun p _ => measurable_pairWeight hg p

theorem boundedOn_prod_pair {s : Finset (ℕ × ℕ)} {g : ℂ × ℂ → ℂ × ℂ → ℝ}
    (hg : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |g d e| ≤ C) :
    BoundedOn K fun c : ℕ → ℂ × ℂ => ∏ p ∈ s, g (c p.1) (c p.2) :=
  BoundedOn.prod _ fun p _ => BoundedOn.pair hg p.1 p.2

theorem measurable_unlinkedIndicator (M lam : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      (if MultipoleLinked M lam q.1 q.2 then (0 : ℝ) else 1) :=
  Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const

theorem measurable_negLinkedIndicator (M lam : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      -(if MultipoleLinked M lam q.1 q.2 then (1 : ℝ) else 0) :=
  (Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const measurable_const).neg

theorem exists_abs_unlinkedIndicator_le (M lam : ℝ) :
    ∃ C, ∀ d ∈ K, ∀ e ∈ K, |(if MultipoleLinked M lam d e then (0 : ℝ) else 1)| ≤ C :=
  ⟨1, fun d _ e _ => by split_ifs <;> simp⟩

theorem exists_abs_negLinkedIndicator_le (M lam : ℝ) :
    ∃ C, ∀ d ∈ K, ∀ e ∈ K, |-(if MultipoleLinked M lam d e then (1 : ℝ) else 0)| ≤ C :=
  ⟨1, fun d _ e _ => by split_ifs <;> simp⟩

theorem linkedIndicator_flipOn (S : Finset ℕ) (c : ℕ → ℂ × ℂ) (p : ℕ × ℕ) :
    MultipoleLinked M lam (flipOn Prod.swap S c p.1) (flipOn Prod.swap S c p.2) ↔
      MultipoleLinked M lam (c p.1) (c p.2) :=
  multipoleLinked_flipOn S c p.1 p.2

/-- A term of the series as `∏_{E} (a + b) G`, with `a + b = f^w 𝟙_{𝓑^c}` and
`G = ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)`. -/
theorem clusterTerm_eq_prod_add_mul {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) (F : Finset (ℕ × ℕ))
    (c : ℕ → ℂ × ℂ) :
    clusterTerm β w M lam Xs Es F c =
      (∏ p ∈ Finset.univ.biUnion Es, (oddBondUnlinked β w M lam (c p.1) (c p.2) +
        evenBondUnlinked β w M lam (c p.1) (c p.2))) *
      ((∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
          if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1) *
        ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)) := by
  have hEI : Finset.univ.biUnion Es ⊆ Finset.univ.biUnion fun l => interPairs (Xs l) :=
    Finset.biUnion_mono fun l _ => hEs l
  unfold clusterTerm
  rw [prod_mul_prod_of_idem hEI (fun p _ => unlinkedIndicator_mul_self _ _)
    (fun p => mayerBondOf β w (c p.1) (c p.2))]
  simp only [mayerBondOf_mul_unlinked]
  ring

/-- The expanded summands are the terms of (4.61). -/
theorem prod_odd_even_mul_eq_eulerTerm {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    {E₁ E₂ : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ Finset.univ.biUnion fun l => interPairs (Xs l))
    (hE₂ : E₂ ⊆ Finset.univ.biUnion fun l => interPairs (Xs l)) (F : Finset (ℕ × ℕ))
    (c : ℕ → ℂ × ℂ) :
    (∏ p ∈ E₁, oddBondUnlinked β w M lam (c p.1) (c p.2)) *
        (∏ p ∈ E₂, evenBondUnlinked β w M lam (c p.1) (c p.2)) *
        ((∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
            if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1) *
          ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0)) =
      eulerTerm β w M lam Xs E₁ E₂ F c := by
  unfold eulerTerm
  simp only [← oddBond_mul_unlinked (β := β) (w := w) (M := M) (lam := lam),
    ← evenBond_mul_unlinked (β := β) (w := w) (M := M) (lam := lam)]
  rw [show ∀ A B C D : ℝ, A * B * (C * D) = (A * (B * C)) * D by intros; ring,
    ← prod_mul_prod_of_idem hE₂ (fun p _ => unlinkedIndicator_mul_self _ _),
    show ∀ A B C D : ℝ, A * (B * C) * D = (A * C) * B * D by intros; ring,
    ← prod_mul_prod_of_idem hE₁ (fun p _ => unlinkedIndicator_mul_self _ _)]
  ring

/-- **(4.61) for one term** of the activity series: with `E = E₁ ∪ ⋯ ∪ Eₙ`,
`𝔼_{𝖯_X}[∏_{E} f^w ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)]
= ∑_{E₁ ⊆ E, E₁ ∈ Eul^X} 𝔼_{𝖯_X}[∏_{E₁} a^w ∏_{E ∖ E₁} b^w ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c}
∏_F (-𝟙_𝓑)]`. -/
theorem ModelHyp.integral_clusterTerm_eq_sum_relEulerian (h : ModelHyp ρ β w ψ K)
    (hρ : MeasurePreserving Prod.swap ρ ρ) (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {Es : Fin n → Finset (ℕ × ℕ)} (hEs : ∀ l, Es l ⊆ interPairs (Xs l)) {F : Finset (ℕ × ℕ)}
    (hF : F ⊆ interPairs (coarsen X (Finset.univ.image Xs))) :
    ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X =
      ∑ E₁ ∈ (Finset.univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X),
        ∫ y, eulerTerm β w M lam Xs E₁ ((Finset.univ.biUnion Es) \ E₁) F
          (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X := by
  have := h.isProbabilityMeasure
  have hEI : Finset.univ.biUnion Es ⊆ Finset.univ.biUnion fun l => interPairs (Xs l) :=
    Finset.biUnion_mono fun l _ => hEs l
  have hIX : (Finset.univ.biUnion fun l => interPairs (Xs l)) ⊆ interPairs X :=
    Finset.biUnion_subset.2 fun l _ => interPairs_subset_of_subset hX (hXs l)
  have hIV : ∀ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
      p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => by
    obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
    exact mem_biUnion_of_mem_interPairs (hXs l) hpl
  have hFV : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => by
    have := mem_biUnion_of_mem_interPairs (le_refl _) (hF hp)
    rwa [biUnion_coarsen fun Y hY => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
      exact hXs l] at this
  -- the factor `G`
  have hGinv : ∀ S ∈ X, ∀ c : ℕ → ℂ × ℂ,
      (fun c : ℕ → ℂ × ℂ => (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
          if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
        ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0))
          (flipOn Prod.swap S c) =
      (fun c : ℕ → ℂ × ℂ => (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
          if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
        ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)) c := by
    intro S _ c
    simp only
    congr 1
    · refine Finset.prod_congr rfl fun p _ => ?_
      exact if_congr (linkedIndicator_flipOn S c p) rfl rfl
    · refine Finset.prod_congr rfl fun p _ => ?_
      rw [if_congr (linkedIndicator_flipOn S c p) rfl rfl]
  -- integrability
  have hoddb := exists_abs_oddBondUnlinked_le (K := K) hwb β M lam
  have hevenb := exists_abs_evenBondUnlinked_le (K := K) hwb β M lam
  have hint : ∀ E₁ ⊆ Finset.univ.biUnion Es, Integrable (fun y =>
      (∏ p ∈ E₁, oddBondUnlinked β w M lam (extendConfig (X.biUnion id) y p.1)
          (extendConfig (X.biUnion id) y p.2)) *
        (∏ p ∈ Finset.univ.biUnion Es \ E₁, evenBondUnlinked β w M lam
          (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)) *
        ((∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
            if MultipoleLinked M lam (extendConfig (X.biUnion id) y p.1)
              (extendConfig (X.biUnion id) y p.2) then (0 : ℝ) else 1) *
          ∏ p ∈ F, -(if MultipoleLinked M lam (extendConfig (X.biUnion id) y p.1)
              (extendConfig (X.biUnion id) y p.2) then (1 : ℝ) else 0)))
      (modelHierarchical ρ β w ψ M lam X) := by
    intro E₁ hE₁
    have hE₁V : ∀ p ∈ E₁, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp =>
      hIV p (hEI (hE₁ hp))
    have hE₂V : ∀ p ∈ Finset.univ.biUnion Es \ E₁, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id :=
      fun p hp => hIV p (hEI (Finset.sdiff_subset hp))
    refine h.integrable_comp_extendConfig
      (g := fun c => (∏ p ∈ E₁, oddBondUnlinked β w M lam (c p.1) (c p.2)) *
        (∏ p ∈ Finset.univ.biUnion Es \ E₁, evenBondUnlinked β w M lam (c p.1) (c p.2)) *
        ((∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
            if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
          ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0))) ?_ ?_ ?_
    · exact ((measurable_prod_pair (g := oddBondUnlinked β w M lam)
        (measurable_oddBondUnlinked h.measurable_w β M lam)).mul
        (measurable_prod_pair (g := evenBondUnlinked β w M lam)
          (measurable_evenBondUnlinked h.measurable_w β M lam))).mul
        ((measurable_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
          (measurable_unlinkedIndicator M lam)).mul
          (measurable_prod_pair
            (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
            (measurable_negLinkedIndicator M lam)))
    · exact ((boundedOn_prod_pair (g := oddBondUnlinked β w M lam) hoddb).mul
        (boundedOn_prod_pair (g := evenBondUnlinked β w M lam) hevenb)).mul
        ((boundedOn_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
          (exists_abs_unlinkedIndicator_le M lam)).mul
          (boundedOn_prod_pair
            (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
            (exists_abs_negLinkedIndicator_le M lam)))
    · intro c c' hcc'
      simp only
      rw [prod_pair_congr hE₁V _ hcc', prod_pair_congr hE₂V _ hcc',
        prod_pair_congr hIV (fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1) hcc',
        prod_pair_congr hFV (fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0)) hcc']
  have hred := integral_prod_add_mul_eq_sum_relEulerian (β := β) (M := M) (lam := lam) hw₁ hw₂
    hψ hρ hX (hEI.trans hIX) (a := oddBondUnlinked β w M lam) (b := evenBondUnlinked β w M lam)
    (G := fun c : ℕ → ℂ × ℂ => (∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
          if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
        ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0))
    (oddBondUnlinked_swap_left hM hw₁)
    (oddBondUnlinked_swap_right hM hw₂) (evenBondUnlinked_swap_left hM hw₁)
    (evenBondUnlinked_swap_right hM hw₂) hGinv hint
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y =>
    clusterTerm_eq_prod_add_mul (β := β) (w := w) (M := M) (lam := lam) hEs F
      (extendConfig (X.biUnion id) y))]
  rw [hred]
  refine Finset.sum_congr rfl fun E₁ hE₁ => integral_congr_ae
    (Filter.Eventually.of_forall fun y => ?_)
  have hE₁s := Finset.mem_powerset.1 (Finset.mem_filter.1 hE₁).1
  exact prod_odd_even_mul_eq_eulerTerm (β := β) (w := w) (M := M) (lam := lam) (hE₁s.trans hEI)
    (Finset.sdiff_subset.trans hEI) F _

end TermReduction

/-! ### Splitting the Eulerian edges among the groups -/

section Split

variable {X : Finset (Finset ℕ)} {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}

theorem biUnion_inter_left' {ι : Type*} (s : Finset ι) (t : ι → Finset (ℕ × ℕ))
    (E : Finset (ℕ × ℕ)) : (s.biUnion fun l => E ∩ t l) = E ∩ s.biUnion t := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro ⟨l, hl, hE, ht⟩
    exact ⟨hE, l, hl, ht⟩
  · rintro ⟨hE, l, hl, ht⟩
    exact ⟨l, hl, hE, ht⟩

theorem biUnion_sdiff_right' {ι : Type*} (s : Finset ι) (t : ι → Finset (ℕ × ℕ))
    (E : Finset (ℕ × ℕ)) : (s.biUnion fun l => t l \ E) = s.biUnion t \ E := by
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨l, hl, ht, hE⟩
    exact ⟨⟨l, hl, ht⟩, hE⟩
  · rintro ⟨⟨l, hl, ht⟩, hE⟩
    exact ⟨l, hl, ht, hE⟩

theorem inter_union_sdiff' (A B : Finset (ℕ × ℕ)) : A ∩ B ∪ B \ A = B := by
  ext p
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem blockDeg_congr {E E' : Finset (ℕ × ℕ)} {S : Finset ℕ} (hE' : E' ⊆ E)
    (h : ∀ p ∈ E, (p.1 ∈ S ∨ p.2 ∈ S) → p ∈ E') : blockDeg E S = blockDeg E' S := by
  unfold blockDeg
  congr 2
  · ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => ⟨h p hp.1 (Or.inl hp.2), hp.2⟩, fun hp => ⟨hE' hp.1, hp.2⟩⟩
  · ext p
    simp only [Finset.mem_filter]
    exact ⟨fun hp => ⟨h p hp.1 (Or.inr hp.2), hp.2⟩, fun hp => ⟨hE' hp.1, hp.2⟩⟩

theorem blockDeg_eq_zero {E : Finset (ℕ × ℕ)} {S : Finset ℕ}
    (h : ∀ p ∈ E, p.1 ∉ S ∧ p.2 ∉ S) : blockDeg E S = 0 := by
  unfold blockDeg
  rw [Finset.card_eq_zero.2, Finset.card_eq_zero.2]
  · rw [Finset.filter_eq_empty_iff]
    exact fun p hp => (h p hp).2
  · rw [Finset.filter_eq_empty_iff]
    exact fun p hp => (h p hp).1

variable (hX : IsSubpartition X) (hXs : ∀ l, Xs l ⊆ X)
  (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j))
include hX hXs hdisj

/-- A pair of `ℰ^inter(Xₗ)` and a pair of `ℰ^inter(Xₘ)` with a common endpoint label belong to
the same group. -/
theorem eq_of_mem_interPairs {l m : Fin n} {p q : ℕ × ℕ} (hp : p ∈ interPairs (Xs l))
    (hq : q ∈ interPairs (Xs m)) (h : p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) : l = m := by
  by_contra hlm
  have hd := disjoint_biUnion_of_disjoint hX (hXs l) (hXs m) (hdisj l m hlm)
  have hp' := interPairs_subset_pairsOn_biUnion _ hp
  have hq' := interPairs_subset_pairsOn_biUnion _ hq
  rcases h with h | h | h | h
  · exact Finset.disjoint_left.1 hd hp'.1 (h ▸ hq'.1)
  · exact Finset.disjoint_left.1 hd hp'.1 (h ▸ hq'.2)
  · exact Finset.disjoint_left.1 hd hp'.2 (h ▸ hq'.1)
  · exact Finset.disjoint_left.1 hd hp'.2 (h ▸ hq'.2)

/-- A block of `Xₗ` is touched only by pairs of `ℰ^inter(Xₗ)`. -/
theorem eq_of_mem_interPairs_of_mem_block {l m : Fin n} {S : Finset ℕ} (hS : S ∈ Xs l)
    {p : ℕ × ℕ} (hp : p ∈ interPairs (Xs m)) (h : p.1 ∈ S ∨ p.2 ∈ S) : m = l := by
  by_contra hml
  have hd := disjoint_biUnion_of_disjoint hX (hXs m) (hXs l) (hdisj m l hml)
  have hp' := interPairs_subset_pairsOn_biUnion _ hp
  rcases h with h | h
  · exact Finset.disjoint_left.1 hd hp'.1 (subset_biUnion_of_mem hS h)
  · exact Finset.disjoint_left.1 hd hp'.2 (subset_biUnion_of_mem hS h)

open scoped Classical in
/-- **Splitting the Eulerian edges among the groups** (the form of (4.61)): summing over the
edge sets `Eₗ ∈ 𝖤^{Xₗ}` and over the Eulerian `E₁ ⊆ E₁ ∪ ⋯ ∪ Eₙ` is summing over the
`E_{l,1} ∈ Eul^{Xₗ}` and the `E_{l,2}` with `E_{l,1} ∩ E_{l,2} = ∅`, `E_{l,1} ∪ E_{l,2} ∈ 𝖤^{Xₗ}`. -/
theorem sum_relEdgeSets_sum_relEulerian_eq {R : Type*} [AddCommMonoid R]
    (g : Finset (ℕ × ℕ) → Finset (ℕ × ℕ) → R) :
    ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
        ∑ E₁ ∈ (Finset.univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X),
          g E₁ (Finset.univ.biUnion Es \ E₁) =
      ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
        ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
            (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
          g (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨fun l => x.2 ∩ x.1 l, fun l => x.1 l \ x.2⟩)
    (fun y => ⟨fun l => y.1 l ∪ y.2 l, Finset.univ.biUnion y.1⟩) ?_ ?_ ?_ ?_ ?_
  · -- `i` maps into the target
    rintro ⟨Es, E₁⟩ hx
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_powerset] at hx
    obtain ⟨hEs, hE₁sub, hE₁eul⟩ := hx
    have hEsI : ∀ l, Es l ⊆ interPairs (Xs l) := fun l => (mem_relEdgeSets.1 (hEs l)).1
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Fintype.mem_piFinset]
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rw [mem_relEulerianPairs]
      refine ⟨Finset.inter_subset_right.trans (hEsI l), fun S hS => ?_⟩
      rw [← blockDeg_congr (E := E₁) Finset.inter_subset_left fun p hp hpS => ?_]
      · exact (mem_relEulerianPairs.1 hE₁eul).2 S (hXs l hS)
      · obtain ⟨m, -, hpm⟩ := Finset.mem_biUnion.1 (hE₁sub hp)
        have := eq_of_mem_interPairs_of_mem_block hX hXs hdisj hS (hEsI m hpm) hpS
        subst this
        exact Finset.mem_inter.2 ⟨hp, hpm⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.sdiff_subset.trans (hEsI l), ?_, ?_⟩
      · exact Finset.disjoint_left.2 fun p hp hp' =>
          (Finset.mem_sdiff.1 hp').2 (Finset.mem_inter.1 hp).1
      · show E₁ ∩ Es l ∪ Es l \ E₁ ∈ relEdgeSets (Xs l)
        rw [inter_union_sdiff']
        exact hEs l
  · -- `j` maps into the paper
    rintro ⟨E₁s, E₂s⟩ hy
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Fintype.mem_piFinset] at hy
    obtain ⟨hE₁s, hE₂s⟩ := hy
    have hE₁I : ∀ l, E₁s l ⊆ interPairs (Xs l) := fun l => (mem_relEulerianPairs.1 (hE₁s l)).1
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun l => (Finset.mem_filter.1 (hE₂s l)).2.2,
      Finset.biUnion_mono fun l _ => Finset.subset_union_left, ?_⟩
    rw [mem_relEulerianPairs]
    refine ⟨Finset.biUnion_subset.2 fun l _ => (hE₁I l).trans
      (interPairs_subset_of_subset hX (hXs l)), fun S hS => ?_⟩
    by_cases hSl : ∃ l, S ∈ Xs l
    · obtain ⟨l, hl⟩ := hSl
      rw [blockDeg_congr (E' := E₁s l) (Finset.subset_biUnion_of_mem _ (Finset.mem_univ l))
        fun p hp hpS => ?_]
      · exact (mem_relEulerianPairs.1 (hE₁s l)).2 S hl
      · obtain ⟨m, -, hpm⟩ := Finset.mem_biUnion.1 hp
        have := eq_of_mem_interPairs_of_mem_block hX hXs hdisj hl (hE₁I m hpm) hpS
        subst this
        exact hpm
    · rw [blockDeg_eq_zero fun p hp => ?_]
      · exact ⟨0, rfl⟩
      obtain ⟨m, -, hpm⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨B, hB, B', hB', -, h1, h2⟩ := exists_of_mem_interPairs (hE₁I m hpm)
      push Not at hSl
      have hBS : B ≠ S := fun h => hSl m (h ▸ hB)
      have hB'S : B' ≠ S := fun h => hSl m (h ▸ hB')
      exact ⟨fun h => Finset.disjoint_left.1 (hX.2 (Finset.mem_coe.2 (hXs m hB))
        (Finset.mem_coe.2 hS) hBS) h1 h,
        fun h => Finset.disjoint_left.1 (hX.2 (Finset.mem_coe.2 (hXs m hB'))
        (Finset.mem_coe.2 hS) hB'S) h2 h⟩
  · -- `j ∘ i = id`
    rintro ⟨Es, E₁⟩ hx
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_powerset] at hx
    simp only [Sigma.mk.injEq]
    refine ⟨funext fun l => ?_, heq_of_eq ?_⟩
    · exact inter_union_sdiff' _ _
    · rw [biUnion_inter_left', Finset.inter_eq_left.2 hx.2.1]
  · -- `i ∘ j = id`
    rintro ⟨E₁s, E₂s⟩ hy
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Fintype.mem_piFinset] at hy
    obtain ⟨hE₁s, hE₂s⟩ := hy
    have hE₁I : ∀ l, E₁s l ⊆ interPairs (Xs l) := fun l => (mem_relEulerianPairs.1 (hE₁s l)).1
    have hE₂I : ∀ l, E₂s l ⊆ interPairs (Xs l) := fun l =>
      Finset.mem_powerset.1 (Finset.mem_filter.1 (hE₂s l)).1
    have hd : ∀ l, Disjoint (E₁s l) (E₂s l) := fun l => (Finset.mem_filter.1 (hE₂s l)).2.1
    -- a pair of `E₁s m` in `E₁s l ∪ E₂s l` is in the group `l`
    have hgrp : ∀ {l m : Fin n} {p : ℕ × ℕ}, p ∈ E₁s m → p ∈ E₁s l ∪ E₂s l → m = l :=
      fun {l m p} hpm hpl => by
        rcases Finset.mem_union.1 hpl with h | h
        · exact eq_of_mem_interPairs hX hXs hdisj (hE₁I m hpm) (hE₁I l h) (Or.inl rfl)
        · exact eq_of_mem_interPairs hX hXs hdisj (hE₁I m hpm) (hE₂I l h) (Or.inl rfl)
    simp only [Sigma.mk.injEq]
    refine ⟨funext fun l => ?_, heq_of_eq (funext fun l => ?_)⟩
    · ext p
      simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨m, hpm⟩, hpl⟩
        rw [← hgrp hpm hpl]
        exact hpm
      · intro hp
        exact ⟨⟨l, hp⟩, Finset.mem_union_left _ hp⟩
    · ext p
      simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
      constructor
      · rintro ⟨hpl, hpn⟩
        rcases Finset.mem_union.1 hpl with h | h
        · exact absurd h (hpn l)
        · exact h
      · intro hp
        refine ⟨Finset.mem_union_right _ hp, fun m hpm => ?_⟩
        have := hgrp hpm (Finset.mem_union_right _ hp)
        subst this
        exact Finset.disjoint_left.1 (hd m) hpm hp
  · -- the summands
    rintro ⟨Es, E₁⟩ hx
    rw [Finset.mem_sigma, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_powerset] at hx
    simp only
    rw [biUnion_inter_left', Finset.inter_eq_left.2 hx.2.1, biUnion_sdiff_right']

end Split

/-! ### Corollary 4.34 -/

section Corollary

open scoped Classical

/-- **Corollary 4.34** (eq. (4.61)) for a model
`(ρ, w, ψ)` with `ρ` and `ψ` invariant under the reversal of a dipole, `w` odd in each dipole and
bounded on `K`, and `M ≥ 1`: for a subpartition `X` with `|X| ≥ 2`,
`𝖪(X) = ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{E_{l,1} ∈ Eul^{Xₗ}}
∑_{E_{l,2} : E_{l,1} ∩ E_{l,2} = ∅, E_{l,1} ∪ E_{l,2} ∈ 𝖤^{Xₗ}} ∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}}
𝔼_{𝖯_X}[∏ₗ (∏_{E_{l,1}} a^w ∏_{E_{l,2}} b^w) ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)]`. -/
theorem ModelHyp.modelActivity_eq_expE11 (h : ModelHyp ρ β w ψ K)
    (hρ : MeasurePreserving Prod.swap ρ ρ) (hw₁ : ∀ d e, w d.swap e = -w d e)
    (hw₂ : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) (h2 : 2 ≤ X.card) :
    modelActivity ρ β w ψ M lam X =
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
            ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
                (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
              ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
                ∫ y, eulerTerm β w M lam Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F
                  (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X := by
  rw [modelActivity, ite_eq_right (by omega : ¬ X.card ≤ 1)]
  refine tsum_congr fun n => ?_
  congr 1
  refine Finset.sum_congr rfl fun Xs hXs => ?_
  rw [Finset.mem_filter] at hXs
  have hXsX : ∀ l, Xs l ⊆ X := fun l => Finset.mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)
  have hterm : ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
        ∫ y, clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y)
          ∂modelHierarchical ρ β w ψ M lam X =
      ∑ E₁ ∈ (Finset.univ.biUnion Es).powerset.filter (· ∈ relEulerianPairs X),
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          ∫ y, eulerTerm β w M lam Xs E₁ (Finset.univ.biUnion Es \ E₁) F
            (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X := by
    intro Es hEs
    have hEsI : ∀ l, Es l ⊆ interPairs (Xs l) := fun l =>
      (mem_relEdgeSets.1 (Fintype.mem_piFinset.1 hEs l)).1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun F hF => ?_
    exact h.integral_clusterTerm_eq_sum_relEulerian hρ hw₁ hw₂ hψ hwb hM hX hXsX hEsI
      (mem_relEdgeSets₀.1 hF).1
  rw [Finset.sum_congr rfl hterm]
  exact sum_relEdgeSets_sum_relEulerian_eq hX hXsX hXs.2
    (fun E₁ E₂ => ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
      ∫ y, eulerTerm β w M lam Xs E₁ E₂ F (extendConfig (X.biUnion id) y)
        ∂modelHierarchical ρ β w ψ M lam X)

end Corollary

/-! ### (4.61) for the activities `𝖪^-_{ε₀}` and `𝖪^0_{ε₀}` -/

section Source

open scoped Classical
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {ε₀ : ℝ}

/-- `ṽ` is bounded on the dipoles charged by `μ_{β,λ,ε₀}`, for `λ ≤ ε₀ R̄`. -/
theorem exists_abs_upperBoundInteraction_le (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) :
    ∃ C, ∀ d ∈ cutoffSet N p₀ β lam ε₀, ∀ e ∈ cutoffSet N p₀ β lam ε₀,
      |upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam) d e| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_screenedInteraction_le hχ hlam
    (τ := 8 * ε₀ * truncationScale p₀ β lam) (by nlinarith)
  refine ⟨C, fun d hd e he => ?_⟩
  have hτ : 8 * ε₀ * truncationScale p₀ β lam / 8 = ε₀ * truncationScale p₀ β lam := by ring
  exact hC d e (by rw [hτ, norm_sub_rev]; exact hd.2) (by rw [hτ, norm_sub_rev]; exact he.2)

/-- `v` is bounded on `Λ² × Λ²`. -/
theorem exists_abs_dipoleInteraction_le (hχ : IsMollifier χ) (hlam : 0 < lam) (N : ℕ) :
    ∃ C, ∀ d ∈ box N ×ˢ box N, ∀ e ∈ box N ×ˢ box N, |dipoleInteraction χ lam d e| ≤ C := by
  have hc := (continuous_dipoleInteraction hχ hlam).continuousOn
    (s := (box N ×ˢ box N) ×ˢ (box N ×ˢ box N))
  obtain ⟨B, hB⟩ :=
    ((isCompact_box_prod N).prod (isCompact_box_prod N)).exists_bound_of_continuousOn hc
  exact ⟨B, fun d hd e he => by simpa [Real.norm_eq_abs] using hB (d, e) ⟨hd, he⟩⟩

theorem gaussianWeight_swap (p₀ : ℕ) (β lam ε₀ L : ℝ) (d : ℂ × ℂ) :
    gaussianWeight p₀ β lam ε₀ L d.swap = gaussianWeight p₀ β lam ε₀ L d := by
  unfold gaussianWeight
  rw [Prod.fst_swap, Prod.snd_swap, norm_sub_rev]

/-- **Corollary 4.34** (eq. (4.61)): for a
subpartition `X` with `|X| ≥ 2`, `λ ∈ (0, ε₀ R̄]`, `N ≥ 1` and `M ≥ 1` (the paper has `M > 20`),
`𝖪^-_{ε₀}(X) = ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint} ∑_{E_{l,1} ∈ Eul^{Xₗ}}
∑_{E_{l,2} : E_{l,1} ∩ E_{l,2} = ∅, E_{l,1} ∪ E_{l,2} ∈ 𝖤^{Xₗ}} ∑_{F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}}
𝔼_{𝖯_X^{-,ε₀}}[∏ₗ (∏_{E_{l,1}} a^ṽ ∏_{E_{l,2}} b^ṽ) ∏_{∪ ℰ^inter(Xₗ)} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)]`. -/
theorem coro_4_34 (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
    (hlamR : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : 1 ≤ M) (L : ℝ)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (h2 : 2 ≤ X.card) :
    minusActivity χ N p₀ β lam M ε₀ L X =
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
            ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
                (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
              ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
                ∫ y, eulerTerm β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam
                  Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F
                  (extendConfig (X.biUnion id) y) ∂minusModel χ N p₀ β lam M ε₀ L X :=
  (modelHyp_minus hχ hlam β hε₀ hN hlamR L).modelActivity_eq_expE11
    (measurePreserving_swap_cutoffDipoleMeasure hχ N p₀ β lam ε₀)
    (fun d e => upperBoundInteraction_swap_left d e χ lam ε₀ _)
    (fun d e => upperBoundInteraction_swap_right d e χ lam ε₀ _)
    (gaussianWeight_swap p₀ β lam ε₀ L)
    (exists_abs_upperBoundInteraction_le hχ hlam hlamR) hM hX h2

/-- (4.61) for `𝖪^0_{ε₀}` ("the same parity argument", proof of Proposition 4.23). -/
theorem zeroActivity_eq_expE11 (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀)
    (hN : 1 ≤ N) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (h2 : 2 ≤ X.card) :
    zeroActivity χ N p₀ β lam M ε₀ X =
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
            ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
                (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
              ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
                ∫ y, eulerTerm β (dipoleInteraction χ lam) M lam
                  Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F
                  (extendConfig (X.biUnion id) y) ∂zeroModel χ N p₀ β lam M ε₀ X :=
  (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN).modelActivity_eq_expE11
    (measurePreserving_swap_cutoffDipoleMeasure hχ N p₀ β lam ε₀)
    (fun d e => dipoleInteraction_swap_left d e hχ lam)
    (fun d e => dipoleInteraction_swap_right d e hχ lam)
    (fun _ => rfl) (exists_abs_dipoleInteraction_le hχ hlam N) hM hX h2

end Source

end Hierarchical

end MultipoleBKT

end
