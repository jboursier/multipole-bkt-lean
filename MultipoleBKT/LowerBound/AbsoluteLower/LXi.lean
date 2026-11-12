/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.StepOne

/-!
# Lemma 4.54: Penrose resummation for integrable weights

Lemma 4.54 (display (4.89), Lemma 4.54).

**Lemma 4.54** (`lemma_4_54`): there is `C₁ ≥ 1` depending only on `β` (and the mollifier `χ`)
such that for every subpartition `X`,
`|𝖪^-_{ε₀}(X)| ≤ C₁^{|V_X|} ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint}
∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} 𝔼_{𝖯_X^{-,ε₀}}[∏_{l=1}^n 𝓛_{C₁}(Xₗ) ∏_{ij ∈ T^b} b^abs_ij]`,
for `0 < λ ≤ ε₀ R̄_{β,λ}`, `ε₀ > 0`, `N ≥ 1` and `M ≥ 1` (the paper has `M > 20`), with
`𝓛_{C₁}` the majorant (4.90) (`MultipoleBKT.AbsoluteLower.eulerMajorant`).

The proof is the paper's:

* Step 1 (`MultipoleBKT.AbsoluteLower.abs_oddEvenSum_le`, eq. (4.92)):
  `|𝒰(Xₗ)| ≤ C^{|V_{Xₗ}|} 𝓛_C(Xₗ)` on the support of `𝖯_X^{-,ε₀}`;
* Step 2 (`abs_sum_negLinked_le`, eqs. (4.93)–(4.94)): the Penrose resummation with
  `c_ij = -𝟙_{𝓑_ij}` and `𝟙_{𝓑_ij} ≤ b^abs_ij`;
* Step 3: starting from (4.61) (`MultipoleBKT.Hierarchical.coro_4_34`), the sums over the
  `E_{l,1}`, `E_{l,2}` factorize into `∏ₗ 𝒰(Xₗ)` (`sum_sum_eulerTerm_eq`), and the two bounds are
  inserted under the expectation. The series have finitely many nonzero terms
  (`exists_eq_empty_of_card_lt`), so the passage to absolute values is legitimate.
-/

@[expose] public section

open MeasureTheory

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity

/-! ### Step 2 -/

section StepTwo

open scoped Classical

/-- **Step 2 of Lemma 4.54** (eqs. (4.93)–(4.94) in the proof of Lemma 4.54): for a subpartition `Y`,
`|∑_{F ∈ 𝖤_0^Y} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})| ≤ ∑_{T ∈ 𝖳_0^Y} ∏_{ij ∈ T} b^abs_ij`. -/
theorem abs_sum_negLinked_le {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y) (M lam ε₀ R : ℝ)
    (c : ℕ → ℂ × ℂ) :
    |∑ F ∈ relEdgeSets₀ Y, ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ)
        else 0)| ≤
      ∑ T ∈ relTreePairs₀ Y, ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2) := by
  refine (abs_sum_relEdgeSets₀_le hY _ fun p _ => ?_).trans (sum_le_sum fun T _ => ?_)
  · split_ifs <;> norm_num
  · refine prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p _ => ?_
    rw [abs_neg]
    have h0 : (0 : ℝ) ≤ if MultipoleLinked M lam (c p.1) (c p.2) then 1 else 0 := by
      split_ifs <;> norm_num
    rw [abs_of_nonneg h0]
    exact linkedIndicator_le_absEvenWeight _ _

end StepTwo

/-! ### The factorization of the sums over `E_{l,1}`, `E_{l,2}` -/

section Factorization

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ}

/-- `∑_{x ∈ ∏ A} ∑_{y ∈ ∏ B(x)} ∏ₗ f(xₗ, yₗ) = ∏ₗ ∑_{x ∈ Aₗ} ∑_{y ∈ Bₗ(x)} fₗ(x, y)`. -/
theorem sum_piFinset_sum_piFinset {n : ℕ} {α γ : Type*} [DecidableEq α] [DecidableEq γ]
    (A : Fin n → Finset α) (B : Fin n → α → Finset γ) (f : Fin n → α → γ → ℝ) :
    ∑ x ∈ Fintype.piFinset A, ∑ y ∈ Fintype.piFinset (fun l => B l (x l)), ∏ l, f l (x l) (y l) =
      ∏ l, ∑ a ∈ A l, ∑ b ∈ B l a, f l a b := by
  rw [prod_univ_sum A (fun l a => ∑ b ∈ B l a, f l a b)]
  refine sum_congr rfl fun x _ => ?_
  exact (prod_univ_sum (fun l => B l (x l)) (fun l b => f l (x l) b)).symm

/-- **The sums over the odd and even edge sets factorize over the groups** (Step 3 of the proof
of proof of Lemma 4.54): for disjoint groups `X₁, …, Xₙ ⊆ X`,
`∑_{E_{l,1} ∈ Eul^{Xₗ}} ∑_{E_{l,2}} ∑_{F ∈ 𝖤_0^{Coarse}} (term of (4.61))
= ∏ₗ 𝒰(Xₗ) · ∑_{F ∈ 𝖤_0^{Coarse}} ∏_{ij ∈ F} (-𝟙_{𝓑_ij})`. -/
theorem sum_sum_eulerTerm_eq {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (c : ℕ → ℂ × ℂ) :
    ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
      ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
          (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          eulerTerm β w M lam Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F c =
      (∏ l, oddEvenSum β w M lam (Xs l) c) *
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0) := by
  set G := ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
    ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)
  have hinter : ∏ p ∈ Finset.univ.biUnion (fun l => interPairs (Xs l)),
      (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) =
      ∏ l, ∏ p ∈ interPairs (Xs l), (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ)
        else 1) :=
    prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX hXs hdisj fun _ => le_rfl)
  have hterm : ∀ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
      ∀ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
          (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
      ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          eulerTerm β w M lam Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F c =
        (∏ l, (∏ p ∈ E₁s l, oddBond β w (c p.1) (c p.2)) *
          (∏ p ∈ E₂s l, evenBond β w (c p.1) (c p.2)) *
            ∏ p ∈ interPairs (Xs l), (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ)
              else 1)) * G := by
    intro E₁s hE₁s E₂s hE₂s
    have h1 : ∏ p ∈ Finset.univ.biUnion E₁s, oddBond β w (c p.1) (c p.2) =
        ∏ l, ∏ p ∈ E₁s l, oddBond β w (c p.1) (c p.2) :=
      prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX hXs hdisj fun l =>
        (mem_relEulerianPairs.1 (Fintype.mem_piFinset.1 hE₁s l)).1)
    have h2 : ∏ p ∈ Finset.univ.biUnion E₂s, evenBond β w (c p.1) (c p.2) =
        ∏ l, ∏ p ∈ E₂s l, evenBond β w (c p.1) (c p.2) :=
      prod_biUnion (pairwiseDisjoint_of_subset_interPairs hX hXs hdisj fun l =>
        mem_powerset.1 (mem_filter.1 (Fintype.mem_piFinset.1 hE₂s l)).1)
    simp only [eulerTerm]
    rw [← mul_sum, h1, h2, hinter, ← prod_mul_distrib, ← prod_mul_distrib]
  rw [sum_congr rfl fun E₁s hE₁s => sum_congr rfl fun E₂s hE₂s => hterm E₁s hE₁s E₂s hE₂s]
  simp_rw [← sum_mul]
  congr 1
  exact sum_piFinset_sum_piFinset (fun l => relEulerianPairs (Xs l))
    (fun l E₁ => (interPairs (Xs l)).powerset.filter
      (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets (Xs l)))
    (fun l E₁ E₂ => (∏ p ∈ E₁, oddBond β w (c p.1) (c p.2)) *
      (∏ p ∈ E₂, evenBond β w (c p.1) (c p.2)) *
        ∏ p ∈ interPairs (Xs l), (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1))

end Factorization

/-! ### Integrability and the bound for one tuple of groups -/

section Generic

open scoped Classical

variable {ρ : Measure (ℂ × ℂ)} {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}
  {K : Set (ℂ × ℂ)} {M lam : ℝ}

/-- The terms of (4.61) are integrable against `𝖯_X`. -/
theorem integrable_eulerTerm (h : ModelHyp ρ β w ψ K)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) {X : Finset (Finset ℕ)}
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    {E₁ E₂ F : Finset (ℕ × ℕ)} (hE₁ : E₁ ⊆ Finset.univ.biUnion fun l => interPairs (Xs l))
    (hE₂ : E₂ ⊆ Finset.univ.biUnion fun l => interPairs (Xs l))
    (hF : F ⊆ interPairs (coarsen X (Finset.univ.image Xs))) :
    Integrable (fun y => eulerTerm β w M lam Xs E₁ E₂ F (extendConfig (X.biUnion id) y))
      (modelHierarchical ρ β w ψ M lam X) := by
  have hIV : ∀ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
      p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => by
    obtain ⟨l, -, hpl⟩ := Finset.mem_biUnion.1 hp
    exact mem_biUnion_of_mem_interPairs (hXs l) hpl
  have hFV : ∀ p ∈ F, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => by
    have := mem_biUnion_of_mem_interPairs (le_refl _) (hF hp)
    rwa [biUnion_coarsen fun Y hY => by
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hY
      exact hXs l] at this
  have hE₁V : ∀ p ∈ E₁, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => hIV p (hE₁ hp)
  have hE₂V : ∀ p ∈ E₂, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := fun p hp => hIV p (hE₂ hp)
  have hint := h.integrable_comp_extendConfig (M := M) (lam := lam) (X := X)
    (g := fun c => (∏ p ∈ E₁, oddBondUnlinked β w M lam (c p.1) (c p.2)) *
      (∏ p ∈ E₂, evenBondUnlinked β w M lam (c p.1) (c p.2)) *
      ((∏ p ∈ Finset.univ.biUnion fun l => interPairs (Xs l),
          if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) *
        ∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0))) ?_ ?_ ?_
  · refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
    exact prod_odd_even_mul_eq_eulerTerm hE₁ hE₂ F _
  · exact ((measurable_prod_pair (g := oddBondUnlinked β w M lam)
      (measurable_oddBondUnlinked h.measurable_w β M lam)).mul
      (measurable_prod_pair (g := evenBondUnlinked β w M lam)
        (measurable_evenBondUnlinked h.measurable_w β M lam))).mul
      ((measurable_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
        (measurable_unlinkedIndicator M lam)).mul
        (measurable_prod_pair
          (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
          (measurable_negLinkedIndicator M lam)))
  · exact ((boundedOn_prod_pair (g := oddBondUnlinked β w M lam)
      (exists_abs_oddBondUnlinked_le hwb β M lam)).mul
      (boundedOn_prod_pair (g := evenBondUnlinked β w M lam)
        (exists_abs_evenBondUnlinked_le hwb β M lam))).mul
      ((boundedOn_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
        (exists_abs_unlinkedIndicator_le M lam)).mul
        (boundedOn_prod_pair
          (g := fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0))
          (exists_abs_negLinkedIndicator_le M lam)))
  · intro c c' hcc'
    beta_reduce
    rw [prod_pair_congr hE₁V _ hcc', prod_pair_congr hE₂V _ hcc',
      prod_pair_congr hIV (fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1) hcc',
      prod_pair_congr hFV (fun d e => -(if MultipoleLinked M lam d e then (1 : ℝ) else 0)) hcc']

/-- The integrand of the right-hand side of (4.89) is integrable against `𝖯_X`. -/
theorem integrable_majorantTerm (h : ModelHyp ρ β w ψ K) (hM : 1 ≤ M) (hlam : 0 < lam)
    (ε₀ R C₁ : ℝ) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X) (T : Finset (ℕ × ℕ)) :
    Integrable (fun y => (∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l)
        (extendConfig (X.biUnion id) y)) *
      ∏ p ∈ T, absEvenWeight M lam ε₀ R
        (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2))
      (modelHierarchical ρ β w ψ M lam X) := by
  have hgm : Measurable fun c : ℕ → ℂ × ℂ => (∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l) c) *
      ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2) :=
    (Finset.measurable_prod _ fun l _ =>
      measurable_eulerMajorant (isSubpartition_mono hX (hXs l))).mul
      (Finset.measurable_prod _ fun p _ =>
        measurable_pairWeight (measurable_absEvenWeight M lam ε₀ R) p)
  have hgb : BoundedOn Set.univ fun c : ℕ → ℂ × ℂ =>
      (∏ l, eulerMajorant M lam ε₀ R C₁ (Xs l) c) *
        ∏ p ∈ T, absEvenWeight M lam ε₀ R (c p.1) (c p.2) := by
    refine (BoundedOn.prod _ fun l _ => boundedOn_eulerMajorant hM hlam
      (isSubpartition_mono hX (hXs l)) _).mul (BoundedOn.prod _ fun p _ => ?_)
    refine BoundedOn.pair ⟨2, fun d _ e _ => ?_⟩ p.1 p.2
    rw [abs_of_nonneg (absEvenWeight_nonneg _ _ _ _ _ _)]
    exact absEvenWeight_le_two hM hlam d e
  obtain ⟨B, hB⟩ := hgb
  exact h.integrable_modelHierarchical (hgm.comp (measurable_extendConfig _))
    ⟨B, fun y _ => hB _ fun _ => Set.mem_univ _⟩

/-- Under `𝖯_X`, almost surely every dipole lies in `K`. -/
theorem ae_mem_modelHierarchical (h : ModelHyp ρ β w ψ K) (X : Finset (Finset ℕ)) :
    ∀ᵐ y ∂modelHierarchical ρ β w ψ M lam X,
      ∀ i ∈ X.biUnion id, extendConfig (X.biUnion id) y i ∈ K := by
  have := h.isProbabilityMeasure
  have hac : modelHierarchical ρ β w ψ M lam X ≪ Measure.pi fun _ : X.biUnion id => ρ := by
    rw [modelHierarchical_eq]
    exact withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le (ae_pi_mem (ι := X.biUnion id) h.ae_mem)] with y hy i hi
  simpa [extendConfig, hi] using hy ⟨i, hi⟩

/-- **Step 3 of Lemma 4.54 for one tuple of groups** (internal form, for a general model): if
`|𝒰(X')| ≤ C^{|V_{X'}|} 𝓛_C(X')` whenever the dipoles of `V_{X'}` lie in `K` (Step 1), then for
disjoint groups `X₁, …, Xₙ ⊆ X` the sum of the terms of (4.61) is at most
`C^{|V_X|} ∑_{T^b ∈ 𝖳_0^{Coarse}} 𝔼_{𝖯_X}[∏ₗ 𝓛_C(Xₗ) ∏_{T^b} b^abs]`. -/
theorem abs_sum_eulerTerm_le (h : ModelHyp ρ β w ψ K)
    (hwb : ∃ C, ∀ d ∈ K, ∀ e ∈ K, |w d e| ≤ C) (hM : 1 ≤ M) (hlam : 0 < lam) {ε₀ R C : ℝ}
    (hC : 1 ≤ C)
    (hU : ∀ {X' : Finset (Finset ℕ)}, IsSubpartition X' → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X'.biUnion id, c i ∈ K) →
      |oddEvenSum β w M lam X' c| ≤ C ^ (X'.biUnion id).card * eulerMajorant M lam ε₀ R C X' c)
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :
    |∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
      ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
          (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          ∫ y, eulerTerm β w M lam Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F
            (extendConfig (X.biUnion id) y) ∂modelHierarchical ρ β w ψ M lam X| ≤
      C ^ (X.biUnion id).card *
        ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
          ∫ y, (∏ l, eulerMajorant M lam ε₀ R C (Xs l) (extendConfig (X.biUnion id) y)) *
            ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (extendConfig (X.biUnion id) y p.1)
              (extendConfig (X.biUnion id) y p.2) ∂modelHierarchical ρ β w ψ M lam X := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  set V := X.biUnion id with hVdef
  set P := modelHierarchical ρ β w ψ M lam X with hPdef
  have := h.isProbabilityMeasure
  have hPfin : IsFiniteMeasure P := h.isFiniteMeasure_modelHierarchical X
  have hTB0 : 0 ≤ ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
      ∫ y, (∏ l, eulerMajorant M lam ε₀ R C (Xs l) (extendConfig V y)) *
        ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (extendConfig V y p.1) (extendConfig V y p.2) ∂P :=
    sum_nonneg fun Tb _ => integral_nonneg fun y => mul_nonneg
      (prod_nonneg fun l _ => eulerMajorant_nonneg hC0 _ _)
      (prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _)
  by_cases hsmall : ∃ l, (Xs l).card ≤ 1
  · obtain ⟨l, hl⟩ := hsmall
    have hempty : ∀ E₁s : Fin n → Finset (ℕ × ℕ),
        Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
          (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))) = ∅ := by
      intro E₁s
      refine Fintype.piFinset_eq_empty.2 ⟨l, ?_⟩
      refine filter_false_of_mem fun E₂ _ hE => ?_
      rw [relEdgeSets_eq_empty_of_card_le_one hl] at hE
      exact notMem_empty _ hE.2
    refine (le_of_eq ?_).trans (mul_nonneg (pow_nonneg hC0 _) hTB0)
    rw [abs_eq_zero]
    refine sum_eq_zero fun E₁s _ => ?_
    rw [hempty E₁s, sum_empty]
  push Not at hsmall
  have hXsub : ∀ l, IsSubpartition (Xs l) := fun l => isSubpartition_mono hX (hXs l)
  have hY₁ : IsSubpartition (coarsen X (Finset.univ.image Xs)) := by
    refine isSubpartition_coarsen hX (fun Y hY => ?_) (fun Y hY => ?_) ?_
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hY
      exact hXs l
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hY
      exact card_pos.1 (by have := hsmall l; omega)
    · intro Y hY Y' hY' hne
      obtain ⟨l, -, rfl⟩ := mem_image.1 (mem_coe.1 hY)
      obtain ⟨l', -, rfl⟩ := mem_image.1 (mem_coe.1 hY')
      exact hdisj l l' fun h => hne (h ▸ rfl)
  -- integrability of the terms
  have hint : ∀ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
      ∀ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
          (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
      ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
      Integrable (fun y => eulerTerm β w M lam Xs (Finset.univ.biUnion E₁s)
        (Finset.univ.biUnion E₂s) F (extendConfig V y)) P := by
    intro E₁s hE₁s E₂s hE₂s F hF
    exact integrable_eulerTerm h hwb hXs
      (biUnion_mono fun l _ => (mem_relEulerianPairs.1 (Fintype.mem_piFinset.1 hE₁s l)).1)
      (biUnion_mono fun l _ => mem_powerset.1 (mem_filter.1 (Fintype.mem_piFinset.1 hE₂s l)).1)
      (mem_relEdgeSets₀.1 hF).1
  have hintR : ∀ Tb : Finset (ℕ × ℕ), Integrable (fun y =>
      (∏ l, eulerMajorant M lam ε₀ R C (Xs l) (extendConfig V y)) *
        ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (extendConfig V y p.1) (extendConfig V y p.2)) P :=
    fun Tb => integrable_majorantTerm h hM hlam ε₀ R C hX hXs Tb
  -- move the sums under the expectation
  have hsum : ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
      ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
          (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          ∫ y, eulerTerm β w M lam Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F
            (extendConfig V y) ∂P =
      ∫ y, (∏ l, oddEvenSum β w M lam (Xs l) (extendConfig V y)) *
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          ∏ p ∈ F, -(if MultipoleLinked M lam (extendConfig V y p.1) (extendConfig V y p.2)
            then (1 : ℝ) else 0) ∂P := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall fun y =>
      sum_sum_eulerTerm_eq (β := β) (w := w) (M := M) (lam := lam) hX hXs hdisj
        (extendConfig V y))]
    rw [integral_finsetSum _ fun E₁s hE₁s => integrable_finsetSum _ fun E₂s hE₂s =>
      integrable_finsetSum _ fun F hF => hint E₁s hE₁s E₂s hE₂s F hF]
    refine sum_congr rfl fun E₁s hE₁s => ?_
    rw [integral_finsetSum _ fun E₂s hE₂s => integrable_finsetSum _ fun F hF =>
      hint E₁s hE₁s E₂s hE₂s F hF]
    refine sum_congr rfl fun E₂s hE₂s => ?_
    rw [integral_finsetSum _ fun F hF => hint E₁s hE₁s E₂s hE₂s F hF]
  have hgint : Integrable (fun y => (∏ l, oddEvenSum β w M lam (Xs l) (extendConfig V y)) *
      ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
        ∏ p ∈ F, -(if MultipoleLinked M lam (extendConfig V y p.1) (extendConfig V y p.2)
          then (1 : ℝ) else 0)) P := by
    refine (integrable_finsetSum _ fun E₁s hE₁s => integrable_finsetSum _ fun E₂s hE₂s =>
      integrable_finsetSum _ fun F hF => hint E₁s hE₁s E₂s hE₂s F hF).congr ?_
    exact Filter.Eventually.of_forall fun y =>
      sum_sum_eulerTerm_eq (β := β) (w := w) (M := M) (lam := lam) hX hXs hdisj
        (extendConfig V y)
  -- the pointwise bound
  have hbound : ∀ᵐ y ∂P,
      |(∏ l, oddEvenSum β w M lam (Xs l) (extendConfig V y)) *
        ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
          ∏ p ∈ F, -(if MultipoleLinked M lam (extendConfig V y p.1) (extendConfig V y p.2)
            then (1 : ℝ) else 0)| ≤
        C ^ V.card * ((∏ l, eulerMajorant M lam ε₀ R C (Xs l) (extendConfig V y)) *
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (extendConfig V y p.1)
              (extendConfig V y p.2)) := by
    filter_upwards [ae_mem_modelHierarchical h (M := M) (lam := lam) X] with y hy
    set c := extendConfig V y
    have hU' : ∀ l, |oddEvenSum β w M lam (Xs l) c| ≤
        C ^ ((Xs l).biUnion id).card * eulerMajorant M lam ε₀ R C (Xs l) c := fun l =>
      hU (hXsub l) c fun i hi => hy i (biUnion_subset_biUnion_of_subset_left id (hXs l) hi)
    have hprod : |∏ l, oddEvenSum β w M lam (Xs l) c| ≤
        C ^ V.card * ∏ l, eulerMajorant M lam ε₀ R C (Xs l) c := by
      rw [abs_prod]
      calc ∏ l, |oddEvenSum β w M lam (Xs l) c|
          ≤ ∏ l, C ^ ((Xs l).biUnion id).card * eulerMajorant M lam ε₀ R C (Xs l) c :=
            prod_le_prod₀ (fun _ _ => abs_nonneg _) fun l _ => hU' l
        _ = C ^ (∑ l, ((Xs l).biUnion id).card) * ∏ l, eulerMajorant M lam ε₀ R C (Xs l) c := by
            rw [prod_mul_distrib, prod_pow_eq_pow_sum]
        _ ≤ C ^ V.card * ∏ l, eulerMajorant M lam ε₀ R C (Xs l) c :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (sum_card_biUnion_le hX hXs hdisj))
              (prod_nonneg fun l _ => eulerMajorant_nonneg hC0 _ _)
    rw [abs_mul, ← mul_assoc]
    exact mul_le_mul hprod (abs_sum_negLinked_le hY₁ M lam ε₀ R c) (abs_nonneg _)
      (mul_nonneg (pow_nonneg hC0 _) (prod_nonneg fun l _ => eulerMajorant_nonneg hC0 _ _))
  rw [hsum]
  calc _ ≤ ∫ y, |(∏ l, oddEvenSum β w M lam (Xs l) (extendConfig V y)) *
          ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            ∏ p ∈ F, -(if MultipoleLinked M lam (extendConfig V y p.1)
              (extendConfig V y p.2) then (1 : ℝ) else 0)| ∂P :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, C ^ V.card * ((∏ l, eulerMajorant M lam ε₀ R C (Xs l) (extendConfig V y)) *
          ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
            ∏ p ∈ Tb, absEvenWeight M lam ε₀ R (extendConfig V y p.1)
              (extendConfig V y p.2)) ∂P := by
        refine integral_mono_ae hgint.abs ?_ hbound
        refine Integrable.const_mul ?_ _
        simp_rw [mul_sum]
        exact integrable_finsetSum _ fun Tb _ => hintR Tb
    _ = _ := by
        rw [integral_const_mul]
        congr 1
        simp_rw [mul_sum]
        exact integral_finsetSum _ fun Tb _ => hintR Tb

end Generic

/-! ### Lemma 4.54 -/

section Main

open scoped Classical

variable {χ : ℂ → ℝ}

/-- **Lemma 4.54** (Lemma 4.54, Penrose resummation for integrable weights, display (4.89),
Lemma 4.54): there is `C₁ ≥ 1` depending only on `β` (and the mollifier `χ`) such that,
for `0 < λ ≤ ε₀ R̄_{β,λ}`, `ε₀ > 0`, `N ≥ 1`, `M ≥ 1` and every subpartition `X`,
`|𝖪^-_{ε₀}(X)| ≤ C₁^{|V_X|} ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ X disjoint}
∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} 𝔼_{𝖯_X^{-,ε₀}}[∏_{l=1}^n 𝓛_{C₁}(Xₗ) ∏_{ij ∈ T^b} b^abs_ij]`,
with `𝓛_{C₁}` as in (4.90) (`eulerMajorant`, `0` on groups of at most one block). -/
theorem lemma_4_54 (hχ : IsMollifier χ) (β : ℝ) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (N p₀ : ℕ) (lam M ε₀ L : ℝ), 0 < lam → 0 < ε₀ → 1 ≤ N →
      lam ≤ ε₀ * truncationScale p₀ β lam → 1 ≤ M →
      ∀ {X : Finset (Finset ℕ)}, IsSubpartition X →
        |minusActivity χ N p₀ β lam M ε₀ L X| ≤
          C₁ ^ (X.biUnion id).card *
            ∑' n : ℕ, 1 / (n.factorial : ℝ) *
              ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
                  (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
                ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
                  ∫ y, (∏ l, eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C₁ (Xs l)
                      (extendConfig (X.biUnion id) y)) *
                    ∏ p ∈ Tb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam)
                      (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)
                    ∂minusModel χ N p₀ β lam M ε₀ L X := by
  obtain ⟨C, hC, h1⟩ := abs_oddEvenSum_le hχ β
  refine ⟨C, hC, fun N p₀ lam M ε₀ L hlam hε₀ hN hlamR hM X hX => ?_⟩
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hmodel := modelHyp_minus hχ hlam β hε₀ hN hlamR L
  have hwb := exists_abs_upperBoundInteraction_le (N := N) hχ hlam hlamR
  have hU : ∀ {X' : Finset (Finset ℕ)}, IsSubpartition X' → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X'.biUnion id, c i ∈ cutoffSet N p₀ β lam ε₀) →
      |oddEvenSum β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam X' c| ≤
        C ^ (X'.biUnion id).card *
          eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C X' c :=
    fun hX' c hc => h1 lam ε₀ _ M hlam hlamR hM hX' c fun i hi => (hc i hi).2
  -- the right-hand side
  set b : ℕ → ℝ := fun n => 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ Tb ∈ relTreePairs₀ (coarsen X (Finset.univ.image Xs)),
        ∫ y, (∏ l, eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C (Xs l)
            (extendConfig (X.biUnion id) y)) *
          ∏ p ∈ Tb, absEvenWeight M lam ε₀ (truncationScale p₀ β lam)
            (extendConfig (X.biUnion id) y p.1) (extendConfig (X.biUnion id) y p.2)
          ∂minusModel χ N p₀ β lam M ε₀ L X with hb
  have hb0 : ∀ n, 0 ≤ b n := fun n => mul_nonneg (by positivity)
    (sum_nonneg fun Xs _ => sum_nonneg fun Tb _ => integral_nonneg fun y => mul_nonneg
      (prod_nonneg fun l _ => eulerMajorant_nonneg hC0 _ _)
      (prod_nonneg fun p _ => absEvenWeight_nonneg _ _ _ _ _ _))
  have hbvan : ∀ n, X.card < n → b n = 0 := by
    intro n hn
    refine mul_eq_zero_of_right _ (sum_eq_zero fun Xs hXs => ?_)
    rw [mem_filter] at hXs
    obtain ⟨l, hl⟩ := exists_eq_empty_of_card_lt
      (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)) hXs.2 hn
    refine sum_eq_zero fun Tb _ => ?_
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    have hzero : eulerMajorant M lam ε₀ (truncationScale p₀ β lam) C (Xs l)
        (extendConfig (X.biUnion id) y) = 0 := by
      rw [hl]
      exact eulerMajorant_eq_zero_of_card_le_one (by simp) _
    simp only [Pi.zero_apply]
    rw [prod_eq_zero (mem_univ l) hzero, zero_mul]
  obtain ⟨hbsum, -⟩ := summable_and_tsum_eq_of_vanish hbvan
  by_cases h1X : X.card ≤ 1
  · rw [minusActivity, modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ h1X, abs_zero]
    exact mul_nonneg (pow_nonneg hC0 _) (tsum_nonneg hb0)
  rw [coro_4_34 hχ hlam hε₀ hN hlamR hM L hX (by omega)]
  set a : ℕ → ℝ := fun n => 1 / (n.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∑ E₁s ∈ Fintype.piFinset (fun l => relEulerianPairs (Xs l)),
        ∑ E₂s ∈ Fintype.piFinset (fun l => (interPairs (Xs l)).powerset.filter
            (fun E₂ => Disjoint (E₁s l) E₂ ∧ E₁s l ∪ E₂ ∈ relEdgeSets (Xs l))),
          ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)),
            ∫ y, eulerTerm β (upperBoundInteraction χ lam ε₀ (truncationScale p₀ β lam)) M lam
              Xs (Finset.univ.biUnion E₁s) (Finset.univ.biUnion E₂s) F
              (extendConfig (X.biUnion id) y) ∂minusModel χ N p₀ β lam M ε₀ L X with ha
  have hab : ∀ n, |a n| ≤ C ^ (X.biUnion id).card * b n := by
    intro n
    rw [ha, hb, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n.factorial : ℝ)),
      mul_left_comm, mul_sum]
    refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans
      (sum_le_sum fun Xs hXs => ?_)) (by positivity)
    rw [mem_filter] at hXs
    exact abs_sum_eulerTerm_le hmodel hwb hM hlam hC hU hX
      (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hXs.1 l)) hXs.2
  have hasum : Summable a :=
    Summable.of_norm_bounded (hbsum.mul_left (C ^ (X.biUnion id).card)) fun n => by
      rw [Real.norm_eq_abs]
      exact hab n
  calc |∑' n, a n| ≤ ∑' n, |a n| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hasum.norm
    _ ≤ ∑' n, C ^ (X.biUnion id).card * b n := hasum.abs.tsum_le_tsum hab (hbsum.mul_left _)
    _ = C ^ (X.biUnion id).card * ∑' n, b n := tsum_mul_left

end Main

end AbsoluteLower

end MultipoleBKT

end
