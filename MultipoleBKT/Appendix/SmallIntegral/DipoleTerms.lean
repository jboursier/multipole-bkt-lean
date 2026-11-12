/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.Majorant
public import MultipoleBKT.Limits.RouteBase.Scaling
public import MultipoleBKT.Limits.RouteDirect.Quantitative
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# The near/far expansion of the dipole integrals

See Lemma A.5, especially (A.29). Split each dipole bond into near and
far parts. For each far-edge set, merge the components of the near graph.
The internal factors are invariant under reversal of a merged component,
and parity cancels the non-Eulerian odd terms. Their retained-tree logarithmic
majorant proves `integrable_anchor_dipSym` for every positive λ. The bound
on the internal weights is uniform in λ and M.

The full singleton average and the subgroup identity relating it to these
merged-part averages are in `Limits/RouteDirect/Dipole` and `Average`.
The paper's quantitative bound is in `Limits/RouteDirect/DipoleBound`.
The dilation helpers below handle the one-vertex compatibility case of
the frozen statement, which permits a connected graph without an edge.

* `dipBond`, `nearBond`, `farBond`: the bond in increasing label order and its two parts.
* `dipBox`, `dipTerm`, `dipBox_eq_sum`: the integrand and its expansion.
* `nearPart`, `blkOf`, `interPart`: the blocks of a term and the far edges between blocks.
* `dipTerm_flip`: a term at a reversed configuration, `W ∏_{e ∈ D} (α'_e + σ_e γ_e) ∏ e^{β g_λ}`.
* `dipSym`: the average of a term over the reversals of the blocks.
* `abs_dipSym_le`, `exists_abs_dipWeight_le`:
  `|dipSym| ≤ C 𝟙_{blocks near-connected} ∏ e^{β g_λ} ∑_{F cut-even} ∏ |α| ∏ |γ|`.
* `exists_abs_integral_dipBox_le`: `|∫_{(Λ²)^ι} dipBox_λ| ≤ A N λ^{(4-β)|ι|-2}` for a connected
  `E` and `|ι| ≤ p*(β)`.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open Limits BoundedLower

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### Bonds -/

section Bonds

variable {ι : Type*} [LinearOrder ι]

/-- The bond `e^{-β v_ij} 𝟙_{𝒜_ij} - 1` of the labels `i, j`, evaluated in increasing label order
(so that it is symmetric in `i, j`). -/
noncomputable def dipBond (χ : ℂ → ℝ) (β lam : ℝ) (c : ι → ℂ × ℂ) (i j : ι) : ℝ :=
  if i < j then stablePairWeight χ β lam (c i) (c j) - 1
  else stablePairWeight χ β lam (c j) (c i) - 1

theorem dipBond_comm (c : ι → ℂ × ℂ) (i j : ι) :
    dipBond χ β lam c i j = dipBond χ β lam c j i := by
  unfold dipBond
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (not_lt.2 h.le)]
  · rfl
  · rw [ite_eq_right (not_lt.2 h.le), ite_eq_left h]

theorem dipBond_of_lt (c : ι → ℂ × ℂ) {i j : ι} (h : i < j) :
    dipBond χ β lam c i j = stablePairWeight χ β lam (c i) (c j) - 1 := by
  unfold dipBond
  rw [ite_eq_left h]

open scoped Classical in
/-- The near part `f_ij 𝟙_{𝓑_ij}` of the bond. -/
noncomputable def nearBond (χ : ℂ → ℝ) (β lam M : ℝ) (c : ι → ℂ × ℂ) (i j : ι) : ℝ :=
  if MultipoleLinked M lam (c i) (c j) then dipBond χ β lam c i j else 0

open scoped Classical in
/-- The far part `f_ij 𝟙_{𝓑_ij^c}` of the bond. -/
noncomputable def farBond (χ : ℂ → ℝ) (β lam M : ℝ) (c : ι → ℂ × ℂ) (i j : ι) : ℝ :=
  if MultipoleLinked M lam (c i) (c j) then 0 else dipBond χ β lam c i j

open scoped Classical in
/-- The indicator `𝟙_{𝓑_ij}` of the multipole relation. -/
noncomputable def linkInd (M lam : ℝ) (c : ι → ℂ × ℂ) (i j : ι) : ℝ :=
  if MultipoleLinked M lam (c i) (c j) then 1 else 0

theorem nearBond_comm (c : ι → ℂ × ℂ) (i j : ι) :
    nearBond χ β lam M c i j = nearBond χ β lam M c j i := by
  unfold nearBond
  rw [dipBond_comm c i j]
  congr 1
  exact propext multipoleLinked_comm

theorem farBond_comm (c : ι → ℂ × ℂ) (i j : ι) :
    farBond χ β lam M c i j = farBond χ β lam M c j i := by
  unfold farBond
  rw [dipBond_comm c i j]
  congr 1
  exact propext multipoleLinked_comm

omit [LinearOrder ι] in
theorem linkInd_comm (c : ι → ℂ × ℂ) (i j : ι) : linkInd M lam c i j = linkInd M lam c j i := by
  unfold linkInd
  congr 1
  exact propext multipoleLinked_comm

/-- The bond as a function of unordered pairs. -/
noncomputable def dipBondE (χ : ℂ → ℝ) (β lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (dipBond χ β lam c) (dipBond_comm c)

/-- The near part as a function of unordered pairs. -/
noncomputable def nearBondE (χ : ℂ → ℝ) (β lam M : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (nearBond χ β lam M c) (nearBond_comm c)

/-- The far part as a function of unordered pairs. -/
noncomputable def farBondE (χ : ℂ → ℝ) (β lam M : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (farBond χ β lam M c) (farBond_comm c)

/-- The indicator of the multipole relation as a function of unordered pairs. -/
noncomputable def linkIndE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (linkInd M lam c) (linkInd_comm c)

theorem dipBondE_eq_add (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    dipBondE χ β lam c e = farBondE χ β lam M c e + nearBondE χ β lam M c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [dipBondE, farBondE, nearBondE, symmLift_mk, farBond, nearBond]
    split_ifs <;> ring

end Bonds

/-! ### The integrand and its expansion -/

section Expansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

open scoped Classical in
/-- The box integrand of `I_{dip,∞}(V; E)` (eq. (A.28) with `ε₀ = ∞`):
`∏_{i<j, ij ∈ E} (e^{-β v_ij} 𝟙_{𝒜_ij} - 1) ∏ᵢ e^{β g_λ(xᵢ - yᵢ)}`. -/
noncomputable def dipBox (χ : ℂ → ℝ) (β lam : ℝ) (E : SimpleGraph ι) (c : ι → ℂ × ℂ) : ℝ :=
  (∏ i, ∏ j, if i < j ∧ E.Adj i j then stablePairWeight χ β lam (c i) (c j) - 1 else 1) *
    ∏ i, pairDensity χ β lam (c i)

open scoped Classical in
/-- The term of the near/far expansion with far edges `E'` (the summand of (A.29) before the
parity argument). -/
noncomputable def dipTerm (χ : ℂ → ℝ) (β lam M : ℝ) (E : SimpleGraph ι) (E' : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : ℝ :=
  (∏ e ∈ E', farBondE χ β lam M c e) * (∏ e ∈ E.edgeFinset \ E', nearBondE χ β lam M c e) *
    ∏ i, pairDensity χ β lam (c i)

open scoped Classical in
omit [DecidableEq ι] in
theorem dipBox_eq_prod (E : SimpleGraph ι) (c : ι → ℂ × ℂ) :
    dipBox χ β lam E c =
      (∏ e ∈ E.edgeFinset, dipBondE χ β lam c e) * ∏ i, pairDensity χ β lam (c i) := by
  unfold dipBox dipBondE
  rw [← prod_prod_ite_lt_adj E (dipBond χ β lam c) (dipBond_comm c)]
  congr 1
  refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ E.Adj i j
  · rw [ite_eq_left h, ite_eq_left h, dipBond_of_lt c h.1]
  · rw [ite_eq_right h, ite_eq_right h]

open scoped Classical in
/-- **The near/far expansion** (the sum over `E' ⊂ E` in (A.29)). -/
theorem dipBox_eq_sum (E : SimpleGraph ι) (c : ι → ℂ × ℂ) :
    dipBox χ β lam E c = ∑ E' ∈ E.edgeFinset.powerset, dipTerm χ β lam M E E' c := by
  rw [dipBox_eq_prod]
  simp_rw [dipBondE_eq_add (M := M) c]
  rw [prod_add, sum_mul]
  rfl

end Expansion

/-! ### The blocks of a term -/

section Blocks

variable {ι : Type*}

/-- The graph `(ι, E \ E')` of the near edges of the term with far edges `E'`. -/
def nearPart (E : SimpleGraph ι) (E' : Finset (Sym2 ι)) : SimpleGraph ι where
  Adj i j := E.Adj i j ∧ s(i, j) ∉ E'
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

/-- The block of a label: its connected component in `(ι, E \ E')`. -/
abbrev blkOf (E : SimpleGraph ι) (E' : Finset (Sym2 ι)) : ι → (nearPart E E').ConnectedComponent :=
  (nearPart E E').connectedComponentMk

/-- The edges of `E` between different blocks (all of them far edges). -/
def interPart (E : SimpleGraph ι) (E' : Finset (Sym2 ι)) : SimpleGraph ι where
  Adj i j := E.Adj i j ∧ blkOf E E' i ≠ blkOf E E' j
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem blkOf_surjective (E : SimpleGraph ι) (E' : Finset (Sym2 ι)) :
    Function.Surjective (blkOf E E') := fun S => S.exists_rep

theorem blkOf_eq_of_not_mem {E : SimpleGraph ι} {E' : Finset (Sym2 ι)} {i j : ι}
    (hij : E.Adj i j) (he : s(i, j) ∉ E') : blkOf E E' i = blkOf E E' j :=
  ConnectedComponent.sound (Adj.reachable (G := nearPart E E') ⟨hij, he⟩)

theorem interPart_adj_ne {E : SimpleGraph ι} {E' : Finset (Sym2 ι)} {i j : ι}
    (h : (interPart E E').Adj i j) : blkOf E E' i ≠ blkOf E E' j := h.2

theorem mem_of_interPart_adj {E : SimpleGraph ι} {E' : Finset (Sym2 ι)} {i j : ι}
    (h : (interPart E E').Adj i j) : s(i, j) ∈ E' := by
  by_contra he
  exact h.2 (blkOf_eq_of_not_mem h.1 he)

/-- The far edges between blocks connect the blocks, if `E` is connected. -/
theorem reachable_interPart [Fintype ι] {E : SimpleGraph ι} (hE : E.Connected)
    (E' : Finset (Sym2 ι)) [DecidableEq (nearPart E E').ConnectedComponent]
    [Fintype (interPart E E').edgeSet] (S S' : (nearPart E E').ConnectedComponent) :
    (nodeGraph (Sym2.map (blkOf E E')) (interPart E E').edgeFinset).Reachable S S' := by
  have hwalk : ∀ u v (p : E.Walk u v),
      (nodeGraph (Sym2.map (blkOf E E')) (interPart E E').edgeFinset).Reachable
        (blkOf E E' u) (blkOf E E' v) := by
    intro u v p
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b c h p ih =>
      refine Reachable.trans ?_ ih
      by_cases hab : blkOf E E' a = blkOf E E' b
      · rw [hab]
      · refine (nodeGraph_adj_of_mem (e := s(a, b)) ?_ (by rw [Sym2.map_mk]) hab).reachable
        rw [mem_edgeFinset]
        exact ⟨h, hab⟩
  obtain ⟨i, rfl⟩ := blkOf_surjective E E' S
  obtain ⟨j, rfl⟩ := blkOf_surjective E E' S'
  obtain ⟨p⟩ := hE.preconnected i j
  exact hwalk i j p

/-- If all the near edges of a term are near pairs of the configuration, every block is
near-connected. -/
theorem induce_connected_of_le {E : SimpleGraph ι} {E' : Finset (Sym2 ι)} {c : ι → ℂ × ℂ}
    (h : ∀ i j, (nearPart E E').Adj i j → MultipoleLinked M lam (c i) (c j))
    (S : (nearPart E E').ConnectedComponent) :
    ((nearGraph M lam c).induce {i | blkOf E E' i = S}).Connected := by
  have hle : nearPart E E' ≤ nearGraph M lam c := fun i j hij =>
    nearGraph_adj.2 ⟨(nearPart E E').ne_of_adj hij, h i j hij⟩
  have hS : ((nearPart E E').induce S.supp).Connected := (S.maximal_connected_induce_supp).1
  exact hS.mono (comap_monotone _ hle)

end Blocks

/-! ### Reversals of blocks -/

section Flip

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [DecidableEq β']

omit [LinearOrder ι] in
theorem flipCfg_blockLabels_empty (blk : ι → β') (c : ι → ℂ × ℂ) :
    flipCfg (blockLabels (β' := β') (ι := ι) blk ∅) c = c := by
  funext i
  simp [flipCfg_apply, mem_blockLabels]

theorem dipBond_flip_of_eq (hχ : IsMollifier χ) (blk : ι → β') (A : Finset β')
    (c : ι → ℂ × ℂ) {i j : ι} (hij : blk i = blk j) :
    dipBond χ β lam (flipCfg (blockLabels blk A) c) i j = dipBond χ β lam c i j := by
  unfold dipBond
  simp only [flipCfg_apply, mem_blockLabels, ← hij]
  by_cases hA : blk i ∈ A
  · simp only [hA, ite_true, stablePairWeight_swap_swap _ _ hχ]
  · simp only [hA, ite_false]

omit [Fintype ι] [LinearOrder ι] [DecidableEq β'] in
theorem multipoleLinked_flip (B : Finset ι) (c : ι → ℂ × ℂ) (i j : ι) :
    MultipoleLinked M lam (flipCfg B c i) (flipCfg B c j) ↔ MultipoleLinked M lam (c i) (c j) := by
  simp only [flipCfg_apply]
  split_ifs
  · rw [multipoleLinked_swap_left, multipoleLinked_swap_right]
  · rw [multipoleLinked_swap_left]
  · rw [multipoleLinked_swap_right]
  · rfl

omit [Fintype ι] [LinearOrder ι] [DecidableEq β'] in
theorem linkInd_flip (B : Finset ι) (c : ι → ℂ × ℂ) (i j : ι) :
    linkInd M lam (flipCfg B c) i j = linkInd M lam c i j := by
  unfold linkInd
  congr 1
  exact propext (multipoleLinked_flip B c i j)

theorem nearBond_flip_of_eq (hχ : IsMollifier χ) (blk : ι → β') (A : Finset β')
    (c : ι → ℂ × ℂ) {i j : ι} (hij : blk i = blk j) :
    nearBond χ β lam M (flipCfg (blockLabels blk A) c) i j = nearBond χ β lam M c i j := by
  unfold nearBond
  rw [dipBond_flip_of_eq hχ blk A c hij]
  congr 1
  exact propext (multipoleLinked_flip _ c i j)

omit [Fintype ι] [DecidableEq ι] [DecidableEq β'] in
/-- With `M ≥ 1`, the far bond is `e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1 + 𝟙_{𝓑_ij}` (since
`𝓑_ij^c ⊂ 𝒜_ij`, Remark 4.6). -/
theorem farBond_eq (hχ : IsMollifier χ) (hM : 1 ≤ M) (c : ι → ℂ × ℂ) (i j : ι) :
    farBond χ β lam M c i j =
      unlinkedPairWeight χ β lam M (c i) (c j) - 1 + linkInd M lam c i j := by
  unfold farBond linkInd unlinkedPairWeight
  by_cases hL : MultipoleLinked M lam (c i) (c j)
  · rw [ite_eq_left hL, ite_eq_left hL, ite_eq_left hL]
    ring
  · rw [ite_eq_right hL, ite_eq_right hL, ite_eq_right hL, add_zero]
    have hL' : ¬ MultipoleLinked M lam (c j) (c i) := fun h => hL (multipoleLinked_comm.1 h)
    unfold dipBond stablePairWeight
    rw [ite_eq_left (remark_4_6 hM hL), ite_eq_left (remark_4_6 hM hL'),
      dipoleInteraction_comm hχ lam (c j) (c i)]
    split_ifs <;> rfl

/-- **The far bond at a reversed configuration**: `α'_e + σ_e(A) γ_e`, with the even part
`α' = α + 𝟙_{𝓑}` (`0` on `𝓑_ij`, `cosh(β v_ij) - 1` on `𝓑_ij^c`). -/
theorem farBondE_flip (hχ : IsMollifier χ) (hM : 1 ≤ M) (blk : ι → β') (A : Finset β')
    (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    farBondE χ β lam M (flipCfg (blockLabels blk A) c) e =
      alphaE hχ β lam M c e + linkIndE M lam c e +
        signCross (Sym2.map blk) A e * gammaE hχ β lam M c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondE, linkIndE, symmLift_mk]
    rw [farBond_eq hχ hM, linkInd_flip, flipCfg_apply, flipCfg_apply]
    simp only [mem_blockLabels]
    rw [unlinkedBond_flip hχ (c i) (c j) (blk i ∈ A) (blk j ∈ A)]
    simp only [alphaE, gammaE, symmLift_mk, signCross, Sym2.map_mk, crosses_mk]
    have : (if (blk i ∈ A ↔ blk j ∈ A) then (1 : ℝ) else -1) =
        if (blk i ∈ A ↔ blk j ∉ A) then -1 else 1 := by
      by_cases hi : blk i ∈ A <;> by_cases hj : blk j ∈ A <;> simp [hi, hj]
    rw [this]
    ring

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem signCross_of_eq (blk : ι → β') (A : Finset β') {i j : ι} (hij : blk i = blk j) :
    signCross (Sym2.map blk) A s(i, j) = 1 := by
  simp only [signCross, Sym2.map_mk, crosses_mk, hij]
  by_cases h : blk j ∈ A <;> simp [h]

/-- A far bond inside a block is invariant under the reversals of blocks. -/
theorem farBondE_flip_of_eq (hχ : IsMollifier χ) (hM : 1 ≤ M) (blk : ι → β') (A : Finset β')
    (c : ι → ℂ × ℂ) {i j : ι} (hij : blk i = blk j) :
    farBondE χ β lam M (flipCfg (blockLabels blk A) c) s(i, j) = farBondE χ β lam M c s(i, j) := by
  have h := farBondE_flip (β := β) (lam := lam) hχ hM blk ∅ c s(i, j)
  rw [flipCfg_blockLabels_empty] at h
  rw [farBondE_flip hχ hM blk A c, h, signCross_of_eq blk A hij, signCross_of_eq blk ∅ hij]

theorem nearBondE_flip_of_eq (hχ : IsMollifier χ) (blk : ι → β') (A : Finset β')
    (c : ι → ℂ × ℂ) {i j : ι} (hij : blk i = blk j) :
    nearBondE χ β lam M (flipCfg (blockLabels blk A) c) s(i, j) = nearBondE χ β lam M c s(i, j) := by
  simp only [nearBondE, symmLift_mk]
  exact nearBond_flip_of_eq hχ blk A c hij

omit [Fintype ι] [DecidableEq ι] [DecidableEq β'] [LinearOrder ι] in
theorem abs_alphaE_add_linkIndE_le (hχ : IsMollifier χ) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    |alphaE hχ β lam M c e + linkIndE M lam c e| ≤ |alphaE hχ β lam M c e| := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [alphaE, linkIndE, symmLift_mk, edgeAlpha, linkInd]
    by_cases hL : MultipoleLinked M lam (c i) (c j)
    · rw [ite_eq_left hL, ite_eq_left hL]
      norm_num
    · rw [ite_eq_right hL, ite_eq_right hL, add_zero]

end Flip

/-! ### Measurability, translations and dilations -/

section Props

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_dipBond (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) (i j : ι) :
    Measurable fun c : ι → ℂ × ℂ => dipBond χ β lam c i j := by
  unfold dipBond
  split_ifs
  · exact (measurable_stablePairWeight_apply hχ hlam β i j).sub_const 1
  · exact (measurable_stablePairWeight_apply hχ hlam β j i).sub_const 1

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem measurableSet_multipoleLinked_apply (M lam : ℝ) (i j : ι) :
    MeasurableSet {c : ι → ℂ × ℂ | MultipoleLinked M lam (c i) (c j)} := by
  have h : Measurable fun c : ι → ℂ × ℂ => (c i, c j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact h (measurableSet_multipoleLinked M lam)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_farBondE (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => farBondE χ β lam M c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondE, symmLift_mk, farBond]
    exact Measurable.ite (measurableSet_multipoleLinked_apply M lam i j) measurable_const
      (measurable_dipBond hχ hlam β i j)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_nearBondE (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => nearBondE χ β lam M c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [nearBondE, symmLift_mk, nearBond]
    exact Measurable.ite (measurableSet_multipoleLinked_apply M lam i j)
      (measurable_dipBond hχ hlam β i j) measurable_const

theorem measurable_dipTerm (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (E : SimpleGraph ι)
    (E' : Finset (Sym2 ι)) : Measurable (dipTerm (ι := ι) χ β lam M E E') := by
  classical
  unfold dipTerm
  exact ((Finset.measurable_prod _ fun e _ => measurable_farBondE hχ hlam β M e).mul
    (Finset.measurable_prod _ fun e _ => measurable_nearBondE hχ hlam β M e)).mul
    (Finset.measurable_prod _ fun i _ => (measurable_pairDensity hχ hlam β).comp
      (measurable_pi_apply i))

omit [Fintype ι] [DecidableEq ι] in
theorem dipBond_translate (a : ℂ) (c : ι → ℂ × ℂ) (i j : ι) :
    dipBond χ β lam (translate a c) i j = dipBond χ β lam c i j := by
  unfold dipBond translate
  simp only [stablePairWeight_translate]

omit [Fintype ι] [DecidableEq ι] in
theorem farBondE_translate (a : ℂ) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    farBondE χ β lam M (translate a c) e = farBondE χ β lam M c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondE, symmLift_mk, farBond, dipBond_translate]
    congr 1
    exact propext (multipoleLinked_translate a (c i) (c j) M lam)

omit [Fintype ι] [DecidableEq ι] in
theorem nearBondE_translate (a : ℂ) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    nearBondE χ β lam M (translate a c) e = nearBondE χ β lam M c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [nearBondE, symmLift_mk, nearBond, dipBond_translate]
    congr 1
    exact propext (multipoleLinked_translate a (c i) (c j) M lam)

theorem dipTerm_translate (E : SimpleGraph ι) (E' : Finset (Sym2 ι)) (a : ℂ)
    (c : ι → ℂ × ℂ) : dipTerm χ β lam M E E' (translate a c) = dipTerm χ β lam M E E' c := by
  unfold dipTerm
  simp only [farBondE_translate, nearBondE_translate]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  exact pairDensity_translate a (c i) χ β lam

omit [Fintype ι] [LinearOrder ι] in
theorem flipCfg_translate (B : Finset ι) (a : ℂ) (c : ι → ℂ × ℂ) :
    flipCfg B (translate a c) = translate a (flipCfg B c) := by
  funext i
  simp only [flipCfg_apply, translate]
  split_ifs <;> simp [Prod.swap]

omit [Fintype ι] [DecidableEq ι] in
theorem dipBond_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (c : ι → ℂ × ℂ) (i j : ι) :
    dipBond χ β lam (lam • c) i j = dipBond χ β 1 c i j := by
  unfold dipBond
  simp only [Pi.smul_apply, stablePairWeight_smul hχ hlam]

omit [Fintype ι] [DecidableEq ι] in
theorem farBondE_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    farBondE χ β lam M (lam • c) e = farBondE χ β 1 M c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondE, symmLift_mk, farBond, dipBond_smul hχ hlam]
    congr 1
    exact propext (multipoleLinked_smul hlam M (c i) (c j))

omit [Fintype ι] [DecidableEq ι] in
theorem nearBondE_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    nearBondE χ β lam M (lam • c) e = nearBondE χ β 1 M c e := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [nearBondE, symmLift_mk, nearBond, dipBond_smul hχ hlam]
    congr 1
    exact propext (multipoleLinked_smul hlam M (c i) (c j))

theorem dipTerm_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (E : SimpleGraph ι)
    (E' : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    dipTerm χ β lam M E E' (lam • c) = (lam ^ (-β)) ^ Fintype.card ι * dipTerm χ β 1 M E E' c := by
  unfold dipTerm
  rw [prod_pairDensity_smul hχ hlam]
  simp only [farBondE_smul hχ hlam, nearBondE_smul hχ hlam]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `|f_ij| ≤ e^{β C}` for the bond in increasing label order. -/
theorem exists_abs_dipBond_le (hχ : IsMollifier χ) : ∃ C, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β →
    ∀ lam : ℝ, 0 < lam → ∀ (c : ι → ℂ × ℂ) (i j : ι),
      |dipBond χ β lam c i j| ≤ Real.exp (β * C) := by
  obtain ⟨C, hC0, hC⟩ := abs_dipoleBond_sub_one_le hχ
  refine ⟨C, hC0, fun β hβ lam hlam c i j => ?_⟩
  unfold dipBond
  split_ifs
  · exact hC β hβ lam hlam (c i) (c j)
  · exact hC β hβ lam hlam (c j) (c i)

omit [Fintype ι] [DecidableEq ι] [LinearOrder ι] in
theorem abs_prod_le_pow {s : Finset (Sym2 ι)} {f : Sym2 ι → ℝ} {B : ℝ} (hB1 : 1 ≤ B)
    (hf : ∀ e ∈ s, |f e| ≤ B) {K : ℕ} (hK : s.card ≤ K) : |∏ e ∈ s, f e| ≤ B ^ K := by
  rw [abs_prod]
  calc ∏ e ∈ s, |f e| ≤ ∏ _e ∈ s, B := prod_le_prod₀ (fun e _ => abs_nonneg _) hf
    _ = B ^ s.card := prod_const B
    _ ≤ B ^ K := pow_le_pow_right₀ hB1 hK

end Props

/-! ### The averaged terms and the parity majorant -/

section Average

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

open scoped Classical in
/-- The average of the term with far edges `E'` over the reversals of its blocks. -/
noncomputable def dipSym (χ : ℂ → ℝ) (β lam M : ℝ) (E : SimpleGraph ι) (E' : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : ℝ :=
  (∑ A : Finset (nearPart E E').ConnectedComponent,
      dipTerm χ β lam M E E' (flipCfg (blockLabels (blkOf E E') A) c)) /
    2 ^ Fintype.card (nearPart E E').ConnectedComponent

theorem measurable_dipSym (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (E : SimpleGraph ι)
    (E' : Finset (Sym2 ι)) : Measurable (dipSym (ι := ι) χ β lam M E E') := by
  classical
  unfold dipSym
  exact (Finset.measurable_sum _ fun A _ => (measurable_dipTerm hχ hlam β M E E').comp
    (measurable_flipCfg _)).div_const _

theorem dipSym_translate (E : SimpleGraph ι) (E' : Finset (Sym2 ι)) (a : ℂ) (c : ι → ℂ × ℂ) :
    dipSym χ β lam M E E' (translate a c) = dipSym χ β lam M E E' c := by
  unfold dipSym
  simp only [flipCfg_translate, dipTerm_translate]

theorem dipSym_smul (hχ : IsMollifier χ) (hlam : 0 < lam) (E : SimpleGraph ι)
    (E' : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    dipSym χ β lam M E E' (lam • c) = (lam ^ (-β)) ^ Fintype.card ι * dipSym χ β 1 M E E' c := by
  unfold dipSym
  simp only [flipCfg_smul, dipTerm_smul hχ hlam]
  rw [← Finset.mul_sum, mul_div_assoc]

open scoped Classical in
/-- The part of a term that is invariant under the reversals of the blocks: the far bonds inside
the blocks and the near bonds. -/
noncomputable def dipWeight (χ : ℂ → ℝ) (β lam M : ℝ) (E : SimpleGraph ι) (E' : Finset (Sym2 ι))
    (c : ι → ℂ × ℂ) : ℝ :=
  (∏ e ∈ E' \ (interPart E E').edgeFinset, farBondE χ β lam M c e) *
    ∏ e ∈ E.edgeFinset \ E', nearBondE χ β lam M c e

open scoped Classical in
/-- **A term at a reversed configuration**: reversing the blocks in `A`, the term is
`W ∏_{e ∈ D} (α'_e + σ_e(A) γ_e) ∏ᵢ e^{β g_λ(xᵢ - yᵢ)}`, `D` the far edges between blocks. -/
theorem dipTerm_flip (hχ : IsMollifier χ) (hM : 1 ≤ M) (E : SimpleGraph ι)
    {E' : Finset (Sym2 ι)} (hE' : E' ⊆ E.edgeFinset)
    (A : Finset (nearPart E E').ConnectedComponent) (c : ι → ℂ × ℂ) :
    dipTerm χ β lam M E E' (flipCfg (blockLabels (blkOf E E') A) c) =
      dipWeight χ β lam M E E' c *
        (∏ e ∈ (interPart E E').edgeFinset, (alphaE hχ β lam M c e + linkIndE M lam c e +
          signCross (Sym2.map (blkOf E E')) A e * gammaE hχ β lam M c e)) *
        ∏ i, pairDensity χ β lam (c i) := by
  have hD : (interPart E E').edgeFinset ⊆ E' := by
    intro e he
    induction e using Sym2.ind with
    | h i j => exact mem_of_interPart_adj (mem_edgeFinset.1 he)
  unfold dipTerm dipWeight
  rw [← prod_sdiff hD]
  have h1 : ∏ e ∈ E' \ (interPart E E').edgeFinset,
      farBondE χ β lam M (flipCfg (blockLabels (blkOf E E') A) c) e =
      ∏ e ∈ E' \ (interPart E E').edgeFinset, farBondE χ β lam M c e := by
    refine prod_congr rfl fun e he => ?_
    obtain ⟨heE', heD⟩ := mem_sdiff.1 he
    induction e using Sym2.ind with
    | h i j =>
      have hij : E.Adj i j := mem_edgeFinset.1 (hE' heE')
      have hblk : blkOf E E' i = blkOf E E' j := by
        by_contra hne
        exact heD (mem_edgeFinset.2 ⟨hij, hne⟩)
      exact farBondE_flip_of_eq hχ hM _ A c hblk
  have h2 : ∏ e ∈ (interPart E E').edgeFinset,
      farBondE χ β lam M (flipCfg (blockLabels (blkOf E E') A) c) e =
      ∏ e ∈ (interPart E E').edgeFinset, (alphaE hχ β lam M c e + linkIndE M lam c e +
        signCross (Sym2.map (blkOf E E')) A e * gammaE hχ β lam M c e) :=
    prod_congr rfl fun e _ => farBondE_flip hχ hM _ A c e
  have h3 : ∏ e ∈ E.edgeFinset \ E',
      nearBondE χ β lam M (flipCfg (blockLabels (blkOf E E') A) c) e =
      ∏ e ∈ E.edgeFinset \ E', nearBondE χ β lam M c e := by
    refine prod_congr rfl fun e he => ?_
    obtain ⟨heE, heE'⟩ := mem_sdiff.1 he
    induction e using Sym2.ind with
    | h i j => exact nearBondE_flip_of_eq hχ _ A c (blkOf_eq_of_not_mem (mem_edgeFinset.1 heE) heE')
  have h4 : ∏ i, pairDensity χ β lam (flipCfg (blockLabels (blkOf E E') A) c i) =
      ∏ i, pairDensity χ β lam (c i) :=
    prod_congr rfl fun i _ => pairDensity_flip hχ _ c i
  rw [h1, h2, h3, h4]
  ring

open scoped Classical in
/-- **The parity bound for the averaged term** (the parity argument of Lemma 4.32 applied to the
far edges between blocks, and `|α'| ≤ |α|`). -/
theorem abs_dipSym_le (hχ : IsMollifier χ) (hM : 1 ≤ M) (E : SimpleGraph ι)
    {E' : Finset (Sym2 ι)} (hE' : E' ⊆ E.edgeFinset) (c : ι → ℂ × ℂ) :
    |dipSym χ β lam M E E' c| ≤
      |dipWeight χ β lam M E E' c| * (∏ i, pairDensity χ β lam (c i)) *
        ∑ F ∈ (interPart E E').edgeFinset.powerset.filter (CutEven (Sym2.map (blkOf E E'))),
          (∏ e ∈ (interPart E E').edgeFinset \ F, |alphaE hχ β lam M c e|) *
            ∏ e ∈ F, |gammaE hχ β lam M c e| := by
  set D := (interPart E E').edgeFinset
  have hpd : 0 ≤ ∏ i, pairDensity χ β lam (c i) :=
    prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
  have heq : dipSym χ β lam M E E' c = dipWeight χ β lam M E E' c *
      (∏ i, pairDensity χ β lam (c i)) *
      ((∑ A : Finset (nearPart E E').ConnectedComponent, ∏ e ∈ D,
        (alphaE hχ β lam M c e + linkIndE M lam c e +
          signCross (Sym2.map (blkOf E E')) A e * gammaE hχ β lam M c e)) /
        2 ^ Fintype.card (nearPart E E').ConnectedComponent) := by
    unfold dipSym
    simp_rw [dipTerm_flip hχ hM E hE']
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine sum_congr rfl fun A _ => ?_
    ring
  rw [heq, abs_mul, abs_mul, abs_of_nonneg hpd]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) hpd)
  refine (abs_avg_prod_le (Sym2.map (blkOf E E')) D _ _).trans ?_
  refine sum_le_sum fun F _ => ?_
  refine mul_le_mul_of_nonneg_right ?_ (prod_nonneg fun e _ => abs_nonneg _)
  exact prod_le_prod₀ (fun e _ => abs_nonneg _) fun e _ => abs_alphaE_add_linkIndE_le hχ c e

open scoped Classical in
/-- **The invariant part of a term** is bounded, and vanishes unless every block is
near-connected (its near bonds carry `𝟙_{𝓑_ij}`). -/
theorem exists_abs_dipWeight_le_uniform (hχ : IsMollifier χ) (hβ0 : 0 ≤ β)
    (E : SimpleGraph ι) : ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, ∀ (E' : Finset (Sym2 ι)), E' ⊆ E.edgeFinset →
      ∀ c : ι → ℂ × ℂ, |dipWeight χ β lam M E E' c| ≤ Cw *
        (if ∀ S, ((nearGraph M lam c).induce {i | blkOf E E' i = S}).Connected then 1 else 0) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_abs_dipBond_le (ι := ι) hχ
  set B := Real.exp (β * C)
  have hB1 : 1 ≤ B := Real.one_le_exp (mul_nonneg hβ0 hC0)
  set K := E.edgeFinset.card
  refine ⟨B ^ K * B ^ K, by positivity, fun lam hlam M E' hE' c => ?_⟩
  have hfar : ∀ e, |farBondE χ β lam M c e| ≤ B := fun e => by
    induction e using Sym2.ind with
    | h i j =>
      simp only [farBondE, symmLift_mk, farBond]
      split_ifs
      · rw [abs_zero]; exact zero_le_one.trans hB1
      · exact hC β hβ0 lam hlam c i j
  have hnear : ∀ e, |nearBondE χ β lam M c e| ≤ B := fun e => by
    induction e using Sym2.ind with
    | h i j =>
      simp only [nearBondE, symmLift_mk, nearBond]
      split_ifs
      · exact hC β hβ0 lam hlam c i j
      · rw [abs_zero]; exact zero_le_one.trans hB1
  by_cases hall : ∀ i j, (nearPart E E').Adj i j → MultipoleLinked M lam (c i) (c j)
  · rw [ite_eq_left fun S => induce_connected_of_le hall S, mul_one]
    unfold dipWeight
    rw [abs_mul]
    refine mul_le_mul (abs_prod_le_pow hB1 (fun e _ => hfar e) ?_)
      (abs_prod_le_pow hB1 (fun e _ => hnear e) ?_) (abs_nonneg _) (by positivity)
    · exact (Finset.card_le_card sdiff_subset).trans (Finset.card_le_card hE')
    · exact Finset.card_le_card sdiff_subset
  · push Not at hall
    obtain ⟨i, j, hadj, hnl⟩ := hall
    have hzero : dipWeight χ β lam M E E' c = 0 := by
      unfold dipWeight
      refine mul_eq_zero_of_right _ (prod_eq_zero (i := s(i, j)) ?_ ?_)
      · exact mem_sdiff.2 ⟨mem_edgeFinset.2 hadj.1, hadj.2⟩
      · simp only [nearBondE, symmLift_mk, nearBond, ite_eq_right hnl]
    rw [hzero, abs_zero]
    positivity

open scoped Classical in
/-- **The invariant part of a term** is bounded, and vanishes unless every block is
near-connected (its near bonds carry `𝟙_{𝓑_ij}`). -/
theorem exists_abs_dipWeight_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    (E : SimpleGraph ι) : ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (E' : Finset (Sym2 ι)), E' ⊆ E.edgeFinset →
      ∀ c : ι → ℂ × ℂ, |dipWeight χ β lam M E E' c| ≤ Cw *
        (if ∀ S, ((nearGraph M lam c).induce {i | blkOf E E' i = S}).Connected then 1 else 0) := by
  obtain ⟨Cw, hCw, hb⟩ := exists_abs_dipWeight_le_uniform hχ hβ0 E
  exact ⟨Cw, hCw, hb lam hlam M⟩

end Average

/-! ### The bound on the dipole integrals -/

section Bound

variable {ι : Type*} [Fintype ι] [decI : DecidableEq ι] [ordI : LinearOrder ι]

open scoped Classical in
/-- The terms are bounded for `λ > 0` (hence integrable on `(Λ²)^ι`). -/
theorem exists_abs_dipTerm_le (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam)
    (E : SimpleGraph ι) : ∃ B : ℝ, ∀ E' ∈ E.edgeFinset.powerset, ∀ c : ι → ℂ × ℂ,
      |dipTerm χ β lam M E E' c| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_dipBond_le (ι := ι) hχ
  obtain ⟨Cp, hCp0, hCp⟩ := exists_exp_smearedKernel_le hχ hβ0
  set Bb := Real.exp (β * C)
  have hB1 : 1 ≤ Bb := Real.one_le_exp (mul_nonneg hβ0 hC0)
  set P := Cp * lam ^ (-β)
  have hpd : ∀ d : ℂ × ℂ, pairDensity χ β lam d ≤ P := fun d => by
    refine (hCp lam hlam (d.1 - d.2)).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _)
      (by linarith)) hCp0.le
  set K := E.edgeFinset.card
  refine ⟨Bb ^ K * Bb ^ K * P ^ Fintype.card ι, fun E' hE' c => ?_⟩
  have hE'sub := mem_powerset.1 hE'
  have hfar : ∀ e, |farBondE χ β lam M c e| ≤ Bb := fun e => by
    induction e using Sym2.ind with
    | h i j =>
      simp only [farBondE, symmLift_mk, farBond]
      split_ifs
      · rw [abs_zero]; exact zero_le_one.trans hB1
      · exact hC β hβ0 lam hlam c i j
  have hnear : ∀ e, |nearBondE χ β lam M c e| ≤ Bb := fun e => by
    induction e using Sym2.ind with
    | h i j =>
      simp only [nearBondE, symmLift_mk, nearBond]
      split_ifs
      · exact hC β hβ0 lam hlam c i j
      · rw [abs_zero]; exact zero_le_one.trans hB1
  unfold dipTerm
  rw [abs_mul, abs_mul]
  have h3 : |∏ i, pairDensity χ β lam (c i)| ≤ P ^ Fintype.card ι := by
    rw [abs_of_nonneg (prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le),
      ← Finset.card_univ (α := ι), ← prod_const]
    exact prod_le_prod₀ (fun i _ => (pairDensity_pos _ _ _ _).le) fun i _ => hpd _
  exact mul_le_mul (mul_le_mul (abs_prod_le_pow hB1 (fun e _ => hfar e) (Finset.card_le_card hE'sub))
    (abs_prod_le_pow hB1 (fun e _ => hnear e) (Finset.card_le_card sdiff_subset)) (abs_nonneg _)
    (by positivity)) h3 (abs_nonneg _) (by positivity)

open scoped Classical in
/-- Integrability of each merged-part average in (A.29).
See Lemma A.5. -/
theorem integrable_anchor_dipSym (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 1 ≤ M) [Nonempty ι] (hk : (Fintype.card ι : ℕ∞) ≤ pStar β)
    (E : SimpleGraph ι) (hE : E.Connected) {E' : Finset (Sym2 ι)}
    (hE' : E' ∈ E.edgeFinset.powerset) (i₀ : ι) :
    Integrable fun c => anchorR i₀ c * dipSym χ β lam M E E' c := by
  cases Subsingleton.elim decI ordI.toDecidableEq
  obtain ⟨Cw, hCw0, hCw⟩ := exists_abs_dipWeight_le (M := M) hχ
    (by linarith : 0 ≤ β) hlam E
  have hE'sub := mem_powerset.1 hE'
  refine Limits.RouteDirect.integrable_anchor_of_parity_bound hχ hβ hlam hM hk (blkOf E E')
    (blkOf_surjective E E') (interPart E E') (fun i j h => h.2)
    (reachable_interPart hE E') i₀ (measurable_dipSym hχ hlam β M E E') hCw0 (fun c => ?_)
  refine (abs_dipSym_le hχ hM E hE'sub c).trans ?_
  have hpd : 0 ≤ ∏ i, pairDensity χ β lam (c i) :=
    prod_nonneg fun i _ => (pairDensity_pos _ _ _ _).le
  have hsum : 0 ≤ ∑ F ∈ (interPart E E').edgeFinset.powerset.filter
      (CutEven (Sym2.map (blkOf E E'))),
      (∏ e ∈ (interPart E E').edgeFinset \ F, |alphaE hχ β lam M c e|) *
        ∏ e ∈ F, |gammaE hχ β lam M c e| :=
    sum_nonneg fun F _ => mul_nonneg (prod_nonneg fun e _ => abs_nonneg _)
      (prod_nonneg fun e _ => abs_nonneg _)
  have h := hCw E' hE'sub c
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hpd) hsum

open scoped Classical in
/-- **Lemma A.5 for one edge set, on a general label type**: if `E` is connected and `|ι| ≤ p*(β)`, there is `A ≥ 0` (depending on `χ, β, E`)
with `|∫_{(Λ²)^ι} ∏_{ij ∈ E} f_ij ∏ᵢ e^{β g_λ(xᵢ - yᵢ)}| ≤ A N λ^{(4-β)|ι|-2}` for every `λ > 0`
and every `N`. -/
theorem exists_abs_integral_dipBox_le (hχ : IsMollifier χ) (hβ : 2 < β) [Nonempty ι]
    (hk : (Fintype.card ι : ℕ∞) ≤ pStar β) (E : SimpleGraph ι) (hE : E.Connected) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ N : ℕ,
      |∫ c in boxConfig ι N, dipBox χ β lam E c| ≤
        A * (N * lam ^ ((4 - β) * Fintype.card ι - 2)) := by
  set i₀ : ι := Classical.arbitrary ι
  have hβ0 : 0 ≤ β := by linarith
  have hint : ∀ E' ∈ E.edgeFinset.powerset,
      Integrable fun c => anchorR i₀ c * dipSym χ β 1 1 E E' c :=
    fun E' hE' => integrable_anchor_dipSym hχ hβ one_pos le_rfl hk E hE hE' i₀
  refine ⟨∑ E' ∈ E.edgeFinset.powerset, ∫ c, |anchorR i₀ c * dipSym χ β 1 1 E E' c|,
    sum_nonneg fun E' _ => integral_nonneg fun c => abs_nonneg _, fun lam hlam N => ?_⟩
  obtain ⟨B, hB⟩ := exists_abs_dipTerm_le (M := 1) hχ hβ0 hlam E
  have hsum : ∫ c in boxConfig ι N, dipBox χ β lam E c =
      ∑ E' ∈ E.edgeFinset.powerset, ∫ c in boxConfig ι N, dipTerm χ β lam 1 E E' c := by
    simp_rw [dipBox_eq_sum (M := 1)]
    exact integral_finsetSum _ fun E' hE' =>
      integrableOn_boxConfig_of_bounded (measurable_dipTerm hχ hlam β 1 E E') (hB E' hE') N
  have hsym : ∀ E' ∈ E.edgeFinset.powerset, ∫ c in boxConfig ι N, dipTerm χ β lam 1 E E' c =
      ∫ c in boxConfig ι N, dipSym χ β lam 1 E E' c := by
    intro E' hE'
    unfold dipSym
    exact (integral_boxConfig_avg_flip (blkOf E E') (measurable_dipTerm hχ hlam β 1 E E')
      (hB E' hE') N).symm
  rw [hsum, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun E' hE' => ?_)
  rw [hsym E' hE']
  refine abs_integral_le_integral_abs.trans ?_
  refine (integral_boxConfig_abs_le_of_smul i₀ hlam β (measurable_dipSym hχ one_pos β 1 E E')
    (fun a c => dipSym_translate E E' a c) (hint E' hE') (dipSym_smul hχ hlam E E') N).trans_eq ?_
  ring

end Bound

end SmallIntegral

end MultipoleBKT

end
