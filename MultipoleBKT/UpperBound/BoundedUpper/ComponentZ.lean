/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.ComponentBound
public import MultipoleBKT.UpperBound.BoundedUpper.JIntegral
public import MultipoleBKT.UpperBound.BoundedUpper.ParityReduction
public import MultipoleBKT.UpperBound.BoundedUpper.Components

/-!
# Radius and support estimates for the upper component bounds

The paper: Proposition 5.18. The separated component proof in `RouteRaw` uses these identifications
of block radii, comparisons of bad distances on the support, odd-bond symmetry,
and uniform absolute-weight bounds. The tail `compTail` keeps the largest tree
edge and largest component radius for the subsequent tail assembly.
-/

@[expose] public section

open Finset SimpleGraph
open scoped NNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Peeling CoreForest Quadratic Parity Hierarchical Multipole

/-! ### Block radii -/

section Radii

variable {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)

/-- The block radius of `MultipoleBKT.Peeling` (`sup'` over the vertices of the block) is
`blockRad`. -/
theorem blockRadius_eq_blockRad (c : ℕ → ℂ × ℂ) (S : Y) :
    blockRadius hY (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) S = blockRad c S := by
  have hSY : (S : Finset ℕ) ⊆ Y.biUnion id := subset_biUnion_of_mem id S.2
  refine le_antisymm ?_ ?_
  · unfold blockRadius
    refine Finset.sup'_le _ _ fun i hi => ?_
    exact le_blockRad c ((blockOf_eq_iff hY).1 (Finset.mem_filter.1 hi).2)
  · refine blockRad_le ?_ fun i hi => ?_
    · have hne := hY.1 S S.2
      obtain ⟨i, hi⟩ := hne
      exact (norm_nonneg _).trans
        (le_blockRadius (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) ⟨i, hSY hi⟩ |>.trans_eq
          (by rw [(blockOf_eq_iff hY).2 hi]))
    · exact (le_blockRadius (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) ⟨i, hSY hi⟩).trans_eq
        (by rw [(blockOf_eq_iff hY).2 hi])

/-- The largest block radius is the largest radius on `V_Y`. -/
theorem blockRad_biUnion_eq (c : ℕ → ℂ × ℂ) {Ŝ : Y}
    (hŜ : ∀ S : Y, blockRad c S ≤ blockRad c Ŝ) : blockRad c Ŝ = blockRad c (Y.biUnion id) := by
  refine le_antisymm (blockRad_mono c (subset_biUnion_of_mem id Ŝ.2)) ?_
  refine blockRad_le (blockRad_nonneg c _) fun i hi => ?_
  obtain ⟨S, hS, hiS⟩ := Finset.mem_biUnion.1 hi
  exact (le_blockRad c hiS).trans (hŜ ⟨S, hS⟩)

/-- `∏_{S ∈ Y, S ≠ Ŝ} r_S² = radialExceptMax c Y` for `Ŝ` of maximal positive radius. -/
theorem prod_erase_blockRadius_eq (c : ℕ → ℂ × ℂ) {Ŝ : Y}
    (hŜ : ∀ S : Y, blockRad c S ≤ blockRad c Ŝ) (hpos : 0 < blockRad c Ŝ) :
    ∏ S ∈ univ.erase Ŝ, blockRadius hY (fun i : Y.biUnion id => ‖(c i).1 - (c i).2‖) S ^ 2 =
      radialExceptMax c Y := by
  rw [radialExceptMax_eq Ŝ.2 (blockRad_biUnion_eq c hŜ) hpos]
  simp_rw [blockRadius_eq_blockRad hY c]
  rw [← Finset.prod_coe_sort (Y.erase Ŝ)]
  refine Finset.prod_bij' (fun S hS => ⟨S.1, Finset.mem_erase.2
      ⟨fun h => (Finset.mem_erase.1 hS).1 (Subtype.ext h), S.2⟩⟩)
    (fun S _ => ⟨S.1, (Finset.mem_erase.1 S.2).2⟩) (fun _ _ => mem_univ _)
    (fun S _ => Finset.mem_erase.2 ⟨fun h => (Finset.mem_erase.1 S.2).1 (congrArg Subtype.val h),
      mem_univ _⟩) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end Radii

/-! ### Comparisons on the support -/

section Support

variable {χ : ℂ → ℝ} {N : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-- **Eq. (5.10) on the support**: inside a block `S` whose dipoles are linked
(`ConnOn S (linkedPairs …)`, i.e. `𝟙_{𝓑_S} = 1`), `d_{j,bad} ≤ (M + 2)^{|S|} d_{i,bad}`. -/
theorem badDistZ_le_of_connOn (hlam : 0 < lam) (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam)
    (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M) (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z)
    {c : ℕ → ℂ × ℂ} {S : Finset ℕ} (hc : ∀ i ∈ S, OnSupportZ p₀ β lam M ε₀ V Z (c i))
    (hS : ConnOn S (linkedPairs M lam c S)) {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) :
    badDistZ p₀ β lam ε₀ V Z (c j) ≤ (M + 2) ^ S.card * badDistZ p₀ β lam ε₀ V Z (c i) := by
  classical
  have hM0 : 0 ≤ M := zero_le_one.trans ((one_le_pow₀ (by norm_num)).trans hM)
  have hcap : 0 ≤ ε₀ * truncationScale p₀ β lam := hlam.le.trans hlamh
  have hsub : linkedPairs M lam c S ⊆ pairsOn S := Finset.filter_subset _ _
  refine le_pow_card_mul (G := edgeGraph (linkedPairs M lam c S))
    (δ := fun v => badDistZ p₀ β lam ε₀ V Z (c v)) (by linarith) (fun u w huw => ?_)
    (fun v => badDistZ_nonneg hcap _) (hS.2 i hi j hj)
    (fun v hv => mem_of_reachable_of_closed (fun a b hab _ => (mem_of_edgeGraph_adj hsub hab).2)
      hi hv)
  obtain ⟨hu, -⟩ := mem_of_edgeGraph_adj hsub huw
  have hlink : MultipoleLinked M lam (c u) (c w) ∨ MultipoleLinked M lam (c w) (c u) := by
    rcases exists_mem_of_edgeGraph_adj huw with h | h
    · exact Or.inl (mem_linkedPairs.1 h).2
    · exact Or.inr (mem_linkedPairs.1 h).2
  exact badDistZ_le_of_linked hlam hlamh hM hVZ (hc u hu).2 (hc u hu).norm_le hlink

/-- `|a^{v^Z}_{de} 𝟙_{𝓑^c}|` is symmetric in `d, e` (`M ≥ 1`). -/
theorem abs_oddBondUnlinked_comm (hχ : IsMollifier χ) (hM : 1 ≤ M) (d e : ℂ × ℂ) :
    |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| =
      |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam e d| := by
  by_cases h : MultipoleLinked M lam d e
  · rw [oddBondUnlinked_of_linked h, oddBondUnlinked_of_linked (Multipole.multipoleLinked_comm.1 h)]
  · rw [oddBondUnlinked_of_not_linked hM h,
      oddBondUnlinked_of_not_linked hM (fun h' => h (Multipole.multipoleLinked_comm.1 h'))]
    unfold interactionGoodZ
    rw [pairInteraction_comm hχ]

/-- A nonzero odd bond forces `v^Z ≠ 0`. -/
theorem interactionGoodZ_ne_zero_of_oddBond (d e : ℂ × ℂ)
    (h : oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e ≠ 0) :
    interactionGoodZ χ p₀ β lam ε₀ V Z d e ≠ 0 := by
  intro h0
  apply h
  unfold oddBondUnlinked oddBond
  rw [h0, mul_zero, Real.sinh_zero, neg_zero]
  split_ifs <;> rfl

/-- **The support of `v^Z`**: if `v^Z(d, e) ≠ 0` then `d(d, e) ≤ d_{d,bad} + d_{e,bad}` (for good
dipoles on the support). -/
theorem dipoleDist_le_of_interactionGoodZ_ne_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hlamh : lam ≤ ε₀ * truncationScale p₀ β lam) (hM : (3 : ℝ) ^ pBeta p₀ β ≤ M)
    (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {d e : ℂ × ℂ}
    (hd : OnSupportZ p₀ β lam M ε₀ V Z d) (he : OnSupportZ p₀ β lam M ε₀ V Z e)
    (hv : interactionGoodZ χ p₀ β lam ε₀ V Z d e ≠ 0) :
    dipoleDist d e ≤ badDistZ p₀ β lam ε₀ V Z d + badDistZ p₀ β lam ε₀ V Z e := by
  set τ := pairRadii p₀ β lam ε₀ V Z d e
  have hp : ∀ k, lam ≤ τ k := by
    intro k
    fin_cases k
    · exact lam_le_goodRadiusZ d
    · exact lam_le_goodRadiusZ e
  have hv' : ballGrowthInteraction χ lam τ τ (pairConfig d e) 0 1 ≠ 0 := by
    rw [← interactionGoodZ_eq_ballGrowth]
    exact hv
  have h := dipoleDist_lt_of_ballGrowthInteraction_ne_zero hχ hlam hp hp hv'
  have hτd : goodRadiusZ p₀ β lam ε₀ V Z d ≤ badDistZ p₀ β lam ε₀ V Z d := by
    unfold goodRadiusZ
    have := lam_le_badDistZ hlam hlamh hM hVZ hd.2 hd.norm_le
    have h0 := badDistZ_nonneg (hlam.le.trans hlamh) (V := V) (Z := Z) (p₀ := p₀) (β := β) d
    exact max_le (by linarith) this
  have hτe : goodRadiusZ p₀ β lam ε₀ V Z e ≤ badDistZ p₀ β lam ε₀ V Z e := by
    unfold goodRadiusZ
    have := lam_le_badDistZ hlam hlamh hM hVZ he.2 he.norm_le
    have h0 := badDistZ_nonneg (hlam.le.trans hlamh) (V := V) (Z := Z) (p₀ := p₀) (β := β) e
    exact max_le (by linarith) this
  have h0 : τ 0 = goodRadiusZ p₀ β lam ε₀ V Z d := rfl
  have h1 : τ 1 = goodRadiusZ p₀ β lam ε₀ V Z e := rfl
  rw [max_self, max_self, h0, h1] at h
  exact h.le.trans (by linarith)

end Support

/-! ### `a^abs ≤ 1`, `b^abs ≤ 2` -/

section AbsBounds

variable {M lam ε₀ R : ℝ}

/-- `a^abs_ij ≤ 1` (for `M ≥ 1`, `λ > 0`): on `𝓑_ij^c`, `d_ij ≥ min(r_i, r_j)` and `d_ij > 0`. -/
theorem absOddWeight_le_one' (hM : 1 ≤ M) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    absOddWeight M lam ε₀ R d e ≤ 1 := by
  classical
  by_cases h : MultipoleLinked M lam d e
  · unfold absOddWeight
    rw [ite_eq_left h]
    simp
  set r₁ := ‖d.1 - d.2‖
  set r₂ := ‖e.1 - e.2‖
  set D := dipoleDist d e
  have hDlt : M * min (max r₁ lam) (max r₂ lam) < D := not_le.1 h
  have hmin0 : lam ≤ min (max r₁ lam) (max r₂ lam) := le_min (le_max_right _ _) (le_max_right _ _)
  have hMmin : min (max r₁ lam) (max r₂ lam) ≤ M * min (max r₁ lam) (max r₂ lam) :=
    le_mul_of_one_le_left (hlam.le.trans hmin0) hM
  have hDpos : 0 < D := (lt_of_lt_of_le hlam (hmin0.trans hMmin)).trans hDlt
  have hminD : min r₁ r₂ ≤ D :=
    ((min_le_min (le_max_left _ _) (le_max_left _ _)).trans hMmin).trans hDlt.le
  set m := max D (max r₁ r₂)
  have hmpos : 0 < m := lt_of_lt_of_le hDpos (le_max_left _ _)
  have hrr : r₁ * r₂ ≤ D * m := by
    rw [← min_mul_max]
    exact mul_le_mul hminD (le_max_right _ _) (by positivity) hDpos.le
  have hA1 : r₁ * r₂ / (D * m) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hrr
  unfold absOddWeight
  rw [ite_eq_right h, mul_one]
  split_ifs
  · rw [mul_one]; exact hA1
  · rw [mul_zero]; exact zero_le_one

/-- `b^abs_ij ≤ 2` (for `M ≥ 1`, `λ > 0`). -/
theorem absEvenWeight_le_two' (hM : 1 ≤ M) (hlam : 0 < lam) (d e : ℂ × ℂ) :
    absEvenWeight M lam ε₀ R d e ≤ 2 := by
  classical
  unfold absEvenWeight
  have h1 := absOddWeight_le_one' (ε₀ := ε₀) (R := R) hM hlam d e
  have h0 := absOddWeight_nonneg M lam ε₀ R d e
  have : (if MultipoleLinked M lam d e then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  nlinarith

end AbsBounds

/-! ### The bound on one odd component -/

section Component

variable {χ : ℂ → ℝ}

open scoped Classical in
/-- The tail `(max_{V_Y} r / max(max_{e ∈ T} d_e, max_{V_Y} r))²` of one component. -/
noncomputable def compTail (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ))
    (T : SimpleGraph (Y.biUnion id)) : ℝ :=
  (blockRad c (Y.biUnion id) / max (maxEdgeDist c T : ℝ) (blockRad c (Y.biUnion id))) ^ 2

theorem compTail_nonneg (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) (T : SimpleGraph (Y.biUnion id)) :
    0 ≤ compTail c Y T :=
  sq_nonneg _

theorem prod_marksOn {Y : Finset (Finset ℕ)} {W' : Finset ℕ} (hW' : W' ⊆ Y.biUnion id)
    (g : ℕ → ℝ) : ∏ i ∈ marksOn Y W', g i = ∏ i ∈ W', g i := by
  classical
  refine Finset.prod_bij (fun i _ => (i : ℕ)) (fun i hi => ?_) (fun i _ j _ h => Subtype.ext h)
    (fun a ha => ⟨⟨a, hW' ha⟩, ?_, rfl⟩) (fun i _ => rfl)
  · unfold marksOn at hi
    exact (Finset.mem_filter.1 hi).2
  · unfold marksOn
    exact Finset.mem_filter.2 ⟨mem_univ _, ha⟩

theorem card_edgeFinset_le_sq {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] {k : ℕ} (hk : Fintype.card W ≤ k) : G.edgeFinset.card ≤ k * k := by
  refine G.card_edgeFinset_le_card_choose_two.trans ?_
  rw [Nat.choose_two_right]
  calc Fintype.card W * (Fintype.card W - 1) / 2 ≤ Fintype.card W * (Fintype.card W - 1) :=
        Nat.div_le_self _ _
    _ ≤ k * k := Nat.mul_le_mul hk (Nat.sub_le_of_le_add (by omega))

end Component

end BoundedUpper

end UpperBound

end MultipoleBKT

end
