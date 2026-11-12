/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.LemmaA6
public import MultipoleBKT.Appendix.SmallIntegral.LemmaA6J2Root

/-!
# The external-gain integral and its minimum bad distance

See (A.18) and
(A.20). These define the external-gain integral.
-/

@[expose] public section

namespace MultipoleBKT
namespace SmallIntegral

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps UpperBound

variable {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}

/-! ### The integrand -/

section Defs

variable {W : Type*} [Fintype W]

/-- `min_{i} d_{i,bad}` for the dipoles `z`, as the fold of `min` from the cap `4 ε₀ R̄`. -/
noncomputable def minBadDist (p₀ : ℕ) (β lam ε₀ : ℝ) {N : ℕ} (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (z : W → ℂ × ℂ) : ℝ :=
  univ.fold min (4 * (ε₀ * truncationScale p₀ β lam)) fun i => badDistZ p₀ β lam ε₀ V Z (z i)

/-- **The gain factor of `J_ext`** `min(max_i r_i / min_i d_{i,bad}, 1)²` (eq. (A.18)). -/
noncomputable def extGain (p₀ : ℕ) (β lam ε₀ : ℝ) {N : ℕ} (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (z : W → ℂ × ℂ) : ℝ :=
  min (univ.fold max 0 (fun i => dipoleLength (z i)) / minBadDist p₀ β lam ε₀ V Z z) 1 ^ 2

end Defs

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- **The integrand of `J_ext`** (eq. (A.18)), for the groups `Xs`, the trees `Ta l` (relative to
`Xs l`) and `Tb` (relative to the coarsening), the selection `hatS` of the blocks `Ŝ_l`, and the
frozen dipoles `(Z j)_{j ∈ V}`, at the configuration `z` of the dipoles of `V_X`. -/
noncomputable def integrandJext (χ : ℂ → ℝ) (β lam M ε₀ : ℝ) (p₀ : ℕ) {N : ℕ}
    (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) (z : X.biUnion id → ℂ × ℂ) : ℝ :=
  extGain p₀ β lam ε₀ V Z z *
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hatS l z),
      blockRadius hX (fun i => dipoleLength (z i)) S ^ 2) *
    (∏ e ∈ univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset,
      keptWeight (dipoleDistOn z) (absIndicator M lam ε₀ (truncationScale p₀ β lam) z) e) *
    (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset,
      (absWeight (fun i => dipoleLength (z i)) (dipoleDistOn z)
        (absIndicator M lam ε₀ (truncationScale p₀ β lam) z) e ^ 2 + linkE M lam z e)) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) z) S) then 1 else 0) *
    ∏ i, cutDens χ β lam (ε₀ * truncationScale p₀ β lam) (z i)

/-- **The integral `J_ext`** of eq. (A.18), over `(Λ²)^{V_X}`, `Λ = Λ_N`. -/
noncomputable def integralJext (χ : ℂ → ℝ) (β lam M ε₀ : ℝ) (p₀ N : ℕ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ)) (Tb : Finset (ℕ × ℕ))
    (hatS : Fin n → (X.biUnion id → ℂ × ℂ) → X) : ENNReal :=
  ∫⁻ z in boxConfig (X.biUnion id) N,
    ENNReal.ofReal (integrandJext χ β lam M ε₀ p₀ V Z hX Xs Ta Tb hatS z)

/-! ### The gain -/

section Gain

variable {W : Type*} [Fintype W] [Nonempty W] {N p₀ : ℕ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-- The fold of `min` from the cap is attained at a dipole (`d_{i,bad} ≤ 4 ε₀ R̄`). -/
theorem exists_minBadDist_eq (z : W → ℂ × ℂ) :
    ∃ j, minBadDist p₀ β lam ε₀ V Z z = badDistZ p₀ β lam ε₀ V Z (z j) := by
  classical
  obtain ⟨j, -, hj⟩ := exists_min_image (univ : Finset W)
    (fun i => badDistZ p₀ β lam ε₀ V Z (z i)) univ_nonempty
  refine ⟨j, le_antisymm ?_ ?_⟩
  · exact (fold_min_le _).2 (Or.inr ⟨j, mem_univ j, le_rfl⟩)
  · exact (le_fold_min _).2 ⟨badDistZ_le_cap _, fun i _ => hj i (mem_univ i)⟩

/-- **The gain is at most the sum of the gains of the dipoles**:
`min(max_i r_i / min_i d_{i,bad}, 1)² ≤ ∑_j min(1, R²/d_{j,bad}²)` for `R ≥ max_i r_i`. -/
theorem extGain_le_sum (hcap : 0 ≤ ε₀ * truncationScale p₀ β lam) (z : W → ℂ × ℂ) {R : ℝ}
    (hR : ∀ i, dipoleLength (z i) ≤ R) :
    extGain p₀ β lam ε₀ V Z z ≤ ∑ j, gainW p₀ β lam ε₀ V Z R (z j) := by
  obtain ⟨j, hj⟩ := exists_minBadDist_eq (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (V := V)
    (Z := Z) z
  refine le_trans ?_ (single_le_sum (fun j _ => gainW_nonneg (p₀ := p₀) (β := β) (lam := lam)
    (ε₀ := ε₀) (V := V) (Z := Z) R (z j)) (mem_univ j))
  unfold extGain gainW
  rw [hj]
  set F := univ.fold max 0 (fun i => dipoleLength (z i))
  set δ := badDistZ p₀ β lam ε₀ V Z (z j)
  have hF0 : 0 ≤ F := (le_fold_max _).2 (Or.inl le_rfl)
  have hR0 : 0 ≤ R := (norm_nonneg ((z j).1 - (z j).2)).trans (hR j)
  have hFR : F ≤ R := (fold_max_le _).2 ⟨hR0, fun i _ => hR i⟩
  have hδ0 : 0 ≤ δ := le_badDistZ (mul_nonneg (by norm_num) hcap) fun _ _ => dipoleDist_nonneg _ _
  rcases hδ0.eq_or_lt with h0 | hδ
  · rw [← h0]
    simp
  · have hq0 : 0 ≤ F / δ := div_nonneg hF0 hδ.le
    have hq : F / δ ≤ R / δ := div_le_div_of_nonneg_right hFR hδ.le
    have e : min (F / δ) 1 ^ 2 = min ((F / δ) ^ 2) 1 := by
      rcases le_total (F / δ) 1 with h | h
      · rw [min_eq_left h, min_eq_left (pow_le_one₀ hq0 h)]
      · rw [min_eq_right h, min_eq_right (one_le_pow₀ h), one_pow]
    rw [e, min_comm]
    refine min_le_min le_rfl ?_
    rw [← div_pow]
    exact pow_le_pow_left₀ hq0 hq 2

end Gain

end SmallIntegral
end MultipoleBKT

end
