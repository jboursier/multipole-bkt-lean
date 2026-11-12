/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Geometry
public import MultipoleBKT.UpperBound.BadPoints.GoodBad
public import MultipoleBKT.UpperBound.BadPoints.Packing

/-!
# The interaction of a good dipole with frozen bad points (eq. (5.26) on the support)

The paper: proof of Proposition 5.18: "The packing argument
of Lemma 5.11 uses only `Z` and gives (5.26) there". This is
Lemma 5.11 for a dipole `e ∈ I_good^Z` and the frozen
bad points `(Z_j)_{j ∈ V}`, whose radii `τ_j^{±,Z}` come from the clusterings run on `V`
(`badRadiusPlusOn`, `badRadiusMinusOn`):

`∑_{j ∈ V} |v^Z(e, Z_j)| ≤ C r_e / d_{e,bad}` (`sum_abs_interactionExtZ_le`), `C` depending on `χ`
and `q(β)` only.

The proof is the paper's (and that of `MultipoleBKT.UpperBound.lemma_5_11`), on the configuration
`(Z_0, …, Z_{N-1}, e)` of `Fin (N + 1)` (`extConfig`):

* `card_le_of_pairwise_le_on`, `card_filter_badRadiusPlusOn_le`, `card_filter_badRadiusMinusOn_le`:
  eqs. (5.15), (5.16) (Lemma 5.9 (7)) for the clusterings run on `V`;
* `badRadiusPlusOn_le_max_div`: Remark 5.10 for the bad radii, `τ_j^{±,Z} ≤ max(r_j/4, λ)`;
* `support_plus_Z`, `support_minus_Z`: eqs. (5.11), (5.12) (Lemma 5.9 (3)–(4)): if
  `v^Z_{e,j,±} ≠ 0` then `d^±_{e,j} ≤ 2 τ_j^{±,Z}` and `τ_j^{±,Z} > λ`;
* the dyadic summation `MultipoleBKT.UpperBound.sum_abs_halfInteractionPlus_le`.
-/

@[expose] public section

open Finset
open MultipoleBKT.TheoremTwo

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

variable {N : ℕ}

/-! ### Packing for the clusterings run on `V` -/

section Packing

variable {lam : ℝ} {q : ℕ} {h : ℝ} {z : Fin N → ℂ} {r : Fin N → ℝ} {V : Finset (Fin N)}

/-- The no-crowding property of the clustering run on `V`, in terms of the removal values. -/
theorem card_lt_of_lt_clusterRemovalValueOn {i : Fin N} (hi : i ∈ V) {s : ℝ} (hs : 0 ≤ s)
    (hsi : s < clusterRemovalValueOn q h z r V i) :
    (V.filter fun j => j ≠ i ∧ ‖z i - z j‖ ≤ 2 * s ∧
      s < clusterRemovalValueOn q h z r V j).card < q := by
  classical
  obtain ⟨p, hp, hip⟩ := exists_mem_clustering (q := q) (h := h) (z := z) (r := r) V i hi
  rw [clusterRemovalValueOn_eq hp hip] at hsi
  refine lt_of_le_of_lt (Finset.card_le_card fun j hj => ?_)
    (card_filter_lt_of_mem_clustering V p hp i hip s hs hsi)
  rw [Finset.mem_filter] at hj ⊢
  obtain ⟨hjV, hji, hdist, hsj⟩ := hj
  obtain ⟨p', hp', hjp'⟩ := exists_mem_clustering (q := q) (h := h) (z := z) (r := r) V j hjV
  rw [clusterRemovalValueOn_eq hp' hjp'] at hsj
  exact ⟨hjV, hji, hdist, p', hp', hjp', hsj⟩

/-- **The core of eq. (5.15)** for the clustering run on `V`: if `0 < λ`, `S ⊆ V`, every member
`a` of `S` has `max(removal value, λ) ≥ t` and `> λ`, and the charges of `S` are pairwise within
distance `t`, then `|S| ≤ q`. -/
theorem card_le_of_pairwise_le_on (hlam : 0 < lam) {t : ℝ} (S : Finset (Fin N)) (hSV : S ⊆ V)
    (hS : ∀ a ∈ S, t ≤ max (clusterRemovalValueOn q h z r V a) lam ∧
      lam < max (clusterRemovalValueOn q h z r V a) lam)
    (hdist : ∀ a ∈ S, ∀ b ∈ S, ‖z a - z b‖ ≤ t) : S.card ≤ q := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set ρ : Fin N → ℝ := fun a => max (clusterRemovalValueOn q h z r V a) lam
  obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image ρ hne
  have hρ : ∀ a ∈ S, ρ a = clusterRemovalValueOn q h z r V a := fun a ha => by
    have := (hS a ha).2
    simp only [ρ] at this ⊢
    rcases le_total lam (clusterRemovalValueOn q h z r V a) with h1 | h1
    · exact max_eq_left h1
    · rw [max_eq_right h1] at this
      exact absurd this (lt_irrefl _)
  set τ := ρ i₀
  set s := (τ + lam) / 2
  have hτlam : lam < τ := (hS i₀ hi₀).2
  have hs0 : 0 ≤ s := by simp only [s]; linarith
  have hsτ : s < clusterRemovalValueOn q h z r V i₀ := by
    rw [← hρ i₀ hi₀]
    simp only [s]
    linarith
  have hcard := card_lt_of_lt_clusterRemovalValueOn (hSV hi₀) hs0 hsτ
  have hsub : S.erase i₀ ⊆ V.filter fun j => j ≠ i₀ ∧ ‖z i₀ - z j‖ ≤ 2 * s ∧
      s < clusterRemovalValueOn q h z r V j := by
    intro j hj
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
    refine Finset.mem_filter.mpr ⟨hSV hjS, hji, ?_, ?_⟩
    · have h1 := hdist i₀ hi₀ j hjS
      have h2 := (hS i₀ hi₀).1
      simp only [s]
      linarith
    · rw [← hρ j hjS]
      have h1 := hmin j hjS
      simp only [s]
      linarith
  have h2 := (Finset.card_le_card hsub).trans_lt hcard
  rw [Finset.card_erase_of_mem hi₀] at h2
  omega

end Packing

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

/-- `τ_j^{+,Z} = max(removal value, λ)` for the clustering of the positive charges run on `V`. -/
theorem badRadiusPlusOn_eq (j : Fin N) :
    badRadiusPlusOn p₀ β lam ε₀ V Z j =
      max (clusterRemovalValueOn (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
        (fun k => (Z k).1) (fun k => ‖(Z k).1 - (Z k).2‖) V j) lam := by
  rw [badRadiusPlusOn, clusterRadiusOn, max_comm lam, max_assoc, max_self]

theorem badRadiusMinusOn_eq (j : Fin N) :
    badRadiusMinusOn p₀ β lam ε₀ V Z j =
      max (clusterRemovalValueOn (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
        (fun k => (Z k).2) (fun k => ‖(Z k).1 - (Z k).2‖) V j) lam := by
  rw [badRadiusMinusOn, clusterRadiusOn, max_comm lam, max_assoc, max_self]

/-- **Eq. (5.15)** for the clustering of the positive charges run on `V`: for every `A`, `t ≥ 0`
and `w`, at most `q(β) (2⌈2A⌉ + 1)²` labels `j ∈ V` have `|x_j - w| ≤ A t`, `τ_j^{+,Z} ≥ t` and
`τ_j^{+,Z} > λ`. -/
theorem card_filter_badRadiusPlusOn_le (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) (A : ℝ) (w : ℂ) :
    (V.filter fun j => ‖(Z j).1 - w‖ ≤ A * t ∧ t ≤ badRadiusPlusOn p₀ β lam ε₀ V Z j ∧
      lam < badRadiusPlusOn p₀ β lam ε₀ V Z j).card ≤ packingConstant (clusterThreshold p₀ β) A := by
  refine card_le_packingConstant ht (fun k => (Z k).1) _
    (fun a ha => (Finset.mem_filter.mp ha).2.1) fun S hS hdist => ?_
  refine card_le_of_pairwise_le_on (V := V) (h := ε₀ * truncationScale p₀ β lam)
    (r := fun k => ‖(Z k).1 - (Z k).2‖) hlam S (fun a ha => (Finset.mem_filter.mp (hS ha)).1)
    (fun a ha => ?_) hdist
  have := (Finset.mem_filter.mp (hS ha)).2.2
  rw [badRadiusPlusOn_eq] at this
  exact this

/-- **Eq. (5.16)** for the clustering of the negative charges run on `V`. -/
theorem card_filter_badRadiusMinusOn_le (hlam : 0 < lam) {t : ℝ} (ht : 0 ≤ t) (A : ℝ) (w : ℂ) :
    (V.filter fun j => ‖(Z j).2 - w‖ ≤ A * t ∧ t ≤ badRadiusMinusOn p₀ β lam ε₀ V Z j ∧
      lam < badRadiusMinusOn p₀ β lam ε₀ V Z j).card ≤ packingConstant (clusterThreshold p₀ β) A := by
  refine card_le_packingConstant ht (fun k => (Z k).2) _
    (fun a ha => (Finset.mem_filter.mp ha).2.1) fun S hS hdist => ?_
  refine card_le_of_pairwise_le_on (V := V) (h := ε₀ * truncationScale p₀ β lam)
    (r := fun k => ‖(Z k).1 - (Z k).2‖) hlam S (fun a ha => (Finset.mem_filter.mp (hS ha)).1)
    (fun a ha => ?_) hdist
  have := (Finset.mem_filter.mp (hS ha)).2.2
  rw [badRadiusMinusOn_eq] at this
  exact this

/-- **Remark 5.10 for the bad radii computed on `V`**: `τ_j^{+,Z} ≤ max(r_j/4, λ)` for `j ∈ V`. -/
theorem badRadiusPlusOn_le_max_div {j : Fin N} (hj : j ∈ V) :
    badRadiusPlusOn p₀ β lam ε₀ V Z j ≤ max (‖(Z j).1 - (Z j).2‖ / 4) lam := by
  classical
  rw [badRadiusPlusOn_eq]
  refine max_le_max ?_ le_rfl
  obtain ⟨p, hp, hjp⟩ := exists_mem_clustering (q := clusterThreshold p₀ β)
    (h := ε₀ * truncationScale p₀ β lam) (z := fun k => (Z k).1)
    (r := fun k => ‖(Z k).1 - (Z k).2‖) V j hj
  rw [clusterRemovalValueOn_eq hp hjp]
  exact snd_le_div_of_mem_clustering hp hjp

theorem badRadiusMinusOn_le_max_div {j : Fin N} (hj : j ∈ V) :
    badRadiusMinusOn p₀ β lam ε₀ V Z j ≤ max (‖(Z j).1 - (Z j).2‖ / 4) lam := by
  classical
  rw [badRadiusMinusOn_eq]
  refine max_le_max ?_ le_rfl
  obtain ⟨p, hp, hjp⟩ := exists_mem_clustering (q := clusterThreshold p₀ β)
    (h := ε₀ * truncationScale p₀ β lam) (z := fun k => (Z k).2)
    (r := fun k => ‖(Z k).1 - (Z k).2‖) V j hj
  rw [clusterRemovalValueOn_eq hp hjp]
  exact snd_le_div_of_mem_clustering hp hjp

/-! ### The configuration `(Z, e)` -/

section Ext

/-- The configuration of `Fin (N + 1)`: the frozen dipoles `Z_j` at `j < N` and the good dipole
`e` at the last label. -/
def extConfig (Z : Fin N → ℂ × ℂ) (e : ℂ × ℂ) : Fin (N + 1) → ℂ × ℂ :=
  Fin.lastCases e Z

/-- The radii `τ^+` of the configuration `(Z, e)`: `τ_j^{+,Z}` (computed on `V`) and `τ_e^Z`. -/
noncomputable def extRadiusPlus (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (e : ℂ × ℂ) : Fin (N + 1) → ℝ :=
  Fin.lastCases (goodRadiusZ p₀ β lam ε₀ V Z e) (badRadiusPlusOn p₀ β lam ε₀ V Z)

/-- The radii `τ^-` of the configuration `(Z, e)`. -/
noncomputable def extRadiusMinus (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (e : ℂ × ℂ) : Fin (N + 1) → ℝ :=
  Fin.lastCases (goodRadiusZ p₀ β lam ε₀ V Z e) (badRadiusMinusOn p₀ β lam ε₀ V Z)

theorem lam_le_extRadiusPlus (e : ℂ × ℂ) (k : Fin (N + 1)) :
    lam ≤ extRadiusPlus p₀ β lam ε₀ V Z e k := by
  induction k using Fin.lastCases with
  | last => simp only [extRadiusPlus, Fin.lastCases_last]; exact lam_le_goodRadiusZ e
  | cast j => simp only [extRadiusPlus, Fin.lastCases_castSucc]; exact lam_le_badRadiusPlusOn j

theorem lam_le_extRadiusMinus (e : ℂ × ℂ) (k : Fin (N + 1)) :
    lam ≤ extRadiusMinus p₀ β lam ε₀ V Z e k := by
  induction k using Fin.lastCases with
  | last => simp only [extRadiusMinus, Fin.lastCases_last]; exact lam_le_goodRadiusZ e
  | cast j => simp only [extRadiusMinus, Fin.lastCases_castSucc]; exact lam_le_badRadiusMinusOn j

/-- `v^Z(e, Z_j) = v'_{e,j,+} - v'_{e,j,-}` on the configuration `(Z, e)`. -/
theorem interactionExtZ_eq (χ : ℂ → ℝ) (e : ℂ × ℂ) (j : Fin N) :
    interactionExtZ χ p₀ β lam ε₀ V Z e j =
      halfInteractionPlus χ lam (extRadiusPlus p₀ β lam ε₀ V Z e)
          (extRadiusMinus p₀ β lam ε₀ V Z e) (extConfig Z e) (Fin.last N) j.castSucc -
        halfInteractionMinus χ lam (extRadiusPlus p₀ β lam ε₀ V Z e)
          (extRadiusMinus p₀ β lam ε₀ V Z e) (extConfig Z e) (Fin.last N) j.castSucc := by
  simp only [interactionExtZ, pairInteraction, halfInteractionPlus, halfInteractionMinus,
    extConfig, extRadiusPlus, extRadiusMinus, badRadiiZ, Fin.lastCases_last,
    Fin.lastCases_castSucc]

end Ext

/-! ### The support of the half interactions -/

section Support

/-- The core of eqs. (5.11)–(5.12) for `e ∈ I_good^Z`: if `D' ≥ d(e, Z_j)` is the distance of
`{x_e, y_e}` to an endpoint of the bad dipole `j ∈ I_bad^V(Z)` whose radius `τ ∈ [λ,
max(r_j/4, λ)]` satisfies `D' < τ_e^Z + τ`, then `D' ≤ 2τ`, `d_{e,bad} ≤ D'` and `λ < τ`. -/
theorem geo_core_Z (hlam : 0 < lam) (hM3 : 3 ≤ M) {e : ℂ × ℂ}
    (he : IsGoodZ p₀ β lam M ε₀ V Z e) {j : Fin N} (hjV : j ∈ V)
    (hj : j ∈ badPointsOn p₀ β lam M ε₀ V Z) {D τ : ℝ}
    (hDij : dipoleDist e (Z j) ≤ D) (hτ : lam ≤ τ)
    (hD : D < goodRadiusZ p₀ β lam ε₀ V Z e + τ) :
    D ≤ 2 * τ ∧ badDistZ p₀ β lam ε₀ V Z e ≤ D ∧ lam < τ := by
  have hbd : badDistZ p₀ β lam ε₀ V Z e ≤ D :=
    (badDistZ_le_dipoleDist (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (Z := Z) e hjV).trans hDij
  have hτi : goodRadiusZ p₀ β lam ε₀ V Z e ≤ max (D / 4) lam := by
    unfold goodRadiusZ
    exact max_le_max (by linarith) le_rfl
  have h2τ : D ≤ 2 * τ := by
    rcases le_total (D / 4) lam with h | h
    · rw [max_eq_right h] at hτi
      linarith
    · rw [max_eq_left h] at hτi
      linarith
  refine ⟨h2τ, hbd, ?_⟩
  have hsep := lt_dipoleDist_of_isGoodZ (zero_le_three.trans hM3) he hj
  have hmin : lam ≤ min (max ‖e.1 - e.2‖ lam) (max ‖(Z j).1 - (Z j).2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  have : 3 * lam ≤ M * min (max ‖e.1 - e.2‖ lam) (max ‖(Z j).1 - (Z j).2‖ lam) :=
    mul_le_mul hM3 hmin hlam.le (zero_le_three.trans hM3)
  linarith

/-- **Eq. (5.11)** for `e ∈ I_good^Z` and `j ∈ V` (Lemma 5.9 (3)): if `v^Z_{e,j,+} ≠ 0` then
`d^+_{e,j} ≤ 2 τ_j^{+,Z}`, `d_{e,bad} ≤ d^+_{e,j}` and `τ_j^{+,Z} > λ`. -/
theorem support_plus_Z {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam) (hM3 : 3 ≤ M)
    (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    {j : Fin N} (hjV : j ∈ V)
    (hv : halfInteractionPlus χ lam (extRadiusPlus p₀ β lam ε₀ V Z e)
      (extRadiusMinus p₀ β lam ε₀ V Z e) (extConfig Z e) (Fin.last N) j.castSucc ≠ 0) :
    min ‖(extConfig Z e (Fin.last N)).1 - (extConfig Z e j.castSucc).1‖
        ‖(extConfig Z e (Fin.last N)).2 - (extConfig Z e j.castSucc).1‖ ≤
        2 * extRadiusPlus p₀ β lam ε₀ V Z e j.castSucc ∧
      badDistZ p₀ β lam ε₀ V Z e ≤
        min ‖(extConfig Z e (Fin.last N)).1 - (extConfig Z e j.castSucc).1‖
          ‖(extConfig Z e (Fin.last N)).2 - (extConfig Z e j.castSucc).1‖ ∧
      lam < extRadiusPlus p₀ β lam ε₀ V Z e j.castSucc := by
  have hsupp := halfInteractionPlus_ne_zero hχ hlam (lam_le_extRadiusPlus e)
    (lam_le_extRadiusMinus e) hv
  simp only [extConfig, extRadiusPlus, extRadiusMinus, Fin.lastCases_last,
    Fin.lastCases_castSucc] at hsupp ⊢
  refine geo_core_Z hlam hM3 he hjV (hVZ hjV) (dipoleDist_le_min_fst _ _)
    (lam_le_badRadiusPlusOn j) ?_
  rcases hsupp with h | h
  · exact (min_le_left _ _).trans_lt h
  · exact (min_le_right _ _).trans_lt h

/-- The exchanged configuration `(Z, e)` with `x ↔ y` in every dipole. -/
theorem swapConfig_extConfig (e : ℂ × ℂ) :
    swapConfig (extConfig Z e) = extConfig (swapConfig Z) e.swap := by
  funext k
  induction k using Fin.lastCases with
  | last => simp [swapConfig, extConfig]; rfl
  | cast j => simp [swapConfig, extConfig]

/-- **Eq. (5.12)** for `e ∈ I_good^Z` and `j ∈ V` (Lemma 5.9 (4)): if `v^Z_{e,j,-} ≠ 0` then
`d^-_{e,j} ≤ 2 τ_j^{-,Z}`, `d_{e,bad} ≤ d^-_{e,j}` and `τ_j^{-,Z} > λ`, in the form of the
exchanged configuration. -/
theorem support_minus_Z {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam) (hM3 : 3 ≤ M)
    (hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z) {e : ℂ × ℂ} (he : IsGoodZ p₀ β lam M ε₀ V Z e)
    {j : Fin N} (hjV : j ∈ V)
    (hv : halfInteractionMinus χ lam (extRadiusPlus p₀ β lam ε₀ V Z e)
      (extRadiusMinus p₀ β lam ε₀ V Z e) (extConfig Z e) (Fin.last N) j.castSucc ≠ 0) :
    min ‖(extConfig Z e (Fin.last N)).1 - (extConfig Z e j.castSucc).2‖
        ‖(extConfig Z e (Fin.last N)).2 - (extConfig Z e j.castSucc).2‖ ≤
        2 * extRadiusMinus p₀ β lam ε₀ V Z e j.castSucc ∧
      badDistZ p₀ β lam ε₀ V Z e ≤
        min ‖(extConfig Z e (Fin.last N)).1 - (extConfig Z e j.castSucc).2‖
          ‖(extConfig Z e (Fin.last N)).2 - (extConfig Z e j.castSucc).2‖ ∧
      lam < extRadiusMinus p₀ β lam ε₀ V Z e j.castSucc := by
  have hsupp := halfInteractionMinus_ne_zero hχ hlam (lam_le_extRadiusPlus e)
    (lam_le_extRadiusMinus e) hv
  simp only [extConfig, extRadiusPlus, extRadiusMinus, Fin.lastCases_last,
    Fin.lastCases_castSucc] at hsupp ⊢
  refine geo_core_Z hlam hM3 he hjV (hVZ hjV) (dipoleDist_le_min_snd _ _)
    (lam_le_badRadiusMinusOn j) ?_
  rcases hsupp with h | h
  · exact (min_le_left _ _).trans_lt h
  · exact (min_le_right _ _).trans_lt h

end Support

/-! ### Lemma 5.11 on the support -/

/-- **Eq. (5.26) on the support of `𝖯^{+,ε₀,Z}`** (Lemma 5.11 for `I_good^Z`, proof of
Proposition 5.18): there is `C > 0`, depending on `χ` and `q(β)` only, such that for
`0 < λ ≤ ε₀ R̄`, `M ≥ max(3, 3^{p(β)})`, the frozen-configuration convention `V ⊆ I_bad^V(Z)` and
every `e ∈ I_good^Z` with `r_e ≤ ε₀ R̄`,
`∑_{j ∈ V} |v^Z(e, Z_j)| ≤ C r_e / d_{e,bad}`. -/
theorem sum_abs_interactionExtZ_le {χ : ℂ → ℝ} (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (lam M ε₀ : ℝ) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ),
      0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam → (3 : ℝ) ^ pBeta p₀ β ≤ M → 3 ≤ M →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ e : ℂ × ℂ, IsGoodZ p₀ β lam M ε₀ V Z e →
      ‖e.1 - e.2‖ ≤ ε₀ * truncationScale p₀ β lam →
        ∑ j ∈ V, |interactionExtZ χ p₀ β lam ε₀ V Z e j| ≤
          C * ‖e.1 - e.2‖ / badDistZ p₀ β lam ε₀ V Z e := by
  classical
  obtain ⟨C₀, hC₀, habs⟩ := sum_abs_halfInteractionPlus_le hχ
  set P := packingConstant (clusterThreshold p₀ β) 8
  refine ⟨2 * C₀ * P + 1, by positivity, ?_⟩
  intro N lam M ε₀ V Z hlam hlamh hM hM3 hVZ e he hr
  set D := badDistZ p₀ β lam ε₀ V Z e
  set τp := extRadiusPlus p₀ β lam ε₀ V Z e
  set τm := extRadiusMinus p₀ β lam ε₀ V Z e
  set d := extConfig Z e
  set T : Finset (Fin (N + 1)) := V.map Fin.castSuccEmb
  have hrD : ‖(d (Fin.last N)).1 - (d (Fin.last N)).2‖ ≤ D := by
    simp only [d, extConfig, Fin.lastCases_last]
    exact norm_le_badDistZ hlam hlamh hM hVZ he hr
  have hlamD : lam ≤ D := lam_le_badDistZ hlam hlamh hM hVZ he hr
  have hD : 0 < D := hlam.trans_le hlamD
  have hr' : ‖(d (Fin.last N)).1 - (d (Fin.last N)).2‖ = ‖e.1 - e.2‖ := by
    simp only [d, extConfig, Fin.lastCases_last]
  have heq : τp (Fin.last N) = τm (Fin.last N) := by
    simp only [τp, τm, extRadiusPlus, extRadiusMinus, Fin.lastCases_last]
  -- the reindexing of the sums over `V`
  have hsumT : ∀ f : Fin (N + 1) → ℝ, ∑ k ∈ T, f k = ∑ j ∈ V, f j.castSucc := fun f => by
    rw [Finset.sum_map]
    rfl
  -- the `+` part
  have hplus : ∑ k ∈ T, |halfInteractionPlus χ lam τp τm d (Fin.last N) k| ≤
      C₀ * P * (‖(d (Fin.last N)).1 - (d (Fin.last N)).2‖ / D) := by
    refine habs lam d τp τm T (Fin.last N) P D hlam (lam_le_extRadiusPlus e) heq hrD hlamD
      (fun t ht z => ?_) fun k hk hv => ?_
    · rw [Finset.filter_map, Finset.card_map]
      refine le_trans (le_of_eq ?_) (card_filter_badRadiusPlusOn_le (p₀ := p₀) (β := β)
        (ε₀ := ε₀) (V := V) (Z := Z) hlam ht 8 z)
      congr 1
      ext j
      simp [d, τp, extConfig, extRadiusPlus, Function.comp]
    · obtain ⟨j, hjV, rfl⟩ := Finset.mem_map.mp hk
      exact support_plus_Z hχ hlam hM3 hVZ he hjV hv
  -- the `-` part, through the exchanged configuration
  have hminus : ∑ k ∈ T, |halfInteractionMinus χ lam τp τm d (Fin.last N) k| ≤
      C₀ * P * (‖(d (Fin.last N)).1 - (d (Fin.last N)).2‖ / D) := by
    have hswap : ∀ k, |halfInteractionMinus χ lam τp τm d (Fin.last N) k| =
        |halfInteractionPlus χ lam τm τp (swapConfig d) (Fin.last N) k| := fun k => by
      rw [halfInteractionMinus_eq_neg_swap, abs_neg]
    simp only [hswap]
    have h := habs lam (swapConfig d) τm τp T (Fin.last N) P D hlam (lam_le_extRadiusMinus e)
      heq.symm (by rw [norm_swapConfig]; exact hrD) hlamD (fun t ht z => ?_) fun k hk hv => ?_
    · rwa [norm_swapConfig] at h
    · rw [Finset.filter_map, Finset.card_map]
      refine le_trans (le_of_eq ?_) (card_filter_badRadiusMinusOn_le (p₀ := p₀) (β := β)
        (ε₀ := ε₀) (V := V) (Z := Z) hlam ht 8 z)
      congr 1
      ext j
      simp [d, τm, swapConfig, extConfig, extRadiusMinus, Function.comp]
    · obtain ⟨j, hjV, rfl⟩ := Finset.mem_map.mp hk
      have hv' : halfInteractionMinus χ lam τp τm d (Fin.last N) j.castSucc ≠ 0 := by
        rw [halfInteractionMinus_eq_neg_swap]
        exact neg_ne_zero.mpr hv
      obtain ⟨h1, h2, h3⟩ := support_minus_Z hχ hlam hM3 hVZ he hjV hv'
      simp only [swapConfig]
      rw [min_comm]
      exact ⟨h1, h2, h3⟩
  have hsplit : ∑ j ∈ V, |interactionExtZ χ p₀ β lam ε₀ V Z e j| ≤
      ∑ k ∈ T, |halfInteractionPlus χ lam τp τm d (Fin.last N) k| +
        ∑ k ∈ T, |halfInteractionMinus χ lam τp τm d (Fin.last N) k| := by
    rw [hsumT, hsumT, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [interactionExtZ_eq]
    exact abs_sub _ _
  rw [hr'] at hplus hminus
  have hrD0 : 0 ≤ ‖e.1 - e.2‖ / D := div_nonneg (norm_nonneg _) hD.le
  rw [mul_div_assoc]
  nlinarith

end BoundedUpper

end UpperBound

end MultipoleBKT

end
