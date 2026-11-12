/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPoints.Clustering
public import MultipoleBKT.Main.TheoremTwo.GoodPoints
public import MultipoleBKT.Energy.BallGrowth
public import MultipoleBKT.Potential.DipoleInteraction
public import MultipoleBKT.Frozen.ClusterThreshold
public import MultipoleBKT.Frozen.TruncationScale

/-!
# Distances to the bad set and the radii of the reduced model (Definitions 5.7–5.8)

The paper: Definition 5.7 (Definition 5.7, eqs. (5.3),
(5.4)) and Definition 5.8 (Definition 5.8, eqs. (5.5), (5.6), (5.7),
(5.8)). Throughout `d : Fin N → ℂ × ℂ` is a dipole configuration, `d i = (x_i, y_i)`,
`r_i = |x_i - y_i|`, `I_bad = badPoints p₀ β λ M ε₀ d`, `I_good = goodPoints p₀ β λ M ε₀ d`,
`R̄ = truncationScale p₀ β λ` and `q(β) = clusterThreshold p₀ β` (on the event `{σ_N = Id}` the
dipoles are the matched pairs).

Definitions:

* `badDist`: `d_{i,bad} = min(dist({x_i, y_i}, Z_bad), 4 ε₀ R̄)`, eq. (5.3), with
  `Z_bad = {x_j, y_j : j ∈ I_bad}`. It is the minimum of the finite nonempty set consisting of
  the cap `4 ε₀ R̄` and the distances `d_ij` (`dipoleDist`) to the bad dipoles; when `I_bad = ∅`
  it is `4 ε₀ R̄`, the reading of the empty infimum as `+∞` in (5.3).
* `badDistSet`: `d_{S,bad} = inf_{i ∈ S} d_{i,bad}`, eq. (5.4), for nonempty `S`.
* `radiusPlusZ`, `radiusMinusZ`: `τ_i^{±,Z}`: `max(d_{i,bad}/4, λ)` for good `i` (eq. (5.5)),
  `max(τ_i^±, λ)` for bad `i`, where `τ_i^± = max(λ, removal value)` are the radii of the
  `q(β)`-clusterings of the positive and negative charges (Definition 5.1, `clusterRadius`).
* `halfInteractionPlus`, `halfInteractionMinus`: `v'_{i,j,±}` of eqs. (3.39), (3.40) for
  radii `τ^±`; `interactionPlusZ`, `interactionMinusZ`, `interactionZ`: `v^Z_{i,j,±}`,
  `v^Z_ij = v^Z_{i,j,+} - v^Z_{i,j,-}` (eqs. (5.6), (5.7), (5.8)), with the radii
  `τ^{±,Z}`.

Basic facts:

* `dipoleDist_le_add`: eq. (5.17) for two-point sets,
  `d(A, C) ≤ d(A, B) + diam(B) + d(B, C)`.
* `badDist_le_dipoleDist`, `badDist_le_cap`, `le_badDist`, `badDist_le_add` (eq. (5.22)).
* `not_multipoleLinked_of_good_of_bad`: Remark 5.6(1): a good and a bad dipole are not linked.
* `lam_le_radiusPlusZ`, `radiusPlusZ_le`, `radiusPlusZ_le_max_div`
  (Remark 5.10 for bad points), and the same for `τ^{-,Z}`; `radiusMinusZ_eq_radiusPlusZ` for
  good points.
* `interactionZ_eq_ballGrowthInteraction`: `v^Z_ij` is the `v'_ij` of Proposition 3.3 with the
  radii `τ^{±,Z}`; `interactionZ_comm` (symmetry).
* `halfInteractionPlus_ne_zero`: the support of `v'_{i,j,+}` (Newton's
  theorem), and its analogues.
-/

@[expose] public section

open Finset

namespace MultipoleBKT

namespace UpperBound

open TheoremTwo

variable {N : ℕ}

/-! ### The triangle inequality for two-point sets -/

theorem le_dipoleDist {a b : ℂ × ℂ} {x : ℝ} (h11 : x ≤ ‖a.1 - b.1‖) (h12 : x ≤ ‖a.1 - b.2‖)
    (h21 : x ≤ ‖a.2 - b.1‖) (h22 : x ≤ ‖a.2 - b.2‖) : x ≤ dipoleDist a b :=
  le_min (le_min h11 h12) (le_min h21 h22)

/-- **Eq. (5.17)** for two-point sets: `d(A, C) ≤ d(A, B) + diam(B) + d(B, C)`, with
`diam {b.1, b.2} = |b.1 - b.2|`. -/
theorem dipoleDist_le_add (a b c : ℂ × ℂ) :
    dipoleDist a c ≤ dipoleDist a b + ‖b.1 - b.2‖ + dipoleDist b c := by
  -- every pair of endpoints `s` of `a`, `t` of `b` and `t'` of `b`, `u` of `c`
  have key : ∀ s ∈ ({a.1, a.2} : Set ℂ), ∀ u ∈ ({c.1, c.2} : Set ℂ),
      ∀ t ∈ ({b.1, b.2} : Set ℂ), ∀ t' ∈ ({b.1, b.2} : Set ℂ),
        dipoleDist a c ≤ ‖s - t‖ + ‖b.1 - b.2‖ + ‖t' - u‖ := by
    intro s hs u hu t ht t' ht'
    have hsu : dipoleDist a c ≤ ‖s - u‖ := by
      rcases hs with rfl | rfl <;> rcases hu with rfl | rfl
      · exact dipoleDist_le_fst_fst a c
      · exact dipoleDist_le_fst_snd a c
      · exact dipoleDist_le_snd_fst a c
      · exact dipoleDist_le_snd_snd a c
    have htt' : ‖t - t'‖ ≤ ‖b.1 - b.2‖ := by
      rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
      · simp
      · exact le_rfl
      · rw [norm_sub_rev]
      · simp
    calc dipoleDist a c ≤ ‖s - u‖ := hsu
      _ = ‖(s - t) + (t - t') + (t' - u)‖ := by ring_nf
      _ ≤ ‖s - t‖ + ‖t - t'‖ + ‖t' - u‖ := norm_add₃_le
      _ ≤ ‖s - t‖ + ‖b.1 - b.2‖ + ‖t' - u‖ := by gcongr
  have hab : ∀ t' ∈ ({b.1, b.2} : Set ℂ), ∀ u ∈ ({c.1, c.2} : Set ℂ),
      dipoleDist a c - ‖b.1 - b.2‖ - ‖t' - u‖ ≤ dipoleDist a b := by
    intro t' ht' u hu
    have h1 := key a.1 (by simp) u hu b.1 (by simp) t' ht'
    have h2 := key a.1 (by simp) u hu b.2 (by simp) t' ht'
    have h3 := key a.2 (by simp) u hu b.1 (by simp) t' ht'
    have h4 := key a.2 (by simp) u hu b.2 (by simp) t' ht'
    refine le_dipoleDist ?_ ?_ ?_ ?_ <;> linarith
  have hbc : dipoleDist a c - ‖b.1 - b.2‖ - dipoleDist a b ≤ dipoleDist b c := by
    have h1 := hab b.1 (by simp) c.1 (by simp)
    have h2 := hab b.1 (by simp) c.2 (by simp)
    have h3 := hab b.2 (by simp) c.1 (by simp)
    have h4 := hab b.2 (by simp) c.2 (by simp)
    refine le_dipoleDist ?_ ?_ ?_ ?_ <;> linarith
  linarith

theorem dipoleDist_nonneg (a b : ℂ × ℂ) : 0 ≤ dipoleDist a b :=
  le_min (le_min (norm_nonneg _) (norm_nonneg _)) (le_min (norm_nonneg _) (norm_nonneg _))

/-- The distance of `{x_i, y_i}` to `x_j` is at least `d_ij`. -/
theorem dipoleDist_le_min_fst (a b : ℂ × ℂ) : dipoleDist a b ≤ min ‖a.1 - b.1‖ ‖a.2 - b.1‖ :=
  le_min (dipoleDist_le_fst_fst a b) (dipoleDist_le_snd_fst a b)

/-- The distance of `{x_i, y_i}` to `y_j` is at least `d_ij`. -/
theorem dipoleDist_le_min_snd (a b : ℂ × ℂ) : dipoleDist a b ≤ min ‖a.1 - b.2‖ ‖a.2 - b.2‖ :=
  le_min (dipoleDist_le_fst_snd a b) (dipoleDist_le_snd_snd a b)

/-! ### Definition 5.7 -/

/-- **`d_{i,bad}`**, eq. (5.3) (Definition 5.7):
`d_{i,bad} = min(dist({x_i, y_i}, Z_bad), 4 ε₀ R̄)`, `Z_bad = {x_j, y_j : j ∈ I_bad}`: the minimum
of the cap `4 ε₀ R̄` and of the distances `d_ij` to the bad dipoles (the cap alone when
`I_bad = ∅`). The paper uses it for `i ∈ I_good`. -/
noncomputable def badDist (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) (i : Fin N) : ℝ :=
  (insert (4 * (ε₀ * truncationScale p₀ β lam))
    ((badPoints p₀ β lam M ε₀ d).image fun j => dipoleDist (d i) (d j))).min'
      (Finset.insert_nonempty _ _)

/-- **`d_{S,bad}`**, eq. (5.4) (Definition 5.7): `inf_{i ∈ S} d_{i,bad}`, for a
nonempty set `S` (of good labels in the paper). -/
noncomputable def badDistSet (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) (S : Finset (Fin N))
    (hS : S.Nonempty) : ℝ :=
  S.inf' hS (badDist p₀ β lam M ε₀ d)

section BadDist

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

theorem badDist_le_cap (i : Fin N) :
    badDist p₀ β lam M ε₀ d i ≤ 4 * (ε₀ * truncationScale p₀ β lam) :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem badDist_le_dipoleDist (i : Fin N) {j : Fin N} (hj : j ∈ badPoints p₀ β lam M ε₀ d) :
    badDist p₀ β lam M ε₀ d i ≤ dipoleDist (d i) (d j) :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj))

theorem le_badDist {i : Fin N} {a : ℝ} (hcap : a ≤ 4 * (ε₀ * truncationScale p₀ β lam))
    (hbad : ∀ j ∈ badPoints p₀ β lam M ε₀ d, a ≤ dipoleDist (d i) (d j)) :
    a ≤ badDist p₀ β lam M ε₀ d i := by
  refine Finset.le_min' _ _ _ fun y hy => ?_
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact hcap
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hbad j hj

/-- `d_{i,bad}` is the cap or the distance to some bad dipole. -/
theorem badDist_eq_cap_or (i : Fin N) :
    badDist p₀ β lam M ε₀ d i = 4 * (ε₀ * truncationScale p₀ β lam) ∨
      ∃ j ∈ badPoints p₀ β lam M ε₀ d, badDist p₀ β lam M ε₀ d i = dipoleDist (d i) (d j) := by
  have hmem := Finset.min'_mem (insert (4 * (ε₀ * truncationScale p₀ β lam))
    ((badPoints p₀ β lam M ε₀ d).image fun j => dipoleDist (d i) (d j)))
      (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hmem with h | h
  · exact Or.inl h
  · obtain ⟨j, hj, hj'⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨j, hj, hj'.symm⟩

theorem badDist_nonneg (hcap : 0 ≤ ε₀ * truncationScale p₀ β lam) (i : Fin N) :
    0 ≤ badDist p₀ β lam M ε₀ d i :=
  le_badDist (by linarith) fun _ _ => dipoleDist_nonneg _ _

/-- **Eq. (5.22)**: `d_{j,bad} ≤ d_{i,bad} + r_i + d_ij`. -/
theorem badDist_le_add (i j : Fin N) :
    badDist p₀ β lam M ε₀ d j ≤
      badDist p₀ β lam M ε₀ d i + ‖(d i).1 - (d i).2‖ + dipoleDist (d i) (d j) := by
  have h1 := norm_nonneg ((d i).1 - (d i).2)
  have h2 := dipoleDist_nonneg (d i) (d j)
  rcases badDist_eq_cap_or (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (d := d) i with
    hi | ⟨l, hl, hi⟩
  · have := badDist_le_cap (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (d := d) j
    linarith
  · have h3 := badDist_le_dipoleDist (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀)
      (d := d) j hl
    have h4 := dipoleDist_le_add (d j) (d i) (d l)
    rw [dipoleDist_comm (d j) (d i)] at h4
    linarith

end BadDist

/-! ### Remark 5.6 (1): good and bad dipoles are not linked -/

section Separation

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

/-- **Remark 5.6 (1)**: a good dipole and a bad dipole are not linked by `↔`
(`I_bad` is a union of full multipoles). -/
theorem not_multipoleLinked_of_good_of_bad (hM : 0 ≤ M) {i j : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hj : j ∈ badPoints p₀ β lam M ε₀ d) :
    ¬ MultipoleLinked M lam (d i) (d j) := by
  intro hlink
  have hj' : j ∉ goodPoints p₀ β lam M ε₀ d := fun h =>
    (Finset.mem_sdiff.mp h).2 hj
  have hne : i ≠ j := by
    rintro rfl
    exact hj' hi
  have hreach : (linkGraph M lam d).Reachable i j := by
    refine SimpleGraph.Adj.reachable ?_
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hne, Or.inl hlink⟩
  exact hj' (good_of_mem_classOn hi ((reachable_iff_mem_classOn hM hi).mp hreach))

/-- Remark 5.6 (1) as a distance bound: `d_ij > M max(min(r_i, r_j), λ)` for `i` good and `j`
bad. -/
theorem lt_dipoleDist_of_good_of_bad (hM : 0 ≤ M) {i j : Fin N}
    (hi : i ∈ goodPoints p₀ β lam M ε₀ d) (hj : j ∈ badPoints p₀ β lam M ε₀ d) :
    M * min (max ‖(d i).1 - (d i).2‖ lam) (max ‖(d j).1 - (d j).2‖ lam) <
      dipoleDist (d i) (d j) := by
  have := not_multipoleLinked_of_good_of_bad hM hi hj
  rw [MultipoleLinked, not_le] at this
  exact this

theorem not_mem_badPoints_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    i ∉ badPoints p₀ β lam M ε₀ d :=
  (Finset.mem_sdiff.mp hi).2

theorem mem_goodPoints_of_not_bad {i : Fin N} (hi : i ∉ badPoints p₀ β lam M ε₀ d) :
    i ∈ goodPoints p₀ β lam M ε₀ d :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩

/-- A label that is not of type 1 has `r_i ≤ ε₀ R̄`. -/
theorem norm_le_of_not_mem_badPointsTypeOne {i : Fin N}
    (hi : i ∉ badPointsTypeOne p₀ β lam ε₀ d) :
    ‖(d i).1 - (d i).2‖ ≤ ε₀ * truncationScale p₀ β lam := by
  classical
  by_contra h
  apply hi
  unfold badPointsTypeOne
  simp only
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp h⟩

/-- **Remark 5.6 (2)**: a good dipole has `r_i ≤ ε₀ R̄`. -/
theorem norm_le_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    ‖(d i).1 - (d i).2‖ ≤ ε₀ * truncationScale p₀ β lam :=
  norm_le_of_not_mem_badPointsTypeOne (mem_goodPoints_iff.mp hi).1

end Separation

/-! ### Definition 5.8: the radii -/

/-- The cutoff `h = ε₀ R̄` of the clustering. -/
noncomputable abbrev clusterCutoff (p₀ : ℕ) (β lam ε₀ : ℝ) : ℝ :=
  ε₀ * truncationScale p₀ β lam

/-- **`τ_i^{+,Z}`** (Definition 5.8): `max(d_{i,bad}/4, λ)` for `i ∈ I_good`
(eq. (5.5)) and `max(τ_i^+, λ)` for `i ∈ I_bad`, where `τ_i^+` is the radius of the
`q(β)`-clustering of the positive charges (Definition 5.1, cutoff `ε₀ R̄`). -/
noncomputable def radiusPlusZ (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) (i : Fin N) : ℝ :=
  if i ∈ goodPoints p₀ β lam M ε₀ d then max (badDist p₀ β lam M ε₀ d i / 4) lam
  else max (clusterRadius (clusterThreshold p₀ β) (clusterCutoff p₀ β lam ε₀) lam
    (fun k => (d k).1) (fun k => ‖(d k).1 - (d k).2‖) i) lam

/-- **`τ_i^{-,Z}`** (Definition 5.8): `max(d_{i,bad}/4, λ)` for `i ∈ I_good` and
`max(τ_i^-, λ)` for `i ∈ I_bad`, where `τ_i^-` is the radius of the `q(β)`-clustering of the
negative charges. -/
noncomputable def radiusMinusZ (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) (i : Fin N) : ℝ :=
  if i ∈ goodPoints p₀ β lam M ε₀ d then max (badDist p₀ β lam M ε₀ d i / 4) lam
  else max (clusterRadius (clusterThreshold p₀ β) (clusterCutoff p₀ β lam ε₀) lam
    (fun k => (d k).2) (fun k => ‖(d k).1 - (d k).2‖) i) lam

/-! ### The half-interactions -/

/-- `v'_{i,j,+}` of eq. (3.39) for radii `τ^±`:
`(g_λ - g * δ₀^{(τ_i^+)} * δ₀^{(τ_j^+)})(x_i - x_j)
  - (g_λ - g * δ₀^{(τ_i^-)} * δ₀^{(τ_j^+)})(y_i - x_j)`. -/
noncomputable def halfInteractionPlus (χ : ℂ → ℝ) (lam : ℝ) (τp τm : Fin N → ℝ)
    (d : Fin N → ℂ × ℂ) (i j : Fin N) : ℝ :=
  (smearedKernel χ lam ((d i).1 - (d j).1) -
      twoRadiusKernel χ (τp i) (τp j) ((d i).1 - (d j).1)) -
    (smearedKernel χ lam ((d i).2 - (d j).1) -
      twoRadiusKernel χ (τm i) (τp j) ((d i).2 - (d j).1))

/-- `v'_{i,j,-}` of eq. (3.40) for radii `τ^±`:
`(g_λ - g * δ₀^{(τ_i^+)} * δ₀^{(τ_j^-)})(x_i - y_j)
  - (g_λ - g * δ₀^{(τ_i^-)} * δ₀^{(τ_j^-)})(y_i - y_j)`. -/
noncomputable def halfInteractionMinus (χ : ℂ → ℝ) (lam : ℝ) (τp τm : Fin N → ℝ)
    (d : Fin N → ℂ × ℂ) (i j : Fin N) : ℝ :=
  (smearedKernel χ lam ((d i).1 - (d j).2) -
      twoRadiusKernel χ (τp i) (τm j) ((d i).1 - (d j).2)) -
    (smearedKernel χ lam ((d i).2 - (d j).2) -
      twoRadiusKernel χ (τm i) (τm j) ((d i).2 - (d j).2))

/-- **`v^Z_{i,j,+}`**, eq. (5.6): `v'_{i,j,+}` with the radii `τ^{±,Z}`. -/
noncomputable def interactionPlusZ (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) : ℝ :=
  halfInteractionPlus χ lam (radiusPlusZ p₀ β lam M ε₀ d) (radiusMinusZ p₀ β lam M ε₀ d) d i j

/-- **`v^Z_{i,j,-}`**, eq. (5.7): `v'_{i,j,-}` with the radii `τ^{±,Z}`. -/
noncomputable def interactionMinusZ (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) : ℝ :=
  halfInteractionMinus χ lam (radiusPlusZ p₀ β lam M ε₀ d) (radiusMinusZ p₀ β lam M ε₀ d) d i j

/-- **`v^Z_ij = v^Z_{i,j,+} - v^Z_{i,j,-}`**, eq. (5.8). -/
noncomputable def interactionZ (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) : ℝ :=
  interactionPlusZ χ p₀ β lam M ε₀ d i j - interactionMinusZ χ p₀ β lam M ε₀ d i j

/-! ### Facts about the radii -/

section RadiiFacts

variable {p₀ : ℕ} {β lam M ε₀ : ℝ} {d : Fin N → ℂ × ℂ}

theorem radiusPlusZ_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    radiusPlusZ p₀ β lam M ε₀ d i = max (badDist p₀ β lam M ε₀ d i / 4) lam := by
  rw [radiusPlusZ, ite_eq_left hi]

theorem radiusMinusZ_of_good {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    radiusMinusZ p₀ β lam M ε₀ d i = max (badDist p₀ β lam M ε₀ d i / 4) lam := by
  rw [radiusMinusZ, ite_eq_left hi]

/-- For good points `τ_i^{+,Z} = τ_i^{-,Z}` (Definition 5.8). -/
theorem radiusMinusZ_eq_radiusPlusZ {i : Fin N} (hi : i ∈ goodPoints p₀ β lam M ε₀ d) :
    radiusMinusZ p₀ β lam M ε₀ d i = radiusPlusZ p₀ β lam M ε₀ d i := by
  rw [radiusPlusZ_of_good hi, radiusMinusZ_of_good hi]

theorem radiusPlusZ_of_bad {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    radiusPlusZ p₀ β lam M ε₀ d i =
      max (clusterRemovalValue (clusterThreshold p₀ β) (clusterCutoff p₀ β lam ε₀)
        (fun k => (d k).1) (fun k => ‖(d k).1 - (d k).2‖) i) lam := by
  have : i ∉ goodPoints p₀ β lam M ε₀ d := fun h => not_mem_badPoints_of_good h hi
  rw [radiusPlusZ, ite_eq_right this, clusterRadius, max_comm lam, max_assoc, max_self]

theorem radiusMinusZ_of_bad {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    radiusMinusZ p₀ β lam M ε₀ d i =
      max (clusterRemovalValue (clusterThreshold p₀ β) (clusterCutoff p₀ β lam ε₀)
        (fun k => (d k).2) (fun k => ‖(d k).1 - (d k).2‖) i) lam := by
  have : i ∉ goodPoints p₀ β lam M ε₀ d := fun h => not_mem_badPoints_of_good h hi
  rw [radiusMinusZ, ite_eq_right this, clusterRadius, max_comm lam, max_assoc, max_self]

theorem lam_le_radiusPlusZ (i : Fin N) : lam ≤ radiusPlusZ p₀ β lam M ε₀ d i := by
  unfold radiusPlusZ
  split_ifs <;> exact le_max_right _ _

theorem lam_le_radiusMinusZ (i : Fin N) : lam ≤ radiusMinusZ p₀ β lam M ε₀ d i := by
  unfold radiusMinusZ
  split_ifs <;> exact le_max_right _ _

/-- **Range of the radii** (Definition 5.8): `τ_i^{+,Z} ≤ ε₀ R̄` when
`λ ≤ ε₀ R̄`. -/
theorem radiusPlusZ_le (hlam : lam ≤ clusterCutoff p₀ β lam ε₀) (i : Fin N) :
    radiusPlusZ p₀ β lam M ε₀ d i ≤ clusterCutoff p₀ β lam ε₀ := by
  unfold radiusPlusZ
  split_ifs
  · refine max_le ?_ hlam
    have := badDist_le_cap (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (d := d) i
    linarith
  · exact max_le (clusterRadius_le lam hlam i) hlam

theorem radiusMinusZ_le (hlam : lam ≤ clusterCutoff p₀ β lam ε₀) (i : Fin N) :
    radiusMinusZ p₀ β lam M ε₀ d i ≤ clusterCutoff p₀ β lam ε₀ := by
  unfold radiusMinusZ
  split_ifs
  · refine max_le ?_ hlam
    have := badDist_le_cap (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) (d := d) i
    linarith
  · exact max_le (clusterRadius_le lam hlam i) hlam

/-- **Remark 5.10, bad points**: `τ_i^{+,Z} ≤ max(r_i/4, λ)` for `i ∈ I_bad`. -/
theorem radiusPlusZ_le_max_div {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    radiusPlusZ p₀ β lam M ε₀ d i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam := by
  rw [radiusPlusZ_of_bad hi]
  exact max_le_max (clusterRemovalValue_le_div i) le_rfl

theorem radiusMinusZ_le_max_div {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d) :
    radiusMinusZ p₀ β lam M ε₀ d i ≤ max (‖(d i).1 - (d i).2‖ / 4) lam := by
  rw [radiusMinusZ_of_bad hi]
  exact max_le_max (clusterRemovalValue_le_div i) le_rfl

/-- **Remark 5.10, bad points**: if `r_i / 4 < λ` then
`τ_i^{+,Z} = τ_i^{-,Z} = λ` (and `r_i ≤ 2(τ_i^{+,Z} + τ_i^{-,Z})`). -/
theorem radiusPlusZ_eq_lam_of_bad {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d)
    (hr : ‖(d i).1 - (d i).2‖ / 4 < lam) : radiusPlusZ p₀ β lam M ε₀ d i = lam :=
  le_antisymm ((radiusPlusZ_le_max_div hi).trans (max_le hr.le le_rfl)) (lam_le_radiusPlusZ i)

theorem radiusMinusZ_eq_lam_of_bad {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d)
    (hr : ‖(d i).1 - (d i).2‖ / 4 < lam) : radiusMinusZ p₀ β lam M ε₀ d i = lam :=
  le_antisymm ((radiusMinusZ_le_max_div hi).trans (max_le hr.le le_rfl)) (lam_le_radiusMinusZ i)

/-- **Remark 5.10, bad points**: if `r_i / 4 ≥ λ` then
`2(τ_i^{+,Z} + τ_i^{-,Z}) ≤ r_i`. -/
theorem two_mul_add_le_of_bad {i : Fin N} (hi : i ∈ badPoints p₀ β lam M ε₀ d)
    (hr : lam ≤ ‖(d i).1 - (d i).2‖ / 4) :
    2 * (radiusPlusZ p₀ β lam M ε₀ d i + radiusMinusZ p₀ β lam M ε₀ d i) ≤
      ‖(d i).1 - (d i).2‖ := by
  have h1 := radiusPlusZ_le_max_div hi
  have h2 := radiusMinusZ_le_max_div hi
  rw [max_eq_left hr] at h1 h2
  linarith

end RadiiFacts

/-! ### Facts about the interactions -/

section InteractionFacts

variable {χ : ℂ → ℝ} {lam : ℝ}

/-- `v'_ij = v'_{i,j,+} - v'_{i,j,-}`: the interaction of Proposition 3.3 (eq. (3.6)). -/
theorem halfInteractionPlus_sub_halfInteractionMinus (τp τm : Fin N → ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) :
    halfInteractionPlus χ lam τp τm d i j - halfInteractionMinus χ lam τp τm d i j =
      ballGrowthInteraction χ lam τp τm d i j := by
  unfold halfInteractionPlus halfInteractionMinus ballGrowthInteraction
  ring

/-- `v^Z_ij` is the interaction `v'_ij` of Proposition 3.3 with the radii `τ^{±,Z}`. -/
theorem interactionZ_eq_ballGrowthInteraction (p₀ : ℕ) (β M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) :
    interactionZ χ p₀ β lam M ε₀ d i j = ballGrowthInteraction χ lam
      (radiusPlusZ p₀ β lam M ε₀ d) (radiusMinusZ p₀ β lam M ε₀ d) d i j :=
  halfInteractionPlus_sub_halfInteractionMinus _ _ d i j

/-- `v'_ij = v'_ji`. -/
theorem ballGrowthInteraction_comm (hχ : IsMollifier χ) (τp τm : Fin N → ℝ)
    (d : Fin N → ℂ × ℂ) (i j : Fin N) :
    ballGrowthInteraction χ lam τp τm d i j = ballGrowthInteraction χ lam τp τm d j i := by
  unfold ballGrowthInteraction
  have eg : ∀ a b : ℂ, smearedKernel χ lam (a - b) = smearedKernel χ lam (b - a) := fun a b => by
    rw [← neg_sub b a, smearedKernel_neg hχ]
  have eK : ∀ α η : ℝ, ∀ a b : ℂ, twoRadiusKernel χ α η (a - b) = twoRadiusKernel χ η α (b - a) :=
    fun α η a b => by rw [← neg_sub b a, twoRadiusKernel_neg hχ, twoRadiusKernel_comm hχ]
  rw [eg (d i).1 (d j).1, eg (d i).2 (d j).2, eg (d i).2 (d j).1, eg (d i).1 (d j).2,
    eK (τp i) (τp j) (d i).1 (d j).1, eK (τm i) (τm j) (d i).2 (d j).2,
    eK (τm i) (τp j) (d i).2 (d j).1, eK (τp i) (τm j) (d i).1 (d j).2]
  ring

/-- `v^Z_ij = v^Z_ji` (used without comment in the proof of Lemma 5.12). -/
theorem interactionZ_comm (hχ : IsMollifier χ) (p₀ : ℕ) (β M ε₀ : ℝ) (d : Fin N → ℂ × ℂ)
    (i j : Fin N) :
    interactionZ χ p₀ β lam M ε₀ d i j = interactionZ χ p₀ β lam M ε₀ d j i := by
  rw [interactionZ_eq_ballGrowthInteraction, interactionZ_eq_ballGrowthInteraction,
    ballGrowthInteraction_comm hχ]

/-- **Support of `v'_{i,j,+}`** (Section 5.2; Newton's theorem): for radii
`≥ λ > 0`, if `v'_{i,j,+} ≠ 0` then `|x_i - x_j| < τ_i^+ + τ_j^+` or
`|y_i - x_j| < τ_i^- + τ_j^+`. -/
theorem halfInteractionPlus_ne_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    {τp τm : Fin N → ℝ} (hp : ∀ k, lam ≤ τp k) (hm : ∀ k, lam ≤ τm k) {d : Fin N → ℂ × ℂ}
    {i j : Fin N} (h : halfInteractionPlus χ lam τp τm d i j ≠ 0) :
    ‖(d i).1 - (d j).1‖ < τp i + τp j ∨ ‖(d i).2 - (d j).1‖ < τm i + τp j := by
  by_contra hc
  push Not at hc
  apply h
  unfold halfInteractionPlus
  rw [smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam (hp i) (hp j) hc.1,
    smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam (hm i) (hp j) hc.2, sub_zero]

/-- **Support of `v'_{i,j,-}`** (Newton's theorem): if `v'_{i,j,-} ≠ 0` then
`|x_i - y_j| < τ_i^+ + τ_j^-` or `|y_i - y_j| < τ_i^- + τ_j^-`. -/
theorem halfInteractionMinus_ne_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    {τp τm : Fin N → ℝ} (hp : ∀ k, lam ≤ τp k) (hm : ∀ k, lam ≤ τm k) {d : Fin N → ℂ × ℂ}
    {i j : Fin N} (h : halfInteractionMinus χ lam τp τm d i j ≠ 0) :
    ‖(d i).1 - (d j).2‖ < τp i + τm j ∨ ‖(d i).2 - (d j).2‖ < τm i + τm j := by
  by_contra hc
  push Not at hc
  apply h
  unfold halfInteractionMinus
  rw [smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam (hp i) (hm j) hc.1,
    smearedKernel_sub_twoRadiusKernel_eq_zero hχ hlam (hm i) (hm j) hc.2, sub_zero]

/-- **Support of `v'_ij`** (Newton's theorem): if `v'_ij ≠ 0` then some endpoint of `i` and
some endpoint of `j` are closer than the sum of their radii; in particular
`d_ij < max(τ_i^+, τ_i^-) + max(τ_j^+, τ_j^-)`. -/
theorem dipoleDist_lt_of_ballGrowthInteraction_ne_zero (hχ : IsMollifier χ) (hlam : 0 < lam)
    {τp τm : Fin N → ℝ} (hp : ∀ k, lam ≤ τp k) (hm : ∀ k, lam ≤ τm k) {d : Fin N → ℂ × ℂ}
    {i j : Fin N} (h : ballGrowthInteraction χ lam τp τm d i j ≠ 0) :
    dipoleDist (d i) (d j) < max (τp i) (τm i) + max (τp j) (τm j) := by
  rw [← halfInteractionPlus_sub_halfInteractionMinus] at h
  have hpi := le_max_left (τp i) (τm i)
  have hmi := le_max_right (τp i) (τm i)
  have hpj := le_max_left (τp j) (τm j)
  have hmj := le_max_right (τp j) (τm j)
  by_cases hplus : halfInteractionPlus χ lam τp τm d i j = 0
  · rw [hplus, zero_sub, neg_ne_zero] at h
    rcases halfInteractionMinus_ne_zero hχ hlam hp hm h with h' | h'
    · linarith [dipoleDist_le_fst_snd (d i) (d j)]
    · linarith [dipoleDist_le_snd_snd (d i) (d j)]
  · rcases halfInteractionPlus_ne_zero hχ hlam hp hm hplus with h' | h'
    · linarith [dipoleDist_le_fst_fst (d i) (d j)]
    · linarith [dipoleDist_le_snd_fst (d i) (d j)]

end InteractionFacts

end UpperBound

end MultipoleBKT

end
