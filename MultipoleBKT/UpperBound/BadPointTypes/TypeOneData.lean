/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.ClusterShape
public import MultipoleBKT.UpperBound.BadPointTypes.Dematch

/-!
# Lemma 5.40: the combinatorial data of a configuration of bad points of type 1

The paper: Lemma 5.40,
Steps 2–5. After removing the pairing, the integrand is evaluated at the matched dipoles
`(x_i, y_{σ(i)})_i`. The charge data retain the geometric factors in (5.124)
 and the dyadic bound (5.128).

Each charge is an overcrowded root (`0`), a long singleton (`1`), an overcrowded member (`2`)
or a good partner (`3`). Its parent is its same-sign representative, itself for a long
singleton, or its opposite-sign partner for a good charge. Scales are recorded only at
overcrowded roots. This representation remains the fixed-data integration interface.

`RouteTypeOne/` projects these data onto the successive bad sets, partner injections
and same-sign partitions of (5.125), (5.126) and (5.127). The four charge kinds are counted through these successive choices.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset MeasureTheory UpperBound TheoremTwo
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {n : ℕ}

/-! ### The cluster of a charge -/

section ClusterOf

variable (q : ℕ) (h : ℝ) (z : Fin n → ℂ) (r : Fin n → ℝ)

/-- The cluster containing `i` in the full `q`-clustering of `(z, r)`. -/
noncomputable def clusterOf (i : Fin n) : Finset (Fin n) := by
  classical
  exact ((sameSignClustering q h z r Finset.univ).filter fun p => i ∈ p.1).biUnion Prod.fst

variable {q h z r}

theorem clusterOf_spec (i : Fin n) :
    ∃ p ∈ sameSignClustering q h z r Finset.univ, i ∈ p.1 ∧ clusterOf q h z r i = p.1 ∧
      clusterRemovalValue q h z r i = p.2 := by
  classical
  obtain ⟨p, hp, hip, hpi⟩ := exists_mem_clustering_univ (q := q) (h := h) (z := z) (r := r) i
  refine ⟨p, hp, hip, ?_, hpi.symm⟩
  unfold clusterOf
  ext j
  simp only [mem_biUnion, mem_filter]
  constructor
  · rintro ⟨p', ⟨hp', hip'⟩, hj⟩
    rwa [eq_of_mem_clustering _ p' hp' p hp i hip' hip] at hj
  · intro hj
    exact ⟨p, ⟨hp, hip⟩, hj⟩

theorem mem_clusterOf_self (i : Fin n) : i ∈ clusterOf q h z r i := by
  obtain ⟨p, -, hip, hp, -⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
  rw [hp]
  exact hip

theorem clusterOf_eq_of_mem {i j : Fin n} (hj : j ∈ clusterOf q h z r i) :
    clusterOf q h z r j = clusterOf q h z r i ∧
      clusterRemovalValue q h z r j = clusterRemovalValue q h z r i := by
  obtain ⟨p, hp, hip, hpi, hτi⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
  obtain ⟨p', hp', hjp', hpj, hτj⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) j
  rw [hpi] at hj
  have := eq_of_mem_clustering _ p' hp' p hp j hjp' hj
  rw [hpj, hpi, hτj, hτi, this]
  exact ⟨rfl, rfl⟩

theorem clusterOf_nonempty (i : Fin n) : (clusterOf q h z r i).Nonempty :=
  ⟨i, mem_clusterOf_self i⟩

/-- The set `J^{1,±}` of the frozen definition: a label is in it iff its dipole is long or its
cluster has `q + 1` elements. -/
theorem mem_J_iff (i : Fin n) :
    (i ∈ Finset.univ.filter (fun i => h < r i) ∪
      ((sameSignClustering q h z r Finset.univ).filter
        (fun Sτ => Sτ.1.card = q + 1)).biUnion Prod.fst) ↔
      h < r i ∨ (clusterOf q h z r i).card = q + 1 := by
  classical
  simp only [mem_union, mem_filter, mem_univ, true_and, mem_biUnion]
  refine or_congr_right ⟨fun ⟨p, ⟨hp, hcard⟩, hip⟩ => ?_, fun hcard => ?_⟩
  · obtain ⟨p', hp', hip', hpi', -⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
    rw [hpi', eq_of_mem_clustering _ p' hp' p hp i hip' hip]
    exact hcard
  · obtain ⟨p, hp, hip, hpi, -⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
    exact ⟨p, ⟨hp, hpi ▸ hcard⟩, hip⟩

/-- **The trichotomy** (Lemma 5.40): without isosceles coincidences, the cluster of `i` is
either overcrowded (`q + 1` charges within `4τ` of its smallest label) or the singleton `{i}`,
removed at `r_i / 4` if `r_i ≤ h` and at least at `h / 4` otherwise. -/
theorem clusterOf_cases (hq : 1 ≤ q) (hh : 0 < h) (hr : ∀ i, 0 ≤ r i) (hz : NoIsosceles z)
    (i : Fin n) :
    ((clusterOf q h z r i).card = q + 1 ∧ ∀ j ∈ clusterOf q h z r i, ∀ m ∈ clusterOf q h z r i,
        ‖z j - z m‖ ≤ 4 * clusterRemovalValue q h z r i) ∨
      ((clusterOf q h z r i).card ≠ q + 1 ∧ clusterOf q h z r i = {i} ∧
        (r i ≤ h → clusterRemovalValue q h z r i = r i / 4) ∧
        (h < r i → h / 4 ≤ clusterRemovalValue q h z r i)) := by
  obtain ⟨p, hp, hip, hpi, hτ⟩ := clusterOf_spec (q := q) (h := h) (z := z) (r := r) i
  rcases clusterShape hq hh hr hz Finset.univ p hp with ⟨i', hi', h1, h2⟩ | ⟨hcard, c, hc, hgeo⟩
  · right
    have hii' : i = i' := by rw [hi'] at hip; exact mem_singleton.1 hip
    subst hii'
    rw [hpi, hi', hτ, card_singleton]
    exact ⟨by omega, rfl, h1, h2⟩
  · left
    rw [hpi, hτ]
    refine ⟨hcard, fun j hj m hm => ?_⟩
    calc ‖z j - z m‖ ≤ ‖z j - z c‖ + ‖z c - z m‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * p.2 + 2 * p.2 := by
          gcongr
          · exact hgeo j hj
          · rw [norm_sub_rev]; exact hgeo _ hm
      _ = 4 * p.2 := by ring

end ClusterOf

/-! ### Charges, data and factors -/

/-- The `2n` charges: `inl i` is the positive charge `x_i`, `inr j` the negative charge `y_j`. -/
abbrev Charge (n : ℕ) := Fin n ⊕ Fin n

/-- The positions of the charges of a configuration. -/
def chargePos (c : Fin n → ℂ × ℂ) : Charge n → ℂ :=
  Sum.elim (fun i => (c i).1) (fun j => (c j).2)

/-- The data `(kind, par, sc)`: the kind of each charge (`0` overcrowded root, `1` long
singleton, `2` overcrowded member, `3` good), its parent and the dyadic scale index of each
overcrowded root. -/
abbrev TOData (n : ℕ) := (Charge n → Fin 4) × (Charge n → Charge n) × (Charge n → ℕ)

/-- The dyadic scales `λ 2^s` (the set `D` in Lemma 5.40). -/
noncomputable def dyad (lam : ℝ) (s : ℕ) : ℝ := lam * 2 ^ s

/-- The dyadic scale index of `τ ≥ λ`: `λ 2^s ≤ τ < λ 2^{s+1}`. -/
noncomputable def scaleIdx (lam τ : ℝ) : ℕ := Nat.log 2 ⌊τ / lam⌋₊

theorem dyad_scaleIdx_le {lam τ : ℝ} (hlam : 0 < lam) (hτ : lam ≤ τ) :
    dyad lam (scaleIdx lam τ) ≤ τ := by
  unfold dyad scaleIdx
  have h1 : (1 : ℝ) ≤ τ / lam := by rw [le_div_iff₀ hlam]; linarith
  have hfl : ⌊τ / lam⌋₊ ≠ 0 := by
    have := Nat.floor_pos.2 h1
    omega
  have h2 : ((2 ^ Nat.log 2 ⌊τ / lam⌋₊ : ℕ) : ℝ) ≤ τ / lam :=
    (Nat.cast_le.2 (Nat.pow_log_le_self 2 hfl)).trans (Nat.floor_le (by linarith))
  push_cast at h2
  rw [le_div_iff₀ hlam] at h2
  linarith

theorem lt_two_mul_dyad_scaleIdx {lam τ : ℝ} (hlam : 0 < lam) (hτ : lam ≤ τ) :
    τ < 2 * dyad lam (scaleIdx lam τ) := by
  unfold dyad scaleIdx
  have h0 : 0 ≤ τ / lam := div_nonneg (hlam.le.trans hτ) hlam.le
  have h2 : τ / lam < ((2 ^ (Nat.log 2 ⌊τ / lam⌋₊).succ : ℕ) : ℝ) :=
    (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) _)
  push_cast at h2
  rw [div_lt_iff₀ hlam, pow_succ] at h2
  linarith

theorem scaleIdx_le {lam τ h : ℝ} (hlam : 0 < lam) (hτh : τ ≤ h) :
    scaleIdx lam τ ≤ Nat.log 2 ⌊h / lam⌋₊ :=
  Nat.log_mono_right (Nat.floor_le_floor (div_le_div_of_nonneg_right hτh hlam.le))

/-- The factor of the charge `v` in the bound on the integrand (Lemma 5.40, the integrand `J`): `𝟙_Λ(z_v) d^{-β/2}` for an overcrowded root at scale `d`, and `𝟙_Λ(z_v) (h/4)^{-β/2}`
for a long singleton. An overcrowded member contributes
`𝟙_{|z_v - z_{par v}| ≤ 8d} d^{-β/2}`. A good charge contributes
`𝟙_{|z_v - z_{par v}| ≤ h} max(|z_v - z_{par v}|/4, λ)^{-β/2}`. -/
noncomputable def typeOneFactor (β lam h : ℝ) (Nₐ : ℕ) (D : TOData n) (z : Charge n → ℂ)
    (v : Charge n) : ℝ≥0∞ :=
  if D.1 v = 0 then (box Nₐ).indicator 1 (z v) * ENNReal.ofReal (dyad lam (D.2.2 v) ^ (-(β / 2)))
  else if D.1 v = 1 then (box Nₐ).indicator 1 (z v) * ENNReal.ofReal ((h / 4) ^ (-(β / 2)))
  else if D.1 v = 2 then
    (Metric.closedBall (0 : ℂ) (8 * dyad lam (D.2.2 (D.2.1 v)))).indicator 1 (z v - z (D.2.1 v)) *
      ENNReal.ofReal (dyad lam (D.2.2 (D.2.1 v)) ^ (-(β / 2)))
  else (Metric.closedBall (0 : ℂ) h).indicator
    (fun u => ENNReal.ofReal (max (‖u‖ / 4) lam ^ (-(β / 2)))) (z v - z (D.2.1 v))

/-- The constraints satisfied by the data of a configuration. -/
def TypeOneValid (q : ℕ) (D : TOData n) : Prop :=
  (∀ v, D.1 v = 2 → D.1 (D.2.1 v) = 0) ∧
  (∀ v, D.1 v = 3 → D.1 (D.2.1 v) = 0 ∨ D.1 (D.2.1 v) = 2) ∧
  (∀ r, D.1 r = 0 → (Finset.univ.filter fun v => D.1 v = 2 ∧ D.2.1 v = r).card = q) ∧
  (Finset.univ.filter fun v => D.1 v = 3).card ≤ n ∧
  (∀ v, D.1 v = 0 ∨ D.1 v = 1 → D.2.1 v = v) ∧
  (∀ v, D.1 v ≠ 0 → D.2.2 v = 0)

/-! ### The data of a configuration -/

section Construction

variable (p₀ : ℕ) (β lam ε₀ : ℝ) (c : Fin n → ℂ × ℂ)

/-- The clusters of the positive charges of the matched dipoles. -/
noncomputable abbrev clP (i : Fin n) : Finset (Fin n) :=
  clusterOf (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (matched c k).1)
    (dipoleLength (matched c)) i

/-- The clusters of the negative charges of the matched dipoles. -/
noncomputable abbrev clM (i : Fin n) : Finset (Fin n) :=
  clusterOf (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀) (fun k => (matched c k).2)
    (dipoleLength (matched c)) i

open scoped Classical in
/-- **The data of a configuration** (kinds, parents, scales) for the matched dipoles. -/
noncomputable def typeOneData : TOData n :=
  let q := clusterThreshold p₀ β
  let h := cutoff p₀ β lam ε₀
  let r := dipoleLength (matched c)
  let σ := stableMatching c
  (Sum.elim
      (fun i => if (clP p₀ β lam ε₀ c i).card = q + 1 then
        (if (clP p₀ β lam ε₀ c i).min' (clusterOf_nonempty i) = i then 0 else 2)
        else if h < r i then 1 else 3)
      (fun j => if (clM p₀ β lam ε₀ c (σ.symm j)).card = q + 1 then
        (if (clM p₀ β lam ε₀ c (σ.symm j)).min' (clusterOf_nonempty _) = σ.symm j then 0 else 2)
        else if h < r (σ.symm j) then 1 else 3),
    Sum.elim
      (fun i => if (clP p₀ β lam ε₀ c i).card = q + 1 then
        Sum.inl ((clP p₀ β lam ε₀ c i).min' (clusterOf_nonempty i))
        else if h < r i then Sum.inl i else Sum.inr (σ i))
      (fun j => if (clM p₀ β lam ε₀ c (σ.symm j)).card = q + 1 then
        Sum.inr (σ ((clM p₀ β lam ε₀ c (σ.symm j)).min' (clusterOf_nonempty _)))
        else if h < r (σ.symm j) then Sum.inr j else Sum.inl (σ.symm j)),
    Sum.elim
      (fun i => if (clP p₀ β lam ε₀ c i).card = q + 1 ∧
          (clP p₀ β lam ε₀ c i).min' (clusterOf_nonempty i) = i then
        scaleIdx lam (radiusPlus p₀ β lam ε₀ (matched c) i) else 0)
      (fun j => if (clM p₀ β lam ε₀ c (σ.symm j)).card = q + 1 ∧
          (clM p₀ β lam ε₀ c (σ.symm j)).min' (clusterOf_nonempty _) = σ.symm j then
        scaleIdx lam (radiusMinus p₀ β lam ε₀ (matched c) (σ.symm j)) else 0))

/-- The positive charge of dipole `i` lies in an overcrowded cluster. -/
abbrev crowdedP (i : Fin n) : Prop :=
  (clP p₀ β lam ε₀ c i).card = clusterThreshold p₀ β + 1

/-- The negative charge of dipole `i` lies in an overcrowded cluster. -/
abbrev crowdedM (i : Fin n) : Prop :=
  (clM p₀ β lam ε₀ c i).card = clusterThreshold p₀ β + 1

/-- The root (smallest label) of the positive cluster of dipole `i`. -/
noncomputable abbrev minP (i : Fin n) : Fin n := (clP p₀ β lam ε₀ c i).min' (clusterOf_nonempty i)

/-- The root (smallest label) of the negative cluster of dipole `i`. -/
noncomputable abbrev minM (i : Fin n) : Fin n := (clM p₀ β lam ε₀ c i).min' (clusterOf_nonempty i)

/-- Dipole `i` (of the matched configuration) is long. -/
abbrev longD (i : Fin n) : Prop := cutoff p₀ β lam ε₀ < dipoleLength (matched c) i

open scoped Classical in
theorem typeOneData_kind_inl (i : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inl i) =
    if crowdedP p₀ β lam ε₀ c i then (if minP p₀ β lam ε₀ c i = i then 0 else 2)
    else if longD p₀ β lam ε₀ c i then 1 else 3 := rfl

open scoped Classical in
theorem typeOneData_kind_inr (j : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr j) =
    if crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) then
      (if minM p₀ β lam ε₀ c ((stableMatching c).symm j) = (stableMatching c).symm j then 0 else 2)
    else if longD p₀ β lam ε₀ c ((stableMatching c).symm j) then 1 else 3 := rfl

open scoped Classical in
theorem typeOneData_par_inl (i : Fin n) : (typeOneData p₀ β lam ε₀ c).2.1 (Sum.inl i) =
    if crowdedP p₀ β lam ε₀ c i then Sum.inl (minP p₀ β lam ε₀ c i)
    else if longD p₀ β lam ε₀ c i then Sum.inl i else Sum.inr (stableMatching c i) := rfl

open scoped Classical in
theorem typeOneData_par_inr (j : Fin n) : (typeOneData p₀ β lam ε₀ c).2.1 (Sum.inr j) =
    if crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) then
      Sum.inr (stableMatching c (minM p₀ β lam ε₀ c ((stableMatching c).symm j)))
    else if longD p₀ β lam ε₀ c ((stableMatching c).symm j) then Sum.inr j
    else Sum.inl ((stableMatching c).symm j) := rfl

open scoped Classical in
theorem typeOneData_sc_inl (i : Fin n) : (typeOneData p₀ β lam ε₀ c).2.2 (Sum.inl i) =
    if crowdedP p₀ β lam ε₀ c i ∧ minP p₀ β lam ε₀ c i = i then
      scaleIdx lam (radiusPlus p₀ β lam ε₀ (matched c) i) else 0 := rfl

open scoped Classical in
theorem typeOneData_sc_inr (j : Fin n) : (typeOneData p₀ β lam ε₀ c).2.2 (Sum.inr j) =
    if crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) ∧
        minM p₀ β lam ε₀ c ((stableMatching c).symm j) = (stableMatching c).symm j then
      scaleIdx lam (radiusMinus p₀ β lam ε₀ (matched c) ((stableMatching c).symm j)) else 0 := rfl

end Construction

/-! ### Validity of the data of a configuration -/

section Validity

variable {p₀ : ℕ} {β lam ε₀ : ℝ} {c : Fin n → ℂ × ℂ}

theorem min'_congr_eq {s t : Finset (Fin n)} (hst : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst hst
  rfl

theorem clP_eq_of_mem {i j : Fin n} (hj : j ∈ clP p₀ β lam ε₀ c i) :
    clP p₀ β lam ε₀ c j = clP p₀ β lam ε₀ c i := (clusterOf_eq_of_mem hj).1

theorem clM_eq_of_mem {i j : Fin n} (hj : j ∈ clM p₀ β lam ε₀ c i) :
    clM p₀ β lam ε₀ c j = clM p₀ β lam ε₀ c i := (clusterOf_eq_of_mem hj).1

theorem minP_eq_of_mem {i j : Fin n} (hj : j ∈ clP p₀ β lam ε₀ c i) :
    minP p₀ β lam ε₀ c j = minP p₀ β lam ε₀ c i := min'_congr_eq (clP_eq_of_mem hj) _ _

theorem minM_eq_of_mem {i j : Fin n} (hj : j ∈ clM p₀ β lam ε₀ c i) :
    minM p₀ β lam ε₀ c j = minM p₀ β lam ε₀ c i := min'_congr_eq (clM_eq_of_mem hj) _ _

theorem minP_mem (i : Fin n) : minP p₀ β lam ε₀ c i ∈ clP p₀ β lam ε₀ c i := min'_mem _ _

theorem minM_mem (i : Fin n) : minM p₀ β lam ε₀ c i ∈ clM p₀ β lam ε₀ c i := min'_mem _ _

theorem kind_inl_eq_zero_iff (i : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inl i) = 0 ↔
    crowdedP p₀ β lam ε₀ c i ∧ minP p₀ β lam ε₀ c i = i := by
  rw [typeOneData_kind_inl]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]
  exact h1

theorem kind_inl_eq_one_iff (i : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inl i) = 1 ↔
    ¬ crowdedP p₀ β lam ε₀ c i ∧ longD p₀ β lam ε₀ c i := by
  rw [typeOneData_kind_inl]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]

theorem kind_inl_eq_two_iff (i : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inl i) = 2 ↔
    crowdedP p₀ β lam ε₀ c i ∧ minP p₀ β lam ε₀ c i ≠ i := by
  rw [typeOneData_kind_inl]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]
  exact h1

theorem kind_inl_eq_three_iff (i : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inl i) = 3 ↔
    ¬ crowdedP p₀ β lam ε₀ c i ∧ ¬ longD p₀ β lam ε₀ c i := by
  rw [typeOneData_kind_inl]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]

theorem kind_inr_eq_zero_iff (j : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr j) = 0 ↔
    crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) ∧
      minM p₀ β lam ε₀ c ((stableMatching c).symm j) = (stableMatching c).symm j := by
  rw [typeOneData_kind_inr]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]
  exact h1

theorem kind_inr_eq_one_iff (j : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr j) = 1 ↔
    ¬ crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) ∧
      longD p₀ β lam ε₀ c ((stableMatching c).symm j) := by
  rw [typeOneData_kind_inr]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]

theorem kind_inr_eq_two_iff (j : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr j) = 2 ↔
    crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) ∧
      minM p₀ β lam ε₀ c ((stableMatching c).symm j) ≠ (stableMatching c).symm j := by
  rw [typeOneData_kind_inr]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]
  exact h1

theorem kind_inr_eq_three_iff (j : Fin n) : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr j) = 3 ↔
    ¬ crowdedM p₀ β lam ε₀ c ((stableMatching c).symm j) ∧
      ¬ longD p₀ β lam ε₀ c ((stableMatching c).symm j) := by
  rw [typeOneData_kind_inr]
  split_ifs with h1 h2 h2 <;> simp [h1, h2]

/-- Every dipole of type 1 is long or has an overcrowded charge. -/
theorem long_or_crowded (hI : badPointsTypeOne p₀ β lam ε₀ (matched c) = Finset.univ)
    (i : Fin n) :
    longD p₀ β lam ε₀ c i ∨ crowdedP p₀ β lam ε₀ c i ∨ crowdedM p₀ β lam ε₀ c i := by
  have hmem : i ∈ badPointsTypeOne p₀ β lam ε₀ (matched c) := hI ▸ mem_univ i
  unfold badPointsTypeOne at hmem
  rcases mem_union.1 hmem with h | h
  · rcases (mem_J_iff i).1 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases (mem_J_iff i).1 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr h')

/-- **The data of a configuration of type-1 bad points is valid.** -/
theorem typeOneData_valid (hI : badPointsTypeOne p₀ β lam ε₀ (matched c) = Finset.univ) :
    TypeOneValid (clusterThreshold p₀ β) (typeOneData p₀ β lam ε₀ c) := by
  classical
  set σ := stableMatching c with hσ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- members point to overcrowded roots
    rintro (i | j) hv
    · obtain ⟨hc, -⟩ := (kind_inl_eq_two_iff i).1 hv
      rw [typeOneData_par_inl, ite_eq_left hc, kind_inl_eq_zero_iff]
      have hmem := minP_mem (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i
      refine ⟨?_, minP_eq_of_mem hmem⟩
      show (clP p₀ β lam ε₀ c _).card = _
      rw [clP_eq_of_mem hmem]
      exact hc
    · obtain ⟨hc, -⟩ := (kind_inr_eq_two_iff j).1 hv
      rw [typeOneData_par_inr, ite_eq_left hc, kind_inr_eq_zero_iff, Equiv.symm_apply_apply]
      have hmem := minM_mem (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) (σ.symm j)
      refine ⟨?_, minM_eq_of_mem hmem⟩
      show (clM p₀ β lam ε₀ c _).card = _
      rw [clM_eq_of_mem hmem]
      exact hc
  · -- the partner of a good charge is overcrowded
    rintro (i | j) hv
    · obtain ⟨hc, hl⟩ := (kind_inl_eq_three_iff i).1 hv
      rw [typeOneData_par_inl, ite_eq_right hc, ite_eq_right hl]
      have hcm : crowdedM p₀ β lam ε₀ c i := by
        rcases long_or_crowded hI i with h | h | h
        · exact absurd h hl
        · exact absurd h hc
        · exact h
      by_cases hmin : minM p₀ β lam ε₀ c i = i
      · left
        rw [kind_inr_eq_zero_iff, Equiv.symm_apply_apply]
        exact ⟨hcm, hmin⟩
      · right
        rw [kind_inr_eq_two_iff, Equiv.symm_apply_apply]
        exact ⟨hcm, hmin⟩
    · obtain ⟨hc, hl⟩ := (kind_inr_eq_three_iff j).1 hv
      rw [typeOneData_par_inr, ite_eq_right hc, ite_eq_right hl]
      have hcp : crowdedP p₀ β lam ε₀ c (σ.symm j) := by
        rcases long_or_crowded hI (σ.symm j) with h | h | h
        · exact absurd h hl
        · exact h
        · exact absurd h hc
      by_cases hmin : minP p₀ β lam ε₀ c (σ.symm j) = σ.symm j
      · left
        exact (kind_inl_eq_zero_iff _).2 ⟨hcp, hmin⟩
      · right
        exact (kind_inl_eq_two_iff _).2 ⟨hcp, hmin⟩
  · -- every overcrowded root has `q` members
    rintro (m | j₀) hr
    · obtain ⟨hc, hm⟩ := (kind_inl_eq_zero_iff m).1 hr
      have hset : (Finset.univ.filter fun v => (typeOneData p₀ β lam ε₀ c).1 v = 2 ∧
          (typeOneData p₀ β lam ε₀ c).2.1 v = Sum.inl m) =
          ((clP p₀ β lam ε₀ c m).erase m).map Function.Embedding.inl := by
        ext v
        rcases v with i | j
        · simp only [mem_filter, mem_univ, true_and, mem_map, mem_erase,
            Function.Embedding.inl_apply, Sum.inl.injEq]
          constructor
          · rintro ⟨hk, hp⟩
            obtain ⟨hci, hmi⟩ := (kind_inl_eq_two_iff i).1 hk
            rw [typeOneData_par_inl, ite_eq_left hci, Sum.inl.injEq] at hp
            refine ⟨i, ⟨fun h => hmi (hp.trans h.symm), ?_⟩, rfl⟩
            have hmem := minP_mem (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i
            rw [hp] at hmem
            rw [clP_eq_of_mem hmem]
            exact mem_clusterOf_self i
          · rintro ⟨i', ⟨hne, hi'⟩, rfl⟩
            have hcl := clP_eq_of_mem hi'
            have hmin : minP p₀ β lam ε₀ c i' = m := (minP_eq_of_mem hi').trans hm
            refine ⟨(kind_inl_eq_two_iff i').2 ⟨?_, fun h => hne (h.symm.trans hmin)⟩, ?_⟩
            · show (clP p₀ β lam ε₀ c i').card = _
              rw [hcl]
              exact hc
            · have hci : crowdedP p₀ β lam ε₀ c i' := by
                show (clP p₀ β lam ε₀ c i').card = _
                rw [hcl]
                exact hc
              rw [typeOneData_par_inl, ite_eq_left hci, hmin]
        · simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.inl_apply,
            reduceCtorEq, and_false, exists_false, iff_false, not_and]
          intro hk
          obtain ⟨hcj, -⟩ := (kind_inr_eq_two_iff j).1 hk
          rw [typeOneData_par_inr, ite_eq_left hcj]
          exact Sum.inr_ne_inl
      rw [hset, card_map, card_erase_of_mem (mem_clusterOf_self m)]
      show (clP p₀ β lam ε₀ c m).card - 1 = _
      rw [hc]
      rfl
    · obtain ⟨hc, hm⟩ := (kind_inr_eq_zero_iff j₀).1 hr
      set i₀ := σ.symm j₀
      have hset : (Finset.univ.filter fun v => (typeOneData p₀ β lam ε₀ c).1 v = 2 ∧
          (typeOneData p₀ β lam ε₀ c).2.1 v = Sum.inr j₀) =
          ((clM p₀ β lam ε₀ c i₀).erase i₀).map (σ.toEmbedding.trans Function.Embedding.inr) := by
        ext v
        rcases v with i | j
        · simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.trans_apply,
            Function.Embedding.inr_apply, reduceCtorEq, and_false, exists_false, iff_false,
            not_and]
          intro hk
          obtain ⟨hci, -⟩ := (kind_inl_eq_two_iff i).1 hk
          rw [typeOneData_par_inl, ite_eq_left hci]
          exact Sum.inl_ne_inr
        · simp only [mem_filter, mem_univ, true_and, mem_map, mem_erase,
            Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Function.Embedding.inr_apply,
            Sum.inr.injEq]
          constructor
          · rintro ⟨hk, hp⟩
            obtain ⟨hcj, hmj⟩ := (kind_inr_eq_two_iff j).1 hk
            rw [typeOneData_par_inr, ite_eq_left hcj, Sum.inr.injEq] at hp
            have hp' : minM p₀ β lam ε₀ c ((stableMatching c).symm j) =
                (stableMatching c).symm j₀ := by
              rw [← hp, Equiv.symm_apply_apply]
            refine ⟨σ.symm j, ⟨fun h => hmj (hp'.trans h.symm), ?_⟩, Equiv.apply_symm_apply σ j⟩
            have hmem := minM_mem (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) (σ.symm j)
            rw [hp'] at hmem
            rw [clM_eq_of_mem hmem]
            exact mem_clusterOf_self _
          · rintro ⟨i', ⟨hne, hi'⟩, rfl⟩
            have hcl := clM_eq_of_mem hi'
            have hmin : minM p₀ β lam ε₀ c i' = i₀ := (minM_eq_of_mem hi').trans hm
            have hci : crowdedM p₀ β lam ε₀ c i' := by
              show (clM p₀ β lam ε₀ c i').card = _
              rw [hcl]
              exact hc
            refine ⟨(kind_inr_eq_two_iff _).2 ⟨?_, ?_⟩, ?_⟩
            · rw [Equiv.symm_apply_apply]
              exact hci
            · rw [Equiv.symm_apply_apply, hmin]
              exact fun h => hne h.symm
            · rw [typeOneData_par_inr, Equiv.symm_apply_apply, ite_eq_left hci, hmin]
              exact congrArg Sum.inr (Equiv.apply_symm_apply σ j₀)
      rw [hset, card_map, card_erase_of_mem (mem_clusterOf_self i₀)]
      show (clM p₀ β lam ε₀ c i₀).card - 1 = _
      rw [hc]
      rfl
  · -- at most `n` good charges
    let f : Charge n → Fin n := Sum.elim id σ.symm
    refine (card_le_card_of_injOn f (fun _ _ => mem_coe.2 (mem_univ _)) ?_).trans_eq
      (by rw [card_univ, Fintype.card_fin])
    intro v hv w hw hvw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hw
    rcases v with i | j <;> rcases w with i' | j'
    · simpa [f] using hvw
    · exfalso
      simp only [f, Sum.elim_inl, Sum.elim_inr, id] at hvw
      obtain ⟨hc, hl⟩ := (kind_inl_eq_three_iff i).1 hv
      obtain ⟨hc', -⟩ := (kind_inr_eq_three_iff j').1 hw
      rw [← hvw] at hc'
      rcases long_or_crowded hI i with h | h | h
      · exact hl h
      · exact hc h
      · exact hc' h
    · exfalso
      simp only [f, Sum.elim_inl, Sum.elim_inr, id] at hvw
      obtain ⟨hc, hl⟩ := (kind_inr_eq_three_iff j).1 hv
      obtain ⟨hc', -⟩ := (kind_inl_eq_three_iff i').1 hw
      rw [hvw] at hc hl
      rcases long_or_crowded hI i' with h | h | h
      · exact hl h
      · exact hc' h
      · exact hc h
    · simp only [f, Sum.elim_inr] at hvw
      rw [σ.symm.injective hvw]
  · -- roots are their own parents
    rintro (i | j) hv
    · rcases hv with hv | hv
      · obtain ⟨hc, hm⟩ := (kind_inl_eq_zero_iff i).1 hv
        rw [typeOneData_par_inl, ite_eq_left hc, hm]
      · obtain ⟨hc, hl⟩ := (kind_inl_eq_one_iff i).1 hv
        rw [typeOneData_par_inl, ite_eq_right hc, ite_eq_left hl]
    · rcases hv with hv | hv
      · obtain ⟨hc, hm⟩ := (kind_inr_eq_zero_iff j).1 hv
        rw [typeOneData_par_inr, ite_eq_left hc, hm, Equiv.apply_symm_apply]
      · obtain ⟨hc, hl⟩ := (kind_inr_eq_one_iff j).1 hv
        rw [typeOneData_par_inr, ite_eq_right hc, ite_eq_left hl]
  · -- scales only at overcrowded roots
    rintro (i | j) hv
    · rw [typeOneData_sc_inl, ite_eq_right]
      exact fun h => hv ((kind_inl_eq_zero_iff i).2 h)
    · rw [typeOneData_sc_inr, ite_eq_right]
      exact fun h => hv ((kind_inr_eq_zero_iff j).2 h)

/-- The scale indices of the data are at most `K = ⌊log₂ ⌊h/λ⌋⌋`. -/
theorem typeOneData_sc_le (hlam : 0 < lam) (hlh : lam ≤ cutoff p₀ β lam ε₀) (v : Charge n) :
    (typeOneData p₀ β lam ε₀ c).2.2 v ≤ Nat.log 2 ⌊cutoff p₀ β lam ε₀ / lam⌋₊ := by
  classical
  rcases v with i | j
  · rw [typeOneData_sc_inl]
    split_ifs
    · exact scaleIdx_le hlam (clusterRadius_le lam hlh i)
    · exact Nat.zero_le _
  · rw [typeOneData_sc_inr]
    split_ifs
    · exact scaleIdx_le hlam (clusterRadius_le lam hlh _)
    · exact Nat.zero_le _

end Validity

/-! ### The integrand is bounded by the product of the factors -/

section Pointwise

variable {p₀ : ℕ} {β lam ε₀ : ℝ} {c : Fin n → ℂ × ℂ} {Nₐ : ℕ}

theorem NoIsosceles.comp_perm {z : Fin n → ℂ} (hz : NoIsosceles z) (σ : Equiv.Perm (Fin n)) :
    NoIsosceles (z ∘ σ) := fun i j j' hji hj'i hjj' =>
  hz (σ i) (σ j) (σ j') (σ.injective.ne hji) (σ.injective.ne hj'i) (σ.injective.ne hjj')

theorem typeOneFactor_of_zero {β lam h : ℝ} {D : TOData n} {z : Charge n → ℂ} {v : Charge n}
    (hv : D.1 v = 0) : typeOneFactor β lam h Nₐ D z v =
      (box Nₐ).indicator 1 (z v) * ENNReal.ofReal (dyad lam (D.2.2 v) ^ (-(β / 2))) := by
  simp [typeOneFactor, hv]

theorem typeOneFactor_of_one {β lam h : ℝ} {D : TOData n} {z : Charge n → ℂ} {v : Charge n}
    (hv : D.1 v = 1) : typeOneFactor β lam h Nₐ D z v =
      (box Nₐ).indicator 1 (z v) * ENNReal.ofReal ((h / 4) ^ (-(β / 2))) := by
  simp [typeOneFactor, hv]

theorem typeOneFactor_of_two {β lam h : ℝ} {D : TOData n} {z : Charge n → ℂ} {v : Charge n}
    (hv : D.1 v = 2) : typeOneFactor β lam h Nₐ D z v =
      (Metric.closedBall (0 : ℂ) (8 * dyad lam (D.2.2 (D.2.1 v)))).indicator 1 (z v - z (D.2.1 v)) *
        ENNReal.ofReal (dyad lam (D.2.2 (D.2.1 v)) ^ (-(β / 2))) := by
  simp [typeOneFactor, hv]

theorem typeOneFactor_of_three {β lam h : ℝ} {D : TOData n} {z : Charge n → ℂ} {v : Charge n}
    (hv : D.1 v = 3) : typeOneFactor β lam h Nₐ D z v =
      (Metric.closedBall (0 : ℂ) h).indicator
        (fun u => ENNReal.ofReal (max (‖u‖ / 4) lam ^ (-(β / 2)))) (z v - z (D.2.1 v)) := by
  simp [typeOneFactor, hv]

/-- The weight of a charge of an overcrowded cluster at the dyadic scale of its radius. -/
theorem rpow_le_dyad_rpow (hβ : 0 ≤ β) (hlam : 0 < lam) {T : ℝ} (hT : lam ≤ T) :
    ENNReal.ofReal (T ^ (-(β / 2))) ≤ ENNReal.ofReal (dyad lam (scaleIdx lam T) ^ (-(β / 2))) := by
  refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ?_ (dyad_scaleIdx_le hlam hT)
    (by linarith))
  unfold dyad
  positivity

/-- **The factor of a positive charge** bounds its weight `(τ_i^{+,Z})^{-β/2}`. -/
theorem factor_plus (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (hlam : 0 < lam) (hβ : 0 ≤ β) (hc : c ∈ boxPi Nₐ n) (hzP : NoIsosceles fun k => (c k).1)
    (i : Fin n) :
    ENNReal.ofReal (radiusPlus p₀ β lam ε₀ (matched c) i ^ (-(β / 2))) ≤
      typeOneFactor β lam (cutoff p₀ β lam ε₀) Nₐ (typeOneData p₀ β lam ε₀ c) (chargePos c)
        (Sum.inl i) := by
  classical
  have hr : ∀ k, 0 ≤ dipoleLength (matched c) k := fun k => norm_nonneg _
  have hbox : chargePos c (Sum.inl i) ∈ box Nₐ := (Set.mem_univ_pi.1 hc i).1
  have hTl : lam ≤ radiusPlus p₀ β lam ε₀ (matched c) i := le_clusterRadius lam i
  have hzP' : NoIsosceles fun k => (matched c k).1 := hzP
  rcases clusterOf_cases (z := fun k => (matched c k).1) hq hh hr hzP' i with
    ⟨hcard, hgeo⟩ | ⟨hcard, -, h1, h2⟩
  · have hcP : crowdedP p₀ β lam ε₀ c i := hcard
    by_cases hm : minP p₀ β lam ε₀ c i = i
    · have hk := (kind_inl_eq_zero_iff (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i).2
        ⟨hcP, hm⟩
      rw [typeOneFactor_of_zero hk, Set.indicator_of_mem hbox, Pi.one_apply, one_mul,
        typeOneData_sc_inl, ite_eq_left ⟨hcP, hm⟩]
      exact rpow_le_dyad_rpow hβ hlam hTl
    · have hk := (kind_inl_eq_two_iff (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i).2
        ⟨hcP, hm⟩
      rw [typeOneFactor_of_two hk, typeOneData_par_inl, ite_eq_left hcP]
      have hmmem := minP_mem (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i
      have hsame := clusterOf_eq_of_mem hmmem
      have hcm : crowdedP p₀ β lam ε₀ c (minP p₀ β lam ε₀ c i) :=
        (congrArg Finset.card hsame.1).trans hcP
      have hmm : minP p₀ β lam ε₀ c (minP p₀ β lam ε₀ c i) = minP p₀ β lam ε₀ c i :=
        minP_eq_of_mem hmmem
      rw [typeOneData_sc_inl, ite_eq_left ⟨hcm, hmm⟩]
      have hTm : radiusPlus p₀ β lam ε₀ (matched c) (minP p₀ β lam ε₀ c i) =
          radiusPlus p₀ β lam ε₀ (matched c) i := by
        show max lam _ = max lam _
        rw [hsame.2]
      rw [hTm]
      have hdist : chargePos c (Sum.inl i) - chargePos c (Sum.inl (minP p₀ β lam ε₀ c i)) ∈
          Metric.closedBall (0 : ℂ)
            (8 * dyad lam (scaleIdx lam (radiusPlus p₀ β lam ε₀ (matched c) i))) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have hg := hgeo i (mem_clusterOf_self i) _ hmmem
        have h2' := lt_two_mul_dyad_scaleIdx hlam hTl
        have h3 : clusterRemovalValue (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀)
            (fun k => (matched c k).1) (dipoleLength (matched c)) i ≤
              radiusPlus p₀ β lam ε₀ (matched c) i := le_max_right _ _
        show ‖(c i).1 - (c (minP p₀ β lam ε₀ c i)).1‖ ≤ _
        exact hg.trans (by linarith)
      rw [Set.indicator_of_mem hdist, Pi.one_apply, one_mul]
      exact rpow_le_dyad_rpow hβ hlam hTl
  · have hcP : ¬ crowdedP p₀ β lam ε₀ c i := hcard
    by_cases hl : longD p₀ β lam ε₀ c i
    · have hk := (kind_inl_eq_one_iff (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i).2
        ⟨hcP, hl⟩
      rw [typeOneFactor_of_one hk, Set.indicator_of_mem hbox, Pi.one_apply, one_mul]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_
        (by linarith))
      exact (h2 hl).trans (le_max_right _ _)
    · have hk := (kind_inl_eq_three_iff (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i).2
        ⟨hcP, hl⟩
      rw [typeOneFactor_of_three hk, typeOneData_par_inl, ite_eq_right hcP, ite_eq_right hl]
      have hrl : dipoleLength (matched c) i ≤ cutoff p₀ β lam ε₀ := not_lt.1 hl
      have hτ := h1 hrl
      have hmem : chargePos c (Sum.inl i) - chargePos c (Sum.inr (stableMatching c i)) ∈
          Metric.closedBall (0 : ℂ) (cutoff p₀ β lam ε₀) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hrl
      rw [Set.indicator_of_mem hmem]
      refine le_of_eq ?_
      congr 2
      show max lam _ = _
      rw [hτ, max_comm]
      rfl

/-- **The factor of a negative charge** bounds its weight `(τ_i^{-,Z})^{-β/2}`. -/
theorem factor_minus (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (hlam : 0 < lam) (hβ : 0 ≤ β) (hc : c ∈ boxPi Nₐ n) (hzM : NoIsosceles fun k => (c k).2)
    (i : Fin n) :
    ENNReal.ofReal (radiusMinus p₀ β lam ε₀ (matched c) i ^ (-(β / 2))) ≤
      typeOneFactor β lam (cutoff p₀ β lam ε₀) Nₐ (typeOneData p₀ β lam ε₀ c) (chargePos c)
        (Sum.inr (stableMatching c i)) := by
  classical
  set σ := stableMatching c with hσ
  have e : σ.symm (σ i) = i := Equiv.symm_apply_apply σ i
  have hr : ∀ k, 0 ≤ dipoleLength (matched c) k := fun k => norm_nonneg _
  have hzM' : NoIsosceles fun k => (matched c k).2 := hzM.comp_perm σ
  have hbox : chargePos c (Sum.inr (σ i)) ∈ box Nₐ := (Set.mem_univ_pi.1 hc (σ i)).2
  have hTl : lam ≤ radiusMinus p₀ β lam ε₀ (matched c) i := le_clusterRadius lam i
  rcases clusterOf_cases (z := fun k => (matched c k).2) hq hh hr hzM' i with
    ⟨hcard, hgeo⟩ | ⟨hcard, -, h1, h2⟩
  · have hcM : crowdedM p₀ β lam ε₀ c i := hcard
    by_cases hm : minM p₀ β lam ε₀ c i = i
    · have hk : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr (σ i)) = 0 := by
        rw [kind_inr_eq_zero_iff, e]
        exact ⟨hcM, hm⟩
      rw [typeOneFactor_of_zero hk, Set.indicator_of_mem hbox, Pi.one_apply, one_mul,
        typeOneData_sc_inr, e, ite_eq_left ⟨hcM, hm⟩]
      exact rpow_le_dyad_rpow hβ hlam hTl
    · have hk : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr (σ i)) = 2 := by
        rw [kind_inr_eq_two_iff, e]
        exact ⟨hcM, hm⟩
      rw [typeOneFactor_of_two hk, typeOneData_par_inr, e, ite_eq_left hcM]
      have hmmem := minM_mem (p₀ := p₀) (β := β) (lam := lam) (ε₀ := ε₀) (c := c) i
      have hsame := clusterOf_eq_of_mem hmmem
      have hcm : crowdedM p₀ β lam ε₀ c (minM p₀ β lam ε₀ c i) :=
        (congrArg Finset.card hsame.1).trans hcM
      have hmm : minM p₀ β lam ε₀ c (minM p₀ β lam ε₀ c i) = minM p₀ β lam ε₀ c i :=
        minM_eq_of_mem hmmem
      rw [typeOneData_sc_inr, Equiv.symm_apply_apply, ite_eq_left ⟨hcm, hmm⟩]
      have hTm : radiusMinus p₀ β lam ε₀ (matched c) (minM p₀ β lam ε₀ c i) =
          radiusMinus p₀ β lam ε₀ (matched c) i := by
        show max lam _ = max lam _
        rw [hsame.2]
      rw [hTm]
      have hdist : chargePos c (Sum.inr (σ i)) -
          chargePos c (Sum.inr (σ (minM p₀ β lam ε₀ c i))) ∈ Metric.closedBall (0 : ℂ)
            (8 * dyad lam (scaleIdx lam (radiusMinus p₀ β lam ε₀ (matched c) i))) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have hg := hgeo i (mem_clusterOf_self i) _ hmmem
        have h2' := lt_two_mul_dyad_scaleIdx hlam hTl
        have h3 : clusterRemovalValue (clusterThreshold p₀ β) (cutoff p₀ β lam ε₀)
            (fun k => (matched c k).2) (dipoleLength (matched c)) i ≤
              radiusMinus p₀ β lam ε₀ (matched c) i := le_max_right _ _
        show ‖(c (σ i)).2 - (c (σ (minM p₀ β lam ε₀ c i))).2‖ ≤ _
        exact hg.trans (by linarith)
      rw [Set.indicator_of_mem hdist, Pi.one_apply, one_mul]
      exact rpow_le_dyad_rpow hβ hlam hTl
  · have hcM : ¬ crowdedM p₀ β lam ε₀ c i := hcard
    by_cases hl : longD p₀ β lam ε₀ c i
    · have hk : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr (σ i)) = 1 := by
        rw [kind_inr_eq_one_iff, e]
        exact ⟨hcM, hl⟩
      rw [typeOneFactor_of_one hk, Set.indicator_of_mem hbox, Pi.one_apply, one_mul]
      refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) ?_
        (by linarith))
      exact (h2 hl).trans (le_max_right _ _)
    · have hk : (typeOneData p₀ β lam ε₀ c).1 (Sum.inr (σ i)) = 3 := by
        rw [kind_inr_eq_three_iff, e]
        exact ⟨hcM, hl⟩
      rw [typeOneFactor_of_three hk, typeOneData_par_inr, e, ite_eq_right hcM, ite_eq_right hl]
      have hrl : dipoleLength (matched c) i ≤ cutoff p₀ β lam ε₀ := not_lt.1 hl
      have hτ := h1 hrl
      have hmem : chargePos c (Sum.inr (σ i)) - chargePos c (Sum.inl i) ∈
          Metric.closedBall (0 : ℂ) (cutoff p₀ β lam ε₀) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        show ‖(c (σ i)).2 - (c i).1‖ ≤ _
        rw [norm_sub_rev]
        exact hrl
      rw [Set.indicator_of_mem hmem]
      refine le_of_eq ?_
      congr 2
      show max lam _ = _
      rw [hτ, max_comm]
      show max (‖(c i).1 - (c (σ i)).2‖ / 4) lam = max (‖(c (σ i)).2 - (c i).1‖ / 4) lam
      rw [norm_sub_rev]

/-- **The pointwise bound** (Steps 2–5 of the proof of Lemma 5.40): at the matched dipoles of
a configuration without isosceles coincidences, the integrand of `Z^{(1)}` is at most the
product of the factors of the data of the configuration. -/
theorem typeOneIntegrand_le (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (hlam : 0 < lam) (hβ : 0 ≤ β) (hc : c ∈ boxPi Nₐ n) (hzP : NoIsosceles fun k => (c k).1)
    (hzM : NoIsosceles fun k => (c k).2) :
    (by classical exact if badPointsTypeOne p₀ β lam ε₀ (matched c) = Finset.univ then 1 else 0) *
        ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ (matched c)) ≤
      ∏ v, typeOneFactor β lam (cutoff p₀ β lam ε₀) Nₐ (typeOneData p₀ β lam ε₀ c)
        (chargePos c) v := by
  classical
  split_ifs with hI
  · rw [one_mul, Fintype.prod_sum_type, ← Equiv.prod_comp (stableMatching c)
      (fun j => typeOneFactor β lam (cutoff p₀ β lam ε₀) Nₐ (typeOneData p₀ β lam ε₀ c)
        (chargePos c) (Sum.inr j)), ← prod_mul_distrib]
    unfold typeOneWeight
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (mul_nonneg
      (hlam.le.trans (le_clusterRadius lam i)) (hlam.le.trans (le_clusterRadius lam i))) _]
    refine prod_le_prod fun i _ => ?_
    rw [Real.mul_rpow (hlam.le.trans (le_clusterRadius lam i))
      (hlam.le.trans (le_clusterRadius lam i)), ENNReal.ofReal_mul (Real.rpow_nonneg
        (hlam.le.trans (le_clusterRadius lam i)) _)]
    exact mul_le_mul' (factor_plus hq hh hlam hβ hc hzP i) (factor_minus hq hh hlam hβ hc hzM i)
  · rw [zero_mul]
    exact zero_le

end Pointwise

end BadPointTypes

end MultipoleBKT

end
