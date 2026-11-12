/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.SameSignClustering
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Measurability of the same-sign clustering

The bad points of type 1 (Definition 5.2)
are defined through the `q`-clustering of Definition 5.1 (`MultipoleBKT.sameSignClustering`). We prove that the clusters depend measurably on the configuration: for measurable
charges `z` and lengths `r` on a measurable space `α`, every fibre of
`a ↦ {clusters of (z a, r a)}` is measurable
(`MultipoleBKT.TheoremTwo.fiberMeasurable_clustering`).

Each step of the clustering is decided by finitely many comparisons between `h`, the `r_i/4`,
the distances `|z_i - z_j|/2` (closed balls of radius `t` meet iff `|z_i - z_j| ≤ 2t`) and the
threshold `τ`, which is measurable (`measurable_clusterTau`): the set of radii at which some
ball is overcrowded is a closed half-line, so `inf ≤ x` iff the balls of radius `x` are
overcrowded. The output is therefore piecewise, on finitely many measurable pieces, a
measurable function of the output on a smaller set of labels (strong induction on the labels).

Fibres are used instead of measurable spaces on `Finset`s: `MultipoleBKT.TheoremTwo.FiberMeasurable`.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace MultipoleBKT

namespace TheoremTwo

/-! ### Maps with measurable fibres -/

/-- `F` has measurable fibres. -/
def FiberMeasurable {α X : Type*} [MeasurableSpace α] (F : α → X) : Prop :=
  ∀ x, MeasurableSet {a | F a = x}

section Fiber

variable {α X Y : Type*} [MeasurableSpace α] {F : α → X}

theorem FiberMeasurable.const (x₀ : X) : FiberMeasurable fun _ : α => x₀ := by
  intro x
  by_cases h : x₀ = x
  · simp [h]
  · simp [h]

theorem FiberMeasurable.preimage [Countable X] (hF : FiberMeasurable F) (s : Set X) :
    MeasurableSet (F ⁻¹' s) := by
  have : F ⁻¹' s = ⋃ x ∈ s, {a | F a = x} := by
    ext a; simp
  rw [this]
  exact MeasurableSet.biUnion s.to_countable fun x _ => hF x

theorem FiberMeasurable.measurableSet [Countable X] (hF : FiberMeasurable F) (P : X → Prop) :
    MeasurableSet {a | P (F a)} :=
  hF.preimage {x | P x}

/-- A map that factors through a map with measurable fibres and countable values has measurable
fibres. -/
theorem FiberMeasurable.of_factor [Countable Y] {Φ : α → Y} (hΦ : FiberMeasurable Φ)
    (h : ∀ a b, Φ a = Φ b → F a = F b) : FiberMeasurable F := by
  intro x
  have : {a | F a = x} = Φ ⁻¹' (Φ '' {a | F a = x}) := by
    ext a
    constructor
    · intro ha; exact ⟨a, ha, rfl⟩
    · rintro ⟨b, hb, hab⟩
      exact (h a b hab.symm).trans hb
  rw [this]
  exact hΦ.preimage _

theorem FiberMeasurable.comp [Countable X] (hF : FiberMeasurable F) (G : X → Y) :
    FiberMeasurable fun a => G (F a) :=
  hF.of_factor fun _ _ h => by rw [h]

theorem FiberMeasurable.prodMk {G : α → Y} (hF : FiberMeasurable F) (hG : FiberMeasurable G) :
    FiberMeasurable fun a => (F a, G a) := by
  rintro ⟨x, y⟩
  have : {a | (F a, G a) = (x, y)} = {a | F a = x} ∩ {a | G a = y} := by
    ext a; simp [Prod.ext_iff]
  rw [this]
  exact (hF x).inter (hG y)

theorem FiberMeasurable.pi {ι : Type*} [Finite ι] {F : ι → α → X}
    (h : ∀ i, FiberMeasurable (F i)) : FiberMeasurable fun a i => F i a := by
  intro x
  have : {a | (fun i => F i a) = x} = ⋂ i, {a | F i a = x i} := by
    ext a; simp [funext_iff]
  rw [this]
  exact MeasurableSet.iInter fun i => h i (x i)

theorem fiberMeasurable_decide {P : α → Prop} [∀ a, Decidable (P a)]
    (hP : MeasurableSet {a | P a}) : FiberMeasurable fun a => decide (P a) := by
  intro b
  cases b
  · have : {a | decide (P a) = false} = {a | P a}ᶜ := by ext a; simp
    rw [this]; exact hP.compl
  · have : {a | decide (P a) = true} = {a | P a} := by ext a; simp
    rw [this]; exact hP

/-- A map that agrees, on each piece of a countable measurable cover, with a map with measurable
fibres has measurable fibres. -/
theorem FiberMeasurable.of_cover {ι : Type*} [Countable ι] (S : ι → Set α) (G : ι → α → X)
    (hS : ∀ k, MeasurableSet (S k)) (hcov : ∀ a, ∃ k, a ∈ S k)
    (hFG : ∀ k a, a ∈ S k → F a = G k a) (hG : ∀ k, FiberMeasurable (G k)) :
    FiberMeasurable F := by
  intro x
  have : {a | F a = x} = ⋃ k, (S k ∩ {a | G k a = x}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro ha
      obtain ⟨k, hk⟩ := hcov a
      exact ⟨k, hk, (hFG k a hk).symm.trans ha⟩
    · rintro ⟨k, hk, hG'⟩
      exact (hFG k a hk).trans hG'
  rw [this]
  exact MeasurableSet.iUnion fun k => (hS k).inter (hG k x)

/-- `a ↦ I.filter (P a)` has measurable fibres if each `{a | P a j}` is measurable. -/
theorem fiberMeasurable_filter {ι : Type*} [DecidableEq ι] (I : Finset ι) {P : α → ι → Prop}
    [∀ a, DecidablePred (P a)] (hP : ∀ j, MeasurableSet {a | P a j}) :
    FiberMeasurable fun a => I.filter (P a) := by
  intro T
  have hiff : ∀ a, I.filter (P a) = T ↔ T ⊆ I ∧ ∀ j ∈ I, (P a j ↔ j ∈ T) := by
    intro a
    constructor
    · rintro rfl
      exact ⟨Finset.filter_subset _ _, fun j hj => by simp [hj]⟩
    · rintro ⟨hTI, h⟩
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj, hPj⟩; exact (h j hj).mp hPj
      · intro hj; exact ⟨hTI hj, (h j (hTI hj)).mpr hj⟩
  have : {a | I.filter (P a) = T} = {_a | T ⊆ I} ∩ ⋂ j ∈ (I : Set ι), {a | P a j ↔ j ∈ T} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe, hiff]
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.const _) (MeasurableSet.biInter I.countable_toSet
    fun j _ => ?_)
  by_cases hj : j ∈ T
  · have : {a | P a j ↔ j ∈ T} = {a | P a j} := by ext a; simp [hj]
    rw [this]; exact hP j
  · have : {a | P a j ↔ j ∈ T} = {a | P a j}ᶜ := by ext a; simp [hj]
    rw [this]; exact (hP j).compl

end Fiber

/-! ### Closed balls -/

theorem closedBall_inter_nonempty_iff (x y : ℂ) (t : ℝ) :
    (closedBall x t ∩ closedBall y t).Nonempty ↔ ‖x - y‖ ≤ 2 * t := by
  constructor
  · rintro ⟨w, hw1, hw2⟩
    rw [mem_closedBall] at hw1 hw2
    rw [← dist_eq_norm]
    calc dist x y ≤ dist x w + dist w y := dist_triangle _ _ _
      _ ≤ t + t := add_le_add (by rw [dist_comm]; exact hw1) hw2
      _ = 2 * t := by ring
  · intro h
    refine ⟨midpoint ℝ x y, ?_, ?_⟩
    · rw [mem_closedBall, dist_comm, dist_left_midpoint (𝕜 := ℝ), dist_eq_norm,
        Real.norm_ofNat]
      linarith
    · rw [mem_closedBall, dist_midpoint_right (𝕜 := ℝ), dist_eq_norm, Real.norm_ofNat]
      linarith

/-! ### The steps of the clustering -/

section Steps

variable {N : ℕ}

open scoped Classical in
/-- `crowded(t)`: the centres whose ball of radius `t` meets at least `q` other balls. -/
noncomputable def crowdedSet (q : ℕ) (z : Fin N → ℂ) (I : Finset (Fin N)) (t : ℝ) :
    Finset (Fin N) :=
  I.filter fun i => q ≤ (I.filter fun j => j ≠ i ∧
    (closedBall (z i) t ∩ closedBall (z j) t).Nonempty).card

open scoped Classical in
/-- The threshold `τ` of one step of the clustering. -/
noncomputable def clusterTau (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) (I : Finset (Fin N))
    (hI : I.Nonempty) : ℝ :=
  if {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}.Nonempty then
    min (min h (I.inf' hI r / 4)) (sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty})
  else min h (I.inf' hI r / 4)

open scoped Classical in
/-- The key `(j ∉ crowded(τ), r_j, j)` of the overcrowding step. -/
noncomputable def clusterKey (q : ℕ) (z : Fin N → ℂ) (r : Fin N → ℝ) (I : Finset (Fin N)) (τ : ℝ)
    (j : Fin N) : Bool ×ₗ (ℝ ×ₗ Fin N) :=
  toLex (decide (j ∉ crowdedSet q z I τ), toLex (r j, j))

open scoped Classical in
/-- The centre chosen in the overcrowding step. -/
noncomputable def clusterChosen (q : ℕ) (z : Fin N → ℂ) (r : Fin N → ℝ) (I : Finset (Fin N))
    (τ : ℝ) (hI : I.Nonempty) : Fin N :=
  (ofLex (ofLex ((I.image (clusterKey q z r I τ)).min' (hI.image _))).2).2

open scoped Classical in
/-- The cluster `J` of the overcrowding step. -/
noncomputable def clusterJ (q : ℕ) (z : Fin N → ℂ) (r : Fin N → ℝ) (I : Finset (Fin N)) (τ : ℝ)
    (hI : I.Nonempty) : Finset (Fin N) :=
  insert (clusterChosen q z r I τ hI) (I.filter fun j =>
    (closedBall (z j) τ ∩ closedBall (z (clusterChosen q z r I τ hI)) τ).Nonempty)

open scoped Classical in
/-- One step of the clustering. -/
theorem sameSignClustering_eq_of_nonempty (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (I : Finset (Fin N)) (hI : I.Nonempty) :
    sameSignClustering q h z r I =
      if clusterTau q h z r I hI = h then I.image fun i => ({i}, h)
      else if hs : (I.filter fun i => r i / 4 = clusterTau q h z r I hI).Nonempty then
        insert ({(I.filter fun i => r i / 4 = clusterTau q h z r I hI).min' hs},
            clusterTau q h z r I hI)
          (sameSignClustering q h z r (I.erase
            ((I.filter fun i => r i / 4 = clusterTau q h z r I hI).min' hs)))
      else insert (clusterJ q z r I (clusterTau q h z r I hI) hI, clusterTau q h z r I hI)
          (sameSignClustering q h z r (I \ clusterJ q z r I (clusterTau q h z r I hI) hI)) := by
  rw [sameSignClustering, dite_eq_left hI]
  rfl

theorem sameSignClustering_of_empty (q : ℕ) (h : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) :
    sameSignClustering q h z r ∅ = ∅ := by
  rw [sameSignClustering, dite_eq_right (by simp)]

open scoped Classical in
theorem crowdedSet_eq (q : ℕ) (z : Fin N → ℂ) (I : Finset (Fin N)) (t : ℝ) :
    crowdedSet q z I t = I.filter fun i => q ≤ (I.filter fun j => j ≠ i ∧
      ‖z i - z j‖ ≤ 2 * t).card := by
  unfold crowdedSet
  refine Finset.filter_congr fun i _ => ?_
  rw [Finset.filter_congr fun j _ => and_congr_right' (closedBall_inter_nonempty_iff (z i) (z j) t)]

theorem crowdedSet_mono (q : ℕ) (z : Fin N → ℂ) (I : Finset (Fin N)) {t t' : ℝ} (htt' : t ≤ t') :
    crowdedSet q z I t ⊆ crowdedSet q z I t' := by
  classical
  rw [crowdedSet_eq, crowdedSet_eq]
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, hi.2.trans (Finset.card_le_card fun j hj => ?_)⟩
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, hj.2.1, hj.2.2.trans (by linarith)⟩

/-- Some ball is overcrowded at some radius iff `|I| ≥ q + 1`. -/
theorem crowded_nonempty_iff (q : ℕ) (z : Fin N → ℂ) {I : Finset (Fin N)} (hI : I.Nonempty) :
    {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}.Nonempty ↔ q + 1 ≤ I.card := by
  classical
  constructor
  · rintro ⟨t, -, i, hi⟩
    rw [crowdedSet_eq, Finset.mem_filter] at hi
    have h1 : (I.filter fun j => j ≠ i ∧ ‖z i - z j‖ ≤ 2 * t) ⊆ I.erase i := fun j hj => by
      rw [Finset.mem_filter] at hj
      exact Finset.mem_erase.mpr ⟨hj.2.1, hj.1⟩
    have h2 := (Finset.card_le_card h1).trans_eq (Finset.card_erase_of_mem hi.1)
    have h3 := hi.2.trans h2
    have h4 := Finset.card_pos.mpr hI
    omega
  · intro hcard
    obtain ⟨i₀, hi₀⟩ := hI
    set t := ∑ j ∈ I, ‖z i₀ - z j‖
    have ht : 0 ≤ t := Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine ⟨t, ht, i₀, ?_⟩
    rw [crowdedSet_eq, Finset.mem_filter]
    refine ⟨hi₀, ?_⟩
    have h1 : I.erase i₀ ⊆ I.filter fun j => j ≠ i₀ ∧ ‖z i₀ - z j‖ ≤ 2 * t := fun j hj => by
      rw [Finset.mem_erase] at hj
      rw [Finset.mem_filter]
      refine ⟨hj.2, hj.1, ?_⟩
      have := Finset.single_le_sum (f := fun j => ‖z i₀ - z j‖) (fun _ _ => norm_nonneg _) hj.2
      linarith
    have h2 := Finset.card_le_card h1
    rw [Finset.card_erase_of_mem hi₀] at h2
    omega

/-- The set of radii at which some ball is overcrowded is closed. -/
theorem isClosed_crowded (q : ℕ) (z : Fin N → ℂ) (I : Finset (Fin N)) :
    IsClosed {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} := by
  classical
  have hset : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} =
      Ici 0 ∩ ⋃ i ∈ (I : Set (Fin N)), ⋃ T ∈ ((I.powerset.filter fun T => q ≤ T.card) :
        Set (Finset (Fin N))), ⋂ j ∈ (T : Set (Fin N)),
          {t : ℝ | j ≠ i ∧ ‖z i - z j‖ ≤ 2 * t} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ici, Set.mem_iUnion, Set.mem_iInter,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset, exists_prop]
    refine and_congr_right fun _ => ?_
    rw [crowdedSet_eq]
    constructor
    · rintro ⟨i, hi⟩
      rw [Finset.mem_filter] at hi
      refine ⟨i, hi.1, _, ⟨Finset.filter_subset _ _, hi.2⟩, fun j hj => ?_⟩
      exact (Finset.mem_filter.mp hj).2
    · rintro ⟨i, hi, T, ⟨hTI, hqT⟩, hT⟩
      refine ⟨i, Finset.mem_filter.mpr ⟨hi, hqT.trans (Finset.card_le_card fun j hj => ?_)⟩⟩
      exact Finset.mem_filter.mpr ⟨hTI hj, hT j hj⟩
  rw [hset]
  refine isClosed_Ici.inter (isClosed_biUnion_finset fun i _ => isClosed_biUnion_finset
    fun T _ => isClosed_biInter fun j _ => ?_)
  by_cases hji : j = i
  · simp [hji]
  · simp only [ne_eq, hji, not_false_eq_true, true_and]
    exact isClosed_le continuous_const (continuous_const.mul continuous_id)

theorem sInf_crowded_le_iff (q : ℕ) (z : Fin N → ℂ) (I : Finset (Fin N))
    (hne : {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty}.Nonempty) (x : ℝ) :
    sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} ≤ x ↔
      0 ≤ x ∧ (crowdedSet q z I x).Nonempty := by
  have hbdd : BddBelow {t : ℝ | 0 ≤ t ∧ (crowdedSet q z I t).Nonempty} := ⟨0, fun t ht => ht.1⟩
  constructor
  · intro hx
    have hmem := (isClosed_crowded q z I).csInf_mem hne hbdd
    exact ⟨hmem.1.trans hx, (hmem.2).mono (crowdedSet_mono q z I hx)⟩
  · intro hx
    exact csInf_le hbdd hx

end Steps

/-! ### Measurability -/

section Measurable

variable {α : Type*} [MeasurableSpace α] {N : ℕ} (q : ℕ) (h : ℝ) {z : α → Fin N → ℂ}
  {r : α → Fin N → ℝ}

theorem measurableSet_dist_le (hz : ∀ i, Measurable fun a => z a i) {t : α → ℝ}
    (ht : Measurable t) (i j : Fin N) : MeasurableSet {a | ‖z a i - z a j‖ ≤ 2 * t a} :=
  measurableSet_le (((hz i).sub (hz j)).norm) (measurable_const.mul ht)

theorem fiberMeasurable_crowdedSet (hz : ∀ i, Measurable fun a => z a i) (I : Finset (Fin N))
    {t : α → ℝ} (ht : Measurable t) : FiberMeasurable fun a => crowdedSet q (z a) I (t a) := by
  classical
  have h1 : ∀ i, FiberMeasurable fun a =>
      I.filter fun j => j ≠ i ∧ ‖z a i - z a j‖ ≤ 2 * t a := fun i =>
    fiberMeasurable_filter I fun j => by
      by_cases hji : j = i
      · simp [hji]
      · simpa [hji] using measurableSet_dist_le hz ht i j
  have h2 : FiberMeasurable fun a =>
      I.filter fun i => q ≤ (I.filter fun j => j ≠ i ∧ ‖z a i - z a j‖ ≤ 2 * t a).card :=
    fiberMeasurable_filter I fun i => (h1 i).measurableSet fun T => q ≤ T.card
  intro T
  simp_rw [crowdedSet_eq]
  exact h2 T

theorem measurable_inf' (hr : ∀ i, Measurable fun a => r a i) {I : Finset (Fin N)}
    (hI : I.Nonempty) : Measurable fun a => I.inf' hI (r a) := by
  refine measurable_of_Iic fun x => ?_
  have : (fun a => I.inf' hI (r a)) ⁻¹' Iic x = ⋃ i ∈ (I : Set (Fin N)), {a | r a i ≤ x} := by
    ext a
    simp [Finset.inf'_le_iff]
  rw [this]
  exact MeasurableSet.biUnion I.countable_toSet fun i _ => measurableSet_le (hr i) measurable_const

theorem measurable_clusterTau (hz : ∀ i, Measurable fun a => z a i)
    (hr : ∀ i, Measurable fun a => r a i) {I : Finset (Fin N)} (hI : I.Nonempty) :
    Measurable fun a => clusterTau q h (z a) (r a) I hI := by
  have hm : Measurable fun a => min h (I.inf' hI (r a) / 4) :=
    measurable_const.min ((measurable_inf' hr hI).div_const 4)
  by_cases hcard : q + 1 ≤ I.card
  · have hne : ∀ a, {t : ℝ | 0 ≤ t ∧ (crowdedSet q (z a) I t).Nonempty}.Nonempty :=
      fun a => (crowded_nonempty_iff q (z a) hI).mpr hcard
    have hs : Measurable fun a => sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q (z a) I t).Nonempty} := by
      refine measurable_of_Iic fun x => ?_
      have : (fun a => sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q (z a) I t).Nonempty}) ⁻¹' Iic x =
          {a | 0 ≤ x ∧ (crowdedSet q (z a) I x).Nonempty} := by
        ext a
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq]
        exact sInf_crowded_le_iff q (z a) I (hne a) x
      rw [this]
      exact (MeasurableSet.const _).inter ((fiberMeasurable_crowdedSet q hz I
        measurable_const).measurableSet fun T => T.Nonempty)
    have heq : (fun a => clusterTau q h (z a) (r a) I hI) =
        fun a => min (min h (I.inf' hI (r a) / 4))
          (sInf {t : ℝ | 0 ≤ t ∧ (crowdedSet q (z a) I t).Nonempty}) := by
      funext a
      unfold clusterTau
      rw [ite_eq_left (hne a)]
    rw [heq]
    exact hm.min hs
  · have heq : (fun a => clusterTau q h (z a) (r a) I hI) =
        fun a => min h (I.inf' hI (r a) / 4) := by
      funext a
      unfold clusterTau
      rw [ite_eq_right fun hn => hcard ((crowded_nonempty_iff q (z a) hI).mp hn)]
    rw [heq]
    exact hm

/-- The comparison of two keys is measurable. -/
theorem measurableSet_key_le (hz : ∀ i, Measurable fun a => z a i)
    (hr : ∀ i, Measurable fun a => r a i) (I : Finset (Fin N)) {τ : α → ℝ} (hτ : Measurable τ)
    (i j : Fin N) :
    MeasurableSet {a | clusterKey q (z a) (r a) I (τ a) i ≤ clusterKey q (z a) (r a) I (τ a) j} := by
  classical
  have hc := fiberMeasurable_crowdedSet q hz I hτ
  have hb : ∀ k : Fin N, FiberMeasurable fun a => decide (k ∉ crowdedSet q (z a) I (τ a)) :=
    fun k => hc.comp fun T => decide (k ∉ T)
  have hset : {a | clusterKey q (z a) (r a) I (τ a) i ≤ clusterKey q (z a) (r a) I (τ a) j} =
      ⋃ b₁ : Bool, ⋃ b₂ : Bool,
        ({a | decide (i ∉ crowdedSet q (z a) I (τ a)) = b₁} ∩
          {a | decide (j ∉ crowdedSet q (z a) I (τ a)) = b₂}) ∩
        {a | b₁ < b₂ ∨ b₁ = b₂ ∧ (r a i < r a j ∨ r a i = r a j ∧ i ≤ j)} := by
    ext a
    simp only [clusterKey, Prod.Lex.toLex_le_toLex, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨_, _, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨b₁, b₂, ⟨rfl, rfl⟩, h⟩; exact h
  rw [hset]
  refine MeasurableSet.iUnion fun b₁ => MeasurableSet.iUnion fun b₂ =>
    ((hb i b₁).inter (hb j b₂)).inter ?_
  refine (MeasurableSet.const _).union ((MeasurableSet.const _).inter ?_)
  exact (measurableSet_lt (hr i) (hr j)).union
    ((measurableSet_eq_fun (hr i) (hr j)).inter (MeasurableSet.const _))

/-- **Measurability of the clustering**: the set of clusters has measurable fibres. -/
theorem fiberMeasurable_clustering (hz : ∀ i, Measurable fun a => z a i)
    (hr : ∀ i, Measurable fun a => r a i) (I : Finset (Fin N)) :
    FiberMeasurable fun a => (sameSignClustering q h (z a) (r a) I).image Prod.fst := by
  classical
  induction I using Finset.strongInduction with
  | H I ih =>
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp_rw [sameSignClustering_of_empty, Finset.image_empty]
    exact FiberMeasurable.const _
  obtain ⟨τ, hτdef⟩ : ∃ τ : α → ℝ, ∀ a, clusterTau q h (z a) (r a) I hI = τ a :=
    ⟨_, fun _ => rfl⟩
  have hτ : Measurable τ := by
    have := measurable_clusterTau q h hz hr hI
    convert this using 1
    funext a
    exact (hτdef a).symm
  -- the pieces: `τ = h`; singleton `{i₀}`; overcrowded centre `i₀` with cluster `J₀`
  let S : Option (Fin N ⊕ (Fin N × Finset (Fin N))) → Set α
    | none => {a | τ a = h}
    | some (Sum.inl i₀) => {a | τ a ≠ h ∧ i₀ ∈ I ∧ r a i₀ / 4 = τ a ∧
        ∀ i ∈ I, i < i₀ → r a i / 4 ≠ τ a}
    | some (Sum.inr (i₀, J₀)) => {a | τ a ≠ h ∧ (∀ i ∈ I, r a i / 4 ≠ τ a) ∧ i₀ ∈ I ∧
        (∀ j ∈ I, clusterKey q (z a) (r a) I (τ a) i₀ ≤ clusterKey q (z a) (r a) I (τ a) j) ∧
        insert i₀ (I.filter fun j => ‖z a j - z a i₀‖ ≤ 2 * τ a) = J₀ ∧ i₀ ∈ J₀}
  let G : Option (Fin N ⊕ (Fin N × Finset (Fin N))) → α → Finset (Finset (Fin N))
    | none => fun _ => I.image fun i => {i}
    | some (Sum.inl i₀) => if i₀ ∈ I then fun a => insert {i₀}
        ((sameSignClustering q h (z a) (r a) (I.erase i₀)).image Prod.fst) else fun _ => ∅
    | some (Sum.inr (i₀, J₀)) => if i₀ ∈ I ∧ i₀ ∈ J₀ then fun a => insert J₀
        ((sameSignClustering q h (z a) (r a) (I \ J₀)).image Prod.fst) else fun _ => ∅
  refine FiberMeasurable.of_cover S G ?_ ?_ ?_ ?_
  · rintro (_ | i₀ | ⟨i₀, J₀⟩)
    · exact measurableSet_eq_fun hτ measurable_const
    · have hlt : MeasurableSet {a | ∀ i ∈ I, i < i₀ → r a i / 4 ≠ τ a} := by
        have : {a | ∀ i ∈ I, i < i₀ → r a i / 4 ≠ τ a} =
            ⋂ i ∈ (I : Set (Fin N)), {a | i < i₀ → r a i / 4 ≠ τ a} := by
          ext a; simp
        rw [this]
        refine MeasurableSet.biInter I.countable_toSet fun i _ => ?_
        by_cases hi : i < i₀
        · have : {a | i < i₀ → r a i / 4 ≠ τ a} = {a | r a i / 4 = τ a}ᶜ := by
            ext a; simp [hi]
          rw [this]
          exact (measurableSet_eq_fun ((hr i).div_const 4) hτ).compl
        · have : {a | i < i₀ → r a i / 4 ≠ τ a} = Set.univ := by
            ext a; simp [hi]
          rw [this]
          exact MeasurableSet.univ
      exact (measurableSet_eq_fun hτ measurable_const).compl.inter
        ((MeasurableSet.const _).inter ((measurableSet_eq_fun ((hr i₀).div_const 4) hτ).inter hlt))
    · have h1 : MeasurableSet {a | ∀ i ∈ I, r a i / 4 ≠ τ a} := by
        have : {a | ∀ i ∈ I, r a i / 4 ≠ τ a} = ⋂ i ∈ (I : Set (Fin N)), {a | r a i / 4 ≠ τ a} := by
          ext a; simp
        rw [this]
        exact MeasurableSet.biInter I.countable_toSet fun i _ =>
          (measurableSet_eq_fun ((hr i).div_const 4) hτ).compl
      have h2 : MeasurableSet {a | ∀ j ∈ I,
          clusterKey q (z a) (r a) I (τ a) i₀ ≤ clusterKey q (z a) (r a) I (τ a) j} := by
        have : {a | ∀ j ∈ I, clusterKey q (z a) (r a) I (τ a) i₀ ≤
            clusterKey q (z a) (r a) I (τ a) j} = ⋂ j ∈ (I : Set (Fin N)),
              {a | clusterKey q (z a) (r a) I (τ a) i₀ ≤ clusterKey q (z a) (r a) I (τ a) j} := by
          ext a; simp
        rw [this]
        exact MeasurableSet.biInter I.countable_toSet fun j _ =>
          measurableSet_key_le q hz hr I hτ i₀ j
      have h3 : MeasurableSet {a | insert i₀ (I.filter fun j => ‖z a j - z a i₀‖ ≤ 2 * τ a) = J₀} :=
        (fiberMeasurable_filter I fun j => measurableSet_dist_le hz hτ j i₀).measurableSet
          fun T => insert i₀ T = J₀
      exact (measurableSet_eq_fun hτ measurable_const).compl.inter (h1.inter
        ((MeasurableSet.const _).inter (h2.inter (h3.inter (MeasurableSet.const _)))))
  · intro a
    by_cases h1 : τ a = h
    · exact ⟨none, h1⟩
    by_cases hs : (I.filter fun i => r a i / 4 = τ a).Nonempty
    · set i₀ := (I.filter fun i => r a i / 4 = τ a).min' hs
      have hmem := Finset.min'_mem _ hs
      rw [Finset.mem_filter] at hmem
      refine ⟨some (Sum.inl i₀), h1, hmem.1, hmem.2, fun i hi hlt heq => ?_⟩
      have := Finset.min'_le (I.filter fun i => r a i / 4 = τ a) i
        (Finset.mem_filter.mpr ⟨hi, heq⟩)
      exact absurd hlt (not_lt.mpr this)
    · have hnone : ∀ i ∈ I, r a i / 4 ≠ τ a := fun i hi heq =>
        hs ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
      set i₀ := clusterChosen q (z a) (r a) I (τ a) hI
      have hkeys := (I.image (clusterKey q (z a) (r a) I (τ a))).min'_mem (hI.image _)
      obtain ⟨j₀, hj₀, hkj₀⟩ := Finset.mem_image.mp hkeys
      have hi₀ : i₀ = j₀ := by
        simp only [i₀, clusterChosen, ← hkj₀]; rfl
      refine ⟨some (Sum.inr (i₀, insert i₀ (I.filter fun j => ‖z a j - z a i₀‖ ≤ 2 * τ a))),
        h1, hnone, hi₀ ▸ hj₀, fun j hj => ?_, rfl, Finset.mem_insert_self _ _⟩
      rw [hi₀, hkj₀]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hj)
  · rintro (_ | i₀ | ⟨i₀, J₀⟩) a ha
    · show (sameSignClustering q h (z a) (r a) I).image Prod.fst = I.image fun i => {i}
      have ha' : τ a = h := ha
      rw [sameSignClustering_eq_of_nonempty q h (z a) (r a) I hI, hτdef a, ite_eq_left ha',
        Finset.image_image]
      rfl
    · obtain ⟨hne, hi₀, hr₀, hlt⟩ := ha
      have hs : (I.filter fun i => r a i / 4 = τ a).Nonempty :=
        ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hr₀⟩⟩
      have hmin : (I.filter fun i => r a i / 4 = τ a).min' hs = i₀ := by
        refine le_antisymm (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hi₀, hr₀⟩)) ?_
        refine Finset.le_min' _ hs _ fun i hi => ?_
        rw [Finset.mem_filter] at hi
        by_contra hlt'
        exact hlt i hi.1 (not_le.mp hlt') hi.2
      show (sameSignClustering q h (z a) (r a) I).image Prod.fst =
        (if i₀ ∈ I then fun a => insert {i₀}
          ((sameSignClustering q h (z a) (r a) (I.erase i₀)).image Prod.fst) else fun _ => ∅) a
      rw [ite_eq_left hi₀, sameSignClustering_eq_of_nonempty q h (z a) (r a) I hI, hτdef a,
        ite_eq_right hne, dite_eq_left hs]
      simp only [Finset.image_insert]
      rw [hmin]
    · obtain ⟨hne, hnone, hi₀, hkey, hJ, hi₀J⟩ := ha
      have hs : ¬ (I.filter fun i => r a i / 4 = τ a).Nonempty := by
        rintro ⟨i, hi⟩
        rw [Finset.mem_filter] at hi
        exact hnone i hi.1 hi.2
      have hchosen : clusterChosen q (z a) (r a) I (τ a) hI = i₀ := by
        have hmin : (I.image (clusterKey q (z a) (r a) I (τ a))).min' (hI.image _) =
            clusterKey q (z a) (r a) I (τ a) i₀ := by
          refine le_antisymm (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hi₀)) ?_
          refine Finset.le_min' _ _ _ fun y hy => ?_
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
          exact hkey j hj
        simp only [clusterChosen, hmin]; rfl
      have hJeq : clusterJ q (z a) (r a) I (τ a) hI = J₀ := by
        rw [← hJ]
        unfold clusterJ
        rw [hchosen]
        congr 1
        exact Finset.filter_congr fun j _ => closedBall_inter_nonempty_iff _ _ _
      show (sameSignClustering q h (z a) (r a) I).image Prod.fst =
        (if i₀ ∈ I ∧ i₀ ∈ J₀ then fun a => insert J₀
          ((sameSignClustering q h (z a) (r a) (I \ J₀)).image Prod.fst) else fun _ => ∅) a
      rw [ite_eq_left ⟨hi₀, hi₀J⟩, sameSignClustering_eq_of_nonempty q h (z a) (r a) I hI, hτdef a,
        ite_eq_right hne, dite_eq_right hs]
      simp only [Finset.image_insert]
      rw [hJeq]
  · rintro (_ | i₀ | ⟨i₀, J₀⟩)
    · exact FiberMeasurable.const _
    · show FiberMeasurable (if i₀ ∈ I then fun a => insert {i₀}
        ((sameSignClustering q h (z a) (r a) (I.erase i₀)).image Prod.fst) else fun _ => ∅)
      by_cases hi₀ : i₀ ∈ I
      · rw [ite_eq_left hi₀]
        exact (ih (I.erase i₀) (Finset.erase_ssubset hi₀)).comp fun T => insert {i₀} T
      · rw [ite_eq_right hi₀]
        exact FiberMeasurable.const _
    · show FiberMeasurable (if i₀ ∈ I ∧ i₀ ∈ J₀ then fun a => insert J₀
        ((sameSignClustering q h (z a) (r a) (I \ J₀)).image Prod.fst) else fun _ => ∅)
      by_cases hg : i₀ ∈ I ∧ i₀ ∈ J₀
      · rw [ite_eq_left hg]
        have hss : I \ J₀ ⊂ I := (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
          ⟨i₀, hg.1, fun h' => (Finset.mem_sdiff.mp h').2 hg.2⟩
        exact (ih (I \ J₀) hss).comp fun T => insert J₀ T
      · rw [ite_eq_right hg]
        exact FiberMeasurable.const _

end Measurable

end TheoremTwo

end MultipoleBKT

end
