/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.FrozenData
public import MultipoleBKT.UpperBound.Hierarchical.FrozenCongr
public import MultipoleBKT.UpperBound.BadPointTypes.Relabel
public import MultipoleBKT.UpperBound.BadPointTypes.SubConfig
public import MultipoleBKT.UpperBound.BadPointTypes.TypeThreePointwise
public import MultipoleBKT.UpperBound.BadPoints.BadBad

/-!
# The bad points of a frozen configuration, relabelled

The paper, Section 5.11: after Lemma 5.16, the bad points
`Z ∈ (Λ²)^{V_bad}` are integrated against
`𝟙_{I_bad = V_bad} ∏_{i<j ∈ V_bad} e^{-β v^Z_ij} 𝟙_{𝒜_ij}
∏_{i ∈ V_bad} (τ_i^{+,Z} τ_i^{-,Z})^{-β/2}`
(`MultipoleBKT.UpperBound.badWeightZ`). The bad-bad interactions are bounded by eq. (5.112)
(Lemma 5.12, applied to the frozen configuration), which leaves the partition function of the bad points (5.113).

Here the labels of `V = V_bad ⊆ [N]` are relabelled to `[m]`, `m = |V|`, along the increasing
enumeration `e : Fin m ↪o Fin N` of `V`: the bad sets, the radii and the interactions of the
frozen configuration `Z` (computed on `V`, with the ambient count threshold `N`) are those of the
sub-configuration `Z ∘ e` (`typeOneOn_eq_map`, `typeTwoOn_eq_map`, `typeThreeOn_eq_map`,
`badRadiusPlusOn_comp`, `badRadiusMinusOn_comp`), by the relabelling of the clustering
(`MultipoleBKT.BadPointTypes.clustering_map`) and of the multipole classes
(`MultipoleBKT.BadPointTypes.classOn_comp_map`).

* `badPartitionFunction`: `Z_{bad,m}` of eq. (5.113), the integral over
  `(Λ²)^m`, `Λ = box Nₐ`, of `𝟙_{I^1 ∪ I^2 ∪ I^3 = [m]} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i (τ_i^+ τ_i^-)^{-β/2}`,
  the bad sets computed with the ambient threshold `Nₐ`;
* `lintegral_badWeightZ_le`: `∫_{(Λ²)^V} badWeightZ ≤ e^{β C |V|} Z_{bad,|V|}`, with `C` the
  constant
  of Lemma 5.12 (eq. (5.112)).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset TheoremTwo BadPointTypes UpperBound
open scoped ENNReal
open TwoComponentCoulomb (box)

/-! ### The partition function of the bad points -/

open scoped Classical in
/-- **`Z_{bad,m}`**, eq. (5.113): the integral over `(Λ²)^m`, `Λ = box Nₐ`, of
`𝟙_{I_bad = [m]} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i (τ_i^{+} τ_i^{-})^{-β/2}`, the bad sets computed from the `m`
dipoles with the ambient count threshold `Nₐ`. -/
noncomputable def badPartitionFunction (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ m : ℕ) : ℝ≥0∞ :=
  ∫⁻ d in boxPi Nₐ m,
    (if badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad Nₐ p₀ β lam M ε₀ d ∪
        typeThreeBad Nₐ p₀ β lam M ε₀ d = univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d)

/-! ### Relabelling the clustering -/

section Relabel

theorem map_biUnion' {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (t : α → Finset β) (f : β ↪ γ) : (s.biUnion t).map f = s.biUnion fun a => (t a).map f := by
  ext x
  simp only [Finset.mem_map, Finset.mem_biUnion]
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, ⟨a, ha, hb⟩, rfl⟩

variable {N m : ℕ} (e : Fin m ↪o Fin N)

theorem clustering_map_eq {q : ℕ} {h : ℝ} (z : Fin N → ℂ) (r : Fin N → ℝ) :
    sameSignClustering q h z r (univ.map e.toEmbedding) =
      (sameSignClustering q h (z ∘ e) (r ∘ e) univ).image
        fun p => (p.1.map e.toEmbedding, p.2) :=
  clustering_map e z r univ

theorem biUnion_fst_filter_map {q : ℕ} {h : ℝ} (z : Fin N → ℂ) (r : Fin N → ℝ) (k : ℕ) :
    ((sameSignClustering q h z r (univ.map e.toEmbedding)).filter
        (fun Sτ => Sτ.1.card = k)).biUnion Prod.fst =
      (((sameSignClustering q h (z ∘ e) (r ∘ e) univ).filter
        (fun Sτ => Sτ.1.card = k)).biUnion Prod.fst).map e.toEmbedding := by
  classical
  rw [clustering_map_eq e z r, Finset.filter_image, Finset.image_biUnion, map_biUnion']
  rw [Finset.filter_congr
    (p := fun a : Finset (Fin m) × ℝ => (a.1.map e.toEmbedding, a.2).1.card = k)
    (q := fun Sτ : Finset (Fin m) × ℝ => Sτ.1.card = k) fun p _ => by simp only [Finset.card_map]]

/-- The type-1 set of the frozen configuration is that of the sub-configuration. -/
theorem typeOneOn_eq_map (p₀ : ℕ) (β lam ε₀ : ℝ) (Z : Fin N → ℂ × ℂ) :
    typeOneOn p₀ β lam ε₀ (univ.map e.toEmbedding) Z =
      (badPointsTypeOne p₀ β lam ε₀ (Z ∘ e)).map e.toEmbedding := by
  classical
  unfold typeOneOn badPointsTypeOne
  simp only []
  rw [Finset.map_union, Finset.map_union, Finset.map_union, Finset.filter_map,
    biUnion_fst_filter_map e (fun i => (Z i).1) (fun i => ‖(Z i).1 - (Z i).2‖),
    biUnion_fst_filter_map e (fun i => (Z i).2) (fun i => ‖(Z i).1 - (Z i).2‖)]
  rfl

/-- The multipole classes of the frozen configuration are those of the sub-configuration. -/
theorem classOn_map_eq (M lam : ℝ) (Z : Fin N → ℂ × ℂ) (U : Finset (Fin m)) (a : Fin m) :
    multipoleClassOn M lam Z (U.map e.toEmbedding) (e a) =
      (multipoleClassOn M lam (Z ∘ e) U a).map e.toEmbedding :=
  (classOn_comp_map (d := Z) e.toEmbedding U a).symm

theorem card_classOn_map (M lam : ℝ) (Z : Fin N → ℂ × ℂ) (U : Finset (Fin m)) (a : Fin m) :
    (multipoleClassOn M lam Z (U.map e.toEmbedding) (e a)).card =
      (multipoleClassOn M lam (Z ∘ e) U a).card := by
  rw [classOn_map_eq e M lam Z U a, Finset.card_map]

theorem filter_classOn_map (M lam : ℝ) (Z : Fin N → ℂ × ℂ) (U : Finset (Fin m)) (P : ℕ → Prop)
    [DecidablePred P] :
    (U.map e.toEmbedding).filter
        (fun i => P (multipoleClassOn M lam Z (U.map e.toEmbedding) i).card)
      = (U.filter fun a => P (multipoleClassOn M lam (Z ∘ e) U a).card).map e.toEmbedding := by
  rw [Finset.filter_map]
  congr 1
  ext a
  simp only [Finset.mem_filter, Function.comp_apply]
  rw [show e.toEmbedding a = e a from rfl, card_classOn_map]

/-- The type-2 set of the frozen configuration is that of the sub-configuration, with the
ambient threshold `N`. -/
theorem typeTwoOn_eq_map (p₀ : ℕ) (β lam M ε₀ : ℝ) (Z : Fin N → ℂ × ℂ) :
    typeTwoOn p₀ β lam M ε₀ (univ.map e.toEmbedding) Z =
      (typeTwoBad N p₀ β lam M ε₀ (Z ∘ e)).map e.toEmbedding := by
  classical
  have hU : univ.map e.toEmbedding \ typeOneOn p₀ β lam ε₀ (univ.map e.toEmbedding) Z =
      (univ \ badPointsTypeOne p₀ β lam ε₀ (Z ∘ e)).map e.toEmbedding := by
    rw [typeOneOn_eq_map, Finset.map_sdiff]
  unfold typeTwoOn typeTwoBad typeTwoOneBad typeTwoTwoBad
  simp only []
  rw [hU, Finset.map_union, filter_classOn_map e M lam Z _ (fun c => pBeta p₀ β < c),
    map_biUnion']
  congr 1
  refine Finset.biUnion_congr rfl fun k _ => ?_
  rw [filter_classOn_map e M lam Z _ (fun c => c = k), Finset.card_map]
  split_ifs
  · rfl
  · exact (Finset.map_empty _).symm

/-- The type-3 set of the frozen configuration is that of the sub-configuration, with the
ambient threshold `N`. -/
theorem typeThreeOn_eq_map (p₀ : ℕ) (β lam M ε₀ : ℝ) (Z : Fin N → ℂ × ℂ) :
    typeThreeOn p₀ β lam M ε₀ (univ.map e.toEmbedding) Z =
      (typeThreeBad N p₀ β lam M ε₀ (Z ∘ e)).map e.toEmbedding := by
  classical
  set y := Z ∘ e
  set I₁₂ := badPointsTypeOne p₀ β lam ε₀ y ∪ typeTwoBad N p₀ β lam M ε₀ y with hI
  have h12 : typeOneOn p₀ β lam ε₀ (univ.map e.toEmbedding) Z ∪
      typeTwoOn p₀ β lam M ε₀ (univ.map e.toEmbedding) Z = I₁₂.map e.toEmbedding := by
    rw [typeOneOn_eq_map, typeTwoOn_eq_map, Finset.map_union]
  have hU : univ.map e.toEmbedding \ typeOneOn p₀ β lam ε₀ (univ.map e.toEmbedding) Z =
      (univ \ badPointsTypeOne p₀ β lam ε₀ y).map e.toEmbedding := by
    rw [typeOneOn_eq_map, Finset.map_sdiff]
  have hV : univ.map e.toEmbedding \ I₁₂.map e.toEmbedding = (univ \ I₁₂).map e.toEmbedding :=
    (Finset.map_sdiff _ _).symm
  -- `J^3`
  have hJ : (univ.map e.toEmbedding \ I₁₂.map e.toEmbedding).filter (fun i => ∃ j ∈ I₁₂.map
      e.toEmbedding, min (min ‖(Z i).1 - (Z j).1‖ ‖(Z i).1 - (Z j).2‖)
        (min ‖(Z i).2 - (Z j).1‖ ‖(Z i).2 - (Z j).2‖) ≤ M * max ‖(Z i).1 - (Z i).2‖ lam) =
      ((univ \ I₁₂).filter fun a => ∃ b ∈ I₁₂, min (min ‖(y a).1 - (y b).1‖ ‖(y a).1 - (y b).2‖)
        (min ‖(y a).2 - (y b).1‖ ‖(y a).2 - (y b).2‖) ≤ M * max ‖(y a).1 - (y a).2‖ lam).map
          e.toEmbedding := by
    rw [hV, Finset.filter_map]
    congr 1
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨ha, j, hj, hnear⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.1 hj
      exact ⟨ha, b, hb, hnear⟩
    · rintro ⟨ha, b, hb, hnear⟩
      exact ⟨ha, e b, Finset.mem_map_of_mem _ hb, hnear⟩
  unfold typeThreeOn typeThreeBad
  simp only []
  rw [h12, hU, hJ, hV, Finset.filter_map]
  congr 1
  ext a
  simp only [Finset.mem_filter, Function.comp_apply]
  rw [show e.toEmbedding a = e a from rfl, classOn_map_eq, ← Finset.map_inter,
    Finset.map_nonempty]

/-- The bad points of the frozen configuration are those of the sub-configuration. -/
theorem badPointsOn_eq_map (p₀ : ℕ) (β lam M ε₀ : ℝ) (Z : Fin N → ℂ × ℂ) :
    badPointsOn p₀ β lam M ε₀ (univ.map e.toEmbedding) Z =
      (badPointsTypeOne p₀ β lam ε₀ (Z ∘ e) ∪ typeTwoBad N p₀ β lam M ε₀ (Z ∘ e) ∪
        typeThreeBad N p₀ β lam M ε₀ (Z ∘ e)).map e.toEmbedding := by
  unfold badPointsOn
  rw [typeOneOn_eq_map, typeTwoOn_eq_map, typeThreeOn_eq_map, Finset.map_union,
    Finset.map_union]

theorem clusterRemovalValueOn_map {q : ℕ} {h : ℝ} (z : Fin N → ℂ) (r : Fin N → ℝ) (a : Fin m) :
    clusterRemovalValueOn q h z r (univ.map e.toEmbedding) (e a) =
      clusterRemovalValue q h (z ∘ e) (r ∘ e) a := by
  unfold clusterRemovalValueOn clusterRemovalValue
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  rw [clustering_map_eq e z r]
  constructor
  · rintro ⟨p, ⟨hp, hap⟩, rfl⟩
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hp
    refine ⟨p', ⟨hp', ?_⟩, rfl⟩
    exact (Finset.mem_map' e.toEmbedding).1 hap
  · rintro ⟨p', ⟨hp', hap'⟩, rfl⟩
    exact ⟨_, ⟨Finset.mem_image_of_mem _ hp', Finset.mem_map_of_mem _ hap'⟩, rfl⟩

/-- The radius `τ^{+,Z}` of the frozen configuration is that of the sub-configuration. -/
theorem badRadiusPlusOn_comp (p₀ : ℕ) (β lam ε₀ : ℝ) (Z : Fin N → ℂ × ℂ) (a : Fin m) :
    badRadiusPlusOn p₀ β lam ε₀ (univ.map e.toEmbedding) Z (e a) =
      radiusPlus p₀ β lam ε₀ (Z ∘ e) a := by
  unfold badRadiusPlusOn clusterRadiusOn radiusPlus clusterRadius
  rw [clusterRemovalValueOn_map e]
  rw [max_comm, ← max_assoc, max_self]
  rfl

/-- The radius `τ^{-,Z}` of the frozen configuration is that of the sub-configuration. -/
theorem badRadiusMinusOn_comp (p₀ : ℕ) (β lam ε₀ : ℝ) (Z : Fin N → ℂ × ℂ) (a : Fin m) :
    badRadiusMinusOn p₀ β lam ε₀ (univ.map e.toEmbedding) Z (e a) =
      radiusMinus p₀ β lam ε₀ (Z ∘ e) a := by
  unfold badRadiusMinusOn clusterRadiusOn radiusMinus clusterRadius
  rw [clusterRemovalValueOn_map e]
  rw [max_comm, ← max_assoc, max_self]
  rfl

end Relabel

/-! ### The weight of the bad points -/

section Weight

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {N : ℕ}

/-- `v^Z_ij = v'_ij`: the interaction of two frozen bad points is the interaction of
Proposition 3.3 with their radii. -/
theorem pairInteraction_eq_ballGrowthInteraction {m : ℕ} (y : Fin m → ℂ × ℂ) (τp τm : Fin m → ℝ)
    (a b : Fin m) :
    pairInteraction χ lam (y a) (y b) (τp a, τm a) (τp b, τm b) =
      ballGrowthInteraction χ lam τp τm y a b := by
  unfold pairInteraction ballGrowthInteraction
  ring

/-- A product over the pairs `i < j` of `V` is the product over the pairs `a < b` of
`Fin |V|`, along the increasing enumeration of `V`. -/
theorem prod_pairs_orderEmbOfFin {α : Type*} [CommMonoid α] (V : Finset (Fin N))
    (g : Fin N → Fin N → α) :
    ∏ i ∈ V, ∏ j ∈ V with i < j, g i j =
      ∏ a : Fin V.card, ∏ b ∈ univ.filter (fun b => a < b),
        g (V.orderEmbOfFin rfl a) (V.orderEmbOfFin rfl b) := by
  classical
  rw [prod_orderEmbOfFin V]
  refine Finset.prod_congr rfl fun a _ => ?_
  set e := V.orderEmbOfFin rfl
  have hV : univ.map e.toEmbedding = V := Finset.map_orderEmbOfFin_univ V rfl
  have hfilt : V.filter (fun j => e a < j) = (univ.filter fun b => a < b).map e.toEmbedding := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hlt⟩
      have : j ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hj
      obtain ⟨b, rfl⟩ := this
      exact ⟨b, e.lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨b, hab, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem V rfl b, e.lt_iff_lt.2 hab⟩
  rw [hfilt, Finset.prod_map]
  rfl

open scoped Classical in
/-- **The pointwise bound with eq. (5.112)**: for the frozen configuration `Z` on `V`, with
`y = Z ∘ e` its sub-configuration, `badWeightZ ≤ e^{β C |V|} 𝟙_{I_bad(y) = [m]} 𝟙_{σ = Id}
∏ (τ^+ τ^-)^{-β/2}`, `C` from Lemma 5.12
(`MultipoleBKT.UpperBound.sum_lt_ballGrowthInteraction_ge`). -/
theorem badWeightZ_le {C : ℝ}
    (hC : ∀ {n : ℕ} (h lam : ℝ) (c : Fin n → ℂ × ℂ) (S : Finset (Fin n)), 0 < lam →
      (∀ i ∈ S, ∀ j ∈ S, i < j → IsStableDipolePair (c i) (c j)) →
      -(C * S.card) ≤ ∑ i ∈ S, ∑ j ∈ S with i < j, ballGrowthInteraction χ lam
        (clusterRadius (clusterThreshold p₀ β) h lam (fun k => (c k).1)
          fun k => ‖(c k).1 - (c k).2‖)
        (clusterRadius (clusterThreshold p₀ β) h lam (fun k => (c k).2)
          fun k => ‖(c k).1 - (c k).2‖) c i j)
    (hβ : 0 ≤ β) (hlam : 0 < lam) (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ) :
    badWeightZ χ p₀ β lam M ε₀ V Z ≤ Real.exp (β * C * V.card) *
      ((if badPointsTypeOne p₀ β lam ε₀ (Z ∘ V.orderEmbOfFin rfl) ∪
          typeTwoBad N p₀ β lam M ε₀ (Z ∘ V.orderEmbOfFin rfl) ∪
          typeThreeBad N p₀ β lam M ε₀ (Z ∘ V.orderEmbOfFin rfl) = univ ∧
          StablePairs (Z ∘ V.orderEmbOfFin rfl) then 1 else 0) *
        typeOneWeight p₀ β lam ε₀ (Z ∘ V.orderEmbOfFin rfl)) := by
  set e := V.orderEmbOfFin rfl with he
  set y := Z ∘ e with hy
  have hV : univ.map e.toEmbedding = V := Finset.map_orderEmbOfFin_univ V rfl
  have hW0 : 0 ≤ typeOneWeight p₀ β lam ε₀ y := typeOneWeight_nonneg p₀ β hlam.le ε₀ y
  have hRHS0 : 0 ≤ Real.exp (β * C * V.card) *
      ((if badPointsTypeOne p₀ β lam ε₀ y ∪ typeTwoBad N p₀ β lam M ε₀ y ∪
          typeThreeBad N p₀ β lam M ε₀ y = univ ∧ StablePairs y then (1 : ℝ) else 0) *
        typeOneWeight p₀ β lam ε₀ y) := by
    refine mul_nonneg (Real.exp_pos _).le (mul_nonneg ?_ hW0)
    split_ifs <;> norm_num
  unfold badWeightZ
  by_cases hbad : badPointsOn p₀ β lam M ε₀ V Z = V
  swap
  · rw [ite_eq_right hbad, zero_mul, zero_mul]
    exact hRHS0
  rw [ite_eq_left hbad, one_mul]
  -- the bad sets of the sub-configuration
  have hsets : badPointsTypeOne p₀ β lam ε₀ y ∪ typeTwoBad N p₀ β lam M ε₀ y ∪
      typeThreeBad N p₀ β lam M ε₀ y = univ := by
    have h := badPointsOn_eq_map e p₀ β lam M ε₀ Z
    rw [hV, hbad] at h
    conv_lhs at h => rw [← hV]
    exact (Finset.map_inj.1 h).symm
  -- the radii
  have hrad : ∏ i ∈ V, 1 / (badRadiusPlusOn p₀ β lam ε₀ V Z i ^ (β / 2) *
      badRadiusMinusOn p₀ β lam ε₀ V Z i ^ (β / 2)) = typeOneWeight p₀ β lam ε₀ y := by
    rw [prod_orderEmbOfFin V]
    unfold typeOneWeight
    refine Finset.prod_congr rfl fun a _ => ?_
    have h1 := badRadiusPlusOn_comp e p₀ β lam ε₀ Z a
    have h2 := badRadiusMinusOn_comp e p₀ β lam ε₀ Z a
    rw [hV] at h1 h2
    rw [h1, h2]
    have hp : 0 < radiusPlus p₀ β lam ε₀ y a := hlam.trans_le (le_clusterRadius lam a)
    have hm : 0 < radiusMinus p₀ β lam ε₀ y a := hlam.trans_le (le_clusterRadius lam a)
    rw [Real.mul_rpow hp.le hm.le, Real.rpow_neg hp.le, Real.rpow_neg hm.le, one_div,
      mul_inv]
  rw [hrad]
  -- the interactions
  by_cases hst : StablePairs y
  · rw [ite_eq_left ⟨hsets, hst⟩, one_mul]
    refine mul_le_mul_of_nonneg_right ?_ hW0
    rw [prod_pairs_orderEmbOfFin V]
    have hpair : ∀ a : Fin V.card, ∀ b ∈ univ.filter (fun b => a < b),
        (if IsStableDipolePair (Z (e a)) (Z (e b)) then
          Real.exp (-β * interactionBadZ χ p₀ β lam ε₀ V Z (e a) (e b)) else 0) =
        Real.exp (-β * ballGrowthInteraction χ lam (radiusPlus p₀ β lam ε₀ y)
          (radiusMinus p₀ β lam ε₀ y) y a b) := by
      intro a b hb
      rw [ite_eq_left (show IsStableDipolePair (Z (e a)) (Z (e b)) from
        hst a b (Finset.mem_filter.1 hb).2)]
      congr 2
      unfold interactionBadZ badRadiiZ
      have h1 := badRadiusPlusOn_comp e p₀ β lam ε₀ Z
      have h2 := badRadiusMinusOn_comp e p₀ β lam ε₀ Z
      rw [hV] at h1 h2
      rw [h1, h2, h1, h2]
      exact pairInteraction_eq_ballGrowthInteraction y _ _ a b
    rw [Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl (hpair a)]
    simp_rw [← Real.exp_sum]
    rw [Real.exp_le_exp]
    have hsum := hC (cutoff p₀ β lam ε₀) lam y univ hlam
      (fun a _ b _ hab => hst a b hab)
    rw [Finset.card_univ, Fintype.card_fin] at hsum
    have hcard : (V.card : ℝ) = (Fintype.card (Fin V.card) : ℝ) := by rw [Fintype.card_fin]
    simp_rw [← Finset.mul_sum]
    have hsum' : -(C * V.card) ≤ ∑ a : Fin V.card, ∑ b ∈ univ.filter (fun b => a < b),
        ballGrowthInteraction χ lam (radiusPlus p₀ β lam ε₀ y) (radiusMinus p₀ β lam ε₀ y) y a b :=
      hsum
    have h2 := mul_le_mul_of_nonneg_left hsum' hβ
    linarith
  · rw [ite_eq_right fun h => hst h.2, zero_mul, mul_zero]
    obtain ⟨a, b, hab, hns⟩ : ∃ a b : Fin V.card, a < b ∧ ¬ IsStableDipolePair (y a) (y b) := by
      by_contra hcon
      push Not at hcon
      exact hst fun a b hab => hcon a b hab
    rw [prod_pairs_orderEmbOfFin V]
    have hzero : ∏ b ∈ univ.filter (fun b => a < b),
        (if IsStableDipolePair (Z (e a)) (Z (e b)) then
          Real.exp (-β * interactionBadZ χ p₀ β lam ε₀ V Z (e a) (e b)) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ b, hab⟩) (ite_eq_right hns)
    rw [Finset.prod_eq_zero (Finset.mem_univ a) hzero, zero_mul]

/-- **The integral of the weight of the bad points**:
`∫_{(Λ²)^V} badWeightZ ≤ e^{β C |V|} Z_{bad,|V|}`,
with `C` the constant of Lemma 5.12 (eq. (5.112)), depending only on `χ`, `p₀`, `β`. -/
theorem lintegral_badWeightZ_le (hχ : IsMollifier χ) (p₀ : ℕ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (V : Finset (Fin N)) (lam M ε₀ : ℝ), 0 < lam →
      ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z')) ≤
        ENNReal.ofReal (Real.exp (β * C * V.card)) *
          badPartitionFunction p₀ β lam M ε₀ N V.card := by
  classical
  obtain ⟨C, hC0, hC⟩ := sum_lt_ballGrowthInteraction_ge hχ (clusterThreshold p₀ β)
  refine ⟨C, hC0, fun {N} V lam M ε₀ hlam => ?_⟩
  set m := V.card
  set e := V.orderEmbOfFin rfl with he
  set f : Fin m ≃ V := (V.orderIsoOfFin rfl).toEquiv with hf
  set Ψ := MeasurableEquiv.piCongrLeft (fun _ : V => ℂ × ℂ) f
  have hΨ : MeasurePreserving Ψ volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : V => ℂ × ℂ) f
  have hΨf : ∀ (y : Fin m → ℂ × ℂ) (a : Fin m), Ψ y (f a) = y a := fun y a =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : V => ℂ × ℂ) f y a
  have hfa : ∀ a : Fin m, (f a : Fin N) = e a := fun a => Finset.coe_orderIsoOfFin_apply V rfl a
  have hext : ∀ y : Fin m → ℂ × ℂ, extendBad V (Ψ y) ∘ e = y := by
    intro y
    funext a
    have hmem : e a ∈ V := Finset.orderEmbOfFin_mem V rfl a
    simp only [Function.comp_apply, extendBad, hmem, ↓reduceDIte]
    have : (⟨e a, hmem⟩ : V) = f a := Subtype.ext (hfa a).symm
    rw [this, hΨf]
  have hboxiff : ∀ y : Fin m → ℂ × ℂ, Ψ y ∈ Set.univ.pi (fun _ : V => box N ×ˢ box N) ↔
      y ∈ boxPi N m := by
    intro y
    simp only [Set.mem_univ_pi, boxPi]
    constructor
    · intro h a
      have := h (f a)
      rwa [hΨf] at this
    · intro h v
      obtain ⟨a, rfl⟩ := f.surjective v
      rw [hΨf]
      exact h a
  set S := Set.univ.pi (fun _ : V => box N ×ˢ box N)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ =>
    (TwoComponentCoulomb.measurableSet_box N).prod (TwoComponentCoulomb.measurableSet_box N)
  set F : (V → ℂ × ℂ) → ℝ≥0∞ := fun Z' =>
    ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z'))
  set G : (Fin m → ℂ × ℂ) → ℝ≥0∞ := (boxPi N m).indicator fun d =>
    (if badPointsTypeOne p₀ β lam ε₀ d ∪ typeTwoBad N p₀ β lam M ε₀ d ∪
        typeThreeBad N p₀ β lam M ε₀ d = univ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d)
  have hpt : ∀ y, S.indicator F (Ψ y) ≤ ENNReal.ofReal (Real.exp (β * C * m)) * G y := by
    intro y
    by_cases hy : y ∈ boxPi N m
    · simp only [G]
      rw [Set.indicator_of_mem ((hboxiff y).2 hy), Set.indicator_of_mem hy]
      have hb := badWeightZ_le (M := M) (ε₀ := ε₀) hC hβ hlam V (extendBad V (Ψ y))
      rw [← he, hext y] at hb
      refine (ENNReal.ofReal_le_ofReal hb).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      split_ifs
      · rw [one_mul, one_mul]
      · rw [zero_mul, zero_mul, ENNReal.ofReal_zero]
    · simp only [G]
      rw [Set.indicator_of_notMem (fun h => hy ((hboxiff y).1 h)), Set.indicator_of_notMem hy,
        mul_zero]
  calc ∫⁻ Z' in S, F Z' = ∫⁻ Z', S.indicator F Z' := (lintegral_indicator hS F).symm
    _ = ∫⁻ y, S.indicator F (Ψ y) := (hΨ.lintegral_comp_emb Ψ.measurableEmbedding _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (β * C * m)) * G y := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (β * C * m)) * ∫⁻ y, G y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Real.exp (β * C * m)) * badPartitionFunction p₀ β lam M ε₀ N m := by
        rw [lintegral_indicator (measurableSet_boxPi N m)]
        rfl

end Weight

end UpperBoundLDP

end MultipoleBKT

end
