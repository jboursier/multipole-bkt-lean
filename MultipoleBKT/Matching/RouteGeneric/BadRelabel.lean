/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.SubConfig
public import MultipoleBKT.UpperBound.Hierarchical.BadSetOn
public import MultipoleBKT.Matching.RouteGeneric.Exceptional

/-!
# Arbitrary relabeling of the derived bad sets

Definition 5.1
and Definitions 5.2 through 5.5.
Distinct dipole lengths remove the index tie breakers. The class correspondence
then transports the count thresholds and the near-bad-point test.
-/

@[expose] public section

namespace MultipoleBKT.BadPointTypes.Permutation

open MeasureTheory Finset TheoremTwo BadPointTypes UpperBound

theorem map_biUnion' {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (t : α → Finset β) (f : β ↪ γ) : (s.biUnion t).map f = s.biUnion fun a => (t a).map f := by
  ext x
  simp only [Finset.mem_map, Finset.mem_biUnion]
  constructor
  · rintro ⟨b, ⟨a, ha, hb⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, ⟨a, ha, hb⟩, rfl⟩

variable {N m : ℕ} (e : Fin m ↪ Fin N)

theorem clustering_map_eq {q : ℕ} {h : ℝ} (z : Fin N → ℂ) (r : Fin N → ℝ) (hr : Function.Injective r) :
    sameSignClustering q h z r (univ.map e) =
      (sameSignClustering q h (z ∘ e) (r ∘ e) univ).image
        fun p => (p.1.map e, p.2) :=
  clustering_embedding e z r hr univ

theorem biUnion_fst_filter_map {q : ℕ} {h : ℝ} (z : Fin N → ℂ) (r : Fin N → ℝ) (hr : Function.Injective r) (k : ℕ) :
    ((sameSignClustering q h z r (univ.map e)).filter
        (fun Sτ => Sτ.1.card = k)).biUnion Prod.fst =
      (((sameSignClustering q h (z ∘ e) (r ∘ e) univ).filter
        (fun Sτ => Sτ.1.card = k)).biUnion Prod.fst).map e := by
  classical
  rw [clustering_map_eq e z r hr, Finset.filter_image, Finset.image_biUnion, map_biUnion']
  rw [Finset.filter_congr
    (p := fun a : Finset (Fin m) × ℝ => (a.1.map e, a.2).1.card = k)
    (q := fun Sτ : Finset (Fin m) × ℝ => Sτ.1.card = k) fun p _ => by simp only [Finset.card_map]]

/-- The type-1 set of the frozen configuration is that of the sub-configuration. -/
theorem typeOneOn_eq_map (p₀ : ℕ) (β lam ε₀ : ℝ) (Z : Fin N → ℂ × ℂ)
    (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) :
    typeOneOn p₀ β lam ε₀ (univ.map e) Z =
      (badPointsTypeOne p₀ β lam ε₀ (Z ∘ e)).map e := by
  classical
  unfold typeOneOn badPointsTypeOne
  simp only []
  rw [Finset.map_union, Finset.map_union, Finset.map_union, Finset.filter_map,
    biUnion_fst_filter_map e (fun i => (Z i).1) (fun i => ‖(Z i).1 - (Z i).2‖) hr,
    biUnion_fst_filter_map e (fun i => (Z i).2) (fun i => ‖(Z i).1 - (Z i).2‖) hr]
  rfl

/-- The multipole classes of the frozen configuration are those of the sub-configuration. -/
theorem classOn_map_eq (M lam : ℝ) (Z : Fin N → ℂ × ℂ) (U : Finset (Fin m)) (a : Fin m) :
    multipoleClassOn M lam Z (U.map e) (e a) =
      (multipoleClassOn M lam (Z ∘ e) U a).map e :=
  (classOn_comp_map (d := Z) e U a).symm

theorem card_classOn_map (M lam : ℝ) (Z : Fin N → ℂ × ℂ) (U : Finset (Fin m)) (a : Fin m) :
    (multipoleClassOn M lam Z (U.map e) (e a)).card =
      (multipoleClassOn M lam (Z ∘ e) U a).card := by
  rw [classOn_map_eq e M lam Z U a, Finset.card_map]

theorem filter_classOn_map (M lam : ℝ) (Z : Fin N → ℂ × ℂ) (U : Finset (Fin m)) (P : ℕ → Prop)
    [DecidablePred P] :
    (U.map e).filter
        (fun i => P (multipoleClassOn M lam Z (U.map e) i).card)
      = (U.filter fun a => P (multipoleClassOn M lam (Z ∘ e) U a).card).map e := by
  rw [Finset.filter_map]
  congr 1
  ext a
  simp only [Finset.mem_filter, Function.comp_apply]
  rw [card_classOn_map]

/-- The type-2 set of the frozen configuration is that of the sub-configuration, with the
ambient threshold `N`. -/
theorem typeTwoOn_eq_map (p₀ : ℕ) (β lam M ε₀ : ℝ) (Z : Fin N → ℂ × ℂ)
    (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) :
    typeTwoOn p₀ β lam M ε₀ (univ.map e) Z =
      (typeTwoBad N p₀ β lam M ε₀ (Z ∘ e)).map e := by
  classical
  have hU : univ.map e \ typeOneOn p₀ β lam ε₀ (univ.map e) Z =
      (univ \ badPointsTypeOne p₀ β lam ε₀ (Z ∘ e)).map e := by
    rw [typeOneOn_eq_map e p₀ β lam ε₀ Z hr, Finset.map_sdiff]
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
theorem typeThreeOn_eq_map (p₀ : ℕ) (β lam M ε₀ : ℝ) (Z : Fin N → ℂ × ℂ)
    (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) :
    typeThreeOn p₀ β lam M ε₀ (univ.map e) Z =
      (typeThreeBad N p₀ β lam M ε₀ (Z ∘ e)).map e := by
  classical
  set y := Z ∘ e
  set I₁₂ := badPointsTypeOne p₀ β lam ε₀ y ∪ typeTwoBad N p₀ β lam M ε₀ y with hI
  have h12 : typeOneOn p₀ β lam ε₀ (univ.map e) Z ∪
      typeTwoOn p₀ β lam M ε₀ (univ.map e) Z = I₁₂.map e := by
    rw [typeOneOn_eq_map e p₀ β lam ε₀ Z hr, typeTwoOn_eq_map e p₀ β lam M ε₀ Z hr, Finset.map_union]
  have hU : univ.map e \ typeOneOn p₀ β lam ε₀ (univ.map e) Z =
      (univ \ badPointsTypeOne p₀ β lam ε₀ y).map e := by
    rw [typeOneOn_eq_map e p₀ β lam ε₀ Z hr, Finset.map_sdiff]
  have hV : univ.map e \ I₁₂.map e = (univ \ I₁₂).map e :=
    (Finset.map_sdiff _ _).symm
  -- `J^3`
  have hJ : (univ.map e \ I₁₂.map e).filter (fun i => ∃ j ∈ I₁₂.map
      e, min (min ‖(Z i).1 - (Z j).1‖ ‖(Z i).1 - (Z j).2‖)
        (min ‖(Z i).2 - (Z j).1‖ ‖(Z i).2 - (Z j).2‖) ≤ M * max ‖(Z i).1 - (Z i).2‖ lam) =
      ((univ \ I₁₂).filter fun a => ∃ b ∈ I₁₂, min (min ‖(y a).1 - (y b).1‖ ‖(y a).1 - (y b).2‖)
        (min ‖(y a).2 - (y b).1‖ ‖(y a).2 - (y b).2‖) ≤ M * max ‖(y a).1 - (y a).2‖ lam).map
          e := by
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
  rw [classOn_map_eq, ← Finset.map_inter,
    Finset.map_nonempty]

/-- The bad points of the frozen configuration are those of the sub-configuration. -/
theorem badPointsOn_eq_map (p₀ : ℕ) (β lam M ε₀ : ℝ) (Z : Fin N → ℂ × ℂ)
    (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) :
    badPointsOn p₀ β lam M ε₀ (univ.map e) Z =
      (badPointsTypeOne p₀ β lam ε₀ (Z ∘ e) ∪ typeTwoBad N p₀ β lam M ε₀ (Z ∘ e) ∪
        typeThreeBad N p₀ β lam M ε₀ (Z ∘ e)).map e := by
  unfold badPointsOn
  rw [typeOneOn_eq_map e p₀ β lam ε₀ Z hr, typeTwoOn_eq_map e p₀ β lam M ε₀ Z hr, typeThreeOn_eq_map e p₀ β lam M ε₀ Z hr, Finset.map_union,
    Finset.map_union]

theorem clusterRemovalValueOn_map {q : ℕ} {h : ℝ} (z : Fin N → ℂ) (r : Fin N → ℝ) (hr : Function.Injective r) (a : Fin m) :
    clusterRemovalValueOn q h z r (univ.map e) (e a) =
      clusterRemovalValue q h (z ∘ e) (r ∘ e) a := by
  unfold clusterRemovalValueOn clusterRemovalValue
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  rw [clustering_map_eq e z r hr]
  constructor
  · rintro ⟨p, ⟨hp, hap⟩, rfl⟩
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hp
    refine ⟨p', ⟨hp', ?_⟩, rfl⟩
    exact (Finset.mem_map' e).1 hap
  · rintro ⟨p', ⟨hp', hap'⟩, rfl⟩
    exact ⟨_, ⟨Finset.mem_image_of_mem _ hp', Finset.mem_map_of_mem _ hap'⟩, rfl⟩

/-- The radius `τ^{+,Z}` of the frozen configuration is that of the sub-configuration. -/
theorem badRadiusPlusOn_comp (p₀ : ℕ) (β lam ε₀ : ℝ) (Z : Fin N → ℂ × ℂ)
    (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) (a : Fin m) :
    badRadiusPlusOn p₀ β lam ε₀ (univ.map e) Z (e a) =
      radiusPlus p₀ β lam ε₀ (Z ∘ e) a := by
  unfold badRadiusPlusOn clusterRadiusOn radiusPlus clusterRadius
  rw [clusterRemovalValueOn_map e _ _ hr]
  rw [max_comm, ← max_assoc, max_self]
  rfl

/-- The radius `τ^{-,Z}` of the frozen configuration is that of the sub-configuration. -/
theorem badRadiusMinusOn_comp (p₀ : ℕ) (β lam ε₀ : ℝ) (Z : Fin N → ℂ × ℂ)
    (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) (a : Fin m) :
    badRadiusMinusOn p₀ β lam ε₀ (univ.map e) Z (e a) =
      radiusMinus p₀ β lam ε₀ (Z ∘ e) a := by
  unfold badRadiusMinusOn clusterRadiusOn radiusMinus clusterRadius
  rw [clusterRemovalValueOn_map e _ _ hr]
  rw [max_comm, ← max_assoc, max_self]
  rfl

/-- The bad set itself commutes with every permutation once dipole lengths are distinct. -/
theorem badPoints_permutation (π : Equiv.Perm (Fin N)) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (Z : Fin N → ℂ × ℂ) (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) :
    badPoints p₀ β lam M ε₀ Z = (badPoints p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding := by
  have ht := badPointsOn_eq_map π.toEmbedding p₀ β lam M ε₀ Z hr
  simpa only [Equiv.coe_toEmbedding, Finset.map_univ_equiv, badPointsOn_univ, typeTwoBad_self, typeThreeBad_self,
    badPoints] using ht

/-- The complementary good labels have the same permutation symmetry. -/
theorem goodPoints_permutation (π : Equiv.Perm (Fin N)) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (Z : Fin N → ℂ × ℂ) (hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖) :
    goodPoints p₀ β lam M ε₀ Z = (goodPoints p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding := by
  rw [goodPoints, goodPoints, badPoints_permutation π p₀ β lam M ε₀ Z hr,
    Finset.map_sdiff, Finset.map_univ_equiv]

/-- Outside the paper's exceptional set, all three bad types, their union,
and the good labels commute with arbitrary permutations. -/
theorem badData_permutation {Z : Fin N → ℂ × ℂ} {h : ℝ}
    (hc : RouteGeneric.OutsideExceptional h Z) (π : Equiv.Perm (Fin N))
    (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    badPointsTypeOne p₀ β lam ε₀ Z =
      (badPointsTypeOne p₀ β lam ε₀ (Z ∘ π)).map π.toEmbedding ∧
    badPointsTypeTwo p₀ β lam M ε₀ Z =
      (badPointsTypeTwo p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding ∧
    badPointsTypeThree p₀ β lam M ε₀ Z =
      (badPointsTypeThree p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding ∧
    badPoints p₀ β lam M ε₀ Z = (badPoints p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding ∧
    goodPoints p₀ β lam M ε₀ Z = (goodPoints p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding := by
  have hr : Function.Injective fun i => ‖(Z i).1 - (Z i).2‖ := by
    intro i j hij
    exact congrArg Prod.fst (hc.1 (show
      (fun p : Fin N × Fin N => ‖(Z p.1).1 - (Z p.2).2‖) (i, i) =
      (fun p : Fin N × Fin N => ‖(Z p.1).1 - (Z p.2).2‖) (j, j) from hij))
  refine ⟨?_, ?_, ?_, badPoints_permutation π p₀ β lam M ε₀ Z hr,
    goodPoints_permutation π p₀ β lam M ε₀ Z hr⟩
  · simpa only [Equiv.coe_toEmbedding, Finset.map_univ_equiv, typeOneOn_univ] using
      typeOneOn_eq_map π.toEmbedding p₀ β lam ε₀ Z hr
  · simpa only [Equiv.coe_toEmbedding, Finset.map_univ_equiv, typeTwoOn_univ, typeTwoBad_self] using
      typeTwoOn_eq_map π.toEmbedding p₀ β lam M ε₀ Z hr
  · simpa only [Equiv.coe_toEmbedding, Finset.map_univ_equiv, typeThreeOn_univ, typeThreeBad_self] using
      typeThreeOn_eq_map π.toEmbedding p₀ β lam M ε₀ Z hr

/-- Almost every configuration has the arbitrary-permutation symmetry of the bad sets,
simultaneously for all parameters and label permutations. -/
theorem ae_badData_permutation :
    ∀ᵐ Z ∂(volume : Measure (Fin N → ℂ × ℂ)),
      ∀ (π : Equiv.Perm (Fin N)) (p₀ : ℕ) (β lam M ε₀ : ℝ),
      badPoints p₀ β lam M ε₀ Z =
        (badPoints p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding ∧
      goodPoints p₀ β lam M ε₀ Z =
        (goodPoints p₀ β lam M ε₀ (Z ∘ π)).map π.toEmbedding := by
  filter_upwards [RouteGeneric.ae_outsideExceptional (ι := Fin N) 0] with Z hZ
  exact fun π p₀ β lam M ε₀ => (badData_permutation hZ π p₀ β lam M ε₀).2.2.2

end MultipoleBKT.BadPointTypes.Permutation

end
