/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.ClusterParity
public import MultipoleBKT.LowerBound.ExpansionErrors.ActivityDiff
public import MultipoleBKT.LowerBound.ExpansionErrors.DipoleDiff
public import MultipoleBKT.LowerBound.Hierarchical.Instances

/-!
# The cluster integrals of the model `0` on labels

See equation (A.48). The cluster integrals
`I_{cl}` are `MultipoleBKT.ExpansionErrors.clusterIntegral` (`I^-_{cl,ε₀}`, `I^0_{cl,ε₀}`,
`I^0_{cl,∞}`: `minusClusterIntegral`, `zeroClusterIntegral`, `zeroClusterIntegralInf`). Their
integrands are functions of the configurations of the labels `ℕ` (through `extendConfig`), with
edge sets of pairs `(i, j)`, `i < j`. Here we transport the integrand of the model `0` to the
labels `V_X` (as a subtype) with edge sets of unordered pairs (`symOf`), in the form
`MultipoleBKT.ExpansionK.clusterBox` used by the parity argument:

* `symOf`, `prod_symOf`: products over pairs as products over unordered pairs of labels;
* `blockWeightOf_extendConfig_eq`: the block weight `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` is
  `MultipoleBKT.Limits.blockW` for the blocks `blockOf X`;
* `clusterTerm_extendConfig_eq`: the bond product of the model `0` is
  `∏_{∪ Eₗ} f 𝟙_{𝓑^c} ∏_{∪ ℰ^inter(Xₗ) \ ∪ Eₗ} 𝟙_{𝓑^c} ∏_F (-𝟙_𝓑)`;
* `reachable_blocks`: the bonds `F ∪ ∪ Eₗ` connect the blocks of `X`.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open Hierarchical Multipole Parity Limits UpperBound SmallIntegral

/-! ### Edge sets as unordered pairs of labels -/

section Sym

variable {U : Finset ℕ}

/-- The pairs of `P` (with `i < j`, both in `U`) as unordered pairs of labels of `U`. -/
def symOf (U : Finset ℕ) (P : Finset (ℕ × ℕ)) : Finset (Sym2 U) :=
  ((univ : Finset (U × U)).filter fun q => q.1 < q.2 ∧ ((q.1 : ℕ), (q.2 : ℕ)) ∈ P).image
    fun q => s(q.1, q.2)

theorem mem_symOf {P : Finset (ℕ × ℕ)} {e : Sym2 U} :
    e ∈ symOf U P ↔ ∃ i j : U, i < j ∧ ((i : ℕ), (j : ℕ)) ∈ P ∧ e = s(i, j) := by
  simp only [symOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨hij, hP⟩, rfl⟩
    exact ⟨i, j, hij, hP, rfl⟩
  · rintro ⟨i, j, hij, hP, rfl⟩
    exact ⟨i, j, ⟨hij, hP⟩, rfl⟩

theorem symOf_mono {P Q : Finset (ℕ × ℕ)} (h : P ⊆ Q) : symOf U P ⊆ symOf U Q := by
  intro e he
  obtain ⟨i, j, hij, hP, rfl⟩ := mem_symOf.1 he
  exact mem_symOf.2 ⟨i, j, hij, h hP, rfl⟩

theorem symOf_union (P Q : Finset (ℕ × ℕ)) : symOf U (P ∪ Q) = symOf U P ∪ symOf U Q := by
  ext e
  simp only [mem_symOf, Finset.mem_union]
  constructor
  · rintro ⟨i, j, hij, hPQ | hPQ, rfl⟩
    · exact Or.inl ⟨i, j, hij, hPQ, rfl⟩
    · exact Or.inr ⟨i, j, hij, hPQ, rfl⟩
  · rintro (⟨i, j, hij, hP, rfl⟩ | ⟨i, j, hij, hQ, rfl⟩)
    · exact ⟨i, j, hij, Or.inl hP, rfl⟩
    · exact ⟨i, j, hij, Or.inr hQ, rfl⟩

theorem symOf_sdiff (P Q : Finset (ℕ × ℕ)) : symOf U (P \ Q) = symOf U P \ symOf U Q := by
  ext e
  simp only [mem_symOf, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, j, hij, ⟨hP, hQ⟩, rfl⟩
    refine ⟨⟨i, j, hij, hP, rfl⟩, ?_⟩
    rintro ⟨i', j', hij', hQ', he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hQ hQ'
    · exact absurd (hij.trans hij') (lt_irrefl _)
  · rintro ⟨⟨i, j, hij, hP, rfl⟩, hQ⟩
    exact ⟨i, j, hij, ⟨hP, fun h => hQ ⟨i, j, hij, h, rfl⟩⟩, rfl⟩

/-- **Products over pairs as products over unordered pairs of labels.** -/
theorem prod_symOf {P : Finset (ℕ × ℕ)} (hP : P ⊆ pairsOn U) (g : ℕ × ℕ → ℝ)
    (gs : Sym2 U → ℝ) (hg : ∀ i j : U, i < j → gs s(i, j) = g ((i : ℕ), (j : ℕ))) :
    ∏ p ∈ P, g p = ∏ e ∈ symOf U P, gs e := by
  classical
  unfold symOf
  rw [prod_image]
  · symm
    refine Finset.prod_bij (fun q _ => ((q.1 : ℕ), (q.2 : ℕ))) ?_ ?_ ?_ ?_
    · intro q hq
      exact (mem_filter.1 hq).2.2
    · intro q hq q' hq' h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · intro p hp
      have := mem_pairsOn.1 (hP hp)
      refine ⟨(⟨p.1, this.1⟩, ⟨p.2, this.2.1⟩), mem_filter.2 ⟨mem_univ _, ?_, hp⟩, rfl⟩
      exact this.2.2
    · intro q hq
      exact hg q.1 q.2 (mem_filter.1 hq).2.1
  · intro q hq q' hq' h
    have h1 := (mem_filter.1 hq).2.1
    have h2 := (mem_filter.1 hq').2.1
    rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Prod.ext e1 e2
    · exfalso
      rw [← e1, ← e2] at h2
      exact lt_asymm h1 h2

theorem extendConfig_coe {U : Finset ℕ} (y : U → ℂ × ℂ) (i : U) :
    extendConfig U y (i : ℕ) = y i := by
  simp [extendConfig, i.2]

theorem restrict_extendConfig (U : Finset ℕ) (y : U → ℂ × ℂ) :
    U.restrict (extendConfig U y) = y := by
  funext i
  exact extendConfig_coe y i

end Sym

/-! ### The integrand of the model `0` on the labels -/

section Transport

variable {χ : ℂ → ℝ} {β lam M : ℝ} {X : Finset (Finset ℕ)}

open scoped Classical in
/-- The block weight of the model `0` is `blockW` on the labels of `V_X`. -/
theorem blockWeightOf_extendConfig_eq (hX : IsSubpartition X) {S : Finset ℕ} (hS : S ∈ X)
    (y : X.biUnion id → ℂ × ℂ) :
    blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam S (extendConfig (X.biUnion id) y) =
      blockW χ β lam M (Limits.blockOf X) ⟨S, hS⟩ y := by
  rw [← hierBlockWeight_restrict β _ _ M lam hS, restrict_extendConfig]
  have hset : {i : X.biUnion id | Limits.blockOf X i = ⟨S, hS⟩} = {i : X.biUnion id | (i : ℕ) ∈ S} := by
    ext i
    exact Limits.blockOf_eq_iff hX i ⟨S, hS⟩
  unfold hierBlockWeight blockW
  rw [hset]
  simp only [Limits.blockOf_eq_iff hX, ite_self, prod_const_one, mul_one]
  rfl

open scoped Classical in
theorem prod_blockWeightOf_extendConfig_eq (hX : IsSubpartition X) (y : X.biUnion id → ℂ × ℂ) :
    ∏ S ∈ X, blockWeightOf β (dipoleInteraction χ lam) (fun _ => 1) M lam S
        (extendConfig (X.biUnion id) y) =
      ∏ S : X, blockW χ β lam M (Limits.blockOf X) S y := by
  rw [← Finset.prod_coe_sort X]
  exact prod_congr rfl fun S _ => blockWeightOf_extendConfig_eq hX S.2 y

open scoped Classical in
/-- **The bond product of the model `0` on the labels.** -/
theorem clusterTerm_extendConfig_eq {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ))
    (hEI : univ.biUnion Es ⊆ univ.biUnion fun l => interPairs (Xs l))
    (hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn (X.biUnion id))
    (hF : F ⊆ pairsOn (X.biUnion id)) (y : X.biUnion id → ℂ × ℂ) :
    clusterTerm β (dipoleInteraction χ lam) M lam Xs Es F (extendConfig (X.biUnion id) y) =
      (∏ e ∈ symOf (X.biUnion id) (univ.biUnion Es), farBondE χ β lam M y e) *
        (∏ e ∈ symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es),
          farInd M lam y e) *
        ∏ e ∈ symOf (X.biUnion id) F, -linkIndE M lam y e := by
  unfold clusterTerm
  set c := extendConfig (X.biUnion id) y
  set E := univ.biUnion Es
  set I := univ.biUnion fun l => interPairs (Xs l)
  rw [← prod_sdiff hEI]
  have hE : (∏ p ∈ E, mayerBondOf β (dipoleInteraction χ lam) (c p.1) (c p.2)) *
      (∏ p ∈ E, if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) =
      ∏ e ∈ symOf (X.biUnion id) E, farBondE χ β lam M y e := by
    rw [← prod_mul_distrib]
    refine prod_symOf (hEI.trans hI) _ _ fun i j hij => ?_
    simp only [c, extendConfig_coe, farBondE, symmLift_mk, farBond, dipBond, ite_eq_left hij,
      mayerBondOf, stablePairWeight]
    split_ifs <;> ring
  have hZ : (∏ p ∈ I \ E, if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) =
      ∏ e ∈ symOf (X.biUnion id) (I \ E), farInd M lam y e := by
    refine prod_symOf (sdiff_subset.trans hI) _ _ fun i j hij => ?_
    simp only [c, extendConfig_coe]
    rfl
  have hN : (∏ p ∈ F, -(if MultipoleLinked M lam (c p.1) (c p.2) then (1 : ℝ) else 0)) =
      ∏ e ∈ symOf (X.biUnion id) F, -linkIndE M lam y e := by
    refine prod_symOf hF _ _ fun i j hij => ?_
    simp only [c, extendConfig_coe, linkIndE, symmLift_mk, linkInd]
  rw [← hE, ← hZ, ← hN]
  ring

end Transport

/-! ### Connectivity of the blocks -/

section Connectivity

variable {X : Finset (Finset ℕ)}

/-- Reachability is transported along a map that sends the edges leaving a set `P` (which they do
not leave) to reachable pairs. -/
theorem reachable_lift {α : Type*} {G : SimpleGraph ℕ} {K : SimpleGraph α} (P : ℕ → Prop)
    (f : ℕ → α) (h : ∀ u v, P u → G.Adj u v → P v ∧ K.Reachable (f u) (f v)) {a b : ℕ}
    (ha : P a) (hab : G.Reachable a b) : K.Reachable (f a) (f b) := by
  obtain ⟨w⟩ := hab
  induction w with
  | nil => exact Reachable.refl _
  | cons hadj p ih =>
    obtain ⟨hv, hr⟩ := h _ _ ha hadj
    exact hr.trans (ih hv)

open scoped Classical in
/-- **The bonds of a cluster connect its blocks**: for `Eₗ ∈ 𝖤^{Xₗ}`, `Xₗ ⊆ X` and
`F ∈ 𝖤_0^{Coarse_X(X₁, …, Xₙ)}`, the blocks of `X` are connected by `F ∪ ∪ₗ Eₗ`. -/
theorem reachable_blocks (hX : IsSubpartition X) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ)) (hXs : ∀ l, Xs l ⊆ X)
    (hEs : ∀ l, Es l ∈ relEdgeSets (Xs l))
    (hF : F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs))) (b b' : X) :
    (nodeGraph (Sym2.map (Limits.blockOf X))
      (symOf (X.biUnion id) F ∪ symOf (X.biUnion id) (univ.biUnion Es))).Reachable b b' := by
  set V := X.biUnion id
  set E := univ.biUnion Es
  set G := edgeGraph (F ∪ E ∪ intraPairs X)
  have hGX : ∀ Y ∈ Finset.univ.image Xs, Y ⊆ X := by
    intro Y hY
    obtain ⟨l, -, rfl⟩ := mem_image.1 hY
    exact hXs l
  have hFsub : F ⊆ pairsOn V := by
    have := (mem_relEdgeSets₀.1 hF).1.trans interPairs_subset_pairsOn
    rwa [biUnion_coarsen hGX] at this
  have hEsub : E ⊆ pairsOn V := by
    intro p hp
    obtain ⟨l, -, hpl⟩ := mem_biUnion.1 hp
    have h1 := (mem_relEdgeSets.1 (hEs l)).1 hpl
    exact interPairs_subset_pairsOn (interPairs_subset_of_subset hX (hXs l) h1)
  have hIsub : intraPairs X ⊆ pairsOn V := by
    intro p hp
    obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hp
    exact pairsOn_mono (Finset.subset_biUnion_of_mem id hB) hpB
  have hAll : F ∪ E ∪ intraPairs X ⊆ pairsOn V :=
    union_subset (union_subset hFsub hEsub) hIsub
  -- reachability of a pair
  have hpair : ∀ p ∈ F ∪ E ∪ intraPairs X, G.Reachable p.1 p.2 := by
    intro p hp
    by_cases hpe : p.1 = p.2
    · rw [hpe]
    · exact Adj.reachable (edgeGraph_adj.2 ⟨hpe, Or.inl hp⟩)
  -- Step A: the labels of `V_X` are connected in `G`
  have hA : ∀ i ∈ V, ∀ j ∈ V, G.Reachable i j := by
    intro i hi j hj
    have hC := (mem_relEdgeSets₀.1 hF).2
    rw [biUnion_coarsen hGX] at hC
    have hr := hC.2 i hi j hj
    have hstep : ∀ q ∈ F ∪ intraPairs (coarsen X (Finset.univ.image Xs)), G.Reachable q.1 q.2 := by
      intro q hq
      rcases mem_union.1 hq with hqF | hqI
      · exact hpair q (mem_union_left _ (mem_union_left _ hqF))
      · obtain ⟨B, hB, hqB⟩ := mem_intraPairs.1 hqI
        simp only [coarsen, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hB
        rcases hB with ⟨Y, hY, rfl⟩ | ⟨hBX, -⟩
        · obtain ⟨l, -, rfl⟩ := hY
          have hq1 := (mem_pairsOn.1 hqB).1
          have hq2 := (mem_pairsOn.1 hqB).2.1
          have hCl := (mem_relEdgeSets.1 (hEs l)).2.2
          refine (hCl.2 _ hq1 _ hq2).mono (edgeGraph_mono ?_)
          intro r hr
          rcases mem_union.1 hr with hrE | hrI
          · exact mem_union_left _ (mem_union_right _ (mem_biUnion.2 ⟨l, mem_univ _, hrE⟩))
          · obtain ⟨B', hB', hrB'⟩ := mem_intraPairs.1 hrI
            exact mem_union_right _ (mem_intraPairs.2 ⟨B', hXs l hB', hrB'⟩)
        · exact hpair q (mem_union_right _ (mem_intraPairs.2 ⟨B, hBX, hqB⟩))
    refine reachable_lift (fun _ => True) id (fun u v _ huv => ⟨trivial, ?_⟩) trivial hr
    rcases edgeGraph_adj.1 huv with ⟨-, h | h⟩
    · exact hstep _ h
    · exact (hstep _ h).symm
  -- Step B: from labels to blocks
  set K := nodeGraph (Sym2.map (Limits.blockOf X)) (symOf V F ∪ symOf V E)
  set f : ℕ → X := fun i => if h : i ∈ V then Limits.blockOf X ⟨i, h⟩ else b
  have hfi : ∀ (i : ℕ) (hi : i ∈ V), f i = Limits.blockOf X ⟨i, hi⟩ := fun i hi => by
    simp only [f, dite_eq_left hi]
  have hKp : ∀ p ∈ F ∪ E ∪ intraPairs X, ∀ (h1 : p.1 ∈ V) (h2 : p.2 ∈ V),
      K.Reachable (Limits.blockOf X ⟨p.1, h1⟩) (Limits.blockOf X ⟨p.2, h2⟩) := by
    intro p hp h1 h2
    by_cases heq : Limits.blockOf X ⟨p.1, h1⟩ = Limits.blockOf X ⟨p.2, h2⟩
    · rw [heq]
    have hlt : p.1 < p.2 := (mem_pairsOn.1 (hAll hp)).2.2
    have hmem : ∀ P : Finset (ℕ × ℕ), p ∈ P →
        s((⟨p.1, h1⟩ : V), ⟨p.2, h2⟩) ∈ symOf V P := fun P hP =>
      mem_symOf.2 ⟨⟨p.1, h1⟩, ⟨p.2, h2⟩, hlt, hP, rfl⟩
    rcases mem_union.1 hp with hp' | hpI
    · refine Adj.reachable (nodeGraph_adj.2 ⟨heq, ?_⟩)
      rcases mem_union.1 hp' with hpF | hpE
      · exact ⟨_, mem_union_left _ (hmem F hpF), rfl⟩
      · exact ⟨_, mem_union_right _ (hmem E hpE), rfl⟩
    · exfalso
      obtain ⟨B, hB, hpB⟩ := mem_intraPairs.1 hpI
      exact heq ((Limits.blockOf_eq hX hB (mem_pairsOn.1 hpB).1).trans
        (Limits.blockOf_eq hX hB (mem_pairsOn.1 hpB).2.1).symm)
  have hB : ∀ u v, u ∈ V → G.Adj u v → v ∈ V ∧ K.Reachable (f u) (f v) := by
    intro u v hu huv
    rcases edgeGraph_adj.1 huv with ⟨-, h | h⟩
    · have hv := (mem_pairsOn.1 (hAll h)).2.1
      refine ⟨hv, ?_⟩
      rw [hfi u hu, hfi v hv]
      exact hKp _ h hu hv
    · have hv := (mem_pairsOn.1 (hAll h)).1
      refine ⟨hv, ?_⟩
      rw [hfi u hu, hfi v hv]
      exact (hKp _ h hv hu).symm
  obtain ⟨i, hi⟩ := hX.1 b b.2
  obtain ⟨j, hj⟩ := hX.1 b' b'.2
  have hiV : i ∈ V := mem_biUnion.2 ⟨b, b.2, hi⟩
  have hjV : j ∈ V := mem_biUnion.2 ⟨b', b'.2, hj⟩
  have hr := reachable_lift (· ∈ V) f hB hiV (hA i hiV j hjV)
  rwa [hfi i hiV, hfi j hjV, Limits.blockOf_eq hX b.2 hi, Limits.blockOf_eq hX b'.2 hj] at hr

end Connectivity

end ExpansionK

end MultipoleBKT

end
