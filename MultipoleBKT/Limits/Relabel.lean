/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.MultipoleActivityLimit
public import MultipoleBKT.Matching.Measurable

/-!
# Relabelling invariance of the multipole integrands

See Lemma 4.26: the limit `𝗄^mult` is a function
of the profile `(#_k X)_k` of `X`, i.e. the activities are invariant under relabelling the
dipoles by a bijection that maps blocks to blocks ("by exchangeability").

The frozen definitions evaluate `𝒜_ij` with the lower label first; `𝒜_ij` is symmetric when the
four opposite-sign distances of the two dipoles are distinct, which holds for Lebesgue-almost
every configuration (`ae_stablePairWeight_comm`). Hence:

* `integral_boxConfig_comp_equiv`: box integrals are invariant under relabelling;
* `integral_multBox_relabel`: `∫_{(Λ²)^ι} multBox_E = ∫_{(Λ²)^ι'} multBox_{e(E)}` for a bijection
  `e : ι ≃ ι'` mapping the blocks to the blocks.
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-- **Relabelling box integrals.** -/
theorem integral_boxConfig_comp_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (F : (ι' → ℂ × ℂ) → ℝ) :
    ∫ c in boxConfig ι N, F (fun i' => c (e.symm i')) = ∫ c' in boxConfig ι' N, F c' := by
  have hmp := measurePreserving_piCongrLeft (fun _ : ι' => (volume : Measure (ℂ × ℂ))) e
  have happ : ∀ c : ι → ℂ × ℂ, MeasurableEquiv.piCongrLeft (fun _ => ℂ × ℂ) e c =
      fun i' => c (e.symm i') := fun c => by
    funext i'
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  rw [← integral_indicator (measurableSet_boxConfig N),
    ← integral_indicator (measurableSet_boxConfig N)]
  have h := hmp.integral_comp' ((boxConfig ι' N).indicator F)
  rw [volume_pi, volume_pi]
  refine Eq.trans ?_ h
  refine integral_congr_ae (Eventually.of_forall fun c => ?_)
  simp only [happ]
  have hmem : (fun i' => c (e.symm i')) ∈ boxConfig ι' N ↔ c ∈ boxConfig ι N := by
    simp only [boxConfig, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun h i => by simpa using h (e i), fun h i' => h _⟩
  by_cases hc : c ∈ boxConfig ι N
  · rw [Set.indicator_of_mem hc, Set.indicator_of_mem (hmem.2 hc)]
  · rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem (mt hmem.1 hc)]

/-- `e^{-β v_ij} 𝟙_{𝒜_ij}` is symmetric for almost every configuration. -/
theorem ae_stablePairWeight_comm (hχ : IsMollifier χ) {ι : Type*} [Fintype ι] :
    ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)), ∀ i j, i ≠ j →
      stablePairWeight χ β lam (c i) (c j) = stablePairWeight χ β lam (c j) (c i) := by
  filter_upwards [ae_injective_norm_sub] with c hc i j hij
  have hnd := nodup_norm_sub_of_injective hc hij
  unfold stablePairWeight
  rw [dipoleInteraction_comm hχ]
  congr 1
  exact propext (isStableDipolePair_comm_of_nodup hnd)

/-- `∏_{r i j, ij ∈ E} f i j = ∏_{e ∈ E} f e` for symmetric `f` and a strict total relation `r`. -/
theorem prod_prod_ite_rel_adj {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop)
    [DecidableRel r] (hasymm : ∀ i j, r i j → ¬ r j i) (htot : ∀ i j, i ≠ j → r i j ∨ r j i)
    (E : SimpleGraph ι) [DecidableRel E.Adj] (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∏ i, ∏ j, (if r i j ∧ E.Adj i j then f i j else 1) = ∏ e ∈ E.edgeFinset, symmLift f hf e := by
  set P : Finset (ι × ι) :=
    (Finset.univ ×ˢ Finset.univ : Finset (ι × ι)).filter fun p => r p.1 p.2 ∧ E.Adj p.1 p.2
  have h1 : ∏ i, ∏ j, (if r i j ∧ E.Adj i j then f i j else 1) = ∏ p ∈ P, f p.1 p.2 := by
    rw [Finset.prod_filter, Finset.prod_product]
  have hinj : Set.InjOn (fun p : ι × ι => s(p.1, p.2)) P := by
    intro p hp q hq hpq
    simp only [P, coe_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      rw [h1, h2] at hp
      exact hasymm _ _ hp.1 hq.1
  have himg : P.image (fun p : ι × ι => s(p.1, p.2)) = E.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [P, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        true_and, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Prod.exists]
      constructor
      · rintro ⟨x, y, ⟨hxy, hadj⟩, he⟩
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj
        · exact hadj.symm
      · intro hab
        rcases htot a b (E.ne_of_adj hab) with h | h
        · exact ⟨a, b, ⟨h, hab⟩, rfl⟩
        · exact ⟨b, a, ⟨h, hab.symm⟩, Sym2.eq_swap⟩
  rw [h1, ← himg, Finset.prod_image hinj]
  rfl

section MultBox

variable {ι ι' β₁ β₂ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype ι']
  [DecidableEq ι'] [LinearOrder ι'] [Fintype β₁] [DecidableEq β₁] [Fintype β₂] [DecidableEq β₂]

omit [Fintype ι'] [DecidableEq ι'] in
/-- Products over pairs do not depend on the order used to list the pairs. -/
theorem prod_prod_ite_lt_comp_equiv (e : ι ≃ ι') (E : SimpleGraph ι) [DecidableRel E.Adj]
    (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∏ i, ∏ j, (if e i < e j ∧ E.Adj i j then f i j else 1) =
      ∏ i, ∏ j, (if i < j ∧ E.Adj i j then f i j else 1) := by
  rw [prod_prod_ite_rel_adj (fun i j => e i < e j) (fun i j h => lt_asymm h)
      (fun i j hij => lt_or_gt_of_ne (e.injective.ne hij)) E f hf,
    prod_prod_ite_rel_adj (· < ·) (fun i j h => lt_asymm h) (fun i j hij => lt_or_gt_of_ne hij)
      E f hf]

open scoped Classical in
omit [DecidableEq ι] [DecidableEq ι'] in
/-- Relabelling a product over the pairs of a graph. -/
theorem prod_prod_ite_map_equiv (e : ι ≃ ι') (E : SimpleGraph ι) (G' : SimpleGraph ι')
    (hG : G' = E.map e.toEmbedding) (f : ι' → ι' → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∏ i', ∏ j', (if i' < j' ∧ G'.Adj i' j' then f i' j' else 1) =
      ∏ i, ∏ j, (if i < j ∧ E.Adj i j then f (e i) (e j) else 1) := by
  rw [prod_prod_ite_lt_adj _ f hf, prod_prod_ite_lt_adj E (fun i j => f (e i) (e j))
    (fun i j => hf _ _)]
  have hedge : G'.edgeFinset = E.edgeFinset.map e.toEmbedding.sym2Map := by
    ext x
    rw [mem_edgeFinset, Finset.mem_map]
    subst hG
    rw [edgeSet_map]
    simp only [Set.mem_image, mem_edgeFinset]
  rw [hedge, Finset.prod_map]
  refine prod_congr rfl fun x _ => ?_
  induction x using Sym2.ind with
  | h a b => rfl

open scoped Classical in
omit [DecidableEq ι] [DecidableEq ι'] in
theorem bondProd_relabel (hχ : IsMollifier χ) (e : ι ≃ ι') (E : SimpleGraph ι)
    (c : ι → ℂ × ℂ) :
    bondProd χ β lam M (E.map e.toEmbedding) (fun i' => c (e.symm i')) = bondProd χ β lam M E c := by
  unfold bondProd
  refine (prod_prod_ite_map_equiv e E _ rfl (fun i' j' => unlinkedPairWeight χ β lam M
    (c (e.symm i')) (c (e.symm j')) - 1) fun i j => by rw [unlinkedPairWeight_comm hχ]).trans ?_
  simp only [Equiv.symm_apply_apply]

open scoped Classical in
omit [Fintype β₁] [Fintype β₂] in
omit [DecidableEq ι] in
theorem blockW_relabel (blk : ι → β₁) (blk' : ι' → β₂) (e : ι ≃ ι') (σ : β₁ ≃ β₂)
    (hblk : ∀ i, blk' (e i) = σ (blk i)) (S : β₁) (c : ι → ℂ × ℂ)
    (hc : ∀ i j, i ≠ j →
      stablePairWeight χ β lam (c i) (c j) = stablePairWeight χ β lam (c j) (c i)) :
    blockW χ β lam M blk' (σ S) (fun i' => c (e.symm i')) = blockW χ β lam M blk S c := by
  have hmem : ∀ i, blk' (e i) = σ S ↔ blk i = S := fun i => by rw [hblk, σ.apply_eq_iff_eq]
  have hiff : ((nearGraph M lam fun i' => c (e.symm i')).induce {i' | blk' i' = σ S}).Connected ↔
      ((nearGraph M lam c).induce {i | blk i = S}).Connected := by
    let f : ↥{i | blk i = S} ≃ ↥{i' | blk' i' = σ S} :=
      e.subtypeEquiv fun i => (hmem i).symm
    let iso : ((nearGraph M lam c).induce {i | blk i = S}) ≃g
        ((nearGraph M lam fun i' => c (e.symm i')).induce {i' | blk' i' = σ S}) :=
      { toEquiv := f
        map_rel_iff' := by
          intro a b
          simp only [comap_adj, Function.Embedding.coe_subtype, nearGraph_adj, f,
            Equiv.subtypeEquiv_apply, Equiv.symm_apply_apply, ne_eq,
            EmbeddingLike.apply_eq_iff_eq] }
    exact iso.connected_iff.symm
  set GS : SimpleGraph ι := SimpleGraph.fromRel fun a b => blk a = S ∧ blk b = S
  obtain ⟨G', hG'⟩ : ∃ G' : SimpleGraph ι', G' = GS.map e.toEmbedding := ⟨_, rfl⟩
  set fs : ι' → ι' → ℝ := fun i' j' =>
    if i' = j' then 1 else stablePairWeight χ β lam (c (e.symm i')) (c (e.symm j'))
  have hfs : ∀ i j, fs i j = fs j i := fun i j => by
    simp only [fs]
    by_cases h : i = j
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), hc _ _ (fun h' => h (e.symm.injective h'))]
  have hprod : ∏ i', ∏ j', (if blk' i' = σ S ∧ blk' j' = σ S ∧ i' < j' then
      stablePairWeight χ β lam (c (e.symm i')) (c (e.symm j')) else 1) =
      ∏ i, ∏ j, (if blk i = S ∧ blk j = S ∧ i < j then
        stablePairWeight χ β lam (c i) (c j) else 1) := by
    have h1 : ∀ i' j', (if blk' i' = σ S ∧ blk' j' = σ S ∧ i' < j' then
        stablePairWeight χ β lam (c (e.symm i')) (c (e.symm j')) else 1) =
        (if i' < j' ∧ G'.Adj i' j' then fs i' j' else 1) := by
      intro i' j'
      have hadj : G'.Adj i' j' ↔
          i' ≠ j' ∧ blk' i' = σ S ∧ blk' j' = σ S := by
        rw [hG', map_adj]
        constructor
        · rintro ⟨a, b, hab, rfl, rfl⟩
          rw [fromRel_adj] at hab
          refine ⟨fun h => hab.1 (e.injective h), ?_⟩
          simp only [Equiv.coe_toEmbedding, hmem]
          rcases hab.2 with h | h
          · exact h
          · exact ⟨h.2, h.1⟩
        · rintro ⟨hne, h1, h2⟩
          refine ⟨e.symm i', e.symm j', ?_, by simp, by simp⟩
          rw [fromRel_adj]
          refine ⟨fun h => hne (e.symm.injective h), Or.inl ⟨?_, ?_⟩⟩
          · rw [← hmem]; simpa using h1
          · rw [← hmem]; simpa using h2
      by_cases h : blk' i' = σ S ∧ blk' j' = σ S ∧ i' < j'
      · rw [ite_eq_left h, ite_eq_left ⟨h.2.2, hadj.2 ⟨h.2.2.ne, h.1, h.2.1⟩⟩]
        simp only [fs, ite_eq_right h.2.2.ne]
      · rw [ite_eq_right h, ite_eq_right]
        rintro ⟨hlt, hadj'⟩
        obtain ⟨-, h1, h2⟩ := hadj.1 hadj'
        exact h ⟨h1, h2, hlt⟩
    simp_rw [h1]
    rw [prod_prod_ite_map_equiv e GS G' hG' fs hfs]
    refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
    have hGS : GS.Adj i j ↔ i ≠ j ∧ blk i = S ∧ blk j = S := by
      simp only [GS, fromRel_adj]
      refine and_congr_right fun _ => ⟨?_, Or.inl⟩
      rintro (h | h)
      · exact h
      · exact ⟨h.2, h.1⟩
    by_cases h : blk i = S ∧ blk j = S ∧ i < j
    · rw [ite_eq_left ⟨h.2.2, hGS.2 ⟨h.2.2.ne, h.1, h.2.1⟩⟩, ite_eq_left h]
      simp only [fs, Equiv.symm_apply_apply, ite_eq_right (e.injective.ne h.2.2.ne)]
    · rw [ite_eq_right h, ite_eq_right]
      rintro ⟨hlt, hadj'⟩
      exact h ⟨(hGS.1 hadj').2.1, (hGS.1 hadj').2.2, hlt⟩
  unfold blockW
  rw [hprod]
  congr 1
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

open scoped Classical in
omit [DecidableEq ι] in
/-- **Relabelling `multBox`** (at configurations where `𝒜_ij` is symmetric). -/
theorem multBox_relabel (hχ : IsMollifier χ) (blk : ι → β₁) (blk' : ι' → β₂) (e : ι ≃ ι')
    (σ : β₁ ≃ β₂) (hblk : ∀ i, blk' (e i) = σ (blk i)) (E : SimpleGraph ι) (c : ι → ℂ × ℂ)
    (hc : ∀ i j, i ≠ j →
      stablePairWeight χ β lam (c i) (c j) = stablePairWeight χ β lam (c j) (c i)) :
    multBox χ β lam M blk' (E.map e.toEmbedding) (fun i' => c (e.symm i')) =
      multBox χ β lam M blk E c := by
  unfold multBox
  rw [bondProd_relabel hχ e E c]
  congr 1
  · congr 1
    rw [← Fintype.prod_equiv σ (fun S => blockW χ β lam M blk' (σ S) fun i' => c (e.symm i')) _
      (fun S => rfl)]
    exact prod_congr rfl fun S _ => blockW_relabel blk blk' e σ hblk S c hc
  · rw [← Fintype.prod_equiv e (fun i => pairDensity χ β lam (c (e.symm (e i)))) _ (fun i => rfl)]
    simp only [Equiv.symm_apply_apply]

omit [DecidableEq ι] in
/-- **Relabelling the box integrals of `multBox`.** -/
theorem integral_multBox_relabel (hχ : IsMollifier χ) (blk : ι → β₁) (blk' : ι' → β₂)
    (e : ι ≃ ι') (σ : β₁ ≃ β₂) (hblk : ∀ i, blk' (e i) = σ (blk i)) (E : SimpleGraph ι) :
    ∫ c' in boxConfig ι' N, multBox χ β lam M blk' (E.map e.toEmbedding) c' =
      ∫ c in boxConfig ι N, multBox χ β lam M blk E c := by
  rw [← integral_boxConfig_comp_equiv e]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_stablePairWeight_comm (β := β) (lam := lam) hχ (ι := ι)] with c hc
  exact multBox_relabel hχ blk blk' e σ hblk E c hc

end MultBox

end Limits

end MultipoleBKT

end
