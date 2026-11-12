/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.CutoffInfrastructure
public import MultipoleBKT.Appendix.GeneralExpansion.Pointwise

/-!
# Cluster integrands of a general model on the labels

See the proof of Lemma A.7, Step 1: the odd/even decomposition of the bonds of a model `(w, ψ)` and the parity
argument, for an interaction `w` that is odd under the reversal of either dipole (`ṽ` and `v`).

On labels `ι` grouped into blocks `blk : ι → β'`:

* `blockWW`: the block weight `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} ψ(x_i, y_i)`;
* `farBondW`: the far bond `f^w_ij 𝟙_{𝓑_ij^c}`, with even and odd parts `alphaW`, `gammaW`
  (`cosh(β w) - 1`, `-sinh(β w)` on `𝓑^c`), `farBondW_flip`;
* `clusterQ`: the integrand of a cluster integral of the model (without the dipole weights);
  `prod_blockWeightOf_extendConfig_eqW`, `clusterTerm_extendConfig_eqW`: the transport of the
  integrand of `MultipoleBKT.ExpansionErrors.clusterIntegral`;
* `abs_avg_sub_le`: the parity expansion of the difference of two averaged products;
* `abs_mul_prod_sub_le`: telescoping a difference of products.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph
open Hierarchical Multipole Parity Limits SmallIntegral

variable {β lam M : ℝ}

/-! ### Definitions -/

section Defs

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

/-- The interaction of two labels, the lower label first. -/
def wOrd (w : ℂ × ℂ → ℂ × ℂ → ℝ) (c : ι → ℂ × ℂ) (i j : ι) : ℝ :=
  if i < j then w (c i) (c j) else w (c j) (c i)

omit [Fintype ι] [DecidableEq ι] in
theorem wOrd_comm (w : ℂ × ℂ → ℂ × ℂ → ℝ) (c : ι → ℂ × ℂ) (i j : ι) :
    wOrd w c i j = wOrd w c j i := by
  unfold wOrd
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (lt_asymm h)]
  · rfl
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h]

/-- The pair weight of two labels, the lower label first. -/
noncomputable def sOrd (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (c : ι → ℂ × ℂ) (i j : ι) : ℝ :=
  if i < j then stableWeight β w (c i) (c j) else stableWeight β w (c j) (c i)

omit [Fintype ι] [DecidableEq ι] in
theorem sOrd_comm (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (c : ι → ℂ × ℂ) (i j : ι) :
    sOrd β w c i j = sOrd β w c j i := by
  unfold sOrd
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (lt_asymm h)]
  · rfl
  · rw [ite_eq_right (lt_asymm h), ite_eq_left h]

open scoped Classical in
/-- The far bond `f^w_ij 𝟙_{𝓑_ij^c}` of two labels. -/
noncomputable def farBondWij (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (c : ι → ℂ × ℂ)
    (i j : ι) : ℝ :=
  if MultipoleLinked M lam (c i) (c j) then 0 else sOrd β w c i j - 1

omit [Fintype ι] [DecidableEq ι] in
theorem farBondWij_comm (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (c : ι → ℂ × ℂ)
    (i j : ι) : farBondWij β w M lam c i j = farBondWij β w M lam c j i := by
  classical
  unfold farBondWij
  rw [sOrd_comm]
  exact if_congr Limits.multipoleLinked_comm rfl rfl

/-- The far bond `f^w_e 𝟙_{𝓑_e^c}` as a function of unordered pairs. -/
noncomputable def farBondW (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (c : ι → ℂ × ℂ) :
    Sym2 ι → ℝ :=
  symmLift (farBondWij β w M lam c) (farBondWij_comm β w M lam c)

open scoped Classical in
/-- The even part `-1` on `𝓑`, `cosh(β w) - 1` on `𝓑^c`. -/
noncomputable def alphaW (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (c : ι → ℂ × ℂ) :
    Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then -1 else
    Real.cosh (β * wOrd w c i j) - 1) fun i j => by
      rw [wOrd_comm]
      exact if_congr Limits.multipoleLinked_comm rfl rfl

open scoped Classical in
/-- The odd part `0` on `𝓑`, `-sinh(β w)` on `𝓑^c`. -/
noncomputable def gammaW (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (M lam : ℝ) (c : ι → ℂ × ℂ) :
    Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 0 else
    -Real.sinh (β * wOrd w c i j)) fun i j => by
      rw [wOrd_comm]
      exact if_congr Limits.multipoleLinked_comm rfl rfl

open scoped Classical in
/-- The indicator `𝟙_{𝓑_S}` that the block `S` is connected by the multipole relation. -/
noncomputable def nearConnInd (M lam : ℝ) (blk : ι → β') (S : β') (c : ι → ℂ × ℂ) : ℝ :=
  if ((nearGraph M lam c).induce {i | blk i = S}).Connected then 1 else 0

/-- The block weight `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β w_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} ψ(x_i, y_i)`. -/
noncomputable def blockWW (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)
    (blk : ι → β') (S : β') (c : ι → ℂ × ℂ) : ℝ :=
  nearConnInd M lam blk S c *
    (∏ i, ∏ j, if blk i = S ∧ blk j = S ∧ i < j then stableWeight β w (c i) (c j) else 1) *
    ∏ i, if blk i = S then ψ (c i) else 1

/-- The flip-invariant part of a cluster integrand. -/
noncomputable def clusterG (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)
    (blk : ι → β') (Dn Dz : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) : ℝ :=
  (∏ S, blockWW β w ψ M lam blk S c) * (∏ e ∈ Dz, farInd M lam c e) *
    ∏ e ∈ Dn, -linkIndE M lam c e

/-- The integrand of a cluster integral of the model `(w, ψ)`, without the dipole weights. -/
noncomputable def clusterQ (β : ℝ) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (ψ : ℂ × ℂ → ℝ) (M lam : ℝ)
    (blk : ι → β') (Dn Dz Df : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) : ℝ :=
  clusterG β w ψ M lam blk Dn Dz c * ∏ e ∈ Df, farBondW β w M lam c e

end Defs

/-! ### Reversals -/

section Flip

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']
variable {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}

theorem stableWeight_swap_swap (hwl : ∀ d e, w d.swap e = -w d e)
    (hwr : ∀ d e, w d e.swap = -w d e) (d e : ℂ × ℂ) :
    stableWeight β w d.swap e.swap = stableWeight β w d e := by
  classical
  unfold stableWeight
  rw [hwl, hwr, neg_neg]
  exact if_congr (Limits.isStableDipolePair_swap_swap d e) rfl rfl

omit [Fintype β'] [LinearOrder ι] in
theorem nearConnInd_flip (blk : ι → β') (S : β') (A : Finset β') (c : ι → ℂ × ℂ) :
    nearConnInd M lam blk S (flipCfg (blockLabels blk A) c) = nearConnInd M lam blk S c := by
  have hc : ((nearGraph M lam (flipCfg (blockLabels blk A) c)).induce {i | blk i = S}).Connected ↔
      ((nearGraph M lam c).induce {i | blk i = S}).Connected := by rw [nearGraph_flipCfg]
  unfold nearConnInd
  by_cases h : ((nearGraph M lam c).induce {i | blk i = S}).Connected
  · rw [ite_eq_left (hc.2 h), ite_eq_left h]
  · rw [ite_eq_right (mt hc.1 h), ite_eq_right h]

omit [Fintype β'] in
theorem blockWW_flip (hwl : ∀ d e, w d.swap e = -w d e) (hwr : ∀ d e, w d e.swap = -w d e)
    (hψ : ∀ d, ψ d.swap = ψ d) (blk : ι → β') (S : β') (A : Finset β') (c : ι → ℂ × ℂ) :
    blockWW β w ψ M lam blk S (flipCfg (blockLabels blk A) c) = blockWW β w ψ M lam blk S c := by
  unfold blockWW
  rw [nearConnInd_flip]
  have h2 : (∏ i, ∏ j, if blk i = S ∧ blk j = S ∧ i < j then
      stableWeight β w (flipCfg (blockLabels blk A) c i) (flipCfg (blockLabels blk A) c j) else 1) =
      ∏ i, ∏ j, if blk i = S ∧ blk j = S ∧ i < j then stableWeight β w (c i) (c j) else 1 := by
    refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
    by_cases h : blk i = S ∧ blk j = S ∧ i < j
    · rw [ite_eq_left h, ite_eq_left h, flipCfg_apply, flipCfg_apply]
      simp only [mem_blockLabels, h.1, h.2.1]
      split_ifs
      · exact stableWeight_swap_swap hwl hwr _ _
      · rfl
    · rw [ite_eq_right h, ite_eq_right h]
  have h3 : (∏ i, if blk i = S then ψ (flipCfg (blockLabels blk A) c i) else 1) =
      ∏ i, if blk i = S then ψ (c i) else 1 := by
    refine prod_congr rfl fun i _ => ?_
    by_cases h : blk i = S
    · rw [ite_eq_left h, ite_eq_left h, flipCfg_apply]
      split_ifs
      · exact hψ _
      · rfl
    · rw [ite_eq_right h, ite_eq_right h]
  rw [h2, h3]

omit [Fintype ι] [DecidableEq ι] in
/-- On `𝓑^c` (and `M ≥ 1`) the ordered pair weight is `e^{-β w}`. -/
theorem sOrd_of_not_linked (hM : 1 ≤ M) (w : ℂ × ℂ → ℂ × ℂ → ℝ) (c : ι → ℂ × ℂ) {i j : ι}
    (hl : ¬ MultipoleLinked M lam (c i) (c j)) :
    sOrd β w c i j = Real.exp (-β * wOrd w c i j) := by
  have hl' : ¬ MultipoleLinked M lam (c j) (c i) := fun h => hl (Limits.multipoleLinked_comm.1 h)
  unfold sOrd wOrd stableWeight
  split_ifs <;> first
    | rfl
    | (exfalso; exact ‹¬ IsStableDipolePair _ _› (remark_4_6 hM hl))
    | (exfalso; exact ‹¬ IsStableDipolePair _ _› (remark_4_6 hM hl'))

theorem w_ite_swap (hwl : ∀ d e, w d.swap e = -w d e) (hwr : ∀ d e, w d e.swap = -w d e)
    (a b : Prop) [Decidable a] [Decidable b] (d e : ℂ × ℂ) :
    w (if a then d.swap else d) (if b then e.swap else e) = (if (a ↔ b) then 1 else -1) * w d e := by
  by_cases ha : a <;> by_cases hb : b
  · rw [ite_eq_left ha, ite_eq_left hb, hwl, hwr, neg_neg, ite_eq_left (iff_of_true ha hb), one_mul]
  · rw [ite_eq_left ha, ite_eq_right hb, hwl, ite_eq_right (fun h => hb (h.1 ha)), neg_one_mul]
  · rw [ite_eq_right ha, ite_eq_left hb, hwr, ite_eq_right (fun h => ha (h.2 hb)), neg_one_mul]
  · rw [ite_eq_right ha, ite_eq_right hb, ite_eq_left (iff_of_false ha hb), one_mul]

omit [Fintype β'] in
theorem wOrd_flip (hwl : ∀ d e, w d.swap e = -w d e) (hwr : ∀ d e, w d e.swap = -w d e)
    (blk : ι → β') (A : Finset β') (c : ι → ℂ × ℂ) (i j : ι) :
    wOrd w (flipCfg (blockLabels blk A) c) i j =
      (if (blk i ∈ A ↔ blk j ∈ A) then 1 else -1) * wOrd w c i j := by
  classical
  unfold wOrd
  by_cases hij : i < j
  · rw [ite_eq_left hij, ite_eq_left hij, flipCfg_apply, flipCfg_apply]
    simp only [mem_blockLabels]
    exact w_ite_swap hwl hwr _ _ _ _
  · rw [ite_eq_right hij, ite_eq_right hij, flipCfg_apply, flipCfg_apply]
    simp only [mem_blockLabels]
    rw [w_ite_swap hwl hwr _ _ _ _]
    exact congrArg (· * _) (if_congr iff_comm rfl rfl)

omit [Fintype β'] in
/-- **The far bond at a reversed configuration**: `α'_e + σ_e(A) γ_e`, `α' = α + 𝟙_𝓑`. -/
theorem farBondW_flip (hM : 1 ≤ M) (hwl : ∀ d e, w d.swap e = -w d e)
    (hwr : ∀ d e, w d e.swap = -w d e) (blk : ι → β') (A : Finset β') (c : ι → ℂ × ℂ)
    (e : Sym2 ι) :
    farBondW β w M lam (flipCfg (blockLabels blk A) c) e =
      alphaW β w M lam c e + linkIndE M lam c e +
        signCross (Sym2.map blk) A e * gammaW β w M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    simp only [farBondW, alphaW, gammaW, linkIndE, symmLift_mk, farBondWij, linkInd,
      signCross, Sym2.map_mk, crosses_mk]
    have hML : MultipoleLinked M lam (flipCfg (blockLabels blk A) c i)
        (flipCfg (blockLabels blk A) c j) ↔ MultipoleLinked M lam (c i) (c j) :=
      multipoleLinked_flip _ c i j
    by_cases hl : MultipoleLinked M lam (c i) (c j)
    · rw [ite_eq_left (hML.2 hl), ite_eq_left hl, ite_eq_left hl, ite_eq_left hl]
      ring
    · rw [ite_eq_right (mt hML.1 hl), ite_eq_right hl, ite_eq_right hl, ite_eq_right hl,
        sOrd_of_not_linked hM w _ (mt hML.1 hl), wOrd_flip hwl hwr blk A c i j, add_zero]
      by_cases hab : (blk i ∈ A ↔ blk j ∈ A)
      · have hnc : ¬ (blk i ∈ A ↔ blk j ∉ A) := by tauto
        rw [ite_eq_left hab, ite_eq_right hnc, one_mul, neg_mul, ← Real.cosh_sub_sinh]
        ring
      · have hc : (blk i ∈ A ↔ blk j ∉ A) := by tauto
        rw [ite_eq_right hab, ite_eq_left hc, show -β * (-1 * wOrd w c i j) =
          β * wOrd w c i j by ring, ← Real.cosh_add_sinh]
        ring

omit [Fintype ι] [LinearOrder ι] in
theorem prod_linkIndE_flip (B : Finset ι) (D : Finset (Sym2 ι)) (c : ι → ℂ × ℂ) :
    ∏ e ∈ D, -linkIndE M lam (flipCfg B c) e = ∏ e ∈ D, -linkIndE M lam c e :=
  prod_congr rfl fun e _ => by rw [linkIndE_flip]

theorem clusterG_flip (hwl : ∀ d e, w d.swap e = -w d e) (hwr : ∀ d e, w d e.swap = -w d e)
    (hψ : ∀ d, ψ d.swap = ψ d) (blk : ι → β') (Dn Dz : Finset (Sym2 ι)) (A : Finset β')
    (c : ι → ℂ × ℂ) :
    clusterG β w ψ M lam blk Dn Dz (flipCfg (blockLabels blk A) c) =
      clusterG β w ψ M lam blk Dn Dz c := by
  unfold clusterG
  simp_rw [blockWW_flip hwl hwr hψ blk _ A c, farInd_flip _ c, prod_linkIndE_flip]

/-- **A cluster integrand at a reversed configuration.** -/
theorem clusterQ_flip (hM : 1 ≤ M) (hwl : ∀ d e, w d.swap e = -w d e)
    (hwr : ∀ d e, w d e.swap = -w d e) (hψ : ∀ d, ψ d.swap = ψ d) (blk : ι → β')
    (Dn Dz Df : Finset (Sym2 ι)) (A : Finset β') (c : ι → ℂ × ℂ) :
    clusterQ β w ψ M lam blk Dn Dz Df (flipCfg (blockLabels blk A) c) =
      clusterG β w ψ M lam blk Dn Dz c * ∏ e ∈ Df, (alphaW β w M lam c e + linkIndE M lam c e +
        signCross (Sym2.map blk) A e * gammaW β w M lam c e) := by
  unfold clusterQ
  rw [clusterG_flip hwl hwr hψ]
  simp_rw [farBondW_flip hM hwl hwr blk A c]

end Flip

/-! ### Transport of the integrands of `MultipoleBKT.ExpansionErrors.clusterIntegral` -/

section Transport

variable {X : Finset (Finset ℕ)} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {ψ : ℂ × ℂ → ℝ}

open scoped Classical in
theorem blockWeightOf_extendConfig_eqW (hX : IsSubpartition X) {S : Finset ℕ} (hS : S ∈ X)
    (y : X.biUnion id → ℂ × ℂ) :
    blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y) =
      blockWW β w ψ M lam (Limits.blockOf X) ⟨S, hS⟩ y := by
  rw [← hierBlockWeight_restrict β w ψ M lam hS, restrict_extendConfig]
  have hset : {i : X.biUnion id | Limits.blockOf X i = ⟨S, hS⟩} =
      {i : X.biUnion id | (i : ℕ) ∈ S} := by
    ext i
    exact Limits.blockOf_eq_iff hX i ⟨S, hS⟩
  have hc : ((nearGraph M lam y).induce {i : X.biUnion id | Limits.blockOf X i = ⟨S, hS⟩}).Connected ↔
      ((SimpleGraph.fromRel fun i j : X.biUnion id => MultipoleLinked M lam (y i) (y j)).induce
        {i : X.biUnion id | (i : ℕ) ∈ S}).Connected := by rw [hset]
  unfold hierBlockWeight blockWW nearConnInd
  have hrest : (∏ i : X.biUnion id, ∏ j : X.biUnion id, if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
        (if IsStableDipolePair (y i) (y j) then Real.exp (-β * w (y i) (y j)) else 0) else 1) *
        (∏ i : X.biUnion id, if (i : ℕ) ∈ S then ψ (y i) else 1) =
      (∏ i, ∏ j, if Limits.blockOf X i = ⟨S, hS⟩ ∧ Limits.blockOf X j = ⟨S, hS⟩ ∧ i < j then
        stableWeight β w (y i) (y j) else 1) *
        ∏ i, if Limits.blockOf X i = ⟨S, hS⟩ then ψ (y i) else 1 := by
    congr 1
    · refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
      simp only [Limits.blockOf_eq_iff hX]
      rfl
    · refine prod_congr rfl fun i _ => ?_
      simp only [Limits.blockOf_eq_iff hX]
  rw [mul_assoc, hrest, ← mul_assoc]
  by_cases h : ((nearGraph M lam y).induce
      {i : X.biUnion id | Limits.blockOf X i = ⟨S, hS⟩}).Connected
  · rw [ite_eq_left (hc.1 h), ite_eq_left h]
  · rw [ite_eq_right (mt hc.2 h), ite_eq_right h]

open scoped Classical in
theorem prod_blockWeightOf_extendConfig_eqW (hX : IsSubpartition X) (y : X.biUnion id → ℂ × ℂ) :
    ∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y) =
      ∏ S : X, blockWW β w ψ M lam (Limits.blockOf X) S y := by
  rw [← Finset.prod_coe_sort X]
  exact prod_congr rfl fun S _ => blockWeightOf_extendConfig_eqW hX S.2 y

open scoped Classical in
/-- **The bond product of a model on the labels.** -/
theorem clusterTerm_extendConfig_eqW {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ))
    (hEI : univ.biUnion Es ⊆ univ.biUnion fun l => interPairs (Xs l))
    (hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn (X.biUnion id))
    (hF : F ⊆ pairsOn (X.biUnion id)) (y : X.biUnion id → ℂ × ℂ) :
    clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) =
      (∏ e ∈ symOf (X.biUnion id) (univ.biUnion Es), farBondW β w M lam y e) *
        (∏ e ∈ symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es),
          farInd M lam y e) *
        ∏ e ∈ symOf (X.biUnion id) F, -linkIndE M lam y e := by
  unfold clusterTerm
  set c := extendConfig (X.biUnion id) y
  set E := univ.biUnion Es
  set I := univ.biUnion fun l => interPairs (Xs l)
  rw [← prod_sdiff hEI]
  have hE : (∏ p ∈ E, mayerBondOf β w (c p.1) (c p.2)) *
      (∏ p ∈ E, if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1) =
      ∏ e ∈ symOf (X.biUnion id) E, farBondW β w M lam y e := by
    rw [← prod_mul_distrib]
    refine prod_symOf (hEI.trans hI) _ _ fun i j hij => ?_
    simp only [c, extendConfig_coe, farBondW, symmLift_mk, farBondWij, sOrd, ite_eq_left hij,
      mayerBondOf, stableWeight]
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

open scoped Classical in
/-- The integrand of `MultipoleBKT.ExpansionErrors.clusterIntegral` (without the dipole weights)
is `clusterQ` on the labels of `V_X`. -/
theorem integrand_eq_clusterQ (hX : IsSubpartition X) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Es : Fin n → Finset (ℕ × ℕ)) (F : Finset (ℕ × ℕ))
    (hEI : univ.biUnion Es ⊆ univ.biUnion fun l => interPairs (Xs l))
    (hI : (univ.biUnion fun l => interPairs (Xs l)) ⊆ pairsOn (X.biUnion id))
    (hF : F ⊆ pairsOn (X.biUnion id)) (y : X.biUnion id → ℂ × ℂ) :
    (∏ S ∈ X, blockWeightOf β w ψ M lam S (extendConfig (X.biUnion id) y)) *
        clusterTerm β w M lam Xs Es F (extendConfig (X.biUnion id) y) =
      clusterQ β w ψ M lam (Limits.blockOf X) (symOf (X.biUnion id) F)
        (symOf (X.biUnion id) ((univ.biUnion fun l => interPairs (Xs l)) \ univ.biUnion Es))
        (symOf (X.biUnion id) (univ.biUnion Es)) y := by
  rw [prod_blockWeightOf_extendConfig_eqW hX y, clusterTerm_extendConfig_eqW Xs Es F hEI hI hF y]
  unfold clusterQ clusterG
  ring

end Transport

end ExpansionK

end MultipoleBKT

end
