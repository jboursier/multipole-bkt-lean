/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Quadratic.Bridges
public import MultipoleBKT.UpperBound.Quadratic.RouteLift.PartBridge
public import MultipoleBKT.UpperBound.Quadratic.RouteLift.LocalBounds

/-!
# The summed quadratic estimate for minimal marked skeletons

The paper: Corollary 5.34 and its proof.

`squares_of_bounds_sum` applies the local summed estimates in the bridge-blocks,
assembles the replacement trees injectively into `B(·,T)`, and compensates the
bridge and mark radii along the lifted heavy-light paths. The explicit comparison
coefficient is `C₁³ C₂ K⁶` per vertex. The quotient by the chosen bad distance is
retained, as in (5.89). Its maximal-radius specialization is in
`SimplifiedUpper.RouteLog.Quadratic`.
-/

@[expose] public section

open Finset SimpleGraph

namespace MultipoleBKT

namespace UpperBound

namespace Quadratic

open CoreForest Peeling

/-- On a bridge, `a^abs_ij ≤ r_i r_j d_ij^{-2} c_ij` (eq. (5.91)). -/
theorem absWeight_le_radProd_mul_keptWeight {V : Type*} {r : V → ℝ} {d c : Sym2 V → ℝ}
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (e : Sym2 V) :
    absWeight r d c e ≤ radProd r e * keptWeight d c e := by
  have hrp : 0 ≤ radProd r e := by
    induction e using Sym2.ind with
    | h u v => exact mul_nonneg (hr u) (hr v)
  have hrm : 0 ≤ radMax r e := by
    induction e using Sym2.ind with
    | h u v => exact (hr u).trans (le_max_left _ _)
  unfold absWeight keptWeight
  rcases (hd e).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hpos
      (hpos.trans_le (le_max_right _ _))) (pow_pos hpos 2)]
    have hmax : d e ≤ max (radMax r e) (d e) := le_max_right _ _
    have hce := hc e
    calc radProd r e * c e * d e ^ 2 = radProd r e * c e * (d e * d e) := by ring
      _ ≤ radProd r e * c e * (d e * max (radMax r e) (d e)) := by gcongr
      _ = _ := by ring

variable {X : Finset (Finset ℕ)} (hX : IsSubpartition X)

open scoped Classical in
/-- The tree-family form of (5.89), Corollary 5.34, the paper. Apply the local block estimates with their
tree-family sums, assemble the choices injectively, then compensate using the
edge-disjoint lifted paths on the extracted tree on `X`. -/
theorem squares_of_bounds_sum {V₁ : Finset (X.biUnion id)} {E₀ E : SimpleGraph (X.biUnion id)}
    (hE₀ : IsRelEulerianOffConnected X V₁ E₀) (hV₁ : V₁.Nonempty)
    (hE : IsMinimalSkeleton (blockOf hX) E₀ E) {r : X.biUnion id → ℝ}
    {dist c : Sym2 (X.biUnion id) → ℝ}
    {v₁ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      X.biUnion id}
    {e₀ : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      Sym2 (X.biUnion id)}
    {Ts Fs : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent →
      SimpleGraph (X.biUnion id)}
    (hP : IsPlusPeeling (blockOf hX) E (blockInnerEdges (blockOf hX) E) r dist v₁ e₀ Ts Fs)
    (hr : ∀ v, 0 ≤ r v) (hd : ∀ e, 0 ≤ dist e) (hc : ∀ e, 0 ≤ c e)
    {A : Sym2 (X.biUnion id) → ℝ} {Ainf δ : X.biUnion id → ℝ} {C₁ C₂ K : ℝ}
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K)
    (hA0 : ∀ e, 0 ≤ A e) (hA : ∀ e ∈ E.edgeSet, A e ≤ C₁ * absWeight r dist c e)
    (hAi0 : ∀ i, 0 ≤ Ainf i) (hAi : ∀ i ∈ V₁, Ainf i ≤ C₂ * (r i / δ i))
    (hδ : ∀ i, 0 < δ i) (hrδ : ∀ i, r i ≤ δ i)
    (hKE : ∀ i j, E.Adj i j → A s(i, j) ≠ 0 → δ j ≤ K * δ i)
    (hKS : ∀ i j, blockOf hX i = blockOf hX j → δ j ≤ K * δ i) (i₀ : X.biUnion id) :
    (∏ e ∈ E.edgeFinset, A e) * ∏ i ∈ V₁, Ainf i ≤
      (C₁ ^ 3 * C₂ * K ^ 6) ^ (X.biUnion id).card * (∏ S, blockRadius hX r S ^ 2) *
        (∑ T' ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts),
          ∏ e ∈ T'.edgeFinset, keptWeight dist c e) *
        (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) / δ i₀ ^ 2 := by
  set n := (X.biUnion id).card with hn
  set ρ := blockRadius hX r with hρ
  have hcross₀ : E₀ ≤ crossBlockGraph (blockOf hX) := interEdges_eq hX ▸ hE₀.1.1
  have hcross : E ≤ crossBlockGraph (blockOf hX) := hE.le.trans hcross₀
  have hconn₀ : (E₀ ⊔ sameBlockGraph (blockOf hX)).Connected := intraEdges_eq hX ▸ hE₀.2.2.2
  have hconn := connected_sup_of_isMinimalSkeleton hE hconn₀
  have hEE := isMinimalSkeleton_self_of_isMinimalSkeleton hcross₀ hE
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hδ0 : ∀ i, 0 ≤ δ i := fun i => (hδ i).le
  have hρ0 : ∀ S, 0 ≤ ρ S := fun S => by
    obtain ⟨i, rfl⟩ := blockOf_surjective hX S
    exact (hr i).trans (le_blockRadius r i)
  -- nonnegativity of the right side
  have hkept0 : ∀ G : SimpleGraph (X.biUnion id), 0 ≤ ∏ e ∈ G.edgeFinset, keptWeight dist c e :=
    fun G => prod_nonneg fun e _ => keptWeight_nonneg hc e
  have hpeel0 : 0 ≤ ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e :=
    prod_nonneg fun l _ => prod_nonneg fun e _ => peelWeight_nonneg hc _ _
  have hρprod0 : 0 ≤ ∏ S, ρ S ^ 2 := prod_nonneg fun S _ => sq_nonneg _
  have hC0 : 0 ≤ C₁ ^ 3 * C₂ * K ^ 6 := by
    have := zero_le_one.trans hC₁
    have := zero_le_one.trans hC₂
    positivity
  have hRHS0 : 0 ≤ (C₁ ^ 3 * C₂ * K ^ 6) ^ n * (∏ S, ρ S ^ 2) *
      (∑ U ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts), ∏ e ∈ U.edgeFinset, keptWeight dist c e) *
      (∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) / δ i₀ ^ 2 := by
    have : 0 ≤ ∑ U ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts), ∏ e ∈ U.edgeFinset, keptWeight dist c e := sum_nonneg fun U _ => hkept0 U
    have := hδ i₀
    positivity
  -- a vanishing odd weight
  by_cases hz : ∃ e ∈ E.edgeFinset, A e = 0
  · obtain ⟨e, he, he0⟩ := hz
    rw [Finset.prod_eq_zero he he0, zero_mul]
    exact hRHS0
  push Not at hz
  -- the comparisons along `E ∪ ℰ^intra`
  have hKG : ∀ u w, (E ⊔ sameBlockGraph (blockOf hX)).Adj u w → δ w ≤ K * δ u := by
    intro u w huw
    rcases huw with hEuw | hs
    · exact hKE u w hEuw (hz _ (mem_edgeFinset.2 hEuw))
    · exact hKS u w (sameBlockGraph_adj.1 hs).2
  -- the top part `Ŝ_l` of each bridge-block of the core
  have hŜ : ∀ l, ∃ S ∈ blockParts (blockOf hX) E l,
      (∀ x, bridgeBlock (blockOf hX) (coreEdges (blockOf hX) E) x = l → r x ≤ ρ S) ∧
        ((blockParts (blockOf hX) E l).card ≠ 1 → S = blockOf hX (v₁ l)) := by
    intro l
    by_cases h1 : (blockParts (blockOf hX) E l).card = 1
    · obtain ⟨S, hS⟩ := Finset.card_eq_one.1 h1
      refine ⟨S, hS ▸ mem_singleton_self S, fun x hx => ?_, fun h => absurd h1 h⟩
      have hbx : blockOf hX x ∈ blockParts (blockOf hX) E l := mem_blockParts.2 ⟨x, hx, rfl⟩
      rw [hS, mem_singleton] at hbx
      rw [← hbx]
      exact le_blockRadius r x
    · obtain ⟨w₁, e₀', Qs, hp, hw₁, -, -, -⟩ := (hP l).1 h1
      refine ⟨blockOf hX (v₁ l), mem_blockParts.2 ⟨v₁ l, hw₁ ▸ w₁.2, rfl⟩, fun x hx => ?_,
        fun _ => rfl⟩
      have := hp.le_radius ⟨x, hx⟩
      rw [hw₁] at this
      exact this.trans (le_blockRadius r (v₁ l))
  choose Ŝ hŜmem hŜr hŜv using hŜ
  -- the sizes of the bridge-blocks
  set s : (bridgelessGraph (blockOf hX) (coreEdges (blockOf hX) E)).ConnectedComponent → ℕ :=
    fun l => (univ.filter fun v => bridgeBlock (blockOf hX) (coreEdges (blockOf hX) E) v = l).card
    with hs
  have hsum : ∑ l, s l = n := by
    have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (X.biUnion id)))
      (t := univ) (f := bridgeBlock (blockOf hX) (coreEdges (blockOf hX) E))
      (fun x _ => mem_univ _)
    rw [card_univ, Fintype.card_coe] at h
    exact h.symm
  -- the blocks of `X` are partitioned by the bridge-blocks
  have hpartX : ∀ g : X → ℝ, ∏ S, g S =
      ∏ l, ∏ S ∈ blockParts (blockOf hX) E l, g S := by
    intro g
    have hcov : (univ : Finset X) = univ.biUnion fun l => blockParts (blockOf hX) E l := by
      ext S
      simp only [mem_univ, mem_biUnion, true_and, true_iff]
      obtain ⟨v, hv⟩ := blockOf_surjective hX S
      exact ⟨_, mem_blockParts.2 ⟨v, rfl, hv⟩⟩
    rw [hcov, Finset.prod_biUnion]
    intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨v, hv, rfl⟩ := mem_blockParts.1 hS
    obtain ⟨w, hw, hwv⟩ := mem_blockParts.1 hS'
    exact hll' (hv.symm.trans ((bridgeBlock_eq_of_eq hwv).symm.trans hw))
  -- the edges of `E`
  have hEeq := eq_iSup_sup_relBridges hcross hEE
  have hprodE : ∀ f : Sym2 (X.biUnion id) → ℝ, ∏ e ∈ E.edgeFinset, f e =
      (∏ l, ∏ e ∈ (blockInnerEdges (blockOf hX) E l).edgeFinset, f e) *
        ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, f e := by
    intro f
    rw [← prod_edgeFinset_iSup_sup (fun l l' h => disjoint_blockInnerEdges h)
      (disjoint_blockInnerEdges_relBridges hcross) f]
    exact Finset.prod_congr (Finset.ext fun e => by
      rw [mem_edgeFinset, mem_edgeFinset, ← hEeq]) fun _ _ => rfl
  have hlocal := fun l => RouteLift.localTree_of_peeling hcross hEE hP l
  -- Step 1: the bridge-blocks
  have hblock : ∀ l, ∏ e ∈ (blockInnerEdges (blockOf hX) E l).edgeFinset, A e ≤
      C₁ ^ (2 * s l) * ((∏ S ∈ (blockParts (blockOf hX) E l).erase (Ŝ l), ρ S ^ 2) *
        (∑ U ∈ RouteLift.blockAgreeingTrees r dist l (Ts l), ∏ e ∈ U.edgeFinset, keptWeight dist c e) *
          ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e) := by
    intro l
    exact RouteLift.block_weight_family_le hcross hEE hP hr hd hc ρ (le_blockRadius r)
      l (Ŝ l) (hŜmem l) (hŜv l) hC₁ hA0 hA
  -- Step 2: the bridges
  have hbr : ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, A e ≤
      C₁ ^ n * ((∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, radProd r e) *
        ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, keptWeight dist c e) := by
    have hcard : (relBridges (blockOf hX) E).edgeFinset.card ≤ n := by
      have h1 := natCard_relBridges_add_one hcross hconn
      have h2 : Nat.card (bridgelessGraph (blockOf hX) E).ConnectedComponent ≤
          Nat.card (X.biUnion id) :=
        Nat.card_le_card_of_surjective (bridgeBlock (blockOf hX) E) fun l => by
          induction l using ConnectedComponent.ind with
          | h x => exact ⟨x, rfl⟩
      have h3 : Nat.card (X.biUnion id) = n := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      rw [edgeFinset_card, ← Nat.card_eq_fintype_card]
      omega
    calc ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, A e
        ≤ ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, (C₁ * absWeight r dist c e) :=
          Finset.prod_le_prod₀ (fun e _ => hA0 e) fun e he =>
            hA e (edgeSet_mono relBridges_le (mem_edgeFinset.1 he))
      _ = C₁ ^ (relBridges (blockOf hX) E).edgeFinset.card *
            ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, absWeight r dist c e := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ C₁ ^ n * ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset,
            (radProd r e * keptWeight dist c e) := by
          refine mul_le_mul (pow_le_pow_right₀ hC₁ hcard)
            (Finset.prod_le_prod₀ (fun e _ => absWeight_nonneg hr hd hc e)
              fun e _ => absWeight_le_radProd_mul_keptWeight hr hd hc e)
            (prod_nonneg fun e _ => absWeight_nonneg hr hd hc e)
            (pow_nonneg (zero_le_one.trans hC₁) _)
      _ = _ := by rw [Finset.prod_mul_distrib]
  -- Step 3: the marks
  have hmarks : ∏ i ∈ V₁, Ainf i ≤ C₂ ^ n * ∏ i ∈ V₁, (r i / δ i) := by
    calc ∏ i ∈ V₁, Ainf i ≤ ∏ i ∈ V₁, (C₂ * (r i / δ i)) :=
          Finset.prod_le_prod₀ (fun i _ => hAi0 i) hAi
      _ = C₂ ^ V₁.card * ∏ i ∈ V₁, (r i / δ i) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ C₂ ^ n * ∏ i ∈ V₁, (r i / δ i) := by
          refine mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC₂ ?_)
            (prod_nonneg fun i _ => div_nonneg (hr i) (hδ0 i))
          have := Finset.card_le_univ V₁
          rwa [Fintype.card_coe] at this
  -- assembling
  set P := ∏ l, ∏ S ∈ (blockParts (blockOf hX) E l).erase (Ŝ l), ρ S ^ 2 with hPdef
  set Tl := ∏ l, ∑ U ∈ RouteLift.blockAgreeingTrees r dist l (Ts l), ∏ e ∈ U.edgeFinset, keptWeight dist c e with hTldef
  set Fl := ∏ l, ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e with hFldef
  set Bk := ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, keptWeight dist c e with hBkdef
  set Br := ∏ e ∈ (relBridges (blockOf hX) E).edgeFinset, radProd r e with hBrdef
  set Mk := ∏ i ∈ V₁, (r i / δ i) with hMkdef
  have hP0 : 0 ≤ P := prod_nonneg fun l _ => prod_nonneg fun S _ => sq_nonneg _
  have hTl0 : 0 ≤ Tl := prod_nonneg fun l _ => sum_nonneg fun U _ => hkept0 U
  have hBk0 : 0 ≤ Bk := hkept0 _
  have hBr0 : 0 ≤ Br := prod_nonneg fun e _ => by
    induction e using Sym2.ind with
    | h u v => exact mul_nonneg (hr u) (hr v)
  have hMk0 : 0 ≤ Mk := prod_nonneg fun i _ => div_nonneg (hr i) (hδ0 i)
  have hinner : ∏ l, ∏ e ∈ (blockInnerEdges (blockOf hX) E l).edgeFinset, A e ≤
      C₁ ^ (2 * n) * (P * Tl * Fl) := by
    calc ∏ l, ∏ e ∈ (blockInnerEdges (blockOf hX) E l).edgeFinset, A e
        ≤ ∏ l, (C₁ ^ (2 * s l) * ((∏ S ∈ (blockParts (blockOf hX) E l).erase (Ŝ l), ρ S ^ 2) *
            (∑ U ∈ RouteLift.blockAgreeingTrees r dist l (Ts l), ∏ e ∈ U.edgeFinset, keptWeight dist c e) *
              ∏ e ∈ (Fs l).edgeFinset, peelWeight r dist c (r (v₁ l)) (e₀ l) e)) :=
          Finset.prod_le_prod₀ (fun l _ => prod_nonneg fun e _ => hA0 e) fun l _ => hblock l
      _ = C₁ ^ (2 * n) * (P * Tl * Fl) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
            Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, hsum]
  have hρS : P * ∏ l, ρ (Ŝ l) ^ 2 = ∏ S, ρ S ^ 2 := by
    rw [hpartX, hPdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [mul_comm, Finset.mul_prod_erase _ (fun S => ρ S ^ 2) (hŜmem l)]
  -- Assemble all local choices before compensating the remaining radii.
  set Tsum := ∑ U ∈ longAgreeingTrees X r dist (plusTree (blockOf hX) E Ts),
    ∏ e ∈ U.edgeFinset, keptWeight dist c e with hTsum
  have hTsum0 : 0 ≤ Tsum := sum_nonneg fun U _ => hkept0 U
  have hT : Tl * Bk ≤ Tsum :=
    RouteLift.prod_block_sums_le_tree_sum hX hcross
      (isRelTree_plusTree_of_peeled hX hE₀ hE hP) hlocal _ (keptWeight_nonneg hc)
  -- Step 4: the bridges and the marks together
  obtain ⟨eqv, heqv⟩ := exists_componentEquiv (bridgelessGraph_eq hcross)
  have hBM := bridges_marks_le_parts hX hE₀ hV₁ hE hconn
    (R := fun m => ρ (Ŝ (eqv m))) hP hr hδ hrδ (fun x => by
      have := heqv x
      show r x ≤ ρ (Ŝ (eqv ((bridgelessGraph (blockOf hX) E).connectedComponentMk x)))
      rw [this]
      exact hŜr _ x rfl) hK hKG i₀
  have hRprod : ∏ m, ρ (Ŝ (eqv m)) ^ 2 = ∏ l, ρ (Ŝ l) ^ 2 :=
    Equiv.prod_comp eqv (fun l => ρ (Ŝ l) ^ 2)
  rw [hRprod] at hBM
  rw [hprodE A]
  exact RouteLift.assembly_compensation_le
    (prod_nonneg fun e _ => hA0 e) (prod_nonneg fun i _ => hAi0 i)
    hP0 hTl0 hpeel0 hBk0 hBr0 hMk0 hTsum0
    hC₁ hC₂ hinner hbr hmarks hT hBM hρS


end Quadratic

end UpperBound

end MultipoleBKT

end
