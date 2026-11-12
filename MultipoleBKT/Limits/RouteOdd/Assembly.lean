/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteOdd.Trees
public import MultipoleBKT.Limits.RouteOdd.Components

/-!
# Separate odd and even trees

See (A.30) and the following
paragraph. Choose one root in each odd component, open its ears,
then connect the components using a separate tree of even edges.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset SimpleGraph

variable {β ε : Type*} [Fintype β] [DecidableEq β] [DecidableEq ε]

/-- Lift a quotient tree through disjoint trees on its vertex fibers. -/
theorem lift_tree_isTree {γ : Type*} (ends : ε → Sym2 β) (q : β → γ)
    (hsurj : Function.Surjective q) {A B : Finset ε}
    (hr : ∀ v w, q v = q w → (nodeGraph ends A).Reachable v w)
    (hAc : A.card + Nat.card γ = Fintype.card β) (hdisj : Disjoint A B)
    (hB : (nodeGraph (Sym2.map q ∘ ends) B).IsTree) (hBc : B.card + 1 = Nat.card γ) :
    (nodeGraph ends (A ∪ B)).IsTree := by
  classical
  let G := nodeGraph ends (A ∪ B)
  have hsame : ∀ v w, q v = q w → G.Reachable v w := fun v w h =>
    (hr v w h).mono (nodeGraph_mono subset_union_left)
  have hstep : ∀ u w, (nodeGraph (Sym2.map q ∘ ends) B).Adj u w →
      ∀ v, (∀ x, q x = u → G.Reachable v x) → ∀ x, q x = w → G.Reachable v x := by
    intro u w huw v hv x hx
    obtain ⟨hne, e, he, hew⟩ := nodeGraph_adj.1 huw
    simp only [Function.comp_apply] at hew
    generalize hend : ends e = z at hew
    induction z using Sym2.ind with
    | h a b =>
      simp only [Sym2.map_mk] at hew
      have hqab : q a ≠ q b := by
        intro h
        rcases Sym2.eq_iff.1 hew with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hne (h1.symm.trans (h.trans h2))
        · exact hne (h2.symm.trans (h.symm.trans h1))
      have hab : G.Adj a b := nodeGraph_adj_of_mem (mem_union_right _ he) hend
        (fun h => hqab (congrArg q h))
      rcases Sym2.eq_iff.1 hew with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact ((hv a ha).trans hab.reachable).trans (hsame b x (hb.trans hx.symm))
      · exact ((hv b hb).trans hab.symm.reachable).trans (hsame a x (ha.trans hx.symm))
  have hlift : ∀ u w (p : (nodeGraph (Sym2.map q ∘ ends) B).Walk u w),
      ∀ v, (∀ x, q x = u → G.Reachable v x) → ∀ x, q x = w → G.Reachable v x := by
    intro u w p
    induction p with
    | nil => exact fun _ h => h
    | cons h p ih => exact fun v hv => ih v (hstep _ _ h v hv)
  have hnon : Nonempty β := by
    obtain ⟨C⟩ := hB.connected.nonempty
    obtain ⟨v, -⟩ := hsurj C
    exact ⟨v⟩
  obtain ⟨v⟩ := hnon
  have hreach : ∀ w, G.Reachable v w := by
    intro w
    obtain ⟨p⟩ := hB.connected.preconnected (q v) (q w)
    exact hlift _ _ p v (fun x hx => hsame v x hx.symm) w rfl
  apply nodeGraph_isTree_of_card ends (A ∪ B) v hreach
  rw [card_union_of_disjoint hdisj]
  omega


/-- Lifting the even quotient tree joins the odd trees without adding a cycle. -/
theorem union_odd_even_isTree (ends : ε → Sym2 β) {F A B : Finset ε}
    (hAF : A ⊆ F)
    (hr : ∀ v w, (nodeGraph ends F).Reachable v w → (nodeGraph ends A).Reachable v w)
    (hAc : A.card + Nat.card (nodeGraph ends F).ConnectedComponent = Fintype.card β)
    (hBF : Disjoint B F)
    (hB : (nodeGraph (Sym2.map (nodeGraph ends F).connectedComponentMk ∘ ends) B).IsTree)
    (hBc : B.card + 1 = Nat.card (nodeGraph ends F).ConnectedComponent) :
    (nodeGraph ends (A ∪ B)).IsTree := by
  apply lift_tree_isTree ends (nodeGraph ends F).connectedComponentMk
    (fun C => C.exists_rep) (fun v w h => hr v w (ConnectedComponent.exact h)) hAc
    (hBF.symm.mono_left hAF) hB hBc

omit [Fintype β] [DecidableEq β] in
/-- Each original odd component carries its own tree inside the assembled tree. -/
theorem odd_component_isTree (ends : ε → Sym2 β) {F A B : Finset ε} (hAF : A ⊆ F)
    (hr : ∀ v w, (nodeGraph ends F).Reachable v w → (nodeGraph ends A).Reachable v w)
    (ht : (nodeGraph ends (A ∪ B)).IsTree) (C : (nodeGraph ends F).ConnectedComponent) :
    ((nodeGraph ends A).induce C.supp).IsTree := by
  classical
  let D := (nodeGraph ends A).connectedComponentMk C.out
  have hsupp : D.supp = C.supp := by
    ext v
    constructor
    · intro hv
      have hAv : (nodeGraph ends A).Reachable C.out v :=
        ConnectedComponent.exact (ConnectedComponent.mem_supp_iff D v |>.mp hv).symm
      exact ConnectedComponent.sound (hAv.mono (nodeGraph_mono hAF)).symm |>.trans C.out_eq
    · intro hv
      exact ConnectedComponent.sound (hr v C.out (C.reachable_of_mem_supp hv C.out_eq))
  refine ⟨?_, ?_⟩
  · rw [← hsupp]
    exact D.connected_toSimpleGraph
  · exact (ht.isAcyclic.anti (nodeGraph_mono subset_union_left)).induce C.supp

open scoped Classical in
/-- The single-tail majorant with separate odd and even trees. The roots may be chosen
at the largest radius in each odd component. The type `β` can be singleton labels or
merged multipole blocks, and `ε` retains parallel edges. -/
theorem separate_trees_singleTail (ends : ε → Sym2 β) {E F : Finset ε}
    (_hFE : F ⊆ E) (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag) (hcut : CutEven ends F)
    (hconn : (nodeGraph ends E).Connected)
    (root : (nodeGraph ends F).ConnectedComponent → β)
    (hroot : ∀ C, (nodeGraph ends F).connectedComponentMk (root C) = C)
    (s : β → ℝ) (hs : ∀ v, 0 < s v) {R : ℝ} (hR : ∀ v, s v ≤ R)
    (d a b : ε → ℝ) (hd : ∀ e ∈ F, 0 < d e)
    (ha0 : ∀ e ∈ F, 0 ≤ a e) (ha1 : ∀ e ∈ F, a e ≤ 1)
    (ha : ∀ e ∈ F, ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w))))
    (hb0 : ∀ e ∈ E \ F, 0 ≤ b e) (hb1 : ∀ e ∈ E \ F, b e ≤ 1) :
    ∃ A ⊆ F, ∃ B ⊆ E \ F,
      (nodeGraph ends (A ∪ B)).IsTree ∧
      (∀ C : (nodeGraph ends F).ConnectedComponent, ((nodeGraph ends A).induce C.supp).IsTree) ∧
      (nodeGraph (Sym2.map (nodeGraph ends F).connectedComponentMk ∘ ends) B).IsTree ∧
      (∀ v w, (nodeGraph ends F).Reachable v w → (nodeGraph ends A).Reachable v w) ∧
      A.card + Nat.card (nodeGraph ends F).ConnectedComponent = Fintype.card β ∧
      B.card + 1 = Nat.card (nodeGraph ends F).ConnectedComponent ∧
      (∏ e ∈ F, a e) * ∏ e ∈ E \ F, b e ≤
        (∏ v ∈ univ \ (univ.filter (fun v => v ∈ Set.range root)), s v ^ 2) * globalTail R d A *
          (∏ e ∈ A, (d e ^ 2)⁻¹) * ∏ e ∈ B, b e := by
  classical
  let : Fintype (nodeGraph ends F).ConnectedComponent := Fintype.ofFinite _
  let Z : Finset β := (univ.filter (fun v => v ∈ Set.range root))
  have hinj : Function.Injective root := fun C D h => by rw [← hroot C, ← hroot D, h]
  have hZc : Z.card = Fintype.card (nodeGraph ends F).ConnectedComponent := by
    have hZeq : Z = univ.image root := by ext v; simp [Z]
    rw [hZeq, card_image_of_injective _ hinj, card_univ]
  obtain ⟨A, hAF, hAc, hAr, haA⟩ := componentwise_odd_forest ends hloop hcut root hroot
    s hs hR d a hd ha0 ha1 ha
  have hZcanonical : @Finset.filter β (fun v => v ∈ Set.range root)
      (fun v => Classical.propDecidable _) univ = Z := by ext v; simp [Z]
  rw [hZcanonical] at hAc hAr haA
  have hsame : ∀ v w, (nodeGraph ends F).Reachable v w → (nodeGraph ends A).Reachable v w := by
    intro v w hvw
    obtain ⟨z, hz, hzv⟩ := hAr v
    obtain ⟨z', hz', hzw⟩ := hAr w
    obtain ⟨C, rfl⟩ := ((mem_filter.1 hz).2)
    obtain ⟨D, rfl⟩ := ((mem_filter.1 hz').2)
    have hCD : C = D := by
      rw [← hroot C, ← hroot D]
      exact ConnectedComponent.sound
        ((hzv.mono (nodeGraph_mono hAF)).trans (hvw.trans (hzw.mono (nodeGraph_mono hAF)).symm))
    subst hCD
    exact hzv.symm.trans hzw
  have hAc' : A.card + Nat.card (nodeGraph ends F).ConnectedComponent = Fintype.card β := by
    rw [hAc, card_sdiff_of_subset (subset_univ Z), card_univ, Nat.card_eq_fintype_card, ← hZc]
    exact Nat.sub_add_cancel (card_le_univ Z)
  obtain ⟨B, hBE, hBt, hBc⟩ := exists_even_quotient_tree ends E F hconn
  have hBF : Disjoint B F := disjoint_of_subset_left hBE sdiff_disjoint
  have hABt := union_odd_even_isTree ends hAF hsame hAc' hBF hBt hBc
  refine ⟨A, hAF, B, hBE, hABt, odd_component_isTree ends hAF hsame hABt, hBt, hsame, hAc', hBc, ?_⟩
  have hbB : ∏ e ∈ E \ F, b e ≤ ∏ e ∈ B, b e := by
    rw [← prod_sdiff hBE]
    have hrest : ∏ e ∈ (E \ F) \ B, b e ≤ 1 :=
      prod_le_one₀ (fun e he => hb0 e (mem_sdiff.1 he).1) (fun e he => hb1 e (mem_sdiff.1 he).1)
    exact (mul_le_mul_of_nonneg_right hrest (prod_nonneg fun e he => hb0 e (hBE he))).trans_eq
      (one_mul _)
  have haA' : ∏ e ∈ F, a e ≤
      (∏ v ∈ univ \ (univ.filter (fun v => v ∈ Set.range root)), s v ^ 2) * globalTail R d A *
        ∏ e ∈ A, (d e ^ 2)⁻¹ := by
    have hZeq : Z = (univ.filter (fun v => v ∈ Set.range root)) := by ext v; simp [Z]
    rw [hZeq] at haA
    exact haA
  convert mul_le_mul haA' hbB (prod_nonneg hb0)
    (mul_nonneg (mul_nonneg (prod_nonneg fun v _ => sq_nonneg _) (globalTail_nonneg R d A))
      (prod_nonneg fun e _ => inv_nonneg.2 (sq_nonneg _))) using 1
  simp

end MultipoleBKT.Limits

end
