/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceTail

/-!
# All spatial alternatives for the omitted integrand

See Lemma A.7.
A surplus long edge is extracted before reducing the skeletons. A long
skeleton edge opens the longest edge in its component. A retained even
edge keeps its quartic kernel for integration outside the cutoff disc.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset SimpleGraph Limits Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- Internal spatial assembly of the omitted-edge alternatives. Concrete
baseline entry points discharge both even-edge bounds. The first alternative
retains the quadratic minimum and one global odd tail. -/
theorem internal_omitted_source_product (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
    (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2))
    (hpos : ∀ p ∈ O, 0 < d s(p.1,p.2))
    (Near Far T : Finset (ℕ × ℕ)) (hFar : Far ⊆ pairsOn (X.biUnion id)) (_hOF : O ⊆ Far)
    (hT : T ⊆ Near ∪ (Far \ O)) (b : ℕ × ℕ → ℝ)
    (hb0 : ∀ p, 0 ≤ b p) (hb1 : ∀ p, b p ≤ 1) (hNear : ∀ p ∈ Near, b p = 1)
    {R H Q : ℝ} (hR : ∀ i ∈ X.biUnion id, r i ≤ R) (hH : 0 < H) (hRH : R ≤ H)
    {p : ℕ × ℕ} (hp : p ∈ Far) (hpH : H ≤ d s(p.1,p.2))
    (hbq : b p ≤ R ^ 2 / H ^ 2) (hbQ : b p ≤ Q) :
    ∃ F : OddFamily hX hOX hpar r,
      ((∏ q ∈ O, absWeight r d c s(q.1,q.2)) * ∏ q ∈ Far \ O, b q ≤
        F.weight d c * min (R ^ 2 / H ^ 2) (globalTail R d F.edges) * ∏ q ∈ T, b q) ∨
      (p ∈ T ∧ (∏ q ∈ O, absWeight r d c s(q.1,q.2)) * ∏ q ∈ Far \ O, b q ≤
        F.weight d c * globalTail R d F.edges * Q * ∏ q ∈ T.erase p, b q) := by
  obtain ⟨P⟩ := exists_source_peeling hX hOX hpar r d
  let F := P.family
  let A := fun q : ℕ × ℕ => absWeight r d c s(q.1,q.2)
  let q := R ^ 2 / H ^ 2
  have hA0 : ∀ p, 0 ≤ A p := fun _ => absWeight_nonneg hr hd hc _
  have hA1 := source_odd_le_one r d c hr hd hc hc1 hfar
  have hF0 := F.weight_nonneg d c hc
  have htail0 := globalTail_nonneg R d F.edges
  have htail1 := globalTail_le_one R d F.edges
  have hq0 : 0 ≤ q := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpV := mem_pairsOn.1 (hFar hp)
  have hR0 : 0 ≤ R := (hr p.1).trans (hR _ hpV.1)
  have hq1 : q ≤ 1 := (div_le_one (pow_pos hH 2)).2 (pow_le_pow_left₀ hR0 hRH 2)
  have hmin : q * globalTail R d F.edges ≤ min q (globalTail R d F.edges) :=
    le_min (mul_le_of_le_one_right hq0 htail1) (mul_le_of_le_one_left htail0 hq1)
  have hskeleton := source_odd_skeleton_drop hX hOX hpar r d c hr hd hc hc1 hfar
  have hfamily := SourcePeeling.family_tail hX hOX hpar r d c hr hd hc hc1 hpos P hR
  have hodd : (∏ p ∈ O, A p) ≤ F.weight d c * globalTail R d F.edges := hskeleton.trans hfamily
  have heven := internal_even_drop_near (Far \ O) Near T hT b hb0 hb1 hNear
  have hbprod0 : 0 ≤ ∏ p ∈ Far \ O, b p := prod_nonneg fun _ _ => hb0 _
  have hTprod0 : 0 ≤ ∏ p ∈ T, b p := prod_nonneg fun _ _ => hb0 _
  refine ⟨F,?_⟩
  by_cases hpO : p ∈ O
  · apply Or.inl
    by_cases hpK : p ∈ sourceSkeletonEdges hX hOX hpar
    · have hlong := SourcePeeling.family_long hX hOX hpar r d c hr hd hc hc1 hpos P hR hH hRH hpK hpH
      exact mul_le_mul (hskeleton.trans hlong) heven hbprod0
        (mul_nonneg hF0 (le_min hq0 htail0))
    · have hgain : A p ≤ q := by
        have hD : 0 < d s(p.1,p.2) := hH.trans_le hpH
        have hden : 0 < d s(p.1,p.2) * max (max (r p.1) (r p.2)) (d s(p.1,p.2)) :=
          mul_pos hD (hD.trans_le (le_max_right _ _))
        have hn : r p.1 * r p.2 ≤ R ^ 2 := by
          rw [sq]
          exact mul_le_mul (hR _ hpV.1) (hR _ hpV.2.1) (hr _) ((hr _).trans (hR _ hpV.1))
        have hD' : H ^ 2 ≤ d s(p.1,p.2) * max (max (r p.1) (r p.2)) (d s(p.1,p.2)) := by
          rw [sq]
          exact mul_le_mul hpH (hpH.trans (le_max_right _ _)) hH.le hD.le
        change (r p.1 * r p.2 / (d s(p.1,p.2) * max (max (r p.1) (r p.2)) (d s(p.1,p.2)))) * c s(p.1,p.2) ≤ _
        exact (mul_le_of_le_one_right (div_nonneg (mul_nonneg (hr _) (hr _)) hden.le) (hc1 _)).trans
          (div_le_div₀ (sq_nonneg R) hn (pow_pos hH 2) hD')
      have hdrop := internal_surplus_product O (sourceSkeletonEdges hX hOX hpar)
        (sourceSkeletonEdges_subset hX hOX hpar) A (fun _ _ => hA0 _) hA1
        (mem_sdiff.2 ⟨hpO,hpK⟩ ) hgain
      calc _ ≤ (q * (F.weight d c * globalTail R d F.edges)) * ∏ p ∈ T, b p :=
             mul_le_mul (hdrop.trans (mul_le_mul_of_nonneg_left hfamily hq0)) heven hbprod0 (by positivity)
           _ = F.weight d c * (q * globalTail R d F.edges) * ∏ p ∈ T, b p := by ring
           _ ≤ _ := by gcongr
  · have hpB : p ∈ Far \ O := mem_sdiff.2 ⟨hp,hpO⟩
    by_cases hpT : p ∈ T
    · apply Or.inr
      refine ⟨hpT,?_⟩
      have heven' : (∏ p ∈ Far \ O, b p) ≤ Q * ∏ p ∈ T.erase p, b p := by
        apply heven.trans
        rw [← mul_prod_erase T b hpT]
        exact mul_le_mul_of_nonneg_right hbQ (prod_nonneg fun _ _ => hb0 _)
      exact mul_le_mul hodd heven' hbprod0 (mul_nonneg hF0 htail0) |>.trans_eq (by ring)
    · apply Or.inl
      have hTE : T ⊆ Near ∪ (Far \ O).erase p := by
        intro e he
        rcases mem_union.1 (hT he) with hn | hs
        · exact mem_union_left _ hn
        · exact mem_union_right _ (mem_erase.2 ⟨fun h => hpT (h ▸ he),hs⟩)
      have hdrop := internal_even_drop_near ((Far \ O).erase p) Near T hTE b hb0 hb1 hNear
      have heven' : (∏ p ∈ Far \ O, b p) ≤ q * ∏ p ∈ T, b p := by
        rw [← mul_prod_erase (Far \ O) b hpB]
        exact mul_le_mul hbq hdrop (prod_nonneg fun _ _ => hb0 _) hq0
      calc _ ≤ (F.weight d c * globalTail R d F.edges) * (q * ∏ p ∈ T, b p) :=
             mul_le_mul hodd heven' hbprod0 (mul_nonneg hF0 htail0)
           _ = F.weight d c * (q * globalTail R d F.edges) * ∏ p ∈ T, b p := by ring
           _ ≤ _ := by gcongr

end MultipoleBKT.ExpansionK.RouteCases

end
