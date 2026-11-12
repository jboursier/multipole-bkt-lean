/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.SourceMarked
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.RefinedControls

/-!
# Complete pointwise alternatives for every mixed summand

See (A.55)–(A.62). Cases A–D give a screening or bad-label gain on a complete
ordinary tree family. Case E keeps its distinguished even kernel and all
other even-tree factors. Common factors multiply both alternatives.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset Limits SimpleGraph Peeling Multipole Hierarchical Parity UpperBound.BoundedUpper

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

open scoped Classical in
/-- The complete spatial boundary for spatial integration. Both alternatives contain every odd
component, the connecting even tree, the gain, and the common factor. -/
def PaperPointwise (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
    (τ v : X.biUnion id → ℝ) (b J : Sym2 (X.biUnion id) → ℝ)
    (T : Finset (Sym2 (X.biUnion id))) (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (R common term : ℝ) : Prop :=
  (∃ (F : OddFamily hX hOX hpar r) (i : X.biUnion id),
    (|term| ≤ common * (R ^ 2 / τ i ^ 2) * F.weight d c * ∏ e ∈ T, b e) ∨
      (i ∈ P.2.2.2.2 ∧ |term| ≤ common * |v i| * F.weight d c * ∏ e ∈ T, b e)) ∨
  (∃ (F : OddFamily hX hOX hpar r) (i j : X.biUnion id),
    s(i,j) ∈ T ∩ P.2.1 ∧
    |term| ≤ common * (τ i ^ 2)⁻¹ * J s(i,j) * F.weight d c *
      ∏ e ∈ T.erase s(i,j), b e)

/-- Enlarging the common coefficient preserves both complete alternatives. -/
theorem PaperPointwise.mono_common {hX : IsSubpartition X} {hOX : O ⊆ interPairs X}
    {hpar : IsParityPair X O ∅} {r : ℕ → ℝ} {d c : Sym2 ℕ → ℝ}
    {τ v : X.biUnion id → ℝ} {b J : Sym2 (X.biUnion id) → ℝ}
    {T : Finset (Sym2 (X.biUnion id))} {P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id)}
    {R C C' t : ℝ} (H : PaperPointwise hX hOX hpar r d c τ v b J T P R C t)
    (hC : C ≤ C') (hc : ∀ e, 0 ≤ c e) (hb : ∀ e, 0 ≤ b e) (hJ : ∀ e, 0 ≤ J e) :
    PaperPointwise hX hOX hpar r d c τ v b J T P R C' t := by
  classical
  rcases H with ⟨F,i,hh⟩ | ⟨F,i,j,he,hh⟩
  · have hF := F.weight_nonneg d c hc
    have hT := prod_nonneg (fun e (_ : e ∈ T) => hb e)
    rcases hh with hh | ⟨hi,hh⟩
    · exact Or.inl ⟨F,i,Or.inl (hh.trans (by gcongr))⟩
    · exact Or.inl ⟨F,i,Or.inr ⟨hi,hh.trans (by gcongr)⟩⟩
  · exact Or.inr ⟨F,i,j,he,hh.trans (by
      have hF := F.weight_nonneg d c hc
      have hT := prod_nonneg (fun e (_ : e ∈ T.erase s(i,j)) => hb e)
      gcongr
      exact hJ _)⟩

section Internal

variable (hX : IsSubpartition X) (hOX : O ⊆ interPairs X) (hpar : IsParityPair X O ∅)
variable (r : ℕ → ℝ) (d c : Sym2 ℕ → ℝ)
variable (hr : ∀ i, 0 ≤ r i) (hd : ∀ e, 0 ≤ d e) (hc : ∀ e, 0 ≤ c e) (hc1 : ∀ e, c e ≤ 1)
variable (hfar : ∀ p ∈ O, min (r p.1) (r p.2) ≤ d s(p.1,p.2))
variable {R : ℝ} (hR : ∀ i ∈ X.biUnion id, r i ≤ R)
variable {S N : Finset (ℕ × ℕ)} (hS : S ⊆ pairsOn (X.biUnion id)) (hOS : O ⊆ S)
variable (T I : Finset (Sym2 (X.biUnion id))) (b J : Sym2 (X.biUnion id) → ℝ)
variable (hb0 : ∀ e, 0 ≤ b e) (hb1 : ∀ e, b e ≤ 1) (hJ : ∀ e, 0 ≤ J e)
variable (hT : T ⊆ symOf (X.biUnion id) N ∪ symOf (X.biUnion id) (S \ O))
variable (hN : ∀ e ∈ symOf (X.biUnion id) N, b e = 1)
variable {K : ℝ} {τ : X.biUnion id → ℝ}
variable {a₁ a₀ b₁ b₀ q : Sym2 (X.biUnion id) → ℝ} {u v : X.biUnion id → ℝ}
variable (H : InternalControls K (fun i : X.biUnion id => r i) τ
  (componentEdge (absWeight r d c)) b a₁ a₀ b₁ b₀ q u v)
variable (hRef : ∀ i j, |b₁ s(i,j) - b₀ s(i,j)| ≤ K * ((τ i ^ 2)⁻¹ * J s(i,j)))

include hr hd hc hc1 hfar hR hS hOS hb0 hb1 hJ hT hN H hRef

omit hS hOS hJ hRef in
open scoped Classical in
/-- Internal assembly of the exhaustive cases. Concrete entry points discharge
the analytic controls. The input graph and support hypotheses are geometric. -/
theorem internal_pointwise_vertex (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hP : P ∈ (fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) (S \ O)) I univ).erase (∅,∅,∅,∅,∅)) (G : ℝ) (i : X.biUnion id) (g : ℝ) (_hg : 0 ≤ g)
    (hgain : (g ≤ R ^ 2 / τ i ^ 2) ∨ (i ∈ P.2.2.2.2 ∧ g ≤ |v i|))
    (hterm : |G * fiveTerm (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) I a₁ a₀ b₁ b₀ q u v P| ≤
      (|G| * K ^ factorCount (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) P) *
      ((∏ e ∈ symOf (X.biUnion id) O, componentEdge (absWeight r d c) e) *
        (∏ e ∈ symOf (X.biUnion id) (S \ O), b e) * g)) :
    PaperPointwise hX hOX hpar r d c τ v b J T P R
      (|G| * K ^ factorCount (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) P)
      (G * fiveTerm (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) I a₁ a₀ b₁ b₀ q u v P) := by
  let A := absWeight r d c
  let OS := symOf (X.biUnion id) O
  let BS := symOf (X.biUnion id) (S \ O)
  let C := |G| * K ^ factorCount OS BS P
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans H.coefficient) _)
  have hA0 : ∀ e, 0 ≤ A e := fun e => absWeight_nonneg hr hd hc e
  have hAS0 : 0 ≤ ∏ e ∈ OS, componentEdge A e := prod_nonneg fun _ _ => hA0 _
  have hBS0 : 0 ≤ ∏ e ∈ BS, b e := prod_nonneg fun _ _ => hb0 _
  have hT0 : 0 ≤ ∏ e ∈ T, b e := prod_nonneg fun _ _ => hb0 _
  have hPe := (mem_erase.1 hP).2
  have hPodd : P.1 ⊆ OS := mem_powerset.1 (mem_product.1 hPe).1
  have hPeven : P.2.1 ⊆ BS := mem_powerset.1 (mem_product.1 (mem_product.1 hPe).2).1
  have hBdrop := internal_even_drop_near BS (symOf (X.biUnion id) N) T hT b hb0 hb1 hN
  obtain ⟨F,hF⟩ := source_skeleton_family hX hOX hpar r d c hr hd hc hc1
  have hfull : (∏ e ∈ OS, componentEdge A e) ≤ F.weight d c := by
    change (∏ e ∈ symOf (X.biUnion id) O, A (Sym2.map Subtype.val e)) ≤ _
    rw [source_product (hOX.trans interPairs_subset_pairsOn) A]
    exact (source_odd_skeleton_drop hX hOX hpar r d c hr hd hc hc1 hfar).trans hF
  have hF0 := F.weight_nonneg d c hc
  have hrprod : ∀ i j : X.biUnion id, r i * r j ≤ R ^ 2 := by
    intro i j
    rw [sq]
    exact mul_le_mul (hR i i.property) (hR j j.property) (hr _) ((hr _).trans (hR i i.property))
  apply Or.inl
  refine ⟨F,i,?_⟩
  rcases hgain with hgain | ⟨hi,hgain⟩
  · apply Or.inl
    apply hterm.trans
    calc _ = C * g * (∏ e ∈ OS, componentEdge A e) * ∏ e ∈ BS, b e := by ring
         _ ≤ C * (R ^ 2 / τ i ^ 2) * F.weight d c * ∏ e ∈ T, b e := by gcongr
  · apply Or.inr
    refine ⟨hi,hterm.trans ?_⟩
    calc _ = C * g * (∏ e ∈ OS, componentEdge A e) * ∏ e ∈ BS, b e := by ring
         _ ≤ C * |v i| * F.weight d c * ∏ e ∈ T, b e := by gcongr

omit hS hOS hJ hRef in
open scoped Classical in
theorem internal_pointwise_odd (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hP : P ∈ (fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) (S \ O)) I univ).erase (∅,∅,∅,∅,∅)) (G : ℝ) (hodd : P.1.Nonempty) :
    PaperPointwise hX hOX hpar r d c τ v b J T P R
      (|G| * K ^ factorCount (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) P)
      (G * fiveTerm (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) I a₁ a₀ b₁ b₀ q u v P) := by
  let A := absWeight r d c
  let OS := symOf (X.biUnion id) O
  let BS := symOf (X.biUnion id) (S \ O)
  let C := |G| * K ^ factorCount OS BS P
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans H.coefficient) _)
  have hA0 : ∀ e, 0 ≤ A e := fun e => absWeight_nonneg hr hd hc e
  have hAS0 : 0 ≤ ∏ e ∈ OS, componentEdge A e := prod_nonneg fun _ _ => hA0 _
  have hBS0 : 0 ≤ ∏ e ∈ BS, b e := prod_nonneg fun _ _ => hb0 _
  have hT0 : 0 ≤ ∏ e ∈ T, b e := prod_nonneg fun _ _ => hb0 _
  have hPe := (mem_erase.1 hP).2
  have hPodd : P.1 ⊆ OS := mem_powerset.1 (mem_product.1 hPe).1
  have hPeven : P.2.1 ⊆ BS := mem_powerset.1 (mem_product.1 (mem_product.1 hPe).2).1
  have hBdrop := internal_even_drop_near BS (symOf (X.biUnion id) N) T hT b hb0 hb1 hN
  obtain ⟨F,hF⟩ := source_skeleton_family hX hOX hpar r d c hr hd hc hc1
  have hfull : (∏ e ∈ OS, componentEdge A e) ≤ F.weight d c := by
    change (∏ e ∈ symOf (X.biUnion id) O, A (Sym2.map Subtype.val e)) ≤ _
    rw [source_product (hOX.trans interPairs_subset_pairsOn) A]
    exact (source_odd_skeleton_drop hX hOX hpar r d c hr hd hc hc1 hfar).trans hF
  have hF0 := F.weight_nonneg d c hc
  have hrprod : ∀ i j : X.biUnion id, r i * r j ≤ R ^ 2 := by
    intro i j
    rw [sq]
    exact mul_le_mul (hR i i.property) (hR j j.property) (hr _) ((hr _).trans (hR i i.property))
  obtain ⟨e,he⟩ := hodd
  obtain ⟨i,j,hij,hp,rfl⟩ := mem_symOf.1 (hPodd he)
  obtain ⟨F',hbound⟩ := source_odd_marked_family hX hOX hpar r d c hr hd hc hc1 hfar hp hR
  have hF'0 := F'.weight_nonneg d c hc
  have hmark := internal_odd_term H OS BS I P hPe G he
  have htransport := source_product_erase (hOX.trans interPairs_subset_pairsOn) A i j
  change (∏ e ∈ OS.erase s(i,j), componentEdge A e) = _ at htransport
  apply Or.inl
  refine ⟨F',i,Or.inl (hmark.trans ?_)⟩
  rw [htransport]
  calc _ = C * (τ i ^ 2)⁻¹ *
        (r i * r j * ∏ p ∈ O, if s(p.1,p.2) = s(i.val,j.val) then 1 else A s(p.1,p.2)) *
        ∏ e ∈ BS, b e := by dsimp only [C]; ring
       _ ≤ C * (τ i ^ 2)⁻¹ * (R ^ 2 * F'.weight d c) * ∏ e ∈ T, b e  := by gcongr
       _ = C * (R ^ 2 / τ i ^ 2) * F'.weight d c * ∏ e ∈ T, b e := by ring

omit hS hOS in
open scoped Classical in
theorem internal_pointwise_even (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hP : P ∈ (fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) (S \ O)) I univ).erase (∅,∅,∅,∅,∅)) (G : ℝ) (heven : P.2.1.Nonempty) :
    PaperPointwise hX hOX hpar r d c τ v b J T P R
      (|G| * K ^ factorCount (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) P)
      (G * fiveTerm (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) I a₁ a₀ b₁ b₀ q u v P) := by
  let A := absWeight r d c
  let OS := symOf (X.biUnion id) O
  let BS := symOf (X.biUnion id) (S \ O)
  let C := |G| * K ^ factorCount OS BS P
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (pow_nonneg (zero_le_one.trans H.coefficient) _)
  have hA0 : ∀ e, 0 ≤ A e := fun e => absWeight_nonneg hr hd hc e
  have hAS0 : 0 ≤ ∏ e ∈ OS, componentEdge A e := prod_nonneg fun _ _ => hA0 _
  have hBS0 : 0 ≤ ∏ e ∈ BS, b e := prod_nonneg fun _ _ => hb0 _
  have hT0 : 0 ≤ ∏ e ∈ T, b e := prod_nonneg fun _ _ => hb0 _
  have hPe := (mem_erase.1 hP).2
  have hPodd : P.1 ⊆ OS := mem_powerset.1 (mem_product.1 hPe).1
  have hPeven : P.2.1 ⊆ BS := mem_powerset.1 (mem_product.1 (mem_product.1 hPe).2).1
  have hBdrop := internal_even_drop_near BS (symOf (X.biUnion id) N) T hT b hb0 hb1 hN
  obtain ⟨F,hF⟩ := source_skeleton_family hX hOX hpar r d c hr hd hc hc1
  have hfull : (∏ e ∈ OS, componentEdge A e) ≤ F.weight d c := by
    change (∏ e ∈ symOf (X.biUnion id) O, A (Sym2.map Subtype.val e)) ≤ _
    rw [source_product (hOX.trans interPairs_subset_pairsOn) A]
    exact (source_odd_skeleton_drop hX hOX hpar r d c hr hd hc hc1 hfar).trans hF
  have hF0 := F.weight_nonneg d c hc
  have hrprod : ∀ i j : X.biUnion id, r i * r j ≤ R ^ 2 := by
    intro i j
    rw [sq]
    exact mul_le_mul (hR i i.property) (hR j j.property) (hr _) ((hr _).trans (hR i i.property))
  obtain ⟨e,he⟩ := heven
  induction e using Sym2.ind with
  | h i j =>
    by_cases heT : s(i,j) ∈ T
    · have hmark := internal_marked_even_term H OS BS I P hPe G he (hRef i j)
      have hTE : T.erase s(i,j) ⊆ symOf (X.biUnion id) N ∪ BS.erase s(i,j) := by
        intro e he'
        rcases mem_union.1 (hT (mem_of_mem_erase he')) with hn | hs
        · exact mem_union_left _ hn
        · exact mem_union_right _ (mem_erase.2 ⟨(mem_erase.1 he').1,hs⟩)
      have hdrop := internal_even_drop_near (BS.erase s(i,j)) (symOf (X.biUnion id) N)
        (T.erase s(i,j)) hTE b hb0 hb1 hN
      have hErase0 : 0 ≤ ∏ e ∈ BS.erase s(i,j), b e := prod_nonneg fun _ _ => hb0 _
      have hJe := hJ s(i,j)
      apply Or.inr
      refine ⟨F,i,j,mem_inter.2 ⟨heT,he⟩,hmark.trans ?_⟩
      calc _ = C * (τ i ^ 2)⁻¹ * J s(i,j) * (∏ e ∈ OS, componentEdge A e) *
          ∏ e ∈ BS.erase s(i,j), b e := by dsimp only [C]; ring
           _ ≤ C * (τ i ^ 2)⁻¹ * J s(i,j) * F.weight d c *
          ∏ e ∈ T.erase s(i,j), b e  := by gcongr
    · have hmark := internal_even_term H OS BS I P hPe G he
      have hTE : T ⊆ symOf (X.biUnion id) N ∪ BS.erase s(i,j) := by
        intro e he'
        rcases mem_union.1 (hT he') with hn | hs
        · exact mem_union_left _ hn
        · exact mem_union_right _ (mem_erase.2 ⟨fun h => heT (h ▸ he'),hs⟩)
      have hdrop := internal_even_drop_near (BS.erase s(i,j)) (symOf (X.biUnion id) N) T hTE b hb0 hb1 hN
      have hErase0 : 0 ≤ ∏ e ∈ BS.erase s(i,j), b e := prod_nonneg fun _ _ => hb0 _
      apply Or.inl
      refine ⟨F,i,Or.inl (hmark.trans ?_)⟩
      calc _ = C * (r i * r j / τ i ^ 2) * (∏ e ∈ OS, componentEdge A e) *
          ∏ e ∈ BS.erase s(i,j), b e := by dsimp only [C]; ring
           _ ≤ C * (R ^ 2 / τ i ^ 2) * F.weight d c * ∏ e ∈ T, b e := by
             have hgain : r i * r j / τ i ^ 2 ≤ R ^ 2 / τ i ^ 2 :=
               div_le_div_of_nonneg_right (hrprod i j) (sq_nonneg _)
             gcongr

omit hS hOS hJ hRef in
open scoped Classical in
theorem internal_pointwise_caseA (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hP : P ∈ (fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) (S \ O)) I univ).erase (∅,∅,∅,∅,∅)) (G : ℝ) (hA : P.2.2.1.Nonempty ∨ P.2.2.2.1.Nonempty ∨ P.2.2.2.2.Nonempty) :
    PaperPointwise hX hOX hpar r d c τ v b J T P R
      (|G| * K ^ factorCount (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) P)
      (G * fiveTerm (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) I a₁ a₀ b₁ b₀ q u v P) := by
  let OS := symOf (X.biUnion id) O
  let BS := symOf (X.biUnion id) (S \ O)
  have hPe := (mem_erase.1 hP).2
  have hrprod : ∀ i j : X.biUnion id, r i * r j ≤ R ^ 2 := by
    intro i j
    rw [sq]
    exact mul_le_mul (hR i i.property) (hR j j.property) (hr _) ((hr _).trans (hR i i.property))
  rcases hA with ⟨e,he⟩ | ⟨i,hi⟩ | ⟨i,hi⟩
  · induction e using Sym2.ind with
    | h i j =>
      exact internal_pointwise_vertex hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hT hN H P hP G i (r i * r j / τ i ^ 2) (div_nonneg (mul_nonneg (hr i) (hr j)) (sq_nonneg _))
        (Or.inl (div_le_div_of_nonneg_right (hrprod i j) (sq_nonneg _)))
        (internal_intra_term H OS BS I P hPe G he)
  · exact internal_pointwise_vertex hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hT hN H P hP G i (r i ^ 2 / τ i ^ 2) (div_nonneg (sq_nonneg _) (sq_nonneg _))
      (Or.inl (div_le_div_of_nonneg_right (by simpa only [sq] using hrprod i i) (sq_nonneg _)))
      (internal_quadratic_term H OS BS I P hPe G hi)
  · exact internal_pointwise_vertex hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hT hN H P hP G i |v i| (abs_nonneg _)
      (Or.inr ⟨hi,le_rfl⟩)
      (internal_bad_term H OS BS I P hPe G hi)

omit hS hOS in
open scoped Classical in
theorem internal_pointwise_cases (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hP : P ∈ (fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) (S \ O)) I univ).erase (∅,∅,∅,∅,∅)) (G : ℝ) :
    PaperPointwise hX hOX hpar r d c τ v b J T P R
      (|G| * K ^ factorCount (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) P)
      (G * fiveTerm (symOf (X.biUnion id) O) (symOf (X.biUnion id) (S \ O)) I a₁ a₀ b₁ b₀ q u v P) := by
  have hcases := five_cases_exhaustive (symOf (X.biUnion id) O)
    (symOf (X.biUnion id) (S \ O)) I univ (symOf (X.biUnion id) (sourceSkeletonEdges hX hOX hpar)) T (by simpa only [mem_erase] using hP)
  rcases hcases with ha | ho | he | ho | he
  · exact internal_pointwise_caseA hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hT hN H P hP G ha
  · exact internal_pointwise_odd hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hT hN H P hP G (ho.mono fun _ hm => (mem_inter.1 hm).2)
  · exact internal_pointwise_even hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hJ hT hN H hRef P hP G (he.mono fun _ hm => (mem_inter.1 hm).2)
  · exact internal_pointwise_odd hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hT hN H P hP G (ho.mono fun _ hm => (mem_inter.1 hm).2)
  · exact internal_pointwise_even hX hOX hpar r d c hr hd hc hc1 hfar hR T I b J hb0 hb1 hJ hT hN H hRef P hP G (he.mono fun _ hm => (mem_inter.1 hm).2)

end Internal

end MultipoleBKT.ExpansionK.RouteCases

end
