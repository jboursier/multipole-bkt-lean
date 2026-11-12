/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Bridge
public import MultipoleBKT.LowerBound.AbsoluteLower.RoutePosition.NearTreeMaximum

/-!
# Fixed-group spatial integrals before tree and group summation

The proof of Lemma 4.58, equation (A.67).

`jLarge_fixed_groups_spatial_le` exports the spatial bound for fixed
`Xs`, `Ta` and `Tb`, with the radius quotient and one logarithm at each
edge of the two fixed far-tree families. The proof integrates the selected
near-tree terms using the four endpoint sectors and tree coordinates.
The exact Cayley product multiplies a maximum over actual near-tree families.
It is absorbed into the explicit constant only after the fixed-tree integral
has been bounded uniformly.

`RoutePosition.fixed_groups_spatial_integral`, in the importing module
`RoutePosition.FixedGroups`, removes the regularization from the
logarithms and the factor 17 from the single-dipole radial weights.
The edge logarithms remain visible until the weighted Cayley sums in
`RouteFixedGroups`. No group summation is used in this module.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Finset SimpleGraph Multipole SetPartition Limits SmallIntegral Parity
open UpperBound.AbsoluteUpper (jLargeIntegrand jLarge simplifiedMajorant)
open scoped ENNReal

variable {M lam ε₀ : ℝ} {χ : ℂ → ℝ} {p₀ : ℕ} {β C₀ : ℝ} {X : Finset (Finset ℕ)}

/-- The edge set of a graph built from a set of edges without loops. -/
theorem edgeFinset_fromEdgeSet_eq {V : Type*} {A : Finset (Sym2 V)}
    (hdiag : ∀ e ∈ A, ¬ e.IsDiag) {_ : Fintype (fromEdgeSet (A : Set (Sym2 V))).edgeSet} :
    (fromEdgeSet (A : Set (Sym2 V))).edgeFinset = A := by
  ext e
  rw [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe]
  exact ⟨fun h => h.1, fun h => ⟨h, hdiag e h⟩⟩

open scoped Classical in
/-- `MultipoleBKT.AbsoluteLower.lintegral_treeTerm_le` with the far edges given as a set `F`. -/
theorem lintegral_treeTerm_le' {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) (β : ℝ) {h : ℝ} (hh : 0 ≤ h) (a R' : ℝ)
    {T : SimpleGraph ι} (hT : T.IsTree) (Nn F : Finset (Sym2 ι)) (hN : ∀ e ∈ Nn, e ∈ T.edgeSet)
    (hF : ∀ e, e ∈ F ↔ e ∈ T.edgeSet ∧ e ∉ Nn) (Nb : ℕ) :
    ∫⁻ c in boxConfig ι Nb, ENNReal.ofReal (radF lam c *
        ((∏ e ∈ Nn, nearE M lam c e) * ∏ e ∈ F, farE M lam R' c e) *
        ∏ i, dipoleWeight χ β lam h a ((c i).2 - (c i).1)) ≤
      (Nb : ℝ≥0∞) * ENNReal.ofReal (4 * Real.pi * M ^ 2) ^ Nn.card *
        ∫⁻ u : ι → ℂ, ENNReal.ofReal (radiusFactor lam u * ∏ i, dipoleWeight χ β lam h a (u i)) *
          ∏ e ∈ F, ENNReal.ofReal (8 * Real.pi * ell R'
            (edgeMin id (fun i => rho lam (u i)) e)) := by
  have hFeq : F = T.edgeFinset \ Nn := by
    ext e
    rw [hF, mem_sdiff, mem_edgeFinset]
  subst hFeq
  exact lintegral_treeTerm_le hχ hlam hM β hh a R' hT Nn (fun e he => mem_edgeFinset.2 (hN e he)) Nb

open scoped Classical in
/-- Integrate one fixed near forest and one even-edge profile choice.
proof of Lemma 4.58. -/
theorem lintegral_flatTerm_edgeLog_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hR : 0 ≤ ε₀ * truncationScale p₀ β lam) (a : ℝ)
    (hX : IsSubpartition X) (hXne : X.Nonempty) (N : ℕ)
    {κ : Type*} [Fintype κ] {G : κ → Finset (Finset ℕ)} {Ta : κ → Finset (ℕ × ℕ)}
    {Tb : Finset (ℕ × ℕ)} (hF : FlatHyp X G Ta Tb)
    (NT : Finset (Sym2 (X.biUnion id))) (hNT : NT ∈ (intraE (Limits.blockOf X)).powerset)
    (A : Finset (Sym2 (X.biUnion id))) (hA : A ∈ (graphOf (X.biUnion id) Tb).edgeFinset.powerset) :
    ∫⁻ y in boxConfig (X.biUnion id) N, ENNReal.ofReal (flatTerm χ β lam M
            (17 * ε₀ * truncationScale p₀ β lam) (ε₀ * truncationScale p₀ β lam) a
            (univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Tb).edgeFinset) NT A y) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal ((max 1 (4 * Real.pi * M ^ 2)) ^
          (X.biUnion id).card) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal (radiusFactor lam u *
            ∏ i, dipoleWeight χ β lam (ε₀ * truncationScale p₀ β lam) a (u i)) *
          ENNReal.ofReal (∏ e ∈ univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Tb).edgeFinset,
            8 * Real.pi * ell (17 * ε₀ * truncationScale p₀ β lam)
              (edgeMin id (fun i => rho lam (u i)) e)) := by
  have : Nonempty (X.biUnion id) := by
    obtain ⟨S, hS⟩ := hXne
    obtain ⟨i, hi⟩ := hX.1 S hS
    exact ⟨⟨i, mem_biUnion.2 ⟨S, hS, hi⟩⟩⟩
  set R := truncationScale p₀ β lam with hRdef
  set R' := 17 * ε₀ * R with hR'def
  set h := ε₀ * R with hhdef
  set Ea : κ → Finset (Sym2 (X.biUnion id)) := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
    with hEa
  set Eb := (graphOf (X.biUnion id) Tb).edgeFinset with hEb
  set E := univ.biUnion Ea ∪ Eb with hE
  set k := (X.biUnion id).card with hk
  set Kn := max 1 (4 * Real.pi * M ^ 2) with hKn
  have hKn1 : 1 ≤ Kn := le_max_left _ _
  set Φ : (X.biUnion id → ℂ) → ℝ≥0∞ := fun u => ENNReal.ofReal (radiusFactor lam u *
      ∏ i, dipoleWeight χ β lam h a (u i)) *
    ENNReal.ofReal (∏ e ∈ E,
      8 * Real.pi * ell R' (edgeMin id (fun i => rho lam (u i)) e)) with hΦ
  obtain ⟨hGdisj, hEaG, hcardl, hinter, hconn, hcount⟩ := flat_structure hX G hF.subset hF.disj
    Ta hF.inter hF.card Tb hF.inter_b hF.conn hF.count
  have hcardV : Fintype.card (X.biUnion id) = k := Fintype.card_coe _
  -- the edges are not loops, and `NT` is disjoint from `E`
  have hdiagE : ∀ e ∈ E, ¬ e.IsDiag := fun e he hd => hinter e he (by
    induction e using Sym2.ind with
    | h a b =>
      rw [Sym2.mk_isDiag_iff] at hd
      rw [Sym2.map_mk, Sym2.mk_isDiag_iff, hd])
  have hNTE : ∀ NT ∈ (intraE (Limits.blockOf X)).powerset, Disjoint NT E := by
    intro NT hNT
    rw [Finset.disjoint_left]
    intro e he he'
    exact hinter e he' (mem_filter.1 (mem_powerset.1 hNT he)).2.1
  -- one tree term, integrated
  have hbound : ∀ NT ∈ (intraE (Limits.blockOf X)).powerset, ∀ A ∈ Eb.powerset,
      ∫⁻ y in boxConfig (X.biUnion id) N,
          ENNReal.ofReal (flatTerm χ β lam M R' h a E NT A y) ≤
        (N : ℝ≥0∞) * ENNReal.ofReal (Kn ^ k) * ∫⁻ u, Φ u := by
    intro NT hNT A hA
    have hAE : A ⊆ E := (mem_powerset.1 hA).trans subset_union_right
    unfold flatTerm
    by_cases ht : (fromEdgeSet ((NT ∪ E : Finset (Sym2 (X.biUnion id))) :
        Set (Sym2 (X.biUnion id)))).IsTree
    swap
    · simp only [ht, ↓reduceIte, ENNReal.ofReal_zero, lintegral_zero]
      exact bot_le
    simp only [ht, ↓reduceIte]
    have hdiag : ∀ e ∈ NT ∪ E, ¬ e.IsDiag := by
      intro e he
      rcases mem_union.1 he with he | he
      · exact (mem_filter.1 (mem_powerset.1 hNT he)).2.2
      · exact hdiagE e he
    have hmemT : ∀ e, e ∈ (fromEdgeSet ((NT ∪ E : Finset (Sym2 (X.biUnion id))) :
        Set (Sym2 (X.biUnion id)))).edgeSet ↔ e ∈ NT ∪ E := by
      intro e
      rw [edgeSet_fromEdgeSet, Set.mem_sdiff, mem_coe]
      exact ⟨fun h => h.1, fun h => ⟨h, hdiag e h⟩⟩
    have hpos := lintegral_treeTerm_le' hχ hlam hM β hR a R' ht (NT ∪ A) (E \ A)
      (fun e he => (hmemT e).2 (union_subset_union le_rfl hAE he)) (fun e => by
        rw [hmemT, mem_sdiff]
        constructor
        · rintro ⟨he, hn⟩
          refine ⟨mem_union_right _ he, fun h' => ?_⟩
          rcases mem_union.1 h' with h'' | h''
          · exact disjoint_left.1 (hNTE NT hNT) h'' he
          · exact hn h''
        · rintro ⟨he, hn⟩
          rcases mem_union.1 he with he | he
          · exact absurd (mem_union_left _ he) hn
          · exact ⟨he, fun h' => hn (mem_union_right _ h')⟩) N
    have hcardN : (NT ∪ A).card ≤ k := by
      have h1 : NT ∪ A ⊆ NT ∪ E := union_subset_union le_rfl hAE
      have h2 := ht.card_edgeFinset
      rw [edgeFinset_fromEdgeSet_eq hdiag, hcardV] at h2
      have := card_le_card h1
      omega
    refine hpos.trans (mul_le_mul' (mul_le_mul' le_rfl ?_) (lintegral_mono fun u => ?_))
    · rw [← ENNReal.ofReal_pow (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (4 * Real.pi * M ^ 2) ^ (NT ∪ A).card ≤ Kn ^ (NT ∪ A).card :=
            pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
        _ ≤ Kn ^ k := pow_le_pow_right₀ hKn1 hcardN
    · refine mul_le_mul' le_rfl ?_
      rw [← ENNReal.ofReal_prod_of_nonneg fun e _ => by
        have := one_le_eight_pi_mul_ell R' (edgeMin id (fun i => rho lam (u i)) e); linarith]
      exact ENNReal.ofReal_le_ofReal
        (prod_le_prod_of_subset_of_one_le_real' sdiff_subset
          (fun e => one_le_eight_pi_mul_ell R' _))
  exact hbound NT hNT A hA

open scoped Classical in
/-- The spatial bound for `J₁`, with its near-tree family still fixed.
proof of Lemma 4.58. -/
theorem lintegral_flatTreeIntegrand_edgeLog_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hC₀ : 0 < C₀) (hR : 0 ≤ ε₀ * truncationScale p₀ β lam) {a : ℝ} (ha : C₀ / M ≤ a)
    (hX : IsSubpartition X) (hXne : X.Nonempty) (N : ℕ)
    {κ : Type*} [Fintype κ] {G : κ → Finset (Finset ℕ)} {Ta : κ → Finset (ℕ × ℕ)}
    {Tb : Finset (ℕ × ℕ)} (hF : FlatHyp X G Ta Tb)
    (Q : RouteJ.NearTreeFamily (Limits.blockOf X)) :
    RoutePosition.jOne χ N p₀ β lam M ε₀ C₀ X G Ta Tb Q ≤
      (N : ℝ≥0∞) * ENNReal.ofReal ((2 * max 1 (4 * Real.pi * M ^ 2)) ^
          (X.biUnion id).card) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal (radiusFactor lam u *
            ∏ i, dipoleWeight χ β lam (ε₀ * truncationScale p₀ β lam) a (u i)) *
          ENNReal.ofReal (∏ e ∈ univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Tb).edgeFinset,
            8 * Real.pi * ell (17 * ε₀ * truncationScale p₀ β lam)
              (edgeMin id (fun i => rho lam (u i)) e)) := by
  have : Nonempty (X.biUnion id) := by
    obtain ⟨S, hS⟩ := hXne
    obtain ⟨i, hi⟩ := hX.1 S hS
    exact ⟨⟨i, mem_biUnion.2 ⟨S, hS, hi⟩⟩⟩
  set R := truncationScale p₀ β lam with hRdef
  set R' := 17 * ε₀ * R with hR'def
  set h := ε₀ * R with hhdef
  set Ea : κ → Finset (Sym2 (X.biUnion id)) := fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
    with hEa
  set Eb := (graphOf (X.biUnion id) Tb).edgeFinset with hEb
  set E := univ.biUnion Ea ∪ Eb with hE
  set k := (X.biUnion id).card with hk
  set Kn := max 1 (4 * Real.pi * M ^ 2) with hKn
  have hKn1 : 1 ≤ Kn := le_max_left _ _
  set Φ : (X.biUnion id → ℂ) → ℝ≥0∞ := fun u => ENNReal.ofReal (radiusFactor lam u *
      ∏ i, dipoleWeight χ β lam h a (u i)) *
    ENNReal.ofReal (∏ e ∈ E,
      8 * Real.pi * ell R' (edgeMin id (fun i => rho lam (u i)) e)) with hΦ
  obtain ⟨hGdisj, hEaG, hcardl, hinter, hconn, hcount⟩ := flat_structure hX G hF.subset hF.disj
    Ta hF.inter hF.card Tb hF.inter_b hF.conn hF.count
  have hcardV : Fintype.card (X.biUnion id) = k := Fintype.card_coe _
  let NT := RouteJ.nearForest (Limits.blockOf X) (fun S => (Q S).val)
  have hNT : NT ∈ (intraE (Limits.blockOf X)).powerset := by
    apply mem_powerset.mpr
    intro e he
    induction e using Sym2.ind with
    | h i j =>
      obtain ⟨hne, hb⟩ := RouteJ.nearForest_endpoints (Limits.blockOf X)
        (fun S => (Q S).val) he
      exact mem_filter.mpr ⟨mem_univ _, by
        simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using And.intro hb hne⟩
  have hmeas (A : Finset (Sym2 (X.biUnion id))) :=
    (measurable_flatTerm hχ (β := β) (M := M) (R' := R') (h := h) (a := a) hlam E NT A).ennreal_ofReal
  have hpt (y : X.biUnion id → ℂ × ℂ) :
      ENNReal.ofReal (flatTreeIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb Q y) ≤
        ∑ A ∈ Eb.powerset, ENNReal.ofReal (flatTerm χ β lam M R' h a E NT A y) := by
    refine (ENNReal.ofReal_le_ofReal
      (flatTreeIntegrand_le hχ hlam hM hC₀ hR ha hX hF Q y)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun A _ => flatTerm_nonneg hlam hR E NT A y)]
  have hcardEb : Eb.card ≤ k := by
    have h2 : X.card ≤ k := card_le_card_biUnion (fun S hS T hT hST => hX.2 hS hT hST)
      fun S hS => hX.1 S hS
    change (∑ l, (Ea l).card) + Eb.card + 1 ≤ Fintype.card X at hcount
    rw [Fintype.card_coe] at hcount
    omega
  calc
    _ ≤ ∫⁻ y in boxConfig (X.biUnion id) N,
        ∑ A ∈ Eb.powerset, ENNReal.ofReal (flatTerm χ β lam M R' h a E NT A y) :=
      lintegral_mono hpt
    _ = ∑ A ∈ Eb.powerset, ∫⁻ y in boxConfig (X.biUnion id) N,
        ENNReal.ofReal (flatTerm χ β lam M R' h a E NT A y) :=
      lintegral_finsetSum _ fun A _ => hmeas A
    _ ≤ ∑ _A ∈ Eb.powerset, (N : ℝ≥0∞) * ENNReal.ofReal (Kn ^ k) * ∫⁻ u, Φ u := by
      apply sum_le_sum
      intro A hA
      exact lintegral_flatTerm_edgeLog_le hχ hlam hM hR a hX hXne N hF NT hNT A hA
    _ = (2 : ℝ≥0∞) ^ Eb.card * ((N : ℝ≥0∞) * ENNReal.ofReal (Kn ^ k) * ∫⁻ u, Φ u) := by
      rw [sum_const, card_powerset, nsmul_eq_mul]
      push_cast
      rfl
    _ ≤ (2 : ℝ≥0∞) ^ k * ((N : ℝ≥0∞) * ENNReal.ofReal (Kn ^ k) * ∫⁻ u, Φ u) :=
      mul_le_mul' (pow_le_pow_right₀ one_le_two hcardEb) le_rfl
    _ = _ := by
      have hKn0 : 0 ≤ Kn := zero_le_one.trans hKn1
      rw [mul_pow, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
      ring

open scoped Classical in
/-- **One flat structure, integrated** (proof of Lemma 4.59, proof of Lemma 4.58. See the module
docstring). -/
theorem lintegral_flatIntegrand_edgeLog_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hC₀ : 0 < C₀) (hR : 0 ≤ ε₀ * truncationScale p₀ β lam) {a : ℝ} (ha : C₀ / M ≤ a)
    (hX : IsSubpartition X) (hXne : X.Nonempty) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p) (N : ℕ)
    {κ : Type*} [Fintype κ] {G : κ → Finset (Finset ℕ)} {Ta : κ → Finset (ℕ × ℕ)}
    {Tb : Finset (ℕ × ℕ)} (hF : FlatHyp X G Ta Tb) :
    ∫⁻ y in boxConfig (X.biUnion id) N,
        ENNReal.ofReal (flatIntegrand χ p₀ β lam M ε₀ C₀ X G Ta Tb
          (extendConfig (X.biUnion id) y)) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal ((2 ^ (p + 1) * max 1 (4 * Real.pi * M ^ 2)) ^
          (X.biUnion id).card) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal (radiusFactor lam u *
            ∏ i, dipoleWeight χ β lam (ε₀ * truncationScale p₀ β lam) a (u i)) *
          ENNReal.ofReal (∏ e ∈ univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Tb).edgeFinset,
            8 * Real.pi * ell (17 * ε₀ * truncationScale p₀ β lam)
              (edgeMin id (fun i => rho lam (u i)) e)) := by
  set k := (X.biUnion id).card
  set Kn := max 1 (4 * Real.pi * M ^ 2)
  set E := univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
    (graphOf (X.biUnion id) Tb).edgeFinset
  set I := ∫⁻ u : X.biUnion id → ℂ,
    ENNReal.ofReal (radiusFactor lam u *
      ∏ i, dipoleWeight χ β lam (ε₀ * truncationScale p₀ β lam) a (u i)) *
      ENNReal.ofReal (∏ e ∈ E, 8 * Real.pi * ell (17 * ε₀ * truncationScale p₀ β lam)
        (edgeMin id (fun i => rho lam (u i)) e))
  have hc : (∏ S ∈ X, S.card ^ (S.card - 2)) ≤ 2 ^ (p * k) := by
    have hcayley := RoutePosition.cayley_product_le (Limits.blockOf X)
      (p := p) (fun S => by rw [RoutePosition.card_block_fibre hX]; exact hXp S S.property)
    simp_rw [RoutePosition.card_block_fibre hX] at hcayley
    rw [prod_coe_sort X (fun S : Finset ℕ => S.card ^ (S.card - 2)), Fintype.card_coe] at hcayley
    exact hcayley
  have hmax : (⨆ Q : RouteJ.NearTreeFamily (Limits.blockOf X),
      RoutePosition.jOne χ N p₀ β lam M ε₀ C₀ X G Ta Tb Q) ≤
      (N : ℝ≥0∞) * ENNReal.ofReal ((2 * Kn) ^ k) * I :=
    iSup_le fun Q => lintegral_flatTreeIntegrand_edgeLog_le hχ hlam hM hC₀ hR ha hX hXne N hF Q
  calc
    _ ≤ (∏ S ∈ X, S.card ^ (S.card - 2) : ℕ) *
        ⨆ Q : RouteJ.NearTreeFamily (Limits.blockOf X),
          RoutePosition.jOne χ N p₀ β lam M ε₀ C₀ X G Ta Tb Q :=
      RoutePosition.lintegral_flatIntegrand_le_cayley_max hχ hlam hX hR N G Ta Tb
    _ ≤ (2 : ℝ≥0∞) ^ (p * k) *
        ((N : ℝ≥0∞) * ENNReal.ofReal ((2 * Kn) ^ k) * I) := by
      apply mul_le_mul' _ hmax
      exact_mod_cast hc
    _ = _ := by
      have hconst : ENNReal.ofReal ((2 ^ (p + 1) * Kn) ^ k) =
          (2 : ℝ≥0∞) ^ (p * k) * ENNReal.ofReal ((2 * Kn) ^ k) := by
        rw [pow_succ, mul_assoc, mul_pow, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 ^ p),
          ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, pow_mul]
      change _ = (N : ℝ≥0∞) * ENNReal.ofReal ((2 ^ (p + 1) * Kn) ^ k) * I
      rw [hconst]
      ring

open scoped Classical in
/-- Spatial integration with fixed groups and fixed odd and even trees.
The edge logarithms remain inside the radial integral, as in
proof of Lemma 4.58. -/
theorem jLarge_fixed_groups_spatial_le (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) (hC₀ : 0 < C₀)
    (hR : 0 ≤ ε₀ * truncationScale p₀ β lam) {a : ℝ} (ha : C₀ / M ≤ a)
    (hX : IsSubpartition X) (hXne : X.Nonempty) {p : ℕ} (hXp : ∀ S ∈ X, S.card ≤ p) (N : ℕ)
    {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)} (hXsX : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    {Ta : Fin n → Finset (ℕ × ℕ)} (hTa : ∀ l, Ta l ∈ relTreePairs (Xs l))
    {Tb : Finset (ℕ × ℕ)} (hTb : Tb ∈ relTreePairs₀ (coarsen X (univ.image Xs))) :
    jLarge χ N p₀ β lam M ε₀ C₀ X Xs Ta Tb ≤
      (N : ℝ≥0∞) * ENNReal.ofReal ((2 ^ (p + 1) * max 1 (4 * Real.pi * M ^ 2)) ^
          (X.biUnion id).card) *
        ∫⁻ u : X.biUnion id → ℂ, ENNReal.ofReal (radiusFactor lam u *
            ∏ i, dipoleWeight χ β lam (ε₀ * truncationScale p₀ β lam) a (u i)) *
          ENNReal.ofReal (∏ e ∈ univ.biUnion (fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) ∪
              (graphOf (X.biUnion id) Tb).edgeFinset,
            8 * Real.pi * ell (17 * ε₀ * truncationScale p₀ β lam)
              (edgeMin id (fun i => rho lam (u i)) e)) :=
  lintegral_flatIntegrand_edgeLog_le hχ hlam hM hC₀ hR ha hX hXne hXp N
    (flatHyp_of_relTree hX hXsX hdisj hTa hTb)

end AbsoluteLower

end MultipoleBKT

end
