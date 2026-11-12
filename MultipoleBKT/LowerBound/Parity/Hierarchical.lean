/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.Parity.MayerBond
public import MultipoleBKT.LowerBound.Parity.Reduction

/-!
# The reduction to Eulerian graphs for the multipole activity (Corollary 4.34 for `𝖪^mult`)

Corollary 4.34 and its use for `𝖪^0_ε₀` and
`𝖪^0_∞ = 𝖪^mult` in the proof of Proposition 4.23 ("the same parity argument", proof of Proposition 4.23). Here the
reversal of a dipole is `Prod.swap : (x_i, y_i) ↦ (y_i, x_i)` (the midpoint `z_i` fixed, `r⃗_i`
changed into `-r⃗_i`, Remark 4.31).

* `measurePreserving_swap_dipoleMeasure`: the dipole measure `μ_{β,λ}` is invariant under the
  reversal (`Λ²` and `e^{β g_λ(x - y)}` are);
* `measurePreserving_flipOn_hierarchicalModel`: the hierarchical model `𝖯^X` is invariant under
  the simultaneous reversal of the dipoles of any block `S₀ ∈ X` (`𝟙_{𝓑_S}` is invariant under
  every reversal, and `e^{-β v_ij} 𝟙_{𝒜_ij}` under the reversal of both dipoles, proof of Corollary 4.34);
* `multipoleActivity_eq_sum_relEulerian`, `multipoleActivity_eq_sum_relEulerian'`: **the
  reduction (4.61) for the frozen multipole activity**: with the bond
  `e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1 = a_ij + b_ij`, `a = a^v 𝟙_{𝓑^c}`, `b = b^v 𝟙_{𝓑^c} - 𝟙_𝓑`,
  `𝖪^mult(X) = ∑_{E₁ ∈ Eul^X} ∑_{E₂ : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X} 𝔼_{𝖯^X}[∏_{E₁} a ∏_{E₂} b]`,
  for a subpartition `X`, `N ≥ 1`, `λ > 0` and `M ≥ 1` (the paper has `M > 20`);
* `exists_bound_bonds`, `integrable_edgeProd_mul_edgeProd`: the odd and even parts are bounded on
  `Λ²`, so every expanded term is integrable against `𝖯^X`.
-/

@[expose] public section

open MeasureTheory Finset SimpleGraph
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace Parity

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### Invariance of the reference measures -/

section Invariance

/-- The dipole measure is invariant under the reversal `(x, y) ↦ (y, x)`. -/
theorem measurePreserving_swap_dipoleMeasure (hχ : IsMollifier χ) (N : ℕ) (β lam : ℝ) :
    MeasurePreserving Prod.swap (dipoleMeasure χ N β lam) (dipoleMeasure χ N β lam) := by
  have hvol : MeasurePreserving (Prod.swap : ℂ × ℂ → ℂ × ℂ) volume volume := by
    rw [Measure.volume_eq_prod]
    exact Measure.measurePreserving_swap
  have hres := hvol.restrict_preimage (measurableSet_box_prod N)
  rw [Set.preimage_swap_prod] at hres
  refine measurePreserving_withDensity_of_comp hres MeasurableEquiv.prodComm.measurableEmbedding
    fun p => ?_
  rw [Prod.fst_swap, Prod.snd_swap, ← smearedKernel_neg hχ lam (p.2 - p.1), neg_sub]

/-- Reversing a dipole does not change whether it is linked to another one. -/
theorem multipoleLinked_flipOn {ι : Type*} [DecidableEq ι] (B : Finset ι) (c : ι → ℂ × ℂ)
    (i j : ι) :
    MultipoleLinked M lam (flipOn Prod.swap B c i) (flipOn Prod.swap B c j) ↔
      MultipoleLinked M lam (c i) (c j) := by
  simp only [flipOn_apply]
  split_ifs
  · rw [multipoleLinked_swap_left, multipoleLinked_swap_right]
  · rw [multipoleLinked_swap_left]
  · rw [multipoleLinked_swap_right]
  · exact Iff.rfl

open scoped Classical in
/-- `e^{-β v_ij} 𝟙_{𝒜_ij}` is invariant under the reversal of both dipoles. -/
theorem stablePairWeight_swap_swap (hχ : IsMollifier χ) (β lam : ℝ) (d e : ℂ × ℂ) :
    stablePairWeight χ β lam d.swap e.swap = stablePairWeight χ β lam d e := by
  unfold stablePairWeight
  rw [dipoleInteraction_swap_left _ _ hχ, dipoleInteraction_swap_right _ _ hχ, neg_neg]
  exact if_congr (isStableDipolePair_swap_swap d e) rfl rfl

open scoped Classical in
/-- The weight `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` of a block `S ∈ X` is invariant under the
simultaneous reversal of the dipoles of a block `S₀ ∈ X`. -/
theorem hierarchicalBlockWeight_flipOn (hχ : IsMollifier χ) {X : Finset (Finset ℕ)}
    (hX : IsSubpartition X) {S₀ S : Finset ℕ} (hS₀ : S₀ ∈ X) (hS : S ∈ X)
    (c : X.biUnion id → ℂ × ℂ) :
    hierarchicalBlockWeight χ β lam M X S (flipOn Prod.swap (blockSet X S₀) c) =
      hierarchicalBlockWeight χ β lam M X S c := by
  have hgraph : (SimpleGraph.fromRel fun i j : X.biUnion id =>
      MultipoleLinked M lam (flipOn Prod.swap (blockSet X S₀) c i)
        (flipOn Prod.swap (blockSet X S₀) c j)) =
      SimpleGraph.fromRel fun i j : X.biUnion id => MultipoleLinked M lam (c i) (c j) :=
    congrArg SimpleGraph.fromRel
      (funext fun i => funext fun j => propext (multipoleLinked_flipOn _ c i j))
  have hprod : (∏ i : X.biUnion id, ∏ j : X.biUnion id,
      if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then
        stablePairWeight χ β lam (flipOn Prod.swap (blockSet X S₀) c i)
          (flipOn Prod.swap (blockSet X S₀) c j) else 1) =
      ∏ i : X.biUnion id, ∏ j : X.biUnion id,
        if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then stablePairWeight χ β lam (c i) (c j)
        else 1 := by
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    by_cases hij : (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j
    · rw [ite_eq_left hij, ite_eq_left hij]
      by_cases hSS : S = S₀
      · subst hSS
        rw [flipOn_apply_of_mem (mem_blockSet.2 hij.1),
          flipOn_apply_of_mem (mem_blockSet.2 hij.2.1), stablePairWeight_swap_swap hχ]
      · have hd : Disjoint S S₀ := hX.2 (Finset.mem_coe.2 hS) (Finset.mem_coe.2 hS₀) hSS
        rw [flipOn_apply_of_notMem fun h => Finset.disjoint_left.1 hd hij.1 (mem_blockSet.1 h),
          flipOn_apply_of_notMem fun h => Finset.disjoint_left.1 hd hij.2.1 (mem_blockSet.1 h)]
    · rw [ite_eq_right hij, ite_eq_right hij]
  unfold hierarchicalBlockWeight
  rw [hgraph, hprod]

/-- The hierarchical model `𝖯^X` is invariant under the simultaneous reversal of the dipoles of a
block `S₀ ∈ X` (proof of Corollary 4.34). -/
theorem measurePreserving_flipOn_hierarchicalModel (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hN : 1 ≤ N) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X)
    (β M : ℝ) :
    MeasurePreserving (flipOn Prod.swap (blockSet X S₀)) (hierarchicalModel χ N β lam M X)
      (hierarchicalModel χ N β lam M X) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [hierarchicalModel_eq]
  refine measurePreserving_withDensity_flipOn measurable_swap Prod.swap_swap
    (measurePreserving_flipOn_pi (measurePreserving_swap_dipoleMeasure hχ N β lam) _)
    fun c => ?_
  unfold hierarchicalModelDensity
  exact Finset.prod_congr rfl fun S hS => by rw [hierarchicalBlockWeight_flipOn hχ hX hS₀ hS]

end Invariance

/-! ### The bonds of the multipole activity -/

section Bonds

/-- The odd part `a^v 𝟙_{𝓑^c}` of the bond of `𝖪^mult` is odd in the first dipole. -/
theorem oddBondUnlinked_dipoleInteraction_swap_left (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (d e : ℂ × ℂ) :
    oddBondUnlinked β (dipoleInteraction χ lam) M lam d.swap e =
      -oddBondUnlinked β (dipoleInteraction χ lam) M lam d e :=
  oddBondUnlinked_swap_left hM (fun d e => dipoleInteraction_swap_left d e hχ lam) d e

theorem oddBondUnlinked_dipoleInteraction_swap_right (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (d e : ℂ × ℂ) :
    oddBondUnlinked β (dipoleInteraction χ lam) M lam d e.swap =
      -oddBondUnlinked β (dipoleInteraction χ lam) M lam d e :=
  oddBondUnlinked_swap_right hM (fun d e => dipoleInteraction_swap_right d e hχ lam) d e

theorem evenBondMult_dipoleInteraction_swap_left (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (d e : ℂ × ℂ) :
    evenBondMult β (dipoleInteraction χ lam) M lam d.swap e =
      evenBondMult β (dipoleInteraction χ lam) M lam d e :=
  evenBondMult_swap_left hM (fun d e => dipoleInteraction_swap_left d e hχ lam) d e

theorem evenBondMult_dipoleInteraction_swap_right (hχ : IsMollifier χ) (hM : 1 ≤ M)
    (d e : ℂ × ℂ) :
    evenBondMult β (dipoleInteraction χ lam) M lam d e.swap =
      evenBondMult β (dipoleInteraction χ lam) M lam d e :=
  evenBondMult_swap_right hM (fun d e => dipoleInteraction_swap_right d e hχ lam) d e

/-- The odd part of the bond of `𝖪^mult` in terms of the bond: `a = (f(d, e) - f(d^swap, e))/2`,
with `f = e^{-β v} 𝟙_{𝓑^c} - 1`. -/
theorem oddBondUnlinked_dipoleInteraction_eq (hχ : IsMollifier χ) (hM : 1 ≤ M) (d e : ℂ × ℂ) :
    oddBondUnlinked β (dipoleInteraction χ lam) M lam d e =
      ((unlinkedPairWeight χ β lam M d e - 1) - (unlinkedPairWeight χ β lam M d.swap e - 1)) /
        2 := by
  rw [unlinkedPairWeight_sub_one_eq hM, unlinkedPairWeight_sub_one_eq hM]
  exact odd_eq_half_sub (fun d e => oddBondUnlinked_dipoleInteraction_swap_left hχ hM d e)
    (fun d e => evenBondMult_dipoleInteraction_swap_left hχ hM d e) d e

/-- The even part of the bond of `𝖪^mult` in terms of the bond:
`b = (f(d, e) + f(d^swap, e))/2`. -/
theorem evenBondMult_dipoleInteraction_eq (hχ : IsMollifier χ) (hM : 1 ≤ M) (d e : ℂ × ℂ) :
    evenBondMult β (dipoleInteraction χ lam) M lam d e =
      ((unlinkedPairWeight χ β lam M d e - 1) + (unlinkedPairWeight χ β lam M d.swap e - 1)) /
        2 := by
  rw [unlinkedPairWeight_sub_one_eq hM, unlinkedPairWeight_sub_one_eq hM]
  exact even_eq_half_add (fun d e => oddBondUnlinked_dipoleInteraction_swap_left hχ hM d e)
    (fun d e => evenBondMult_dipoleInteraction_swap_left hχ hM d e) d e

theorem measurable_oddBondUnlinked_dipoleInteraction (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : 1 ≤ M) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      oddBondUnlinked β (dipoleInteraction χ lam) M lam q.1 q.2 := by
  have h := measurable_unlinkedPairWeight hχ hlam β M
  have hs : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => (q.1.swap, q.2) := by fun_prop
  simp_rw [oddBondUnlinked_dipoleInteraction_eq hχ hM]
  exact (((h.sub_const 1).sub ((h.comp hs).sub_const 1)).div_const 2)

theorem measurable_evenBondMult_dipoleInteraction (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hM : 1 ≤ M) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      evenBondMult β (dipoleInteraction χ lam) M lam q.1 q.2 := by
  have h := measurable_unlinkedPairWeight hχ hlam β M
  have hs : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => (q.1.swap, q.2) := by fun_prop
  simp_rw [evenBondMult_dipoleInteraction_eq hχ hM]
  exact (((h.sub_const 1).add ((h.comp hs).sub_const 1)).div_const 2)

/-- On `Λ²`, the odd and even parts of the bond of `𝖪^mult` are bounded. -/
theorem exists_bound_bonds (hχ : IsMollifier χ) (hlam : 0 < lam) (hM : 1 ≤ M) (β : ℝ)
    (N : ℕ) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ d ∈ box N ×ˢ box N, ∀ e ∈ box N ×ˢ box N,
      |oddBondUnlinked β (dipoleInteraction χ lam) M lam d e| ≤ W ∧
        |evenBondMult β (dipoleInteraction χ lam) M lam d e| ≤ W := by
  obtain ⟨W, hW1, hW⟩ := exists_pairWeight_bound hχ hlam β M N
  refine ⟨W, hW1, fun d hd e he => ?_⟩
  have hds : d.swap ∈ box N ×ˢ box N := Set.mem_prod.2 ⟨(Set.mem_prod.1 hd).2,
    (Set.mem_prod.1 hd).1⟩
  have hg : ∀ d' ∈ box N ×ˢ box N, |unlinkedPairWeight χ β lam M d' e - 1| ≤ W := by
    intro d' hd'
    have h1 := (hW d' hd' e he).2
    have h0 := unlinkedPairWeight_nonneg χ β lam M d' e
    rw [abs_le]
    constructor <;> linarith
  have h1 := hg d hd
  have h2 := hg d.swap hds
  rw [oddBondUnlinked_dipoleInteraction_eq hχ hM, evenBondMult_dipoleInteraction_eq hχ hM]
  constructor
  · rw [abs_div, abs_two, div_le_iff₀ two_pos]
    calc |unlinkedPairWeight χ β lam M d e - 1 - (unlinkedPairWeight χ β lam M d.swap e - 1)|
        ≤ |unlinkedPairWeight χ β lam M d e - 1| +
            |unlinkedPairWeight χ β lam M d.swap e - 1| := abs_sub _ _
      _ ≤ W * 2 := by linarith
  · rw [abs_div, abs_two, div_le_iff₀ two_pos]
    calc |unlinkedPairWeight χ β lam M d e - 1 + (unlinkedPairWeight χ β lam M d.swap e - 1)|
        ≤ |unlinkedPairWeight χ β lam M d e - 1| +
            |unlinkedPairWeight χ β lam M d.swap e - 1| := abs_add_le _ _
      _ ≤ W * 2 := by linarith

open scoped Classical in
theorem measurable_edgeProd {ι : Type*} [Fintype ι] [LinearOrder ι] (E : SimpleGraph ι)
    {f : ι → ι → ℂ × ℂ → ℂ × ℂ → ℝ}
    (hf : ∀ i j, Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => f i j q.1 q.2) :
    Measurable (edgeProd E f) := by
  unfold edgeProd
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases h : i < j ∧ E.Adj i j
  · simp only [h, and_self, ite_true]
    have hij : Measurable fun c : ι → ℂ × ℂ => (c i, c j) := by fun_prop
    exact (hf i j).comp hij
  · simp only [h, ite_false]
    exact measurable_const

open scoped Classical in
theorem abs_edgeProd_le {ι α : Type*} [Fintype ι] [LinearOrder ι] (E : SimpleGraph ι)
    {f : ι → ι → α → α → ℝ} {c : ι → α} {W : ℝ} (hW : 1 ≤ W)
    (hf : ∀ i j, |f i j (c i) (c j)| ≤ W) :
    |edgeProd E f c| ≤ W ^ (Fintype.card ι * Fintype.card ι) := by
  unfold edgeProd
  refine abs_prod_prod_le _ fun i j => ?_
  split_ifs
  · exact hf i j
  · rw [abs_one]
    exact hW

/-- The expanded terms of `𝖪^mult` are integrable against `𝖯^X`. -/
theorem integrable_edgeProd_mul_edgeProd (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (hM : 1 ≤ M) (β : ℝ) {X : Finset (Finset ℕ)} (E₁ E₂ : SimpleGraph (X.biUnion id)) :
    Integrable (fun c => edgeProd E₁ (fun _ _ => oddBondUnlinked β (dipoleInteraction χ lam) M lam)
        c * edgeProd E₂ (fun _ _ => evenBondMult β (dipoleInteraction χ lam) M lam) c)
      (hierarchicalModel χ N β lam M X) := by
  have := isFiniteMeasure_hierarchicalModel hχ hlam β M hN X
  obtain ⟨W, hW1, hW⟩ := exists_bound_bonds hχ hlam hM β N
  have hmeas : Measurable fun c => edgeProd E₁
      (fun _ _ => oddBondUnlinked β (dipoleInteraction χ lam) M lam) c *
        edgeProd E₂ (fun _ _ => evenBondMult β (dipoleInteraction χ lam) M lam) c :=
    (measurable_edgeProd E₁ fun _ _ => measurable_oddBondUnlinked_dipoleInteraction hχ hlam hM).mul
      (measurable_edgeProd E₂ fun _ _ => measurable_evenBondMult_dipoleInteraction hχ hlam hM)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (W ^ (Fintype.card (X.biUnion id) * Fintype.card (X.biUnion id)) *
      W ^ (Fintype.card (X.biUnion id) * Fintype.card (X.biUnion id))) ?_
  have hae := (hierarchicalModel_absolutelyContinuous χ N β lam M X).ae_le
    (ae_pi_dipoleMeasure_mem_box hχ hlam β hN (ι := X.biUnion id))
  filter_upwards [hae] with c hc
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (abs_edgeProd_le E₁ hW1 fun i j => (hW _ (hc i) _ (hc j)).1)
    (abs_edgeProd_le E₂ hW1 fun i j => (hW _ (hc i) _ (hc j)).2) (abs_nonneg _)
    (by positivity)

end Bonds

/-! ### Corollary 4.34 for the multipole activity -/

section Reduction

open scoped Classical

/-- The integrand of `𝖪^mult` is the product of the bonds `a + b`. -/
theorem multipoleActivityIntegrand_eq_edgeProd (hM : 1 ≤ M) {X : Finset (Finset ℕ)}
    (E : SimpleGraph (X.biUnion id)) (c : X.biUnion id → ℂ × ℂ) :
    multipoleActivityIntegrand χ β lam M E c =
      edgeProd E (fun _ _ d e => oddBondUnlinked β (dipoleInteraction χ lam) M lam d e +
        evenBondMult β (dipoleInteraction χ lam) M lam d e) c := by
  unfold multipoleActivityIntegrand edgeProd
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · exact unlinkedPairWeight_sub_one_eq hM χ _ _
  · rfl

/-- **The parity reduction (Corollary 4.34) for `𝖪^mult = 𝖪^0_∞`**, in the defining form of
`𝖪^mult` (Definition 2.13; "the same parity argument", proof of Proposition 4.23): for a subpartition `X`, `N ≥ 1`,
`λ > 0` and `M ≥ 1`, `𝖪^mult(X) = ∑_{E ∈ 𝖤^X} ∑_{E₁ ⊆ E, E₁ ∈ Eul^X}
𝔼_{𝖯^X}[∏_{E₁} a^v 𝟙_{𝓑^c} ∏_{E ∖ E₁} (b^v 𝟙_{𝓑^c} - 𝟙_𝓑)]`. -/
theorem multipoleActivity_eq_sum_relEulerian (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hN : 1 ≤ N) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (β : ℝ) :
    multipoleActivity χ N β lam M X =
      ∑ E ∈ relConnected X, ∑ E₁ ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter
          (fun E₁ => E₁ ≤ E ∧ IsRelEulerian X E₁),
        ∫ c, edgeProd E₁ (fun _ _ => oddBondUnlinked β (dipoleInteraction χ lam) M lam) c *
          edgeProd (E \ E₁) (fun _ _ => evenBondMult β (dipoleInteraction χ lam) M lam) c
          ∂hierarchicalModel χ N β lam M X := by
  rw [multipoleActivity_eq_sum]
  refine Finset.sum_congr rfl fun E hE => ?_
  have hE' : E ≤ interEdges X := (mem_relConnected.1 hE).1
  simp_rw [multipoleActivityIntegrand_eq_edgeProd hM]
  have h := integral_edgeProd_add_mul_eq_sum_relEulerian (G := fun _ => (1 : ℝ))
    measurable_swap Prod.swap_swap
    (fun S hS => measurePreserving_flipOn_hierarchicalModel hχ hlam hN hX hS β M) hE'
    (fun _ _ _ _ => oddBondUnlinked_dipoleInteraction_swap_left hχ hM)
    (fun _ _ _ _ => oddBondUnlinked_dipoleInteraction_swap_right hχ hM)
    (fun _ _ _ _ => evenBondMult_dipoleInteraction_swap_left hχ hM)
    (fun _ _ _ _ => evenBondMult_dipoleInteraction_swap_right hχ hM)
    (fun _ _ _ => rfl)
    (fun E₁ _ => by
      simp_rw [mul_one]
      exact integrable_edgeProd_mul_edgeProd hχ hlam hN hM β E₁ (E \ E₁))
  simp_rw [mul_one] at h
  exact h

/-- **The parity reduction (Corollary 4.34) for `𝖪^mult`** in the indexing of eq. (4.61):
`𝖪^mult(X) = ∑_{E₁ ∈ Eul^X} ∑_{E₂ : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X}
  𝔼_{𝖯^X}[∏_{ij ∈ E₁} a^v_ij 𝟙_{𝓑_ij^c} ∏_{ij ∈ E₂} (b^v_ij 𝟙_{𝓑_ij^c} - 𝟙_{𝓑_ij})]`. -/
theorem multipoleActivity_eq_sum_relEulerian' (hχ : IsMollifier χ) (hlam : 0 < lam)
    (hN : 1 ≤ N) (hM : 1 ≤ M) {X : Finset (Finset ℕ)} (hX : IsSubpartition X) (β : ℝ) :
    multipoleActivity χ N β lam M X =
      ∑ E₁ ∈ relEulerian X, ∑ E₂ ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter
          (fun E₂ => Disjoint E₁ E₂ ∧ IsRelConnected X (E₁ ⊔ E₂)),
        ∫ c, edgeProd E₁ (fun _ _ => oddBondUnlinked β (dipoleInteraction χ lam) M lam) c *
          edgeProd E₂ (fun _ _ => evenBondMult β (dipoleInteraction χ lam) M lam) c
          ∂hierarchicalModel χ N β lam M X := by
  rw [multipoleActivity_eq_sum_relEulerian hχ hlam hN hM hX β,
    sum_sum_sdiff_eq_sum_sum (relConnected X) (IsRelEulerian X)
      (fun E₁ E₂ => ∫ c, edgeProd E₁
        (fun _ _ => oddBondUnlinked β (dipoleInteraction χ lam) M lam) c *
          edgeProd E₂ (fun _ _ => evenBondMult β (dipoleInteraction χ lam) M lam) c
          ∂hierarchicalModel χ N β lam M X)]
  refine Finset.sum_congr rfl fun E₁ _ => Finset.sum_congr ?_ fun _ _ => rfl
  exact Finset.filter_congr fun E₂ _ => by rw [mem_relConnected]

end Reduction

end Parity

end MultipoleBKT

end
