/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Gibbs.Basic
public import MultipoleBKT.Frozen.DipoleActivity
public import MultipoleBKT.Frozen.MultipoleActivity
public import MultipoleBKT.Frozen.MultipoleCount
public import MultipoleBKT.Matching.Measurable

/-!
# Plumbing for the activities and the hierarchical model

Routine facts about the frozen objects `MultipoleLinked`, `multipoleGraph`, `multipoleCount`,
`dipoleActivity`, `multipolePartitionFunction`, `hierarchicalModel` and `multipoleActivity` of
the paper, used by every later proof.
Throughout, `χ` is an admissible mollifier, `λ > 0` and `N ≥ 1` where needed.

* `measurableSet_setOf_apply_of_fibres`, `measurableSet_setOf_graph`: a set defined through a
  finite-valued random variable, resp. a graph-valued random variable with measurable edge
  indicators, is measurable.
* `measurableSet_multipoleLinked`, `measurableSet_setOf_multipoleLinked`: the relation
  `MultipoleLinked` (the events `𝓑_ij`) is Borel.
* `measurableSet_setOf_adj_multipoleGraph`, `measurableSet_setOf_multipoleGraph`,
 `measurableSet_multipoleCount_eq`, `measurable_multipoleCount`: the multipole graph and the
  counts `𝒩_k` of multipoles are random variables.
* `stablePairWeight`, `unlinkedPairWeight`: the pair factors `e^{-β v_ij} 𝟙_{𝒜_ij}` and
  `e^{-β v_ij} 𝟙_{𝓑_ij^c}` of the integrands, with their measurability, signs and a uniform bound
  on `Λ²` (`exists_pairWeight_bound`).
* `dipoleActivityIntegrand`, `multipolePartitionFunctionIntegrand`, `hierarchicalBlockWeight`,
 `hierarchicalModelDensity`, `multipoleActivityIntegrand`: the integrands and the density of the
  frozen definitions, named (the `*_eq_sum`, `*_eq_integral` and `hierarchicalModel_eq` lemmas
  are `rfl`), each with `measurable_*`, `exists_bound_*` (bounded on configurations with all
  dipoles in `Λ²`) and `integrable_*` (against `Measure.pi dipoleMeasure`, resp.
  `hierarchicalModel`).
* `isFiniteMeasure_hierarchicalModel`, `hierarchicalModel_absolutelyContinuous`: `𝖯^X` is a
  finite measure, absolutely continuous with respect to `μ^{⊗ V_X}`.
* `dipoleActivity_eq_zero_of_card_le_one`, `multipolePartitionFunction_singleton`,
 `multipoleActivity_eq_zero_of_card_le_one`: the elementary values.
* `multipolePartitionFunction_nonneg`, `multipolePartitionFunction_pos`: `𝖬_{β,λ}(S) ≥ 0`, and
  `> 0` for `S` nonempty and `M > 0` (a positive-measure cluster of `|S|` tiny, well-separated,
  mutually linked dipoles: `exists_cluster`, `isStableDipolePair_of_near`,
  `multipoleLinked_of_near`, `pi_dipoleMeasure_cluster_pos`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open TwoComponentCoulomb (box logKernel)

namespace MultipoleBKT

variable {χ : ℂ → ℝ} {lam β M : ℝ} {N : ℕ}

/-! ### Measurable sets defined through a finite-valued random variable -/

section Generic

/-- If `σ : α → β` has measurable fibres and `β` is countable, then `{a | P (σ a) a}` is
measurable as soon as each `{a | P b a}` is. -/
theorem measurableSet_setOf_apply_of_fibres {α β : Type*} [MeasurableSpace α] [Countable β]
    (σ : α → β) (P : β → α → Prop) (hσ : ∀ b, MeasurableSet {a | σ a = b})
    (hP : ∀ b, MeasurableSet {a | P b a}) : MeasurableSet {a | P (σ a) a} := by
  have h : {a | P (σ a) a} = ⋃ b, {a | σ a = b} ∩ {a | P b a} := by
    ext a
    simp
  rw [h]
  exact MeasurableSet.iUnion fun b => (hσ b).inter (hP b)

/-- A random simple graph on a finite vertex set, each of whose edge indicators is measurable,
has measurable level sets for every graph property. -/
theorem measurableSet_setOf_graph {α ι : Type*} [MeasurableSpace α] [Finite ι]
    (G : α → SimpleGraph ι) (hG : ∀ i j, MeasurableSet {a | (G a).Adj i j})
    (P : SimpleGraph ι → Prop) : MeasurableSet {a | P (G a)} := by
  have h : {a | P (G a)} = ⋃ H : SimpleGraph ι, ⋃ _ : P H, {a | G a = H} := by
    ext a
    simp
  have h2 : ∀ H : SimpleGraph ι, MeasurableSet {a | G a = H} := by
    intro H
    have : {a | G a = H} = ⋂ i, ⋂ j, {a | (G a).Adj i j ↔ H.Adj i j} := by
      ext a
      simp [SimpleGraph.ext_iff, funext_iff]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hH : H.Adj i j
    · have : {a | (G a).Adj i j ↔ H.Adj i j} = {a | (G a).Adj i j} := by
        ext a
        simp [hH]
      rw [this]
      exact hG i j
    · have : {a | (G a).Adj i j ↔ H.Adj i j} = {a | (G a).Adj i j}ᶜ := by
        ext a
        simp [hH]
      rw [this]
      exact (hG i j).compl
  rw [h]
  exact MeasurableSet.iUnion fun H => MeasurableSet.iUnion fun _ => h2 H

end Generic

/-! ### The multipole relation -/

/-- The multipole relation `MultipoleLinked M λ d e` is a closed condition on the pair of
dipoles, hence a Borel set. -/
theorem measurableSet_multipoleLinked (M lam : ℝ) :
    MeasurableSet {q : (ℂ × ℂ) × (ℂ × ℂ) | MultipoleLinked M lam q.1 q.2} := by
  unfold MultipoleLinked
  exact measurableSet_le (by fun_prop) (by fun_prop)

/-- The event `{c | c_i ↔ c_j}` (the event `𝓑_ij`) is measurable. -/
theorem measurableSet_setOf_multipoleLinked (M lam : ℝ) {ι : Type*} (i j : ι) :
    MeasurableSet {c : ι → ℂ × ℂ | MultipoleLinked M lam (c i) (c j)} :=
  have h : Measurable fun c : ι → ℂ × ℂ => (c i, c j) := by fun_prop
  (measurableSet_multipoleLinked M lam).preimage h

/-! ### The multipole graph and the multipole counts -/

section Graph

/-- The set `{c | i ↔_{σ_N} j}` (the event `𝖡_ij`) is measurable. -/
theorem measurableSet_setOf_multipoleLinked_stableMatching (M lam : ℝ) (i j : Fin N) :
    MeasurableSet {c : Fin N → ℂ × ℂ | MultipoleLinked M lam ((c i).1, (c (stableMatching c i)).2)
      ((c j).1, (c (stableMatching c j)).2)} := by
  refine measurableSet_setOf_apply_of_fibres (stableMatching (N := N))
    (fun σ c => MultipoleLinked M lam ((c i).1, (c (σ i)).2) ((c j).1, (c (σ j)).2))
    measurableSet_stableMatching_eq fun σ => ?_
  have h : Measurable fun c : Fin N → ℂ × ℂ =>
      (((c i).1, (c (σ i)).2), ((c j).1, (c (σ j)).2)) := by fun_prop
  exact (measurableSet_multipoleLinked M lam).preimage h

/-- The edge indicators of the multipole graph are measurable. -/
theorem measurableSet_setOf_adj_multipoleGraph (M lam : ℝ) (i j : Fin N) :
    MeasurableSet {c : Fin N → ℂ × ℂ | (multipoleGraph M lam c).Adj i j} := by
  simp only [multipoleGraph, SimpleGraph.fromRel_adj, Set.ofPred_and]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  rw [Set.ofPred_or]
  exact (measurableSet_setOf_multipoleLinked_stableMatching M lam i j).union
    (measurableSet_setOf_multipoleLinked_stableMatching M lam j i)

/-- Every graph property of the multipole graph defines a measurable set of configurations. -/
theorem measurableSet_setOf_multipoleGraph (M lam : ℝ) (P : SimpleGraph (Fin N) → Prop) :
    MeasurableSet {c : Fin N → ℂ × ℂ | P (multipoleGraph M lam c)} :=
  measurableSet_setOf_graph (multipoleGraph M lam) (measurableSet_setOf_adj_multipoleGraph M lam) P

/-- `{c | 𝒩_k = m}` is measurable: the number of multipoles of size `k` is a random variable. -/
theorem measurableSet_multipoleCount_eq (M lam : ℝ) (k m : ℕ) :
    MeasurableSet {c : Fin N → ℂ × ℂ | multipoleCount M lam c k = m} :=
  measurableSet_setOf_multipoleGraph M lam
    (fun G => Nat.card {C : G.ConnectedComponent // Nat.card C.supp = k} = m)

theorem measurable_multipoleCount (M lam : ℝ) (k : ℕ) :
    Measurable fun c : Fin N → ℂ × ℂ => multipoleCount M lam c k :=
  measurable_to_countable' fun m => measurableSet_multipoleCount_eq M lam k m

end Graph

/-! ### The weights of a pair of dipoles -/

open scoped Classical in
/-- The Boltzmann weight `e^{-β v_ij} 𝟙_{𝒜_ij}` of a pair of dipoles `d = (x_i, y_i)`,
`e = (x_j, y_j)` with `i < j`, which is the factor of the integrands of `dipoleActivity`,
`multipolePartitionFunction` and `hierarchicalModel`. -/
noncomputable def stablePairWeight (χ : ℂ → ℝ) (β lam : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if IsStableDipolePair d e then Real.exp (-β * dipoleInteraction χ lam d e) else 0

open scoped Classical in
/-- The factor `e^{-β v_ij} 𝟙_{𝓑_ij^c}` of the integrand of `multipoleActivity`. -/
noncomputable def unlinkedPairWeight (χ : ℂ → ℝ) (β lam M : ℝ) (d e : ℂ × ℂ) : ℝ :=
  if MultipoleLinked M lam d e then 0 else Real.exp (-β * dipoleInteraction χ lam d e)

theorem measurable_stablePairWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => stablePairWeight χ β lam q.1 q.2 := by
  have h := measurable_dipoleInteraction hχ hlam
  unfold stablePairWeight
  exact Measurable.ite measurableSet_isStableDipolePair (by fun_prop) measurable_const

theorem measurable_unlinkedPairWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) :
    Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) => unlinkedPairWeight χ β lam M q.1 q.2 := by
  have h := measurable_dipoleInteraction hχ hlam
  unfold unlinkedPairWeight
  exact Measurable.ite (measurableSet_multipoleLinked M lam) measurable_const (by fun_prop)

theorem measurable_stablePairWeight_apply (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    {ι : Type*} (i j : ι) :
    Measurable fun c : ι → ℂ × ℂ => stablePairWeight χ β lam (c i) (c j) := by
  have h := measurable_stablePairWeight hχ hlam β
  fun_prop

theorem measurable_unlinkedPairWeight_apply (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    {ι : Type*} (i j : ι) :
    Measurable fun c : ι → ℂ × ℂ => unlinkedPairWeight χ β lam M (c i) (c j) := by
  have h := measurable_unlinkedPairWeight hχ hlam β M
  fun_prop

theorem stablePairWeight_nonneg (χ : ℂ → ℝ) (β lam : ℝ) (d e : ℂ × ℂ) :
    0 ≤ stablePairWeight χ β lam d e := by
  unfold stablePairWeight
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem unlinkedPairWeight_nonneg (χ : ℂ → ℝ) (β lam M : ℝ) (d e : ℂ × ℂ) :
    0 ≤ unlinkedPairWeight χ β lam M d e := by
  unfold unlinkedPairWeight
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem stablePairWeight_pos {χ : ℂ → ℝ} {β lam : ℝ} {d e : ℂ × ℂ} (h : IsStableDipolePair d e) :
    0 < stablePairWeight χ β lam d e := by
  unfold stablePairWeight
  simp only [h, ite_true]
  exact Real.exp_pos _

/-- On the square `Λ²` the pair interaction `v_ij` is bounded: the weights of a pair of dipoles
are bounded by a constant `W ≥ 1`. -/
theorem exists_pairWeight_bound (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ) (N : ℕ) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ d ∈ box N ×ˢ box N, ∀ e ∈ box N ×ˢ box N,
      stablePairWeight χ β lam d e ≤ W ∧ unlinkedPairWeight χ β lam M d e ≤ W := by
  have hc := (continuous_dipoleInteraction hχ hlam).continuousOn
    (s := (box N ×ˢ box N) ×ˢ (box N ×ˢ box N))
  obtain ⟨B, hB⟩ := ((isCompact_box_prod N).prod (isCompact_box_prod N)).exists_bound_of_continuousOn hc
  refine ⟨Real.exp (|β| * |B|), ?_, fun d hd e he => ?_⟩
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  · have hv : |dipoleInteraction χ lam d e| ≤ |B| := by
      have := hB (d, e) ⟨hd, he⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self B)
    have hexp : Real.exp (-β * dipoleInteraction χ lam d e) ≤ Real.exp (|β| * |B|) := by
      refine Real.exp_le_exp.2 ?_
      calc -β * dipoleInteraction χ lam d e ≤ |-β * dipoleInteraction χ lam d e| := le_abs_self _
        _ = |β| * |dipoleInteraction χ lam d e| := by rw [abs_mul, abs_neg]
        _ ≤ |β| * |B| := by gcongr
    have hW : 0 ≤ Real.exp (|β| * |B|) := (Real.exp_pos _).le
    constructor
    · unfold stablePairWeight
      split_ifs
      · exact hexp
      · exact hW
    · unfold unlinkedPairWeight
      split_ifs
      · exact hW
      · exact hexp

/-! ### The integrands -/

/-- A product of `n × n` factors of absolute value at most `W` has absolute value at most
`W ^ (n * n)`. -/
theorem abs_prod_prod_le {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) {W : ℝ}
    (hf : ∀ i j, |f i j| ≤ W) : |∏ i, ∏ j, f i j| ≤ W ^ (Fintype.card ι * Fintype.card ι) := by
  rw [Finset.abs_prod]
  calc ∏ i, |∏ j, f i j| = ∏ i, ∏ j, |f i j| := by simp only [Finset.abs_prod]
    _ ≤ ∏ _i : ι, ∏ _j : ι, W :=
      Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
        fun i _ => Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hf i j
    _ = W ^ (Fintype.card ι * Fintype.card ι) := by
      simp [Finset.prod_const, pow_mul]

/-- Integrability of a measurable function that is bounded on the configurations all of whose
dipoles lie in `Λ²`, against the finite power of the dipole measure. -/
theorem integrable_pi_dipoleMeasure_of_bound (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) {ι : Type*} [Fintype ι] {f : (ι → ℂ × ℂ) → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ c : ι → ℂ × ℂ, (∀ i, c i ∈ box N ×ˢ box N) → |f c| ≤ B) :
    Integrable f (Measure.pi fun _ : ι => dipoleMeasure χ N β lam) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  refine Integrable.of_bound hf.aestronglyMeasurable B ?_
  filter_upwards [ae_pi_dipoleMeasure_mem_box hχ hlam β hN (ι := ι)] with c hc
  rw [Real.norm_eq_abs]
  exact hB c hc

section DipoleActivity

variable {V : Finset ℕ}

open scoped Classical in
/-- The integrand of `dipoleActivity` for the edge set `E`:
`∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝒜_ij} - 1)` (Definition 2.5). -/
noncomputable def dipoleActivityIntegrand (χ : ℂ → ℝ) (β lam : ℝ) (E : SimpleGraph V)
    (c : V → ℂ × ℂ) : ℝ :=
  ∏ i : V, ∏ j : V,
    if i < j ∧ E.Adj i j then stablePairWeight χ β lam (c i) (c j) - 1 else 1

open scoped Classical in
/-- `dipoleActivity` unfolded: the sum over connected edge sets of integrals of
`dipoleActivityIntegrand`. -/
theorem dipoleActivity_eq_sum (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (V : Finset ℕ) :
    dipoleActivity χ N β lam V =
      ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
          (fun E => E.Connected ∧ E.edgeSet.Nonempty),
        ∫ c : V → ℂ × ℂ, dipoleActivityIntegrand χ β lam E c
          ∂Measure.pi fun _ : V => dipoleMeasure χ N β lam := rfl

theorem measurable_dipoleActivityIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (E : SimpleGraph V) : Measurable (dipoleActivityIntegrand χ β lam E) := by
  unfold dipoleActivityIntegrand
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases h : i < j ∧ E.Adj i j
  · simp only [h, and_self, ite_true]
    exact (measurable_stablePairWeight_apply hχ hlam β i j).sub_const 1
  · simp only [h, ite_false]
    exact measurable_const

/-- The integrand of `dipoleActivity` is bounded on configurations with all dipoles in `Λ²`. -/
theorem exists_bound_dipoleActivityIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (N : ℕ) (E : SimpleGraph V) :
    ∃ B : ℝ, ∀ c : V → ℂ × ℂ, (∀ i, c i ∈ box N ×ˢ box N) →
      |dipoleActivityIntegrand χ β lam E c| ≤ B := by
  obtain ⟨W, hW1, hW⟩ := exists_pairWeight_bound hχ hlam β 0 N
  refine ⟨W ^ (Fintype.card V * Fintype.card V), fun c hc => ?_⟩
  unfold dipoleActivityIntegrand
  refine abs_prod_prod_le _ fun i j => ?_
  by_cases h : i < j ∧ E.Adj i j
  · simp only [h, and_self, ite_true]
    have h1 := (hW _ (hc i) _ (hc j)).1
    have h0 := stablePairWeight_nonneg χ β lam (c i) (c j)
    rw [abs_le]
    constructor <;> linarith
  · simp only [h, ite_false, abs_one]
    exact hW1

theorem integrable_dipoleActivityIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) (E : SimpleGraph V) :
    Integrable (dipoleActivityIntegrand χ β lam E)
      (Measure.pi fun _ : V => dipoleMeasure χ N β lam) := by
  obtain ⟨B, hB⟩ := exists_bound_dipoleActivityIntegrand hχ hlam β N E
  exact integrable_pi_dipoleMeasure_of_bound hχ hlam β hN
    (measurable_dipoleActivityIntegrand hχ hlam β E) hB

end DipoleActivity

/-- Graph properties of `fromRel (c_i ↔ c_j)` define measurable sets of configurations. -/
theorem measurableSet_setOf_fromRel_multipoleLinked (M lam : ℝ) {ι : Type*} [Finite ι]
    (P : SimpleGraph ι → Prop) :
    MeasurableSet {c : ι → ℂ × ℂ |
      P (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j))} := by
  refine measurableSet_setOf_graph
    (fun c : ι → ℂ × ℂ => SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j))
    (fun i j => ?_) P
  simp only [SimpleGraph.fromRel_adj, Set.ofPred_and, Set.ofPred_or]
  exact MeasurableSet.inter (MeasurableSet.const _)
    ((measurableSet_setOf_multipoleLinked M lam i j).union
      (measurableSet_setOf_multipoleLinked M lam j i))

section MultipolePartitionFunction

variable {S : Finset ℕ}

open scoped Classical in
/-- The integrand of `multipolePartitionFunction`:
`𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` (eq. (2.41)). -/
noncomputable def multipolePartitionFunctionIntegrand (χ : ℂ → ℝ) (β lam M : ℝ)
    (c : S → ℂ × ℂ) : ℝ :=
  (if (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected
      then 1 else 0) *
    ∏ i : S, ∏ j : S, if i < j then stablePairWeight χ β lam (c i) (c j) else 1

/-- `multipolePartitionFunction` unfolded: the integral of `multipolePartitionFunctionIntegrand`
against the `|S|`-fold power of the dipole measure. -/
theorem multipolePartitionFunction_eq_integral (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (S : Finset ℕ) :
    multipolePartitionFunction χ N β lam M S =
      ∫ c : S → ℂ × ℂ, multipolePartitionFunctionIntegrand χ β lam M c
        ∂Measure.pi fun _ : S => dipoleMeasure χ N β lam := rfl

theorem multipolePartitionFunctionIntegrand_nonneg (χ : ℂ → ℝ) (β lam M : ℝ)
    (c : S → ℂ × ℂ) : 0 ≤ multipolePartitionFunctionIntegrand χ β lam M c := by
  unfold multipolePartitionFunctionIntegrand
  refine mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => ?_)
  split_ifs
  · exact stablePairWeight_nonneg χ β lam _ _
  · exact zero_le_one

theorem measurable_multipolePartitionFunctionIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β M : ℝ) : Measurable (multipolePartitionFunctionIntegrand (S := S) χ β lam M) := by
  unfold multipolePartitionFunctionIntegrand
  refine Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam (fun G => G.Connected))
    measurable_const measurable_const) ?_
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases h : i < j
  · simp only [h, ite_true]
    exact measurable_stablePairWeight_apply hχ hlam β i j
  · simp only [h, ite_false]
    exact measurable_const

/-- The integrand of `multipolePartitionFunction` is bounded on configurations with all dipoles
in `Λ²`. -/
theorem exists_bound_multipolePartitionFunctionIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β M : ℝ) (N : ℕ) :
    ∃ B : ℝ, ∀ c : S → ℂ × ℂ, (∀ i, c i ∈ box N ×ˢ box N) →
      |multipolePartitionFunctionIntegrand χ β lam M c| ≤ B := by
  obtain ⟨W, hW1, hW⟩ := exists_pairWeight_bound hχ hlam β M N
  refine ⟨W ^ (Fintype.card S * Fintype.card S), fun c hc => ?_⟩
  unfold multipolePartitionFunctionIntegrand
  rw [abs_mul]
  refine (mul_le_mul (b := (1 : ℝ)) ?_ (abs_prod_prod_le _ fun i j => ?_) (abs_nonneg _)
    zero_le_one).trans_eq (one_mul _)
  · split_ifs <;> simp
  · by_cases h : i < j
    · simp only [h, ite_true]
      have h1 := (hW _ (hc i) _ (hc j)).1
      have h0 := stablePairWeight_nonneg χ β lam (c i) (c j)
      rw [abs_of_nonneg h0]
      exact h1
    · simp only [h, ite_false, abs_one]
      exact hW1

theorem integrable_multipolePartitionFunctionIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β M : ℝ) (hN : 1 ≤ N) :
    Integrable (multipolePartitionFunctionIntegrand (S := S) χ β lam M)
      (Measure.pi fun _ : S => dipoleMeasure χ N β lam) := by
  obtain ⟨B, hB⟩ := exists_bound_multipolePartitionFunctionIntegrand (S := S) hχ hlam β M N
  exact integrable_pi_dipoleMeasure_of_bound hχ hlam β hN
    (measurable_multipolePartitionFunctionIntegrand hχ hlam β M) hB

/-- `𝖬_{β,λ}(S) ≥ 0`. -/
theorem multipolePartitionFunction_nonneg (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (S : Finset ℕ) :
    0 ≤ multipolePartitionFunction χ N β lam M S :=
  integral_nonneg fun c => multipolePartitionFunctionIntegrand_nonneg χ β lam M c

end MultipolePartitionFunction

section Hierarchical

variable {X : Finset (Finset ℕ)}

open scoped Classical in
/-- The weight `𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}` of the block `S ∈ X` in the density of
`hierarchicalModel` (eq. (2.42)), as a function of a
configuration of all the dipoles `V_X = ⋃_{S ∈ X} S`. -/
noncomputable def hierarchicalBlockWeight (χ : ℂ → ℝ) (β lam M : ℝ) (X : Finset (Finset ℕ))
    (S : Finset ℕ) (c : X.biUnion id → ℂ × ℂ) : ℝ :=
  (if ((SimpleGraph.fromRel fun i j : X.biUnion id =>
        MultipoleLinked M lam (c i) (c j)).induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected
      then 1 else 0) *
    ∏ i : X.biUnion id, ∏ j : X.biUnion id,
      if (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j then stablePairWeight χ β lam (c i) (c j) else 1

open scoped Classical in
/-- The density of `hierarchicalModel` with respect to the product of dipole measures:
`∏_{S ∈ X} 𝖬(S)⁻¹ 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v_ij} 𝟙_{𝒜_ij}`. -/
noncomputable def hierarchicalModelDensity (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) (c : X.biUnion id → ℂ × ℂ) : ℝ≥0∞ :=
  ∏ S ∈ X, ENNReal.ofReal ((multipolePartitionFunction χ N β lam M S)⁻¹ *
    hierarchicalBlockWeight χ β lam M X S c)

/-- `hierarchicalModel` is the measure with density `hierarchicalModelDensity` with respect to
the product of the dipole measures. -/
theorem hierarchicalModel_eq (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (X : Finset (Finset ℕ)) :
    hierarchicalModel χ N β lam M X =
      (Measure.pi fun _ : X.biUnion id => dipoleMeasure χ N β lam).withDensity
        (hierarchicalModelDensity χ N β lam M X) := rfl

theorem hierarchicalBlockWeight_nonneg (χ : ℂ → ℝ) (β lam M : ℝ) (X : Finset (Finset ℕ))
    (S : Finset ℕ) (c : X.biUnion id → ℂ × ℂ) : 0 ≤ hierarchicalBlockWeight χ β lam M X S c := by
  unfold hierarchicalBlockWeight
  refine mul_nonneg (by split_ifs <;> norm_num) (Finset.prod_nonneg fun i _ =>
    Finset.prod_nonneg fun j _ => ?_)
  split_ifs
  · exact stablePairWeight_nonneg χ β lam _ _
  · exact zero_le_one

theorem measurable_hierarchicalBlockWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    (S : Finset ℕ) : Measurable (hierarchicalBlockWeight χ β lam M X S) := by
  unfold hierarchicalBlockWeight
  refine Measurable.mul (Measurable.ite
    (measurableSet_setOf_fromRel_multipoleLinked M lam
      (fun G => (G.induce {i : X.biUnion id | (i : ℕ) ∈ S}).Connected))
    measurable_const measurable_const) ?_
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases h : (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j
  · simp only [h, and_self, ite_true]
    exact measurable_stablePairWeight_apply hχ hlam β i j
  · simp only [h, ite_false]
    exact measurable_const

theorem measurable_hierarchicalModelDensity (hχ : IsMollifier χ) (hlam : 0 < lam) (N : ℕ)
    (β M : ℝ) : Measurable (hierarchicalModelDensity χ N β lam M X) := by
  unfold hierarchicalModelDensity
  exact Finset.measurable_prod _ fun S _ => ENNReal.measurable_ofReal.comp
    ((measurable_hierarchicalBlockWeight hχ hlam β M S).const_mul _)

/-- The block weights are bounded on configurations with all dipoles in `Λ²`. -/
theorem exists_bound_hierarchicalBlockWeight (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    (N : ℕ) (X : Finset (Finset ℕ)) :
    ∃ B : ℝ, ∀ (S : Finset ℕ) (c : X.biUnion id → ℂ × ℂ), (∀ i, c i ∈ box N ×ˢ box N) →
      |hierarchicalBlockWeight χ β lam M X S c| ≤ B := by
  obtain ⟨W, hW1, hW⟩ := exists_pairWeight_bound hχ hlam β M N
  refine ⟨W ^ (Fintype.card (X.biUnion id) * Fintype.card (X.biUnion id)), fun S c hc => ?_⟩
  unfold hierarchicalBlockWeight
  rw [abs_mul]
  refine (mul_le_mul (b := (1 : ℝ)) ?_ (abs_prod_prod_le _ fun i j => ?_) (abs_nonneg _)
    zero_le_one).trans_eq (one_mul _)
  · split_ifs <;> simp
  · by_cases h : (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S ∧ i < j
    · simp only [h, and_self, ite_true]
      have h1 := (hW _ (hc i) _ (hc j)).1
      have h0 := stablePairWeight_nonneg χ β lam (c i) (c j)
      rw [abs_of_nonneg h0]
      exact h1
    · simp only [h, ite_false, abs_one]
      exact hW1

/-- `hierarchicalModel` is a finite measure (for `N ≥ 1`, `λ > 0`): its density with respect to
the product of the dipole measures is bounded on the support of the latter. -/
theorem isFiniteMeasure_hierarchicalModel (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    (hN : 1 ≤ N) (X : Finset (Finset ℕ)) : IsFiniteMeasure (hierarchicalModel χ N β lam M X) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  obtain ⟨B, hB⟩ := exists_bound_hierarchicalBlockWeight hχ hlam β M N X
  rw [hierarchicalModel_eq]
  refine isFiniteMeasure_withDensity ?_
  have hle : ∀ᵐ c ∂(Measure.pi fun _ : X.biUnion id => dipoleMeasure χ N β lam),
      hierarchicalModelDensity χ N β lam M X c ≤
        ∏ S ∈ X, ENNReal.ofReal (|(multipolePartitionFunction χ N β lam M S)⁻¹| * B) := by
    filter_upwards [ae_pi_dipoleMeasure_mem_box hχ hlam β hN (ι := X.biUnion id)] with c hc
    unfold hierarchicalModelDensity
    refine Finset.prod_le_prod fun S _ => ENNReal.ofReal_le_ofReal ?_
    calc (multipolePartitionFunction χ N β lam M S)⁻¹ * hierarchicalBlockWeight χ β lam M X S c
        ≤ |(multipolePartitionFunction χ N β lam M S)⁻¹ *
            hierarchicalBlockWeight χ β lam M X S c| := le_abs_self _
      _ = |(multipolePartitionFunction χ N β lam M S)⁻¹| *
            |hierarchicalBlockWeight χ β lam M X S c| := abs_mul _ _
      _ ≤ |(multipolePartitionFunction χ N β lam M S)⁻¹| * B := by
        gcongr
        exact hB S c hc
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae hle) ?_)
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.prod_lt_top fun S _ => ENNReal.ofReal_lt_top

theorem hierarchicalModel_absolutelyContinuous (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    (X : Finset (Finset ℕ)) :
    hierarchicalModel χ N β lam M X ≪
      Measure.pi fun _ : X.biUnion id => dipoleMeasure χ N β lam :=
  withDensity_absolutelyContinuous _ _

open scoped Classical in
/-- The integrand of `multipoleActivity` for the edge set `E`:
`∏_{ij ∈ E} (e^{-β v_ij} 𝟙_{𝓑_ij^c} - 1)` (Definition 2.13). -/
noncomputable def multipoleActivityIntegrand (χ : ℂ → ℝ) (β lam M : ℝ)
    (E : SimpleGraph (X.biUnion id)) (c : X.biUnion id → ℂ × ℂ) : ℝ :=
  ∏ i : X.biUnion id, ∏ j : X.biUnion id,
    if i < j ∧ E.Adj i j then unlinkedPairWeight χ β lam M (c i) (c j) - 1 else 1

open scoped Classical in
/-- `multipoleActivity` unfolded: the sum over the admissible edge sets of integrals of
`multipoleActivityIntegrand` against `hierarchicalModel`. -/
theorem multipoleActivity_eq_sum (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ) (X : Finset (Finset ℕ)) :
    multipoleActivity χ N β lam M X =
      ∑ E ∈ (Finset.univ : Finset (SimpleGraph (X.biUnion id))).filter (fun E =>
          (∀ i j : X.biUnion id, E.Adj i j →
              ∃ S ∈ X, ∃ S' ∈ X, S ≠ S' ∧ (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S') ∧
            E.edgeSet.Nonempty ∧
            (E ⊔ SimpleGraph.fromRel fun i j : X.biUnion id =>
              ∃ S ∈ X, (i : ℕ) ∈ S ∧ (j : ℕ) ∈ S).Connected),
        ∫ c : X.biUnion id → ℂ × ℂ, multipoleActivityIntegrand χ β lam M E c
          ∂hierarchicalModel χ N β lam M X := rfl

theorem measurable_multipoleActivityIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    (E : SimpleGraph (X.biUnion id)) : Measurable (multipoleActivityIntegrand χ β lam M E) := by
  unfold multipoleActivityIntegrand
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
  by_cases h : i < j ∧ E.Adj i j
  · simp only [h, and_self, ite_true]
    exact (measurable_unlinkedPairWeight_apply hχ hlam β M i j).sub_const 1
  · simp only [h, ite_false]
    exact measurable_const

/-- The integrand of `multipoleActivity` is bounded on configurations with all dipoles in
`Λ²`. -/
theorem exists_bound_multipoleActivityIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam)
    (β M : ℝ) (N : ℕ) (E : SimpleGraph (X.biUnion id)) :
    ∃ B : ℝ, ∀ c : X.biUnion id → ℂ × ℂ, (∀ i, c i ∈ box N ×ˢ box N) →
      |multipoleActivityIntegrand χ β lam M E c| ≤ B := by
  obtain ⟨W, hW1, hW⟩ := exists_pairWeight_bound hχ hlam β M N
  refine ⟨W ^ (Fintype.card (X.biUnion id) * Fintype.card (X.biUnion id)), fun c hc => ?_⟩
  unfold multipoleActivityIntegrand
  refine abs_prod_prod_le _ fun i j => ?_
  by_cases h : i < j ∧ E.Adj i j
  · simp only [h, and_self, ite_true]
    have h1 := (hW _ (hc i) _ (hc j)).2
    have h0 := unlinkedPairWeight_nonneg χ β lam M (c i) (c j)
    rw [abs_le]
    constructor <;> linarith
  · simp only [h, ite_false, abs_one]
    exact hW1

/-- The integrand of `multipoleActivity` is integrable against `hierarchicalModel` (for
`N ≥ 1`, `λ > 0`). -/
theorem integrable_multipoleActivityIntegrand (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    (hN : 1 ≤ N) (E : SimpleGraph (X.biUnion id)) :
    Integrable (multipoleActivityIntegrand χ β lam M E) (hierarchicalModel χ N β lam M X) := by
  have := isFiniteMeasure_hierarchicalModel hχ hlam β M hN X
  obtain ⟨B, hB⟩ := exists_bound_multipoleActivityIntegrand hχ hlam β M N E
  refine Integrable.of_bound (measurable_multipoleActivityIntegrand hχ hlam β M E).aestronglyMeasurable B ?_
  have hae := (hierarchicalModel_absolutelyContinuous χ N β lam M X).ae_le
    (ae_pi_dipoleMeasure_mem_box hχ hlam β hN (ι := X.biUnion id))
  filter_upwards [hae] with c hc
  rw [Real.norm_eq_abs]
  exact hB c hc

end Hierarchical

/-! ### Elementary values -/

/-- A graph on a subsingleton vertex type has no edge. -/
theorem not_edgeSet_nonempty_of_subsingleton {V : Type*} [Subsingleton V] (E : SimpleGraph V) :
    ¬ E.edgeSet.Nonempty := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
    exact E.ne_of_adj he (Subsingleton.elim a b)

open scoped Classical in
/-- `K^dip(V) = 0` if `|V| ≤ 1`: there is no connected graph with an edge on at most one
vertex. -/
theorem dipoleActivity_eq_zero_of_card_le_one (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) {V : Finset ℕ}
    (hV : V.card ≤ 1) : dipoleActivity χ N β lam V = 0 := by
  have hsub : Subsingleton V := Finset.card_le_one_iff_subsingleton_coe.1 hV
  unfold dipoleActivity
  refine Finset.sum_eq_zero fun E hE => ?_
  exact absurd (Finset.mem_filter.1 hE).2.2 (not_edgeSet_nonempty_of_subsingleton E)

open scoped Classical in
/-- `𝖪^mult(X) = 0` if `|X| ≤ 1`: there is no edge between two distinct blocks. -/
theorem multipoleActivity_eq_zero_of_card_le_one (χ : ℂ → ℝ) (N : ℕ) (β lam M : ℝ)
    {X : Finset (Finset ℕ)} (hX : X.card ≤ 1) : multipoleActivity χ N β lam M X = 0 := by
  unfold multipoleActivity
  refine Finset.sum_eq_zero fun E hE => ?_
  obtain ⟨-, hadj, hne, -⟩ := Finset.mem_filter.1 hE
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | h a b =>
    obtain ⟨S, hS, S', hS', hSS', -⟩ := hadj a b he
    exact absurd (Finset.card_le_one.1 hX S hS S' hS') hSS'

/-- `𝖬_{β,λ}({i}) = 1`. -/
theorem multipolePartitionFunction_singleton (hχ : IsMollifier χ) (hlam : 0 < lam) (β M : ℝ)
    (hN : 1 ≤ N) (i : ℕ) : multipolePartitionFunction χ N β lam M {i} = 1 := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  have hsub : Subsingleton ({i} : Finset ℕ) :=
    Finset.card_le_one_iff_subsingleton_coe.1 (by simp)
  rw [multipolePartitionFunction_eq_integral]
  have h1 : ∀ c : ({i} : Finset ℕ) → ℂ × ℂ,
      multipolePartitionFunctionIntegrand χ β lam M c = 1 := by
    intro c
    unfold multipolePartitionFunctionIntegrand
    have hconn : (SimpleGraph.fromRel fun a b : ({i} : Finset ℕ) =>
        MultipoleLinked M lam (c a) (c b)).Connected :=
      (SimpleGraph.connected_iff _).2 ⟨fun u v => by rw [Subsingleton.elim u v], ⟨⟨i, by simp⟩⟩⟩
    simp only [hconn, ite_true, one_mul]
    refine Finset.prod_eq_one fun a _ => Finset.prod_eq_one fun b _ => ?_
    simp [Subsingleton.elim a b]
  simp [h1]

/-! ### Positivity of `𝖬_{β,λ}(S)` -/

section Positivity

/-- A disc whose centre is at distance at least `ε` from the sides of the box lies in the
box. -/
theorem ball_subset_box {z : ℂ} {ε : ℝ} (hre : ε ≤ z.re) (hre' : z.re + ε ≤ Real.sqrt N)
    (him : ε ≤ z.im) (him' : z.im + ε ≤ Real.sqrt N) : Metric.ball z ε ⊆ box N := by
  intro w hw
  have hd : ‖w - z‖ < ε := by rwa [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : |w.re - z.re| < ε :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w - z)) hd
  have h2 : |w.im - z.im| < ε :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - z)) hd
  rw [abs_lt] at h1 h2
  rw [box, Complex.mem_reProdIm]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A set of positive volume inside `Λ²` has positive mass for the dipole measure. -/
theorem dipoleMeasure_pos_of_subset (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) {A : Set (ℂ × ℂ)} (hA : A ⊆ box N ×ˢ box N) (hvol : 0 < volume A) :
    0 < dipoleMeasure χ N β lam A := by
  have hpos := natCast_mul_dipoleNormalization_pos hχ hlam β hN
  have hac : (volume.restrict (box N ×ˢ box N)) ≪ dipoleMeasure χ N β lam := by
    unfold dipoleMeasure
    have hc : Continuous fun p : ℂ × ℂ => ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ *
        Real.exp (β * smearedKernel χ lam (p.1 - p.2)) :=
      continuous_const.mul (continuous_exp_smearedKernel_sub hχ hlam β)
    refine withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp hc.measurable).aemeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    exact (ENNReal.ofReal_pos.2 (mul_pos (inv_pos.2 hpos) (Real.exp_pos _))).ne'
  by_contra hcon
  have h0 : dipoleMeasure χ N β lam A = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hcon)
  have h1 := hac h0
  rw [Measure.restrict_apply' (measurableSet_box_prod N), Set.inter_eq_left.2 hA] at h1
  exact hvol.ne' h1

/-- A product of small discs inside `Λ²` has positive mass for the `ι`-fold power of the dipole
measure. -/
theorem pi_dipoleMeasure_cluster_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hN : 1 ≤ N) {ι : Type*} [Fintype ι] (z : ι → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ i, Metric.ball (z i) ε ⊆ box N) :
    0 < Measure.pi (fun _ : ι => dipoleMeasure χ N β lam)
      (Set.univ.pi fun i => Metric.ball (z i) ε ×ˢ Metric.ball (z i) ε) := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [Measure.pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  refine (dipoleMeasure_pos_of_subset hχ hlam β hN (Set.prod_mono (hball i) (hball i)) ?_).ne'
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_pos (Metric.measure_ball_pos _ _ hε).ne' (Metric.measure_ball_pos _ _ hε).ne'

/-- Two dipoles `(x, y)`, `(x', y')` with `x, y` within `ε` of `z` and `x', y'` within `ε` of
`z'`, where `‖z - z'‖ ≥ 4 ε`, form a stable pair. -/
theorem isStableDipolePair_of_near {d e : ℂ × ℂ} {z z' : ℂ} {ε : ℝ}
    (hd1 : ‖d.1 - z‖ < ε) (hd2 : ‖d.2 - z‖ < ε) (he1 : ‖e.1 - z'‖ < ε) (he2 : ‖e.2 - z'‖ < ε)
    (hz : 4 * ε ≤ ‖z - z'‖) : IsStableDipolePair d e := by
  have hr : ‖d.1 - d.2‖ < 2 * ε := by
    calc ‖d.1 - d.2‖ = ‖(d.1 - z) - (d.2 - z)‖ := by congr 1; ring
      _ ≤ ‖d.1 - z‖ + ‖d.2 - z‖ := norm_sub_le _ _
      _ < 2 * ε := by linarith
  have hc1 : 2 * ε < ‖d.1 - e.2‖ := by
    have : ‖z - z'‖ ≤ ‖d.1 - z‖ + ‖d.1 - e.2‖ + ‖e.2 - z'‖ := by
      calc ‖z - z'‖ = ‖-(d.1 - z) + (d.1 - e.2) + (e.2 - z')‖ := by congr 1; ring
        _ ≤ ‖-(d.1 - z) + (d.1 - e.2)‖ + ‖e.2 - z'‖ := norm_add_le _ _
        _ ≤ ‖-(d.1 - z)‖ + ‖d.1 - e.2‖ + ‖e.2 - z'‖ := by gcongr; exact norm_add_le _ _
        _ = ‖d.1 - z‖ + ‖d.1 - e.2‖ + ‖e.2 - z'‖ := by rw [norm_neg]
    linarith
  have hc2 : 2 * ε < ‖e.1 - d.2‖ := by
    have : ‖z - z'‖ ≤ ‖d.2 - z‖ + ‖e.1 - d.2‖ + ‖e.1 - z'‖ := by
      calc ‖z - z'‖ = ‖-(d.2 - z) + -(e.1 - d.2) + (e.1 - z')‖ := by congr 1; ring
        _ ≤ ‖-(d.2 - z) + -(e.1 - d.2)‖ + ‖e.1 - z'‖ := norm_add_le _ _
        _ ≤ ‖-(d.2 - z)‖ + ‖-(e.1 - d.2)‖ + ‖e.1 - z'‖ := by gcongr; exact norm_add_le _ _
        _ = ‖d.2 - z‖ + ‖e.1 - d.2‖ + ‖e.1 - z'‖ := by rw [norm_neg, norm_neg]
    linarith
  exact isStableDipolePair_of_lt ((min_le_left _ _).trans_lt (hr.trans hc1))
    ((min_le_left _ _).trans_lt (hr.trans hc2))

/-- Two dipoles near `z` and `z'`, with `‖z - z'‖ + 2 ε ≤ M λ`, are linked. -/
theorem multipoleLinked_of_near {d e : ℂ × ℂ} {z z' : ℂ} {ε M lam : ℝ} (hM : 0 < M)
    (hd1 : ‖d.1 - z‖ < ε) (he1 : ‖e.1 - z'‖ < ε) (hz : ‖z - z'‖ + 2 * ε ≤ M * lam) :
    MultipoleLinked M lam d e := by
  unfold MultipoleLinked
  have h1 : min (min ‖d.1 - e.1‖ ‖d.1 - e.2‖) (min ‖d.2 - e.1‖ ‖d.2 - e.2‖) ≤ ‖d.1 - e.1‖ :=
    (min_le_left _ _).trans (min_le_left _ _)
  have h2 : ‖d.1 - e.1‖ < M * lam := by
    have : ‖d.1 - e.1‖ ≤ ‖d.1 - z‖ + ‖z - z'‖ + ‖z' - e.1‖ := by
      calc ‖d.1 - e.1‖ = ‖(d.1 - z) + (z - z') + (z' - e.1)‖ := by congr 1; ring
        _ ≤ ‖(d.1 - z) + (z - z')‖ + ‖z' - e.1‖ := norm_add_le _ _
        _ ≤ ‖d.1 - z‖ + ‖z - z'‖ + ‖z' - e.1‖ := by gcongr; exact norm_add_le _ _
    rw [norm_sub_rev z' e.1] at this
    linarith
  have h3 : lam ≤ min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) :=
    le_min (le_max_right _ _) (le_max_right _ _)
  exact h1.trans (h2.le.trans (mul_le_mul_of_nonneg_left h3 hM.le))

/-- The distance between two points of the row `{ε (2 + 4 k) + 2 i ε}`. -/
theorem norm_clusterCentre_sub {ε : ℝ} (hε : 0 ≤ ε) (a b : ℕ) :
    ‖(⟨ε * (2 + 4 * a), 2 * ε⟩ : ℂ) - ⟨ε * (2 + 4 * b), 2 * ε⟩‖ = 4 * ε * |(a : ℝ) - b| := by
  have h : (⟨ε * (2 + 4 * a), 2 * ε⟩ : ℂ) - ⟨ε * (2 + 4 * b), 2 * ε⟩ =
      ((4 * ε * ((a : ℝ) - b) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re]
      ring
    · simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 4 * ε)]

/-- Existence of a cluster of `|S|` well-separated small discs inside `Λ`, with centres within
`M λ` of each other (up to the radius): the geometric input of the positivity of
`𝖬_{β,λ}(S)`. -/
theorem exists_cluster (hlam : 0 < lam) (hM : 0 < M) (hN : 1 ≤ N) (S : Finset ℕ) :
    ∃ (z : S → ℂ) (ε : ℝ), 0 < ε ∧ (∀ i, Metric.ball (z i) ε ⊆ box N) ∧
      (∀ i j, i ≠ j → 4 * ε ≤ ‖z i - z j‖) ∧ ∀ i j, ‖z i - z j‖ + 2 * ε ≤ M * lam := by
  set K : ℕ := S.sup id + 1 with hK
  have hKi : ∀ i : S, ((i : ℕ) : ℝ) + 1 ≤ K := fun i => by
    have : (i : ℕ) ≤ S.sup id := Finset.le_sup (f := id) i.2
    exact_mod_cast Nat.succ_le_succ this
  set m : ℝ := min (M * lam) 1 with hm
  have hm0 : 0 < m := lt_min (mul_pos hM hlam) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hm2 : m ≤ M * lam := min_le_left _ _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have ht : 0 < 4 * (K : ℝ) + 4 := by positivity
  set ε : ℝ := m / (4 * K + 4) with hε
  have hε0 : 0 < ε := div_pos hm0 ht
  have hεt : ε * (4 * K + 4) = m := div_mul_cancel₀ _ ht.ne'
  have hεK : 0 ≤ ε * K := mul_nonneg hε0.le hK0
  have hsqrt : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast hN)
  refine ⟨fun i => ⟨ε * (2 + 4 * (i : ℕ)), 2 * ε⟩, ε, hε0, fun i => ?_, fun i j hij => ?_,
    fun i j => ?_⟩
  · have h := mul_le_mul_of_nonneg_left (hKi i) hε0.le
    have hi0 : 0 ≤ ε * ((i : ℕ) : ℝ) := mul_nonneg hε0.le (Nat.cast_nonneg _)
    refine ball_subset_box ?_ ?_ ?_ ?_
    all_goals (dsimp only; linarith)
  · rw [norm_clusterCentre_sub hε0.le]
    have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
    have h1 : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]
        linarith
    exact le_mul_of_one_le_right (by positivity) h1
  · rw [norm_clusterCentre_sub hε0.le]
    have h1 : |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| ≤ K := by
      have := hKi i
      have := hKi j
      have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_le]
      constructor <;> linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4 * ε)
    linarith

/-- `𝖬_{β,λ}(S) > 0` for `S` nonempty, `M > 0`, `λ > 0` and `N ≥ 1`: on a set of positive
measure (a cluster of `|S|` well-separated tiny dipoles, all within `M λ` of each other) the
dipoles form stable pairs, are all linked to each other, and the integrand is positive. -/
theorem multipolePartitionFunction_pos (hχ : IsMollifier χ) (hlam : 0 < lam) (β : ℝ)
    (hM : 0 < M) (hN : 1 ≤ N) {S : Finset ℕ} (hS : S.Nonempty) :
    0 < multipolePartitionFunction χ N β lam M S := by
  obtain ⟨z, ε, hε, hball, hsep, hlink⟩ := exists_cluster (M := M) hlam hM hN S
  rw [multipolePartitionFunction_eq_integral,
    integral_pos_iff_support_of_nonneg
      (fun c => multipolePartitionFunctionIntegrand_nonneg χ β lam M c)
      (integrable_multipolePartitionFunctionIntegrand hχ hlam β M hN)]
  refine lt_of_lt_of_le (pi_dipoleMeasure_cluster_pos hχ hlam β hN z hε hball)
    (measure_mono fun c hc => ?_)
  rw [Set.mem_univ_pi] at hc
  have hc' : ∀ i, ‖(c i).1 - z i‖ < ε ∧ ‖(c i).2 - z i‖ < ε := fun i => by
    obtain ⟨h1, h2⟩ := hc i
    exact ⟨by rwa [Metric.mem_ball, dist_eq_norm] at h1, by rwa [Metric.mem_ball, dist_eq_norm] at h2⟩
  have hconn : (SimpleGraph.fromRel fun i j : S => MultipoleLinked M lam (c i) (c j)).Connected := by
    refine (SimpleGraph.connected_iff _).2 ⟨fun u v => ?_, ?_⟩
    · by_cases huv : u = v
      · rw [huv]
      · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromRel_adj _ _ _).2 ⟨huv, Or.inl
          (multipoleLinked_of_near hM (hc' u).1 (hc' v).1 (hlink u v))⟩)
    · obtain ⟨k, hk⟩ := hS
      exact ⟨⟨k, hk⟩⟩
  rw [Function.mem_support]
  refine ne_of_gt ?_
  unfold multipolePartitionFunctionIntegrand
  simp only [hconn, ite_true, one_mul]
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  by_cases h : i < j
  · simp only [h, ite_true]
    exact stablePairWeight_pos (isStableDipolePair_of_near (hc' i).1 (hc' i).2 (hc' j).1
      (hc' j).2 (hsep i j h.ne))
  · simp only [h, ite_false]
    exact one_pos

end Positivity

end MultipoleBKT

end
