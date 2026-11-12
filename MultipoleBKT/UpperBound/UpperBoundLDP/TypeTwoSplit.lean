/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.Measurable
public import MultipoleBKT.UpperBound.UpperBoundLDP.Split
public import MultipoleBKT.UpperBound.BadPointTypes.TypeThreeIntegral

/-!
# The splitting of the bad points of type 2 (eq. (5.132))

The paper: eq. (5.132): the partition function
of the bad points of type 2 is split according to the type-2 classes,

  `Z^{(2)}_{bad,n} ≤
    ∑_{τ : [n] → {0, 1, …, p}} Z^{(2,1)}_{bad,|τ⁻¹(0)|} ∏_{k=1}^{p} Z^{(2,2,k)}_{bad,|τ⁻¹(k)|}`

(`typeTwoPartitionFunction_le_sum`), where `τ(i) = 0` for the labels of `I^{2,1}_bad` and
`τ(i) = k` for those of `I^{2,2,k}_bad`. The paper writes the sum over the `(p+1)^{n}` labellings
as `(p(β)+1)^{N₂}` times a maximum of multinomial terms; here the sum is kept.

* On `{I^2_bad = [n]}` there is no bad point of type 1, so (off the null set of isosceles
  coincidences) every cluster of Definition 5.1 is a singleton; the classes of `I^{2,1}_bad` and of
  `I^{2,2,k}_bad` are unions of classes, so the sub-configurations on them have the same classes and
  counts (`typeTwoOneBad_comp_eq_univ`, `typeTwoTwoBad_comp_eq_univ`).
* The labellings `τ` cover `{I^2_bad = [n]}` by measurable sets
  (`MultipoleBKT.UpperBoundLDP.Measurable`);
  on each, the integrand is at most the product of the integrands of the classes (the matching
  constraints between different classes are dropped), and Tonelli along the labelling
  (`lintegral_prod_fiber_le`) concludes.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset TheoremTwo BadPointTypes UpperBound MultipoleIntegral
open scoped ENNReal

variable {n m : ℕ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-! ### Sub-configurations on a union of type-2 classes -/

section Locality

variable {Nₐ : ℕ} {d : Fin n → ℂ × ℂ}

/-- If every label is of type 2, there is no bad point of type 1. -/
theorem badPointsTypeOne_eq_empty_of_typeTwoBad (h : typeTwoBad Nₐ p₀ β lam M ε₀ d = univ) :
    badPointsTypeOne p₀ β lam ε₀ d = ∅ := by
  refine eq_empty_of_forall_notMem fun i hi => ?_
  have := ((mem_typeTwoBad_iff Nₐ).1 (h ▸ mem_univ i)).1
  exact (mem_sdiff.1 this).2 hi

/-- Without bad points of type 1, the sub-configuration on any set of labels has no bad point of
type 1 (for configurations without isosceles coincidences). -/
theorem badPointsTypeOne_comp_eq_empty (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hz : NoIsosceles (fun k => (d k).1))
    (hz' : NoIsosceles (fun k => (d k).2)) (hone : badPointsTypeOne p₀ β lam ε₀ d = ∅)
    (e : Fin m ↪o Fin n) : badPointsTypeOne p₀ β lam ε₀ (d ∘ e) = ∅ := by
  have hU : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e.toEmbedding) :=
    clusterUnion_of_split hq hh hz hz' (Or.inr (by rw [hone]; exact disjoint_empty_left _))
  refine eq_empty_of_forall_notMem fun a ha => ?_
  rw [mem_badPointsTypeOne_comp_iff e hU, hone] at ha
  exact notMem_empty _ ha

/-- On a union of classes, the classes of the sub-configuration have the same cardinalities. -/
theorem card_classOn_comp (e : Fin m ↪o Fin n)
    (hW : ∀ i ∈ univ.map e.toEmbedding,
      multipoleClassOn M lam d univ i ⊆ univ.map e.toEmbedding) (a : Fin m) :
    (multipoleClassOn M lam (d ∘ e) univ a).card = (multipoleClassOn M lam d univ (e a)).card := by
  have h := classOn_comp_map (d := d) (M := M) (lam := lam) e.toEmbedding univ a
  have hea : e a ∈ univ.map e.toEmbedding := mem_map_of_mem _ (mem_univ a)
  have h2 := classOn_of_union (subset_univ _) hW hea
  have h3 := congrArg Finset.card (h.trans h2)
  rw [card_map] at h3
  exact h3

/-- **The sub-configuration on the labels of `I^{2,1}_bad`**: if every label of `d` is of type 2
and `e` enumerates `I^{2,1}_bad(d)`, every label of `d ∘ e` is in `I^{2,1}_bad`. -/
theorem typeTwoOneBad_comp_eq_univ (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hz : NoIsosceles (fun k => (d k).1))
    (hz' : NoIsosceles (fun k => (d k).2)) (htwo : typeTwoBad Nₐ p₀ β lam M ε₀ d = univ)
    (e : Fin m ↪o Fin n) (hrange : univ.map e.toEmbedding = typeTwoOneBad p₀ β lam M ε₀ d) :
    typeTwoOneBad p₀ β lam M ε₀ (d ∘ e) = univ := by
  have hone := badPointsTypeOne_eq_empty_of_typeTwoBad htwo
  have hone' := badPointsTypeOne_comp_eq_empty hq hh hz hz' hone e
  have hmem : ∀ i, i ∈ typeTwoOneBad p₀ β lam M ε₀ d ↔
      pBeta p₀ β < (multipoleClassOn M lam d univ i).card := by
    intro i
    unfold typeTwoOneBad
    simp only [hone, sdiff_empty, mem_filter, mem_univ, true_and]
  have hW : ∀ i ∈ univ.map e.toEmbedding,
      multipoleClassOn M lam d univ i ⊆ univ.map e.toEmbedding := by
    intro i hi j hj
    rw [hrange, hmem] at hi ⊢
    rwa [classOn_eq_of_mem hj]
  refine eq_univ_of_forall fun a => ?_
  unfold typeTwoOneBad
  simp only [hone', sdiff_empty, mem_filter, mem_univ, true_and]
  rw [card_classOn_comp e hW a, ← hmem, ← hrange]
  exact mem_map_of_mem _ (mem_univ a)

/-- **The sub-configuration on the labels of `I^{2,2,k}_bad`**: if every label of `d` is of
type 2 and `e` enumerates `I^{2,2,k}_bad(d)`, every label of `d ∘ e` is in `I^{2,2,k}_bad`, with
the same ambient threshold. -/
theorem typeTwoTwoBad_comp_eq_univ (k : ℕ) (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hz : NoIsosceles (fun k => (d k).1))
    (hz' : NoIsosceles (fun k => (d k).2)) (htwo : typeTwoBad Nₐ p₀ β lam M ε₀ d = univ)
    (e : Fin m ↪o Fin n) (hrange : univ.map e.toEmbedding = typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d) :
    typeTwoTwoBad Nₐ k p₀ β lam M ε₀ (d ∘ e) = univ := by
  classical
  have hone := badPointsTypeOne_eq_empty_of_typeTwoBad htwo
  have hone' := badPointsTypeOne_comp_eq_empty hq hh hz hz' hone e
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Subsingleton.elim _ _
  -- the set `I^{2,2,k}_bad(d)` is nonempty, hence given by the class sizes
  have hne : (typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d).Nonempty := by
    rw [← hrange]
    exact ⟨e ⟨0, hm⟩, mem_map_of_mem _ (mem_univ _)⟩
  set S := univ.filter fun i => (multipoleClassOn M lam d univ i).card = k with hS
  have hdef : typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d =
      if ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (k - 1)) < (S.card : ℝ) then S else ∅ := by
    unfold typeTwoTwoBad
    simp only [hone, sdiff_empty, hS]
  have hcond : ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (k - 1)) < (S.card : ℝ) := by
    by_contra hc
    rw [hdef, ite_eq_right hc] at hne
    exact not_nonempty_empty hne
  have hset : typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = S := by rw [hdef, ite_eq_left hcond]
  have hW : ∀ i ∈ univ.map e.toEmbedding,
      multipoleClassOn M lam d univ i ⊆ univ.map e.toEmbedding := by
    intro i hi j hj
    rw [hrange, hset, hS, mem_filter] at hi ⊢
    exact ⟨mem_univ j, by rw [classOn_eq_of_mem hj]; exact hi.2⟩
  have hcard : ∀ a, (multipoleClassOn M lam (d ∘ e) univ a).card = k := by
    intro a
    rw [card_classOn_comp e hW a]
    have : e a ∈ S := by rw [← hset, ← hrange]; exact mem_map_of_mem _ (mem_univ a)
    exact (mem_filter.1 this).2
  have hfilt : (univ.filter fun a => (multipoleClassOn M lam (d ∘ e) univ a).card = k) = univ :=
    filter_true_of_mem fun a _ => hcard a
  have hcardS : S.card = m := by
    rw [← hset, ← hrange, card_map, card_univ, Fintype.card_fin]
  unfold typeTwoTwoBad
  simp only [hone', sdiff_empty, hfilt, card_univ, Fintype.card_fin]
  rw [ite_eq_left (by rw [← hcardS]; exact hcond)]

end Locality

/-! ### The integrands of the classes -/

section Integrands

variable (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ : ℕ)

open scoped Classical in
/-- The condition of the class `j` of type 2: `I^{2,1}_bad = [m]` for `j = 0`, `I^{2,2,j}_bad = [m]`
for `j ≥ 1`. -/
def typeTwoClassCond (j : ℕ) {m : ℕ} (y : Fin m → ℂ × ℂ) : Prop :=
  if j = 0 then typeTwoOneBad p₀ β lam M ε₀ y = univ else typeTwoTwoBad Nₐ j p₀ β lam M ε₀ y = univ

open scoped Classical in
/-- The integrand of the partition function of the class `j` of type 2. -/
noncomputable def typeTwoClassIntegrand (j m : ℕ) (y : Fin m → ℂ × ℂ) : ℝ≥0∞ :=
  (boxPi Nₐ m).indicator (fun y =>
    (if typeTwoClassCond p₀ β lam M ε₀ Nₐ j y ∧ StablePairs y then 1 else 0) *
      ENNReal.ofReal (dipoleWeight χ β lam y)) y

/-- The partition function of the class `j` of type 2: `Z^{(2,1)}_{bad,m}` for `j = 0`,
`Z^{(2,2,j)}_{bad,m}` for `j ≥ 1`. -/
noncomputable def typeTwoClassPartitionFunction (j m : ℕ) : ℝ≥0∞ :=
  if j = 0 then typeTwoOnePartitionFunction χ p₀ β lam M ε₀ Nₐ m
  else typeTwoTwoPartitionFunction χ j p₀ β lam M ε₀ Nₐ m

theorem lintegral_typeTwoClassIntegrand (j m : ℕ) :
    ∫⁻ y, typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j m y =
      typeTwoClassPartitionFunction χ p₀ β lam M ε₀ Nₐ j m := by
  classical
  unfold typeTwoClassIntegrand typeTwoClassPartitionFunction
  rw [lintegral_indicator (measurableSet_boxPi Nₐ m)]
  by_cases hj : j = 0
  · simp only [typeTwoClassCond, hj, ite_true]
    rfl
  · simp only [typeTwoClassCond, hj, ite_false]
    rfl

theorem typeTwoClassIntegrand_ne_top (j m : ℕ) (y : Fin m → ℂ × ℂ) :
    typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j m y ≠ ⊤ := by
  classical
  unfold typeTwoClassIntegrand
  by_cases hy : y ∈ boxPi Nₐ m
  · rw [Set.indicator_of_mem hy]
    split_ifs <;> simp
  · rw [Set.indicator_of_notMem hy]
    exact ENNReal.zero_ne_top

/-- The partition functions of the classes are finite. -/
theorem lintegral_typeTwoClassIntegrand_ne_top {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hβ : 0 ≤ β)
    (hlam : 0 < lam) (j m : ℕ) :
    ∫⁻ y, typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j m y ≠ ⊤ := by
  classical
  set c := Real.exp (β * kernelConst χ) * lam ^ (-β) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ y : Fin m → ℂ × ℂ, typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j m y ≤
      (boxPi Nₐ m).indicator (fun _ => ENNReal.ofReal (c ^ m)) y := by
    intro y
    unfold typeTwoClassIntegrand
    by_cases hy : y ∈ boxPi Nₐ m
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      have h1 : (if typeTwoClassCond p₀ β lam M ε₀ Nₐ j y ∧ StablePairs y then (1 : ℝ≥0∞)
          else 0) ≤ 1 := by split_ifs <;> simp
      refine (mul_le_of_le_one_left' h1).trans (ENNReal.ofReal_le_ofReal ?_)
      unfold dipoleWeight
      rw [show c ^ m = ∏ _i : Fin m, c by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
      refine Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => ?_
      refine (exp_smearedKernel_le hχ hβ hlam _).trans ?_
      rw [hc]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hlam (le_max_right _ _)
        (by linarith)) (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_indicator (measurableSet_boxPi Nₐ m), setLIntegral_const]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volume_boxPi_lt_top Nₐ m)).ne

end Integrands

/-! ### The labelling of a configuration of type 2 -/

section Labelling

variable {Nₐ : ℕ}

/-- The set of configurations whose type-2 classes are the fibres of `τ`. -/
def typeTwoLabelSet (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ : ℕ) (τ : Fin n → Fin (pBeta p₀ β + 1)) :
    Set (Fin n → ℂ × ℂ) :=
  {d | typeTwoOneBad p₀ β lam M ε₀ d = fiber τ 0 ∧
    ∀ k : Fin (pBeta p₀ β + 1), k ≠ 0 → typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = fiber τ k}

theorem measurableSet_typeTwoLabelSet (τ : Fin n → Fin (pBeta p₀ β + 1)) :
    MeasurableSet (typeTwoLabelSet p₀ β lam M ε₀ Nₐ τ) := by
  have : typeTwoLabelSet p₀ β lam M ε₀ Nₐ τ =
      {d | typeTwoOneBad p₀ β lam M ε₀ d = fiber τ 0} ∩
        ⋂ k : Fin (pBeta p₀ β + 1),
          {d | k ≠ 0 → typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d = fiber τ k} := by
    ext d
    simp [typeTwoLabelSet]
  rw [this]
  refine (fiberMeasurable_typeTwoOneBad p₀ β lam M ε₀ _).inter (MeasurableSet.iInter fun k => ?_)
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ne_eq, not_false_eq_true, forall_const]
    exact fiberMeasurable_typeTwoTwoBad Nₐ k p₀ β lam M ε₀ _

open scoped Classical in
/-- Every configuration of type 2 lies in the set of some labelling. -/
theorem exists_typeTwoLabelSet {d : Fin n → ℂ × ℂ} (htwo : typeTwoBad Nₐ p₀ β lam M ε₀ d = univ) :
    ∃ τ : Fin n → Fin (pBeta p₀ β + 1), d ∈ typeTwoLabelSet p₀ β lam M ε₀ Nₐ τ := by
  have hone := badPointsTypeOne_eq_empty_of_typeTwoBad htwo
  set p := pBeta p₀ β
  set c : Fin n → ℕ := fun a => (multipoleClassOn M lam d univ a).card with hc
  have hmem1 : ∀ a, a ∈ typeTwoOneBad p₀ β lam M ε₀ d ↔ p < c a := by
    intro a
    unfold typeTwoOneBad
    simp only [hone, sdiff_empty, mem_filter, mem_univ, true_and, hc, p]
  -- the classes and the counts
  set S : ℕ → Finset (Fin n) := fun k => univ.filter fun a => c a = k with hS
  have hmem2 : ∀ k, typeTwoTwoBad Nₐ k p₀ β lam M ε₀ d =
      if ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (k - 1)) < ((S k).card : ℝ) then S k
      else ∅ := by
    intro k
    unfold typeTwoTwoBad
    simp only [hone, sdiff_empty, hS, hc]
  -- each label of size at most `p` is in its class set
  have hsmall : ∀ a, c a ≤ p → a ∈ typeTwoTwoBad Nₐ (c a) p₀ β lam M ε₀ d := by
    intro a hap
    have h := (mem_typeTwoBad_iff Nₐ).1 (htwo ▸ mem_univ a)
    rw [hone, sdiff_empty] at h
    rcases h.2 with h' | ⟨-, hcond⟩
    · exact absurd h' (not_lt.2 hap)
    · rw [hmem2]
      have hcond' : ε₀ ^ (-alphaExponent β) * Nₐ * lam ^ (2 * (c a - 1)) < ((S (c a)).card : ℝ) :=
        hcond
      rw [ite_eq_left hcond']
      exact mem_filter.2 ⟨mem_univ a, rfl⟩
  set τ : Fin n → Fin (p + 1) := fun a => if h : c a ≤ p then ⟨c a, by omega⟩ else 0 with hτ
  have hc0 : ∀ a, 0 < c a := fun a => card_pos.2 ⟨a, mem_classOn_self univ a⟩
  refine ⟨τ, ?_, fun k hk => ?_⟩
  · ext a
    rw [hmem1, mem_fiber]
    simp only [hτ]
    split_ifs with h
    · simp only [Fin.ext_iff, Fin.val_zero]
      constructor
      · intro h'; omega
      · intro h'; have := hc0 a; omega
    · exact ⟨fun _ => rfl, fun _ => by omega⟩
  · have hk0 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    ext a
    rw [mem_fiber]
    simp only [hτ]
    constructor
    · intro ha
      have hsub := typeTwoTwoBad_subset Nₐ k p₀ β lam M ε₀ d ha
      rw [hmem2] at ha
      split_ifs at ha with hcond
      · have hca : c a = k := (mem_filter.1 ha).2
        have hcp : c a ≤ p := hca ▸ Nat.lt_succ_iff.1 k.2
        rw [dite_eq_left hcp]
        exact Fin.ext hca
      · exact absurd ha (notMem_empty a)
    · intro ha
      split_ifs at ha with hcp
      · have hca : c a = k := by rw [← ha]
        rw [← hca]
        exact hsmall a hcp
      · exact absurd ha.symm hk

end Labelling

/-! ### The pointwise bound and the splitting -/

section Split

variable {χ : ℂ → ℝ} {Nₐ : ℕ}

open scoped Classical in
/-- **The pointwise bound**: on the set of a labelling `τ`, the integrand of `Z^{(2)}_{bad,n}` is
at most the product of the integrands of the classes, evaluated on the sub-configurations of the
fibres of `τ` (for a configuration without isosceles coincidences). -/
theorem typeTwoIntegrand_le_prod (hq : 1 ≤ clusterThreshold p₀ β) (hh : 0 < cutoff p₀ β lam ε₀)
    (τ : Fin n → Fin (pBeta p₀ β + 1)) {d : Fin n → ℂ × ℂ}
    (hd : d ∈ typeTwoLabelSet p₀ β lam M ε₀ Nₐ τ)
    (hz : NoIsosceles (fun k => (d k).1)) (hz' : NoIsosceles (fun k => (d k).2)) :
    typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ n d ≤
      ∏ j : Fin (pBeta p₀ β + 1),
        typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card (d ∘ fiberEmb τ j) := by
  unfold typeTwoIntegrand
  by_cases hbox : d ∈ boxPi Nₐ n
  swap
  · rw [Set.indicator_of_notMem hbox]; exact zero_le
  rw [Set.indicator_of_mem hbox]
  split_ifs with hE
  swap
  · rw [zero_mul]; exact zero_le
  obtain ⟨htwo, hst⟩ := hE
  rw [one_mul]
  obtain ⟨h0, hk⟩ := hd
  have hboxk : ∀ j, d ∘ fiberEmb τ j ∈ boxPi Nₐ (fiber τ j).card := fun j =>
    Set.mem_univ_pi.2 fun a => Set.mem_univ_pi.1 hbox _
  have hstk : ∀ j, StablePairs (d ∘ fiberEmb τ j) := fun j a b hab =>
    hst _ _ ((fiberEmb τ j).strictMono hab)
  have hrange : ∀ j, univ.map (fiberEmb τ j).toEmbedding = fiber τ j := fun j =>
    Finset.map_orderEmbOfFin_univ _ rfl
  have hcond : ∀ j : Fin (pBeta p₀ β + 1),
      typeTwoClassCond p₀ β lam M ε₀ Nₐ j (d ∘ fiberEmb τ j) := by
    intro j
    unfold typeTwoClassCond
    by_cases hj : (j : ℕ) = 0
    · rw [ite_eq_left hj]
      have hj' : j = 0 := Fin.ext hj
      subst hj'
      exact typeTwoOneBad_comp_eq_univ hq hh hz hz' htwo _ (by rw [hrange, h0])
    · rw [ite_eq_right hj]
      exact typeTwoTwoBad_comp_eq_univ (j : ℕ) hq hh hz hz' htwo _
        (by rw [hrange, hk j (fun h => hj (by rw [h]; rfl))])
  have hval : ∀ j : Fin (pBeta p₀ β + 1),
      typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card
        (d ∘ fiberEmb τ j) = ENNReal.ofReal (dipoleWeight χ β lam (d ∘ fiberEmb τ j)) := by
    intro j
    unfold typeTwoClassIntegrand
    rw [Set.indicator_of_mem (hboxk j), ite_eq_left ⟨hcond j, hstk j⟩, one_mul]
  simp_rw [hval]
  rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => dipoleWeight_nonneg χ β lam _]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold dipoleWeight
  rw [← Finset.prod_fiberwise_of_maps_to (s := univ) (t := univ) (g := τ)
    (fun a _ => Finset.mem_univ (τ a))]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact prod_orderEmbOfFin (fiber τ j) _

open scoped Classical in
/-- **Eq. (5.132)**: `Z^{(2)}_{bad,n}` is at most the sum over the labellings
`τ : [n] → {0, …, p(β)}` of the products of the partition functions of the classes. -/
theorem typeTwoPartitionFunction_le_sum (hχ : IsMollifier χ) (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hβ : 0 ≤ β) (hlam : 0 < lam) (Nₐ n : ℕ) :
    typeTwoPartitionFunction χ p₀ β lam M ε₀ Nₐ n ≤
      ∑ τ : Fin n → Fin (pBeta p₀ β + 1),
        ∏ j : Fin (pBeta p₀ β + 1),
          typeTwoClassPartitionFunction χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card := by
  set g := typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ n
  set E : (Fin n → Fin (pBeta p₀ β + 1)) → Set (Fin n → ℂ × ℂ) :=
    typeTwoLabelSet p₀ β lam M ε₀ Nₐ with hE
  set S : Option (Fin n → Fin (pBeta p₀ β + 1)) → Set (Fin n → ℂ × ℂ) :=
    fun o => o.elim (⋃ τ, E τ)ᶜ E with hS
  have hSm : ∀ o, MeasurableSet (S o) := by
    rintro (_ | τ)
    · exact (MeasurableSet.iUnion fun τ => measurableSet_typeTwoLabelSet τ).compl
    · exact measurableSet_typeTwoLabelSet τ
  have hcov : (⋃ o, S o) = Set.univ := by
    ext d
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hd : d ∈ ⋃ τ, E τ
    · obtain ⟨τ, hτ⟩ := Set.mem_iUnion.1 hd
      exact ⟨some τ, hτ⟩
    · exact ⟨none, hd⟩
  -- off the sets of the labellings, the integrand vanishes
  have hnone : ∫⁻ d in S none, g d = 0 := by
    refine le_antisymm ?_ zero_le
    calc ∫⁻ d in S none, g d ≤ ∫⁻ _d in S none, 0 := setLIntegral_mono' (hSm none) fun d hd => by
          simp only [hS, Option.elim_none, Set.mem_compl_iff] at hd
          simp only [g]
          unfold typeTwoIntegrand
          by_cases hbox : d ∈ boxPi Nₐ n
          · rw [Set.indicator_of_mem hbox]
            split_ifs with h
            · obtain ⟨τ, hτ⟩ := exists_typeTwoLabelSet h.1
              exact absurd (Set.mem_iUnion.2 ⟨τ, hτ⟩) hd
            · rw [zero_mul]
          · rw [Set.indicator_of_notMem hbox]
      _ = 0 := lintegral_zero
  -- on the set of a labelling
  have hsome : ∀ τ : Fin n → Fin (pBeta p₀ β + 1), ∫⁻ d in S (some τ), g d ≤
      ∏ j : Fin (pBeta p₀ β + 1),
        typeTwoClassPartitionFunction χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card := by
    intro τ
    calc ∫⁻ d in S (some τ), g d
        ≤ ∫⁻ d in S (some τ), ∏ j : Fin (pBeta p₀ β + 1),
            typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card (d ∘ fiberEmb τ j) := by
          refine setLIntegral_mono_ae' (hSm _) ?_
          filter_upwards [ae_noIsosceles_config] with d hd hdS
          exact typeTwoIntegrand_le_prod hq hh τ hdS hd.1 hd.2
      _ ≤ ∫⁻ d, ∏ j : Fin (pBeta p₀ β + 1),
            typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card (d ∘ fiberEmb τ j) :=
          setLIntegral_le_lintegral _ _
      _ ≤ ∏ j : Fin (pBeta p₀ β + 1),
            ∫⁻ y, typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j (fiber τ j).card y :=
          lintegral_prod_fiber_le (pBeta p₀ β + 1) τ
            (fun j => typeTwoClassIntegrand χ p₀ β lam M ε₀ Nₐ j)
            (fun j m y => typeTwoClassIntegrand_ne_top χ p₀ β lam M ε₀ Nₐ j m y)
            (fun j m => lintegral_typeTwoClassIntegrand_ne_top p₀ β lam M ε₀ Nₐ hχ hβ hlam j m)
      _ = _ := by simp_rw [lintegral_typeTwoClassIntegrand]
  rw [typeTwoPartitionFunction_eq_lintegral, ← setLIntegral_univ, ← hcov]
  refine (lintegral_iUnion_le S g).trans ?_
  rw [tsum_fintype, Fintype.sum_option, hnone, zero_add]
  exact Finset.sum_le_sum fun τ _ => hsome τ

end Split

end UpperBoundLDP

end MultipoleBKT

end
