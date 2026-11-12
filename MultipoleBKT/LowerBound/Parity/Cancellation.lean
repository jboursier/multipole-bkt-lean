/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.Relative
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Circle
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Cancellation at a block of odd degree (Lemma 4.32)

Lemma 4.32. The
proof reverses the variables of one block `S₀`; every edge of `E₁` contributes one sign per
endpoint in `S₀`, so the integrand changes by `(-1)^{deg_{E₁}(S₀)}`, with
`deg_E(S) = ∑_{i ∈ S} deg_E(i)` (Definition 4.10(7)).

We work with a general involution `σ` of the single-site space `α` (`σ = Prod.swap` on dipoles
`(x_i, y_i)`, i.e. the reversal `x_i ↔ y_i` with the midpoint fixed, in all applications;
`σ = -·` on the circle in the paper's statement) and with a general measure `P` on
configurations `ι → α` that is invariant under the reversal of a set of labels.

* `flipOn σ B c`: apply `σ` to the coordinates with label in `B`; `flipOnEquiv`,
  `measurePreserving_flipOn_pi` (product measures), `measurePreserving_withDensity_flipOn`
  (densities invariant under the reversal), `apply_flipOn_of_local` and
  `prod_apply_flipOn_of_local` (block weights depending only on their own block).
* `edgeProd E f c = ∏_{i < j, ij ∈ E} f_ij(c_i, c_j)`.
* `prod_prod_ite_mul_eq_prod_pow`: `∏_{i<j, ij ∈ E} s_i s_j = ∏_i s_i^{deg_E(i)}` (handshake).
* `edgeProd_flipOn_of_odd`, `edgeProd_flipOn_of_even`: if each `a_ij`, `ij ∈ E`, is odd in both
  variables, reversing `B` multiplies `∏_E a` by `(-1)^{∑_{i ∈ B} deg_E(i)}`; even `b_ij` are
  unchanged. No assumption on `E` is needed: an edge inside `B` contributes `(-1)² = 1`.
* `integral_edgeProd_mul_eq_zero`: the general form of Lemma 4.32.
* `lemma_4_32`: Lemma 4.32 as stated in the paper, on `(𝕊¹)^{V_X}` for any negation-invariant
  measure on the circle (in particular arc length); `integral_eq_zero_of_odd_blockDegree`: the
  form used in Section 4–Section 5, for a subpartition `X`, a block `S₀ ∈ X` of odd `E₁`-degree and a measure
  invariant under the reversal of `S₀`.

The paper assumes the functions measurable and the product integrable; neither is needed (the
Bochner integral of a non-integrable function is `0`, and the change of variables holds for every
function), and neither is assumed. Nor are the hypotheses `E₁, E₂ ⊆ ℰ^inter(X)` and
`E₁ ∩ E₂ = ∅` used.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal

namespace MultipoleBKT

namespace Parity

/-! ### Reversing the coordinates of a set of labels -/

section Flip

variable {ι α : Type*} [DecidableEq ι]

/-- `flipOn σ B c` applies the involution `σ` to the coordinates of `c` with label in `B`. For
`σ = Prod.swap` on dipoles `(x_i, y_i)` it performs the simultaneous reversals `x_i ↔ y_i`,
`i ∈ B` (proof of Lemma 4.32). -/
def flipOn (σ : α → α) (B : Finset ι) (c : ι → α) : ι → α :=
  fun i => if i ∈ B then σ (c i) else c i

variable {σ : α → α} {B : Finset ι}

theorem flipOn_apply (σ : α → α) (B : Finset ι) (c : ι → α) (i : ι) :
    flipOn σ B c i = if i ∈ B then σ (c i) else c i := rfl

theorem flipOn_apply_of_mem {c : ι → α} {i : ι} (hi : i ∈ B) : flipOn σ B c i = σ (c i) := by
  rw [flipOn_apply, ite_eq_left hi]

theorem flipOn_apply_of_notMem {c : ι → α} {i : ι} (hi : i ∉ B) : flipOn σ B c i = c i := by
  rw [flipOn_apply, ite_eq_right hi]

theorem flipOn_flipOn (hσ : Function.Involutive σ) (B : Finset ι) (c : ι → α) :
    flipOn σ B (flipOn σ B c) = c := by
  funext i
  unfold flipOn
  split_ifs
  · exact hσ _
  · rfl

theorem measurable_flipOn [MeasurableSpace α] (hσ : Measurable σ) (B : Finset ι) :
    Measurable (flipOn σ B) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold flipOn
  split_ifs
  · exact hσ.comp (measurable_pi_apply i)
  · exact measurable_pi_apply i

/-- `flipOn σ B` as a measurable involution. -/
def flipOnEquiv [MeasurableSpace α] (hσ : Measurable σ) (hσσ : Function.Involutive σ)
    (B : Finset ι) : (ι → α) ≃ᵐ (ι → α) where
  toFun := flipOn σ B
  invFun := flipOn σ B
  left_inv := flipOn_flipOn hσσ B
  right_inv := flipOn_flipOn hσσ B
  measurable_toFun := measurable_flipOn hσ B
  measurable_invFun := measurable_flipOn hσ B

theorem coe_flipOnEquiv [MeasurableSpace α] (hσ : Measurable σ) (hσσ : Function.Involutive σ)
    (B : Finset ι) : ⇑(flipOnEquiv hσ hσσ B) = flipOn σ B := rfl

/-- A product of `σ`-invariant measures is invariant under `flipOn σ B`. -/
theorem measurePreserving_flipOn_pi [Fintype ι] [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] (hμ : MeasurePreserving σ μ μ) (B : Finset ι) :
    MeasurePreserving (flipOn σ B) (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  have h := measurePreserving_pi (fun _ : ι => μ) (fun _ : ι => μ)
    (f := fun i => if i ∈ B then σ else id) fun i => by
      split_ifs
      · exact hμ
      · exact MeasurePreserving.id μ
  convert h using 1
  funext c i
  unfold flipOn
  split_ifs <;> rfl

/-- A function of the configuration that depends only on the coordinates in `S` and is invariant
under the reversal of all of them is invariant under the reversal of any `B` equal to `S` or
disjoint from it (e.g. a block weight `F_S` of Lemma 4.32 under the reversal of a block of a
subpartition). -/
theorem apply_flipOn_of_local {γ : Type*} {φ : (ι → α) → γ} {S B : Finset ι}
    (hloc : ∀ c c' : ι → α, (∀ i ∈ S, c i = c' i) → φ c = φ c')
    (hinv : ∀ c, φ (flipOn σ S c) = φ c) (hSB : S = B ∨ Disjoint S B) (c : ι → α) :
    φ (flipOn σ B c) = φ c := by
  rcases hSB with rfl | hSB
  · exact hinv c
  · exact hloc _ _ fun i hi => flipOn_apply_of_notMem (Finset.disjoint_left.1 hSB hi)

omit [DecidableEq ι] in
/-- A measure with a density invariant under a measure-preserving measurable embedding `f` is
invariant under `f`. -/
theorem measurePreserving_withDensity_of_comp {γ : Type*} [MeasurableSpace γ] {f : γ → γ}
    {μ : Measure γ} (hf : MeasurePreserving f μ μ) (hfe : MeasurableEmbedding f)
    {ρ : γ → ℝ≥0∞} (hρ : ∀ x, ρ (f x) = ρ x) :
    MeasurePreserving f (μ.withDensity ρ) (μ.withDensity ρ) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  rw [show ∫⁻ x in f ⁻¹' s, ρ x ∂μ = ∫⁻ x in f ⁻¹' s, ρ (f x) ∂μ from
    lintegral_congr fun x => (hρ x).symm]
  exact hf.setLIntegral_comp_preimage_emb hfe ρ s

/-- A measure with a density invariant under `flipOn σ B`, with respect to a measure invariant
under `flipOn σ B`, is invariant under `flipOn σ B`. -/
theorem measurePreserving_withDensity_flipOn [MeasurableSpace α] (hσ : Measurable σ)
    (hσσ : Function.Involutive σ) {P : Measure (ι → α)} (hP : MeasurePreserving (flipOn σ B) P P)
    {ρ : (ι → α) → ℝ≥0∞} (hρ : ∀ c, ρ (flipOn σ B c) = ρ c) :
    MeasurePreserving (flipOn σ B) (P.withDensity ρ) (P.withDensity ρ) :=
  measurePreserving_withDensity_of_comp hP (flipOnEquiv hσ hσσ B).measurableEmbedding hρ

end Flip

/-! ### Products over the edges of a graph -/

section EdgeProd

variable {ι α : Type*} [Fintype ι] [LinearOrder ι]

open scoped Classical in
/-- `∏_{ij ∈ E, i < j} f_ij(c_i, c_j)`: the product of the pair functions `f_ij` over the edges of
`E`, each edge taken with its endpoints in increasing order (as in the frozen activities). -/
noncomputable def edgeProd (E : SimpleGraph ι) (f : ι → ι → α → α → ℝ) (c : ι → α) : ℝ :=
  ∏ i, ∏ j, if i < j ∧ E.Adj i j then f i j (c i) (c j) else 1

open scoped Classical

omit [LinearOrder ι] in
/-- `∏_j (if E.Adj i j then x else 1) = x^{deg_E(i)}`. -/
theorem prod_ite_adj_eq_pow {M : Type*} [CommMonoid M] (E : SimpleGraph ι) (i : ι) (x : M) :
    ∏ j, (if E.Adj i j then x else 1) = x ^ E.degree i := by
  rw [← Finset.prod_filter, Finset.prod_const, ← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_eq_filter]

/-- The handshake identity for signs: `∏_{i<j, ij ∈ E} s_i s_j = ∏_i s_i^{deg_E(i)}`. -/
theorem prod_prod_ite_mul_eq_prod_pow {M : Type*} [CommMonoid M] (E : SimpleGraph ι)
    (s : ι → M) :
    ∏ i, ∏ j, (if i < j ∧ E.Adj i j then s i * s j else 1) = ∏ i, s i ^ E.degree i := by
  have hsplit : ∀ i j, (if i < j ∧ E.Adj i j then s i * s j else 1) =
      (if i < j ∧ E.Adj i j then s i else 1) * (if i < j ∧ E.Adj i j then s j else 1) := by
    intro i j
    split_ifs <;> simp
  simp_rw [hsplit, Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i j => if i < j ∧ E.Adj i j then s j else 1),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib, ← prod_ite_adj_eq_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hij : E.Adj i j
  · have hne := hij.ne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [ite_eq_left ⟨h, hij⟩, ite_eq_right fun h' => lt_asymm h h'.1, ite_eq_left hij, mul_one]
    · rw [ite_eq_right fun h' => lt_asymm h h'.1, ite_eq_left ⟨h, hij.symm⟩, ite_eq_left hij,
        one_mul]
  · rw [ite_eq_right fun h' => hij h'.2, ite_eq_right fun h' => hij h'.2.symm, ite_eq_right hij,
      mul_one]

variable [DecidableEq ι] {σ : α → α}

omit [LinearOrder ι] in
/-- `∏_i ((-1)^{[i ∈ B]})^{f(i)} = (-1)^{∑_{i ∈ B} f(i)}`. -/
theorem prod_ite_mem_pow (B : Finset ι) (f : ι → ℕ) :
    ∏ i, (if i ∈ B then (-1 : ℝ) else 1) ^ f i = (-1) ^ (∑ i ∈ B, f i) := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (· ∈ B)]
  have h1 : ∏ i ∈ Finset.univ.filter (· ∈ B), (if i ∈ B then (-1 : ℝ) else 1) ^ f i =
      ∏ i ∈ B, (-1 : ℝ) ^ f i := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.prod_congr rfl fun i hi => by simp [hi]
  have h2 : ∏ i ∈ Finset.univ.filter (fun i => i ∉ B), (if i ∈ B then (-1 : ℝ) else 1) ^ f i =
      1 := Finset.prod_eq_one fun i hi => by simp [(Finset.mem_filter.1 hi).2]
  rw [h1, h2, mul_one]

/-- If every `a_ij`, `ij ∈ E`, is odd in each variable, reversing the labels in `B` multiplies
`∏_E a` by `(-1)^{∑_{i ∈ B} deg_E(i)}`. -/
theorem edgeProd_flipOn_of_odd (E : SimpleGraph ι) {a : ι → ι → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    (B : Finset ι) (c : ι → α) :
    edgeProd E a (flipOn σ B c) = (-1) ^ (∑ i ∈ B, E.degree i) * edgeProd E a c := by
  set s : ι → ℝ := fun i => if i ∈ B then -1 else 1 with hs
  have hfac : ∀ i j, (if i < j ∧ E.Adj i j then a i j (flipOn σ B c i) (flipOn σ B c j) else 1) =
      (if i < j ∧ E.Adj i j then s i * s j else 1) *
        (if i < j ∧ E.Adj i j then a i j (c i) (c j) else 1) := by
    intro i j
    by_cases h : i < j ∧ E.Adj i j
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      simp only [hs, flipOn_apply]
      split_ifs <;> simp [ha₁ i j h.1 h.2, ha₂ i j h.1 h.2]
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h, mul_one]
  have hsign : ∏ i, s i ^ E.degree i = (-1) ^ (∑ i ∈ B, E.degree i) :=
    prod_ite_mem_pow B fun i => E.degree i
  unfold edgeProd
  simp_rw [hfac, Finset.prod_mul_distrib]
  rw [prod_prod_ite_mul_eq_prod_pow, hsign]

/-- If every `b_ij`, `ij ∈ E`, is even in each variable, `∏_E b` is invariant under reversals. -/
theorem edgeProd_flipOn_of_even (E : SimpleGraph ι) {b : ι → ι → α → α → ℝ}
    (hb₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j (σ x) y = b i j x y)
    (hb₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, b i j x (σ y) = b i j x y)
    (B : Finset ι) (c : ι → α) :
    edgeProd E b (flipOn σ B c) = edgeProd E b c := by
  unfold edgeProd
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  by_cases h : i < j ∧ E.Adj i j
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [flipOn_apply]
    split_ifs <;> simp [hb₁ i j h.1 h.2, hb₂ i j h.1 h.2]
  · rw [ite_eq_right h, ite_eq_right h]

omit [Fintype ι] [LinearOrder ι] in
/-- If every `u_i`, `i ∈ V₁`, is odd, reversing the labels in `B` multiplies `∏_{i ∈ V₁} u_i` by
`(-1)^{|B ∩ V₁|}` (the vertex weights `a_{i∞}` of Section 5, Definition 5.21). -/
theorem prod_flipOn_of_odd (V₁ : Finset ι) {u : ι → α → ℝ}
    (hu : ∀ i ∈ V₁, ∀ x, u i (σ x) = -u i x) (B : Finset ι) (c : ι → α) :
    ∏ i ∈ V₁, u i (flipOn σ B c i) = (-1) ^ (B ∩ V₁).card * ∏ i ∈ V₁, u i (c i) := by
  have hfac : ∀ i ∈ V₁, u i (flipOn σ B c i) = (if i ∈ B then (-1 : ℝ) else 1) * u i (c i) := by
    intro i hi
    rw [flipOn_apply]
    split_ifs
    · rw [hu i hi, neg_one_mul]
    · rw [one_mul]
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const,
    Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter, Finset.inter_comm]

omit [Fintype ι] [LinearOrder ι] in
/-- If every `v_i`, `i ∈ V₂`, is even, `∏_{i ∈ V₂} v_i` is invariant under reversals. -/
theorem prod_flipOn_of_even (V₂ : Finset ι) {v : ι → α → ℝ}
    (hv : ∀ i ∈ V₂, ∀ x, v i (σ x) = v i x) (B : Finset ι) (c : ι → α) :
    ∏ i ∈ V₂, v i (flipOn σ B c i) = ∏ i ∈ V₂, v i (c i) := by
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [flipOn_apply]
  split_ifs
  · exact hv i hi _
  · rfl

end EdgeProd

/-! ### Lemma 4.32 -/

section Cancellation

variable {ι α : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι] [MeasurableSpace α]
  {σ : α → α}

open scoped Classical

/-- **Lemma 4.32**, general form: if `P` is invariant under the reversal of the labels in `B`,
each `a_ij`, `ij ∈ E`, is odd in both variables, `G` is invariant under the reversal of `B`, and
`∑_{i ∈ B} deg_E(i)` is odd, then `∫ ∏_{ij ∈ E} a_ij(c_i, c_j) G(c) dP(c) = 0`. -/
theorem integral_edgeProd_mul_eq_zero (hσ : Measurable σ) (hσσ : Function.Involutive σ)
    {P : Measure (ι → α)} {B : Finset ι} (hP : MeasurePreserving (flipOn σ B) P P)
    {E : SimpleGraph ι} {a : ι → ι → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    {G : (ι → α) → ℝ} (hG : ∀ c, G (flipOn σ B c) = G c)
    (hodd : Odd (∑ i ∈ B, E.degree i)) :
    ∫ c, edgeProd E a c * G c ∂P = 0 := by
  have h := hP.integral_comp' (f := flipOnEquiv hσ hσσ B) (fun c => edgeProd E a c * G c)
  simp only [coe_flipOnEquiv, edgeProd_flipOn_of_odd E ha₁ ha₂, hG, hodd.neg_one_pow,
    neg_mul, one_mul, integral_neg] at h
  linarith

/-- **Lemma 4.32 with odd vertex weights** (the form behind Corollary 5.24): with, in addition,
vertex weights `u_i`, `i ∈ V₁`, odd under `σ`, the integral vanishes as soon as
`∑_{i ∈ B} deg_E(i) + |B ∩ V₁|` is odd. -/
theorem integral_edgeProd_mul_prod_mul_eq_zero (hσ : Measurable σ) (hσσ : Function.Involutive σ)
    {P : Measure (ι → α)} {B : Finset ι} (hP : MeasurePreserving (flipOn σ B) P P)
    {E : SimpleGraph ι} {a : ι → ι → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    {V₁ : Finset ι} {u : ι → α → ℝ} (hu : ∀ i ∈ V₁, ∀ x, u i (σ x) = -u i x)
    {G : (ι → α) → ℝ} (hG : ∀ c, G (flipOn σ B c) = G c)
    (hodd : Odd (∑ i ∈ B, E.degree i + (B ∩ V₁).card)) :
    ∫ c, edgeProd E a c * (∏ i ∈ V₁, u i (c i)) * G c ∂P = 0 := by
  have h := hP.integral_comp' (f := flipOnEquiv hσ hσσ B)
    (fun c => edgeProd E a c * (∏ i ∈ V₁, u i (c i)) * G c)
  simp only [coe_flipOnEquiv, edgeProd_flipOn_of_odd E ha₁ ha₂, prod_flipOn_of_odd V₁ hu, hG]
    at h
  have hsign : ((-1 : ℝ) ^ (∑ i ∈ B, E.degree i)) * (-1) ^ (B ∩ V₁).card = -1 := by
    rw [← pow_add, hodd.neg_one_pow]
  have key : ∀ c : ι → α, (-1) ^ (∑ i ∈ B, E.degree i) * edgeProd E a c *
      ((-1) ^ (B ∩ V₁).card * ∏ i ∈ V₁, u i (c i)) * G c =
        -(edgeProd E a c * (∏ i ∈ V₁, u i (c i)) * G c) := fun c => by
    linear_combination (edgeProd E a c * (∏ i ∈ V₁, u i (c i)) * G c) * hsign
  simp_rw [key, integral_neg] at h
  linarith

/-- The labels of the block `S` as a finset of `V_X`. -/
def blockSet (X : Finset (Finset ℕ)) (S : Finset ℕ) : Finset (X.biUnion id) :=
  S.subtype (· ∈ X.biUnion id)

theorem mem_blockSet {X : Finset (Finset ℕ)} {S : Finset ℕ} {i : X.biUnion id} :
    i ∈ blockSet X S ↔ (i : ℕ) ∈ S := by
  rw [blockSet, Finset.mem_subtype]

/-- The labels of two distinct blocks of a subpartition are disjoint. -/
theorem blockSet_eq_or_disjoint {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {S S₀ : Finset ℕ}
    (hS : S ∈ X) (hS₀ : S₀ ∈ X) : blockSet X S = blockSet X S₀ ∨
      Disjoint (blockSet X S) (blockSet X S₀) := by
  by_cases h : S = S₀
  · exact Or.inl (h ▸ rfl)
  · refine Or.inr (Finset.disjoint_left.2 fun i hi hi₀ => ?_)
    exact Finset.disjoint_left.1 (hX.2 (Finset.mem_coe.2 hS) (Finset.mem_coe.2 hS₀) h)
      (mem_blockSet.1 hi) (mem_blockSet.1 hi₀)

omit [MeasurableSpace α] in
/-- A product over the blocks `S ∈ X` of block weights `φ_S`, each depending only on the dipoles of
`S` and invariant under their simultaneous reversal (the density of a hierarchical model), is
invariant under the reversal of the dipoles of any block `S₀ ∈ X`. -/
theorem prod_apply_flipOn_of_local {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    {M₀ : Type*} [CommMonoid M₀] {φ : Finset ℕ → (X.biUnion id → α) → M₀}
    (hloc : ∀ S ∈ X, ∀ c c' : X.biUnion id → α, (∀ i ∈ blockSet X S, c i = c' i) →
      φ S c = φ S c')
    (hinv : ∀ S ∈ X, ∀ c, φ S (flipOn σ (blockSet X S) c) = φ S c) {S₀ : Finset ℕ}
    (hS₀ : S₀ ∈ X) (c : X.biUnion id → α) :
    ∏ S ∈ X, φ S (flipOn σ (blockSet X S₀) c) = ∏ S ∈ X, φ S c :=
  Finset.prod_congr rfl fun S hS =>
    apply_flipOn_of_local (hloc S hS) (hinv S hS) (blockSet_eq_or_disjoint hX hS hS₀) c

/-- `deg_E(S) = ∑_{i ∈ S} deg_E(i)` (Definition 4.10(7)). -/
theorem blockDegree_eq_sum (X : Finset (Finset ℕ)) (E : SimpleGraph (X.biUnion id))
    (S : Finset ℕ) : blockDegree X E S = ∑ i ∈ blockSet X S, E.degree i := rfl

/-- **Lemma 4.32** in the form used in Section 4–Section 5: for a subpartition `X`, a block `S₀ ∈ X` with
`deg_{E₁}(S₀)` odd, a measure `P` on configurations of `V_X` invariant under the simultaneous
reversal of the dipoles of `S₀`, pair functions `a_ij` odd in both variables, and `G` invariant
under that reversal (the even bonds of `E₂` and the block weights `F_S`),
`∫ ∏_{ij ∈ E₁} a_ij G dP = 0`. -/
theorem integral_eq_zero_of_odd_blockDegree {X : Finset (Finset ℕ)} (hσ : Measurable σ)
    (hσσ : Function.Involutive σ) {P : Measure (X.biUnion id → α)} {S₀ : Finset ℕ}
    (hP : MeasurePreserving (flipOn σ (blockSet X S₀)) P P) {E₁ : SimpleGraph (X.biUnion id)}
    {a : X.biUnion id → X.biUnion id → α → α → ℝ}
    (ha₁ : ∀ i j, i < j → E₁.Adj i j → ∀ x y, a i j (σ x) y = -a i j x y)
    (ha₂ : ∀ i j, i < j → E₁.Adj i j → ∀ x y, a i j x (σ y) = -a i j x y)
    {G : (X.biUnion id → α) → ℝ} (hG : ∀ c, G (flipOn σ (blockSet X S₀) c) = G c)
    (hodd : Odd (blockDegree X E₁ S₀)) :
    ∫ c, edgeProd E₁ a c * G c ∂P = 0 :=
  integral_edgeProd_mul_eq_zero hσ hσσ hP ha₁ ha₂ hG hodd

/-- **Lemma 4.32**, as stated in the paper, on
`(𝕊¹)^{V_X}`: let `X` be a subpartition, `a_ij` (`ij ∈ E₁`) and `b_ij` (`ij ∈ E₂`) functions
`(𝕊¹)² → ℝ` odd, resp. even, in both variables, `F_S : (𝕊¹)^S → ℝ` invariant under
`(x_i)_{i ∈ S} ↦ (-x_i)_{i ∈ S}`, and `S₀ ∈ X` with `deg_{E₁}(S₀)` odd. Then
`∫ ∏_{E₁} a_ij ∏_{E₂} b_ij ∏_{S ∈ X} F_S ∏_i dr_i = 0`, for any negation-invariant measure `dr`
on the circle (in particular arc length). The paper's
hypotheses `E₁, E₂ ⊆ ℰ^inter(X)`, `E₁ ∩ E₂ = ∅`, measurability and integrability are not
needed. -/
theorem lemma_4_32 {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (E₁ E₂ : SimpleGraph (X.biUnion id)) (μ : Measure Circle) [SigmaFinite μ]
    (hμ : MeasurePreserving (fun x : Circle => -x) μ μ)
    (a b : X.biUnion id → X.biUnion id → Circle → Circle → ℝ)
    (ha : ∀ i j, i < j → E₁.Adj i j → ∀ x y,
      a i j (-x) y = -a i j x y ∧ a i j x (-y) = -a i j x y)
    (hb : ∀ i j, i < j → E₂.Adj i j → ∀ x y,
      b i j (-x) y = b i j x y ∧ b i j x (-y) = b i j x y)
    (F : (S : X) → ({i : X.biUnion id // (i : ℕ) ∈ (S : Finset ℕ)} → Circle) → ℝ)
    (hF : ∀ S y, F S (fun i => -y i) = F S y) {S₀ : Finset ℕ} (hS₀ : S₀ ∈ X)
    (hodd : Odd (blockDegree X E₁ S₀)) :
    ∫ c, edgeProd E₁ a c * edgeProd E₂ b c * ∏ S : X, F S (fun i => c i.1)
      ∂(Measure.pi fun _ : X.biUnion id => μ) = 0 := by
  have hσ : Measurable fun x : Circle => -x := continuous_neg.measurable
  have hσσ : Function.Involutive fun x : Circle => -x := neg_neg
  simp_rw [mul_assoc]
  refine integral_eq_zero_of_odd_blockDegree hσ hσσ (measurePreserving_flipOn_pi hμ _)
    (fun i j hij h x y => (ha i j hij h x y).1) (fun i j hij h x y => (ha i j hij h x y).2)
    (fun c => ?_) hodd
  rw [edgeProd_flipOn_of_even E₂ (fun i j hij h x y => (hb i j hij h x y).1)
    (fun i j hij h x y => (hb i j hij h x y).2)]
  congr 1
  refine Finset.prod_congr rfl fun S _ => ?_
  by_cases hS : (S : Finset ℕ) = S₀
  · have h : (fun i : {i : X.biUnion id // (i : ℕ) ∈ (S : Finset ℕ)} =>
        flipOn (fun x : Circle => -x) (blockSet X S₀) c i.1) = fun i => -c i.1 := by
      funext i
      rw [flipOn_apply_of_mem (mem_blockSet.2 (hS ▸ i.2))]
    rw [h, hF]
  · have h : (fun i : {i : X.biUnion id // (i : ℕ) ∈ (S : Finset ℕ)} =>
        flipOn (fun x : Circle => -x) (blockSet X S₀) c i.1) = fun i => c i.1 := by
      funext i
      refine flipOn_apply_of_notMem fun hi => ?_
      have hd := hX.2 (Finset.mem_coe.2 S.2) (Finset.mem_coe.2 hS₀) hS
      exact Finset.disjoint_left.1 hd i.2 (mem_blockSet.1 hi)
    rw [h]

end Cancellation

end Parity

end MultipoleBKT

end
