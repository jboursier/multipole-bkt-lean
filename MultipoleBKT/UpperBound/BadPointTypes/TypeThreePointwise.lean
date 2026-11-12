/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypedEvent
public import MultipoleBKT.UpperBound.BadPointTypes.TypeThreeSplit
public import MultipoleBKT.Potential.BondBound

/-!
# Lemma 5.39: the pointwise bound

The paper: proof of Lemma 5.39. On the event `{I^1_bad = V_1, I^2_bad = V_2, I^3_bad = V_3}`
(`V_1 ∪ V_2 ∪ V_3 = [n]`, a partition), for a configuration without isosceles coincidences
(`typedIntegrand_le`):

`𝟙_{(Λ²)^n} 𝟙_{event} ∏_{i<j} 𝟙_{𝒜_ij} ∏_i (τ_i^+ τ_i^-)^{-β/2}
  ≤ F_1(d ∘ e_1) · (12^β)^{N_2} · F_2(d ∘ e_2) · ∑_{S} ∑_{par} T_{S,par}(d ∘ e_1, d ∘ e_2, d ∘ e_3)`,

where `e_k` enumerates `V_k`, `F_1`, `F_2` are the integrands of `Z^{(1)}_{bad,N_1}` and
`Z^{(2)}_{bad,N_2}` (the restrictions preserve the type-1 clustering and radii on `V_1` and the
type-2 classes and counts on `V_2`, `SubConfig.lean`), the sum runs over the seed sets `S` of
`V_3` with `N_3 ≤ p(β) |S|` (Step 1) and over the parent maps of the nonseeds, and
`T_{S,par}` is `𝟙_{par is a forest towards S}` times the product over the seeds of
`(∑_{j ∈ V_1 ∪ V_2} 𝟙_{near}) 𝟙_{r ≤ h} 4^β max(r, λ)^{-β}` and over the nonseeds of
`𝟙_{near its parent} 𝟙_{r ≤ h} 4^β max(r, λ)^{-β}` (Steps 2–3). On `V_2 ∪ V_3`,
`τ^± = max(λ, r/4)` and `max(λ, r/4)^{-β} ≤ 4^β max(r, λ)^{-β} ≤ 12^β e^{β g_λ}`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open MeasureTheory Finset TheoremTwo UpperBound
open scoped ENNReal

variable {n : ℕ}

/-! ### The weights -/

/-- The weight `𝟙_{|w| ≤ h} 4^β max(|w|, λ)^{-β}` of a type-3 dipole. -/
noncomputable def lengthWeight (β lam h : ℝ) (w : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) h).indicator
    (fun w => ENNReal.ofReal (4 ^ β * max ‖w‖ lam ^ (-β))) w

/-- The pairs of dipoles in the near-bond relation. -/
def nearPairs (M lam : ℝ) : Set ((ℂ × ℂ) × (ℂ × ℂ)) := {p | IsNear M lam p.1 p.2}

/-- `𝟙_{IsNear}`. -/
noncomputable def nearIndicator (M lam : ℝ) (a b : ℂ × ℂ) : ℝ≥0∞ :=
  (nearPairs M lam).indicator 1 (a, b)

/-- The weight of a nonseed with parent `b`. -/
noncomputable def nonseedWeight (M β lam h : ℝ) (a b : ℂ × ℂ) : ℝ≥0∞ :=
  nearIndicator M lam a b * lengthWeight β lam h (a.1 - a.2)

/-- The weight of a seed near the background `(u, v)`. -/
noncomputable def seedWeight (M β lam h : ℝ) {m₁ m₂ : ℕ} (u : Fin m₁ → ℂ × ℂ)
    (v : Fin m₂ → ℂ × ℂ) (a : ℂ × ℂ) : ℝ≥0∞ :=
  ((∑ j, nearIndicator M lam a (u j)) + ∑ j, nearIndicator M lam a (v j)) *
    lengthWeight β lam h (a.1 - a.2)

/-- `par` is a forest towards `S`: a depth decreases along `par` off `S`. -/
def IsForest {k : ℕ} (S : Finset (Fin k)) (par : Fin k → Fin k) : Prop :=
  ∃ dep : Fin k → ℕ, ∀ c, c ∉ S → dep (par c) < dep c

/-- The parent maps of the nonseeds (the identity on the seeds). -/
noncomputable def parentSet {k : ℕ} (S : Finset (Fin k)) : Finset (Fin k → Fin k) :=
  Fintype.piFinset fun c => if c ∈ S then {c} else univ

/-- The seed sets `S` with `k ≤ p |S|`. -/
noncomputable def seedSets (k p : ℕ) : Finset (Finset (Fin k)) :=
  univ.filter fun S => k ≤ p * S.card

open scoped Classical in
/-- The term of a seed set and a parent map. -/
noncomputable def typeThreeTerm (M β lam h : ℝ) {m₁ m₂ k : ℕ} (S : Finset (Fin k))
    (par : Fin k → Fin k) (u : Fin m₁ → ℂ × ℂ) (v : Fin m₂ → ℂ × ℂ) (w : Fin k → ℂ × ℂ) :
    ℝ≥0∞ :=
  (if IsForest S par then 1 else 0) * ((∏ s ∈ S, seedWeight M β lam h u v (w s)) *
    ∏ c ∈ Sᶜ, nonseedWeight M β lam h (w c) (w (par c)))

/-! ### The integrands -/

open scoped Classical in
/-- The integrand of `Z^{(1)}_{bad,m}`. -/
noncomputable def typeOneIntegrand (p₀ : ℕ) (β lam ε₀ : ℝ) (Nₐ m : ℕ) (u : Fin m → ℂ × ℂ) :
    ℝ≥0∞ :=
  (boxPi Nₐ m).indicator (fun u =>
    (if badPointsTypeOne p₀ β lam ε₀ u = univ ∧ StablePairs u then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ u)) u

open scoped Classical in
/-- The integrand of `Z^{(2)}_{bad,m}`. -/
noncomputable def typeTwoIntegrand (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ m : ℕ)
    (v : Fin m → ℂ × ℂ) : ℝ≥0∞ :=
  (boxPi Nₐ m).indicator (fun v =>
    (if typeTwoBad Nₐ p₀ β lam M ε₀ v = univ ∧ StablePairs v then 1 else 0) *
      ENNReal.ofReal (dipoleWeight χ β lam v)) v

open scoped Classical in
/-- The integrand of `Z_{bad,N₁,N₂,N₃}`. -/
noncomputable def typedIntegrand (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ n : ℕ)
    (V₁ V₂ V₃ : Finset (Fin n)) (d : Fin n → ℂ × ℂ) : ℝ≥0∞ :=
  (boxPi Nₐ n).indicator (fun d =>
    (if badPointsTypeOne p₀ β lam ε₀ d = V₁ ∧ typeTwoBad Nₐ p₀ β lam M ε₀ d = V₂ ∧
        typeThreeBad Nₐ p₀ β lam M ε₀ d = V₃ ∧ StablePairs d then 1 else 0) *
      ENNReal.ofReal (typeOneWeight p₀ β lam ε₀ d)) d

theorem typeOnePartitionFunction_eq_lintegral (p₀ : ℕ) (β lam ε₀ : ℝ) (Nₐ m : ℕ) :
    typeOnePartitionFunction p₀ β lam ε₀ Nₐ m =
      ∫⁻ u, typeOneIntegrand p₀ β lam ε₀ Nₐ m u :=
  (lintegral_indicator (measurableSet_boxPi Nₐ m) _).symm

theorem typeTwoPartitionFunction_eq_lintegral (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ)
    (Nₐ m : ℕ) :
    typeTwoPartitionFunction χ p₀ β lam M ε₀ Nₐ m =
      ∫⁻ v, typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ m v :=
  (lintegral_indicator (measurableSet_boxPi Nₐ m) _).symm

theorem typedBadPartitionFunction_eq_lintegral (p₀ : ℕ) (β lam M ε₀ : ℝ) (Nₐ n : ℕ)
    (V₁ V₂ V₃ : Finset (Fin n)) :
    typedBadPartitionFunction p₀ β lam M ε₀ Nₐ n V₁ V₂ V₃ =
      ∫⁻ d, typedIntegrand p₀ β lam M ε₀ Nₐ n V₁ V₂ V₃ d :=
  (lintegral_indicator (measurableSet_boxPi Nₐ n) _).symm

/-! ### The radius weights off type 1 -/

section Radius

variable {p₀ : ℕ} {β lam ε₀ : ℝ} {d : Fin n → ℂ × ℂ}

/-- Off type 1, `(τ^+ τ^-)^{-β/2} = max(λ, r/4)^{-β} ≤ 4^β max(r, λ)^{-β}`, and `r ≤ h`. -/
theorem radiusWeight_le_of_not_mem (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (hz : NoIsosceles (fun k => (d k).1)) (hz' : NoIsosceles (fun k => (d k).2)) {i : Fin n}
    (hi : i ∉ badPointsTypeOne p₀ β lam ε₀ d) :
    dipoleLength d i ≤ cutoff p₀ β lam ε₀ ∧
      (radiusPlus p₀ β lam ε₀ d i * radiusMinus p₀ β lam ε₀ d i) ^ (-(β / 2)) ≤
        4 ^ β * max (dipoleLength d i) lam ^ (-β) := by
  obtain ⟨hr, hp, hm⟩ := radius_of_not_mem hq hh hz hz' hi
  refine ⟨hr, ?_⟩
  rw [hp, hm]
  set m := max lam (dipoleLength d i / 4)
  have hm0 : 0 < m := lt_max_of_lt_left hlam
  have hR : 0 < max (dipoleLength d i) lam := lt_max_of_lt_right hlam
  have h1 : (m * m) ^ (-(β / 2)) = m ^ (-β) := by
    rw [Real.mul_rpow hm0.le hm0.le, ← Real.rpow_add hm0]
    ring_nf
  have h2 : max (dipoleLength d i) lam / 4 ≤ m := by
    rcases le_total (dipoleLength d i) lam with h | h
    · rw [max_eq_right h]
      exact (by linarith : lam / 4 ≤ lam).trans (le_max_left _ _)
    · rw [max_eq_left h]
      exact le_max_right _ _
  rw [h1]
  calc m ^ (-β) ≤ (max (dipoleLength d i) lam / 4) ^ (-β) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
    _ = 4 ^ β * max (dipoleLength d i) lam ^ (-β) := by
        rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        field_simp

/-- `4^β max(|w|, λ)^{-β} ≤ 12^β e^{β g_λ(w)}`. -/
theorem four_rpow_le_exp {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hlam : 0 < lam) (hβ : 0 ≤ β)
    (w : ℂ) :
    4 ^ β * max ‖w‖ lam ^ (-β) ≤ 12 ^ β * Real.exp (β * smearedKernel χ lam w) := by
  have hm : 0 < max ‖w‖ lam := lt_max_of_lt_right hlam
  have hg := neg_log_three_sub_le_smearedKernel hχ hlam w
  have h3 : max ‖w‖ lam ^ (-β) ≤ 3 ^ β * Real.exp (β * smearedKernel χ lam w) := by
    have : Real.exp (β * (-Real.log 3 - Real.log (max ‖w‖ lam))) ≤
        Real.exp (β * smearedKernel χ lam w) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hg hβ)
    have heq : Real.exp (β * (-Real.log 3 - Real.log (max ‖w‖ lam))) =
        (3 : ℝ) ^ (-β) * max ‖w‖ lam ^ (-β) := by
      rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hm, ← Real.exp_add]
      ring_nf
    rw [heq] at this
    have h3pos : (0 : ℝ) < 3 ^ β := by positivity
    calc max ‖w‖ lam ^ (-β) = 3 ^ β * ((3 : ℝ) ^ (-β) * max ‖w‖ lam ^ (-β)) := by
          rw [← mul_assoc, ← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ 3 ^ β * Real.exp (β * smearedKernel χ lam w) :=
          mul_le_mul_of_nonneg_left this h3pos.le
  calc 4 ^ β * max ‖w‖ lam ^ (-β) ≤ 4 ^ β * (3 ^ β * Real.exp (β * smearedKernel χ lam w)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 12 ^ β * Real.exp (β * smearedKernel χ lam w) := by
        rw [← mul_assoc, ← Real.mul_rpow (by norm_num) (by norm_num)]
        norm_num

end Radius

/-- A product over `V` is the product over its increasing enumeration. -/
theorem prod_orderEmbOfFin {α : Type*} [CommMonoid α] (V : Finset (Fin n)) (f : Fin n → α) :
    ∏ i ∈ V, f i = ∏ a : Fin V.card, f (V.orderEmbOfFin rfl a) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ V rfl]
  rw [Finset.prod_map]
  rfl

/-! ### The pointwise bound -/

section Pointwise

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ} {Nₐ : ℕ} {V₁ V₂ V₃ : Finset (Fin n)}

/-- **The pointwise bound of Lemma 5.39** (Steps 1–3), for a configuration without
isosceles coincidences. -/
theorem typedIntegrand_le (hχ : IsMollifier χ) (hq : 1 ≤ clusterThreshold p₀ β)
    (hh : 0 < cutoff p₀ β lam ε₀) (hlam : 0 < lam) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (h12 : Disjoint V₁ V₂) (h13 : Disjoint V₁ V₃) (h23 : Disjoint V₂ V₃)
    (hcov : V₁ ∪ V₂ ∪ V₃ = univ) (d : Fin n → ℂ × ℂ)
    (hz : NoIsosceles (fun k => (d k).1)) (hz' : NoIsosceles (fun k => (d k).2)) :
    typedIntegrand p₀ β lam M ε₀ Nₐ n V₁ V₂ V₃ d ≤
      typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card (d ∘ V₁.orderEmbOfFin rfl) *
        ENNReal.ofReal ((12 ^ β) ^ V₂.card) *
        typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card (d ∘ V₂.orderEmbOfFin rfl) *
        ∑ S ∈ seedSets V₃.card (pBeta p₀ β), ∑ par ∈ parentSet S,
          typeThreeTerm M β lam (cutoff p₀ β lam ε₀) S par (d ∘ V₁.orderEmbOfFin rfl)
            (d ∘ V₂.orderEmbOfFin rfl) (d ∘ V₃.orderEmbOfFin rfl) := by
  classical
  unfold typedIntegrand
  by_cases hbox : d ∈ boxPi Nₐ n
  swap
  · rw [Set.indicator_of_notMem hbox]; exact zero_le
  rw [Set.indicator_of_mem hbox]
  split_ifs with hE
  swap
  · rw [zero_mul]; exact zero_le
  obtain ⟨h1, h2, h3, hst⟩ := hE
  rw [one_mul]
  set e₁ := V₁.orderEmbOfFin rfl with he₁
  set e₂ := V₂.orderEmbOfFin rfl with he₂
  set e₃ := V₃.orderEmbOfFin rfl with he₃
  set h := cutoff p₀ β lam ε₀ with hhdef
  set f : Fin n → ℝ := fun i =>
    (radiusPlus p₀ β lam ε₀ d i * radiusMinus p₀ β lam ε₀ d i) ^ (-(β / 2)) with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => Real.rpow_nonneg (mul_nonneg
    (hlam.le.trans (le_clusterRadius lam i)) (hlam.le.trans (le_clusterRadius lam i))) _
  have hboxk : ∀ V : Finset (Fin n), d ∘ V.orderEmbOfFin rfl ∈ boxPi Nₐ V.card := fun V =>
    Set.mem_univ_pi.2 fun a => Set.mem_univ_pi.1 hbox _
  have hstk : ∀ V : Finset (Fin n), StablePairs (d ∘ V.orderEmbOfFin rfl) := fun V a b hab =>
    hst _ _ ((V.orderEmbOfFin rfl).strictMono hab)
  have hnot1 : ∀ i, i ∉ V₁ → i ∉ badPointsTypeOne p₀ β lam ε₀ d := fun i hi => h1 ▸ hi
  -- the split of the weight
  have hsplit : typeOneWeight p₀ β lam ε₀ d =
      (∏ i ∈ V₁, f i) * (∏ i ∈ V₂, f i) * ∏ i ∈ V₃, f i := by
    unfold typeOneWeight
    rw [← Finset.prod_union h12, ← Finset.prod_union (Finset.disjoint_union_left.2 ⟨h13, h23⟩),
      hcov]
  -- `V₁`
  have hm1 : univ.map e₁.toEmbedding = V₁ := Finset.map_orderEmbOfFin_univ V₁ rfl
  have hU1 : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e₁.toEmbedding) := by
    refine clusterUnion_of_split hq hh hz hz' (Or.inr ?_)
    rw [hm1, h1]; exact Finset.disjoint_sdiff
  have hI1 : badPointsTypeOne p₀ β lam ε₀ (d ∘ e₁) = univ :=
    Finset.eq_univ_of_forall fun a => (mem_badPointsTypeOne_comp_iff e₁ hU1 a).2
      (by rw [h1]; exact Finset.orderEmbOfFin_mem V₁ rfl a)
  have hW1 : typeOneIntegrand p₀ β lam ε₀ Nₐ V₁.card (d ∘ e₁) =
      ENNReal.ofReal (∏ i ∈ V₁, f i) := by
    unfold typeOneIntegrand
    rw [Set.indicator_of_mem (hboxk V₁), ite_eq_left ⟨hI1, hstk V₁⟩, one_mul, prod_orderEmbOfFin V₁ f]
    unfold typeOneWeight
    congr 1
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [radiusPlus_comp e₁ hU1, radiusMinus_comp e₁ hU1]
  -- `V₂`
  have hm2 : univ.map e₂.toEmbedding = V₂ := Finset.map_orderEmbOfFin_univ V₂ rfl
  have hU2 : ClusterUnion p₀ β lam ε₀ d (univ \ univ.map e₂.toEmbedding) := by
    refine clusterUnion_of_split hq hh hz hz' (Or.inl ?_)
    rw [hm2, h1]
    intro i hi
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ i, Finset.disjoint_left.1 h12 hi⟩
  have hI2 : typeTwoBad Nₐ p₀ β lam M ε₀ (d ∘ e₂) = univ :=
    typeTwoBad_comp_eq_univ Nₐ e₂ (by rw [hm2, h2]) hU2
  have hW2 : typeTwoIntegrand χ p₀ β lam M ε₀ Nₐ V₂.card (d ∘ e₂) =
      ENNReal.ofReal (dipoleWeight χ β lam (d ∘ e₂)) := by
    unfold typeTwoIntegrand
    rw [Set.indicator_of_mem (hboxk V₂), ite_eq_left ⟨hI2, hstk V₂⟩, one_mul]
  have hw2 : ∏ i ∈ V₂, f i ≤ (12 ^ β) ^ V₂.card * dipoleWeight χ β lam (d ∘ e₂) := by
    rw [prod_orderEmbOfFin V₂ f]
    unfold dipoleWeight
    rw [show ((12 : ℝ) ^ β) ^ V₂.card = ∏ _a : Fin V₂.card, (12 : ℝ) ^ β by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun a _ => hf0 _) fun a _ => ?_
    have hi : e₂ a ∉ V₁ := Finset.disjoint_right.1 h12 (Finset.orderEmbOfFin_mem V₂ rfl a)
    obtain ⟨-, hle⟩ := radiusWeight_le_of_not_mem hq hh hlam hβ hz hz' (hnot1 _ hi)
    exact hle.trans (four_rpow_le_exp hχ hlam hβ _)
  -- `V₃`: the seeds
  set w := d ∘ e₃ with hw
  set J := nearSet M lam d (V₁ ∪ V₂) with hJ
  set S : Finset (Fin V₃.card) := univ.filter fun a => e₃ a ∈ J with hSdef
  have hm3 : univ.map e₃.toEmbedding = V₃ := Finset.map_orderEmbOfFin_univ V₃ rfl
  have hJ3 : J ⊆ V₃ := nearSet_subset_typeThree h1 h2 h3
  have hSmap : S.map e₃.toEmbedding = J := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, hSdef]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hj
      have : j ∈ Set.range e₃ := by rw [Finset.range_orderEmbOfFin]; exact hJ3 hj
      obtain ⟨a, rfl⟩ := this
      exact ⟨a, hj, rfl⟩
  have hS : S ∈ seedSets V₃.card (pBeta p₀ β) := by
    unfold seedSets
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := card_typeThree_le h1 h2 h3
    rw [← hJ, ← hSmap, Finset.card_map] at this
    exact this
  -- `V₃`: the forest of the nonseeds
  have hV3U : V₃ ⊆ univ \ V₁ := fun i hi =>
    Finset.mem_sdiff.2 ⟨Finset.mem_univ i, Finset.disjoint_right.1 h13 hi⟩
  have hreach : ∀ a, ∃ s ∈ (S : Set (Fin V₃.card)), (classGraph M lam w univ).Reachable a s := by
    intro a
    have ha3 : e₃ a ∈ V₃ := Finset.orderEmbOfFin_mem V₃ rfl a
    obtain ⟨-, j, hj⟩ := (mem_typeThree_iff h1 h2 h3).1 ha3
    rw [Finset.mem_inter] at hj
    have hcl : multipoleClassOn M lam d (univ \ V₁) (e₃ a) =
        (multipoleClassOn M lam w univ a).map e₃.toEmbedding := by
      have h' := classOn_comp_map (d := d) (M := M) (lam := lam) e₃.toEmbedding univ a
      rw [hm3] at h'
      exact (h'.trans (classOn_of_union hV3U
        (fun i hi => classOn_subset_typeThree h1 h2 h3 hi) ha3)).symm
    rw [hcl] at hj
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 hj.1
    refine ⟨s, ?_, mem_classOn_iff.1 hs⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, hSdef]
    exact hj.2
  obtain ⟨par, dep, hpar⟩ := exists_forest (classGraph M lam w univ)
    (S : Set (Fin V₃.card)) hreach
  set par' : Fin V₃.card → Fin V₃.card := fun c => if c ∈ S then c else par c with hpar'
  have hpar'mem : par' ∈ parentSet S := by
    unfold parentSet
    rw [Fintype.mem_piFinset]
    intro c
    by_cases hc : c ∈ S
    · simp [hpar', hc]
    · simp [hpar', hc]
  have hforest : IsForest S par' := ⟨dep, fun c hc => by
    simp only [hpar', ite_eq_right hc]
    exact (hpar c (by exact_mod_cast hc)).2⟩
  have hnear : ∀ c, c ∉ S → IsNear M lam (w c) (w (par' c)) := by
    intro c hc
    have hadj := (hpar c (by exact_mod_cast hc)).1
    rw [SimpleGraph.fromRel_adj] at hadj
    simp only [hpar', ite_eq_right hc]
    unfold IsNear
    refine min4_le_of_linked hM ?_
    rcases hadj.2 with h' | h'
    · exact Or.inl h'.2.2
    · exact Or.inr h'.2.2
  have hseed : ∀ s ∈ S, (1 : ℝ≥0∞) ≤ (∑ j, nearIndicator M lam (w s) ((d ∘ e₁) j)) +
      ∑ j, nearIndicator M lam (w s) ((d ∘ e₂) j) := by
    intro s hs
    have hsJ : e₃ s ∈ J := (Finset.mem_filter.1 hs).2
    have hsJ' := hsJ
    rw [hJ] at hsJ'
    unfold nearSet at hsJ'
    rw [Finset.mem_filter] at hsJ'
    obtain ⟨-, j, hjB, hnr⟩ := hsJ'
    rcases Finset.mem_union.1 hjB with hj1 | hj2
    · have : j ∈ Set.range e₁ := by rw [Finset.range_orderEmbOfFin]; exact hj1
      obtain ⟨b, rfl⟩ := this
      have h1' : nearIndicator M lam (w s) ((d ∘ e₁) b) = 1 := by
        unfold nearIndicator
        rw [Set.indicator_of_mem (show (w s, (d ∘ e₁) b) ∈ nearPairs M lam from hnr)]
        rfl
      calc (1 : ℝ≥0∞) = nearIndicator M lam (w s) ((d ∘ e₁) b) := h1'.symm
        _ ≤ ∑ j, nearIndicator M lam (w s) ((d ∘ e₁) j) :=
            Finset.single_le_sum (f := fun j => nearIndicator M lam (w s) ((d ∘ e₁) j))
              (fun _ _ => zero_le) (Finset.mem_univ b)
        _ ≤ _ := le_self_add
    · have : j ∈ Set.range e₂ := by rw [Finset.range_orderEmbOfFin]; exact hj2
      obtain ⟨b, rfl⟩ := this
      have h1' : nearIndicator M lam (w s) ((d ∘ e₂) b) = 1 := by
        unfold nearIndicator
        rw [Set.indicator_of_mem (show (w s, (d ∘ e₂) b) ∈ nearPairs M lam from hnr)]
        rfl
      calc (1 : ℝ≥0∞) = nearIndicator M lam (w s) ((d ∘ e₂) b) := h1'.symm
        _ ≤ ∑ j, nearIndicator M lam (w s) ((d ∘ e₂) j) :=
            Finset.single_le_sum (f := fun j => nearIndicator M lam (w s) ((d ∘ e₂) j))
              (fun _ _ => zero_le) (Finset.mem_univ b)
        _ ≤ _ := le_add_self
  -- `V₃`: the weights
  have hlen : ∀ a, ENNReal.ofReal (f (e₃ a)) ≤ lengthWeight β lam h ((w a).1 - (w a).2) := by
    intro a
    have hi : e₃ a ∉ V₁ := Finset.disjoint_right.1 h13 (Finset.orderEmbOfFin_mem V₃ rfl a)
    obtain ⟨hr, hle⟩ := radiusWeight_le_of_not_mem hq hh hlam hβ hz hz' (hnot1 _ hi)
    unfold lengthWeight
    rw [Set.indicator_of_mem (by rw [Metric.mem_closedBall, dist_zero_right]; exact hr)]
    exact ENNReal.ofReal_le_ofReal hle
  have hw3 : ENNReal.ofReal (∏ i ∈ V₃, f i) ≤
      typeThreeTerm M β lam h S par' (d ∘ e₁) (d ∘ e₂) w := by
    unfold typeThreeTerm
    rw [ite_eq_left hforest, one_mul, prod_orderEmbOfFin V₃ f,
      ENNReal.ofReal_prod_of_nonneg (fun a _ => hf0 _), ← Finset.prod_mul_prod_compl S]
    refine mul_le_mul' (Finset.prod_le_prod fun s hs => ?_) (Finset.prod_le_prod fun c hc => ?_)
    · unfold seedWeight
      calc ENNReal.ofReal (f (e₃ s)) ≤ lengthWeight β lam h ((w s).1 - (w s).2) := hlen s
        _ = 1 * lengthWeight β lam h ((w s).1 - (w s).2) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_left (hseed s hs) _
    · unfold nonseedWeight
      have : nearIndicator M lam (w c) (w (par' c)) = 1 := by
        unfold nearIndicator
        rw [Set.indicator_of_mem (show (w c, w (par' c)) ∈ nearPairs M lam from
          hnear c (Finset.mem_compl.1 hc))]
        rfl
      rw [this, one_mul]
      exact hlen c
  have hsum : typeThreeTerm M β lam h S par' (d ∘ e₁) (d ∘ e₂) w ≤
      ∑ S ∈ seedSets V₃.card (pBeta p₀ β), ∑ par ∈ parentSet S,
        typeThreeTerm M β lam h S par (d ∘ e₁) (d ∘ e₂) w :=
    (Finset.single_le_sum (f := fun par => typeThreeTerm M β lam h S par (d ∘ e₁) (d ∘ e₂) w)
      (fun _ _ => zero_le) hpar'mem).trans
      (Finset.single_le_sum (f := fun S => ∑ par ∈ parentSet S,
        typeThreeTerm M β lam h S par (d ∘ e₁) (d ∘ e₂) w) (fun _ _ => zero_le) hS)
  have hp1 : 0 ≤ ∏ i ∈ V₁, f i := Finset.prod_nonneg fun i _ => hf0 i
  have hp2 : 0 ≤ ∏ i ∈ V₂, f i := Finset.prod_nonneg fun i _ => hf0 i
  rw [hsplit, ENNReal.ofReal_mul (mul_nonneg hp1 hp2), ENNReal.ofReal_mul hp1, hW1, hW2]
  have h2' : ENNReal.ofReal (∏ i ∈ V₂, f i) ≤
      ENNReal.ofReal ((12 ^ β) ^ V₂.card) * ENNReal.ofReal (dipoleWeight χ β lam (d ∘ e₂)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hw2
  calc ENNReal.ofReal (∏ i ∈ V₁, f i) * ENNReal.ofReal (∏ i ∈ V₂, f i) *
        ENNReal.ofReal (∏ i ∈ V₃, f i)
      ≤ ENNReal.ofReal (∏ i ∈ V₁, f i) * (ENNReal.ofReal ((12 ^ β) ^ V₂.card) *
          ENNReal.ofReal (dipoleWeight χ β lam (d ∘ e₂))) *
          ∑ S ∈ seedSets V₃.card (pBeta p₀ β), ∑ par ∈ parentSet S,
            typeThreeTerm M β lam h S par (d ∘ e₁) (d ∘ e₂) w :=
        mul_le_mul' (mul_le_mul_right h2' _) (hw3.trans hsum)
    _ = _ := by ring

end Pointwise

end BadPointTypes

end MultipoleBKT

end
