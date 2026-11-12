/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Components

/-!
# Step 1 of Lemma 4.54: `|𝒰(X')| ≤ C^{|V_{X'}|} 𝓛_C(X')` (eq. (4.92))

Step 1 of the proof of Lemma 4.54, equation (4.92).

* `abs_sum_odd_even_le` (the combinatorial core, for abstract weights): if on `ℰ^inter(X)`
  `|f| ≤ C a`, `0 ≤ g ≤ C b` and `b ≤ a`, with `C ≥ 1`, then
  `|∑_{E₁ ∈ Eul^X} ∑_{E₂} ∏_{E₁} f ∏_{E₂} g| ≤ C^{|V_X|} groupSeries C a b X ∏_{ℰ^inter(X)} e^{C a}`.
  Each `E₁` is split into its connected components relative to `X`
  (`MultipoleBKT.AbsoluteLower.comps`, eq. (4.91)); the sum over `E₂` is bounded by the Penrose
  resummation (`sum_evenEdges_le`); the components of `E₁` and their parts determine `E₁`, which
  injects the sum over `E₁` into the sum over the disjoint families of groups and the connected
  Eulerian edge sets of the groups.
* `abs_oddEvenSum_le` (eq. (4.92)): there is `C ≥ 1` depending only on `β` and the mollifier
  `χ` such that, when every dipole of `V_{X'}` has length at most `ε₀ R̄`,
  `|𝒰(X')| ≤ C^{|V_{X'}|} 𝓛_C(X')`, for `𝒰` built on the interaction `ṽ`
  (`MultipoleBKT.upperBoundInteraction`). The bounds `|a^ṽ| ≤ C a^abs`, `0 ≤ b^ṽ ≤ C b^abs` on
  `𝓑^c` are Remark 4.30 (`MultipoleBKT.Parity.remark_4_30`), and `b^abs ≤ a^abs` on `𝓑^c`
  (stated implicitly in the paper) is `absEvenWeight_le_absOddWeight`.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Multipole Hierarchical SetPartition Parity

section Core

open scoped Classical

variable {X : Finset (Finset ℕ)}

/-- The sum over `E₁ ∈ Eul^X` grouped by components is bounded by the sum over the disjoint
families of groups of the products of the group sums. -/
theorem sum_relEulerianPairs_le (hX : IsSubpartition X) (k : ℕ × ℕ → ℝ)
    (hk : ∀ p, 0 ≤ k p) (h : Finset (Finset (Finset ℕ)) → ℝ) (hh : ∀ 𝒱, 0 ≤ h 𝒱) :
    ∑ E₁ ∈ relEulerianPairs X, (∏ p ∈ E₁, k p) * h (comps X E₁) ≤
      ∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
        (∏ Y ∈ 𝒱, ∑ E ∈ relEulerianConnectedPairs Y, ∏ p ∈ E, k p) * h 𝒱 := by
  have hmaps : ∀ E₁ ∈ relEulerianPairs X,
      comps X E₁ ∈ disjointFamilies X (fun Y => 2 ≤ Y.card) := fun E₁ hE₁ =>
    comps_mem_disjointFamilies hX (mem_relEulerianPairs.1 hE₁).1
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun 𝒱 _ => ?_
  -- the fibre over `𝒱`
  set Fib := (relEulerianPairs X).filter fun E₁ => comps X E₁ = 𝒱 with hFib
  have hE : ∀ E₁ ∈ Fib, E₁ ⊆ interPairs X := fun E₁ hE₁ =>
    (mem_relEulerianPairs.1 (mem_filter.1 hE₁).1).1
  have hcomps : ∀ E₁ ∈ Fib, comps X E₁ = 𝒱 := fun E₁ hE₁ => (mem_filter.1 hE₁).2
  set Ψ : Finset (ℕ × ℕ) → ((Y : Finset (Finset ℕ)) → Y ∈ 𝒱 → Finset (ℕ × ℕ)) :=
    fun E₁ Y _ => E₁ ∩ interPairs Y with hΨ
  have hΨinj : Set.InjOn Ψ Fib := by
    intro E₁ hE₁ E₁' hE₁' heq
    rw [eq_biUnion_comps hX (hE E₁ hE₁), eq_biUnion_comps hX (hE E₁' hE₁'),
      hcomps E₁ hE₁, hcomps E₁' hE₁']
    refine biUnion_congr rfl fun Y hY => ?_
    exact congrFun (congrFun heq Y) hY
  have hΨmem : ∀ E₁ ∈ Fib, Ψ E₁ ∈ 𝒱.pi fun Y => relEulerianConnectedPairs Y := by
    intro E₁ hE₁
    refine mem_pi.2 fun Y hY => ?_
    have hY' : Y ∈ comps X E₁ := (hcomps E₁ hE₁).symm ▸ hY
    exact inter_mem_relEulerianConnectedPairs hX (mem_filter.1 hE₁).1 hY'
  have hterm : ∀ E₁ ∈ Fib, (∏ p ∈ E₁, k p) * h (comps X E₁) =
      (∏ Y ∈ 𝒱.attach, ∏ p ∈ Ψ E₁ Y.1 Y.2, k p) * h 𝒱 := by
    intro E₁ hE₁
    rw [prod_eq_prod_comps hX (hE E₁ hE₁), hcomps E₁ hE₁]
    congr 1
    exact (prod_attach 𝒱 fun Y => ∏ p ∈ E₁ ∩ interPairs Y, k p).symm
  have hnn : ∀ ψ ∈ 𝒱.pi fun Y => relEulerianConnectedPairs Y,
      0 ≤ (∏ Y ∈ 𝒱.attach, ∏ p ∈ ψ Y.1 Y.2, k p) * h 𝒱 := fun ψ _ =>
    mul_nonneg (prod_nonneg fun _ _ => prod_nonneg fun p _ => hk p) (hh 𝒱)
  calc ∑ E₁ ∈ Fib, (∏ p ∈ E₁, k p) * h (comps X E₁)
      = ∑ ψ ∈ Fib.image Ψ, (∏ Y ∈ 𝒱.attach, ∏ p ∈ ψ Y.1 Y.2, k p) * h 𝒱 := by
        rw [sum_image hΨinj]
        exact sum_congr rfl hterm
    _ ≤ ∑ ψ ∈ 𝒱.pi fun Y => relEulerianConnectedPairs Y,
          (∏ Y ∈ 𝒱.attach, ∏ p ∈ ψ Y.1 Y.2, k p) * h 𝒱 := by
        refine sum_le_sum_of_subset_of_nonneg (fun ψ hψ => ?_) fun ψ hψ _ => hnn ψ hψ
        obtain ⟨E₁, hE₁, rfl⟩ := mem_image.1 hψ
        exact hΨmem E₁ hE₁
    _ = (∏ Y ∈ 𝒱, ∑ E ∈ relEulerianConnectedPairs Y, ∏ p ∈ E, k p) * h 𝒱 := by
        rw [← sum_mul, prod_sum]

/-- **The combinatorial core of Step 1 of Lemma 4.54** (eqs. (4.91)–(4.92)): if on `ℰ^inter(X)`
`|f| ≤ C a`, `0 ≤ g ≤ C b` and `b ≤ a`, with `C ≥ 1` and `a, b ≥ 0`, then
`|∑_{E₁ ∈ Eul^X} ∑_{E₂ : E₁ ∩ E₂ = ∅, E₁ ∪ E₂ ∈ 𝖤^X} ∏_{E₁} f ∏_{E₂} g|
≤ C^{|V_X|} groupSeries C a b X ∏_{ℰ^inter(X)} e^{C a}`. -/
theorem abs_sum_odd_even_le (hX : IsSubpartition X) {C : ℝ} (hC : 1 ≤ C)
    (f g a b : ℕ × ℕ → ℝ) (ha : ∀ p, 0 ≤ a p) (hb : ∀ p, 0 ≤ b p)
    (hf : ∀ p ∈ interPairs X, |f p| ≤ C * a p) (hg0 : ∀ p ∈ interPairs X, 0 ≤ g p)
    (hg : ∀ p ∈ interPairs X, g p ≤ C * b p) (hba : ∀ p ∈ interPairs X, b p ≤ a p) :
    |∑ E₁ ∈ relEulerianPairs X, ∑ E₂ ∈ (interPairs X).powerset.filter
        (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X),
        (∏ p ∈ E₁, f p) * ∏ p ∈ E₂, g p| ≤
      C ^ (X.biUnion id).card * groupSeries C a b X *
        ∏ p ∈ interPairs X, Real.exp (C * a p) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  set n := (X.biUnion id).card
  set Q := ∏ p ∈ interPairs X, Real.exp (C * a p) with hQ
  have hQ0 : 0 ≤ Q := prod_nonneg fun _ _ => (Real.exp_pos _).le
  set h : Finset (Finset (Finset ℕ)) → ℝ :=
    fun 𝒱 => ∑ T ∈ relTreePairs₀ (coarsen X 𝒱), ∏ p ∈ T, b p with hh
  have hh0 : ∀ 𝒱, 0 ≤ h 𝒱 := fun 𝒱 => sum_nonneg fun T _ => prod_nonneg fun p _ => hb p
  -- the bound for one `E₁`
  have hone : ∀ E₁ ∈ relEulerianPairs X,
      |∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X),
          (∏ p ∈ E₁, f p) * ∏ p ∈ E₂, g p| ≤
        C ^ n * ((∏ p ∈ E₁, C * a p) * h (comps X E₁)) * Q := by
    intro E₁ hE₁
    have hE := (mem_relEulerianPairs.1 hE₁).1
    have hGX : ∀ Y ∈ comps X E₁, Y ⊆ X := fun _ hY => comps_subset hY
    have hY₀ := isSubpartition_coarsen_comps hX hE
    rw [← mul_sum, abs_mul, abs_of_nonneg (sum_nonneg fun E₂ hE₂ => prod_nonneg fun p hp =>
      hg0 p (mem_powerset.1 (mem_filter.1 hE₂).1 hp))]
    have hf' : |∏ p ∈ E₁, f p| ≤ ∏ p ∈ E₁, C * a p := by
      rw [abs_prod]
      exact prod_le_prod₀ (fun _ _ => abs_nonneg _) fun p hp => hf p (hE hp)
    have hg' := sum_evenEdges_le hX hE₁ g hg0
    have htree : ∑ T ∈ relTreePairs₀ (coarsen X (comps X E₁)), ∏ p ∈ T, g p ≤
        C ^ n * h (comps X E₁) := by
      rw [hh, mul_sum]
      refine sum_le_sum fun T hT => ?_
      have hTI : T ⊆ interPairs X :=
        (subset_interPairs_of_mem_relTreePairs₀ hY₀ hT).trans (interPairs_coarsen_subset hGX)
      have hTn : T.card ≤ n := by
        have := card_le_of_mem_relTreePairs₀ hY₀ hT
        rwa [biUnion_coarsen hGX] at this
      calc ∏ p ∈ T, g p ≤ ∏ p ∈ T, C * b p :=
            prod_le_prod₀ (fun p hp => hg0 p (hTI hp)) fun p hp => hg p (hTI hp)
        _ = C ^ T.card * ∏ p ∈ T, b p := by rw [prod_mul_distrib, prod_const]
        _ ≤ C ^ n * ∏ p ∈ T, b p :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hTn) (prod_nonneg fun p _ => hb p)
    have hexp : ∏ p ∈ interPairs X, (1 + g p) ≤ Q := by
      refine prod_le_prod₀ (fun p hp => by have := hg0 p hp; linarith) fun p hp => ?_
      calc 1 + g p ≤ 1 + C * a p := by
            have := hg p hp
            have := hba p hp
            nlinarith
        _ ≤ Real.exp (C * a p) := by
            have := Real.add_one_le_exp (C * a p)
            linarith
    calc |∏ p ∈ E₁, f p| * ∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X), ∏ p ∈ E₂, g p
        ≤ (∏ p ∈ E₁, C * a p) * ((C ^ n * h (comps X E₁)) * Q) := by
          refine mul_le_mul hf' (hg'.trans ?_) (sum_nonneg fun E₂ hE₂ => prod_nonneg fun p hp =>
            hg0 p (mem_powerset.1 (mem_filter.1 hE₂).1 hp))
            (prod_nonneg fun p _ => mul_nonneg hC0 (ha p))
          refine mul_le_mul htree hexp (prod_nonneg fun p hp => by
            have := hg0 p hp
            linarith) ?_
          exact mul_nonneg (pow_nonneg hC0 _) (hh0 _)
      _ = C ^ n * ((∏ p ∈ E₁, C * a p) * h (comps X E₁)) * Q := by ring
  calc _ ≤ ∑ E₁ ∈ relEulerianPairs X, |∑ E₂ ∈ (interPairs X).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X),
          (∏ p ∈ E₁, f p) * ∏ p ∈ E₂, g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ E₁ ∈ relEulerianPairs X, C ^ n * ((∏ p ∈ E₁, C * a p) * h (comps X E₁)) * Q :=
        sum_le_sum hone
    _ = C ^ n * (∑ E₁ ∈ relEulerianPairs X, (∏ p ∈ E₁, C * a p) * h (comps X E₁)) * Q := by
        rw [← sum_mul, ← mul_sum]
    _ ≤ C ^ n * (∑ 𝒱 ∈ disjointFamilies X (fun Y => 2 ≤ Y.card),
          (∏ Y ∈ 𝒱, ∑ E ∈ relEulerianConnectedPairs Y, ∏ p ∈ E, C * a p) * h 𝒱) * Q := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC0 _)) hQ0
        exact sum_relEulerianPairs_le hX (fun p => C * a p) (fun p => mul_nonneg hC0 (ha p)) h hh0
    _ = C ^ n * groupSeries C a b X * Q := by
        rw [groupSeries_eq_sum hX]
        rfl

end Core

/-! ### Eq. (4.92) -/

section Bound

open scoped Classical

variable {χ : ℂ → ℝ}

/-- **Step 1 of Lemma 4.54** (eq. (4.92) in the proof of Lemma 4.54): there is `C ≥ 1`
depending only on `β` and the mollifier `χ` such that for `0 < λ ≤ ε₀ R`, `M ≥ 1`, every
subpartition `X'` and every configuration `c` whose dipoles of `V_{X'}` have length at most `ε₀ R`
(the support of `𝖯_X^{-,ε₀}`), `|𝒰(X')| ≤ C^{|V_{X'}|} 𝓛_C(X')`, for the interaction
`ṽ = MultipoleBKT.upperBoundInteraction χ λ ε₀ R` (`R` in the role of `R̄_{β,λ}`). -/
theorem abs_oddEvenSum_le (hχ : IsMollifier χ) (β : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ lam ε₀ R M : ℝ, 0 < lam → lam ≤ ε₀ * R → 1 ≤ M →
      ∀ {X' : Finset (Finset ℕ)}, IsSubpartition X' → ∀ c : ℕ → ℂ × ℂ,
        (∀ i ∈ X'.biUnion id, ‖(c i).1 - (c i).2‖ ≤ ε₀ * R) →
        |oddEvenSum β (upperBoundInteraction χ lam ε₀ R) M lam X' c| ≤
          C ^ (X'.biUnion id).card * eulerMajorant M lam ε₀ R C X' c := by
  obtain ⟨C, hC, h430⟩ := remark_4_30 hχ β
  refine ⟨C, hC, fun lam ε₀ R M hlam hlamR hM X' hX' c hc => ?_⟩
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  by_cases h1 : X'.card ≤ 1
  · rw [oddEvenSum_eq_zero_of_card_le_one h1, eulerMajorant_eq_zero_of_card_le_one h1, abs_zero,
      mul_zero]
  have h2 : 2 ≤ X'.card := by omega
  have hRHS : 0 ≤ C ^ (X'.biUnion id).card * eulerMajorant M lam ε₀ R C X' c :=
    mul_nonneg (pow_nonneg hC0 _) (eulerMajorant_nonneg hC0 X' c)
  by_cases hlink : ∃ p ∈ interPairs X', MultipoleLinked M lam (c p.1) (c p.2)
  · obtain ⟨p, hp, hpl⟩ := hlink
    have h0 : oddEvenSum β (upperBoundInteraction χ lam ε₀ R) M lam X' c = 0 := by
      refine sum_eq_zero fun E₁ _ => sum_eq_zero fun E₂ _ => ?_
      rw [prod_eq_zero (f := fun p => if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)
        hp (ite_eq_left hpl), mul_zero]
    rw [h0, abs_zero]
    exact hRHS
  push Not at hlink
  -- on the event `⋂ 𝓑^c`, the indicators are `1`
  have hind : ∏ p ∈ interPairs X', (if MultipoleLinked M lam (c p.1) (c p.2) then (0 : ℝ) else 1)
      = 1 := prod_eq_one fun p hp => ite_eq_right (hlink p hp)
  have hU : oddEvenSum β (upperBoundInteraction χ lam ε₀ R) M lam X' c =
      ∑ E₁ ∈ relEulerianPairs X', ∑ E₂ ∈ (interPairs X').powerset.filter
        (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets X'),
        (∏ p ∈ E₁, oddBond β (upperBoundInteraction χ lam ε₀ R) (c p.1) (c p.2)) *
          ∏ p ∈ E₂, evenBond β (upperBoundInteraction χ lam ε₀ R) (c p.1) (c p.2) := by
    refine sum_congr rfl fun E₁ _ => sum_congr rfl fun E₂ _ => ?_
    rw [hind, mul_one]
  have hexpU : expUnlinked M lam ε₀ R C X' c =
      ∏ p ∈ interPairs X', Real.exp (C * absOddWeight M lam ε₀ R (c p.1) (c p.2)) := by
    refine prod_congr rfl fun p hp => ?_
    rw [ite_eq_right (hlink p hp), mul_one]
  rw [hU, eulerMajorant_eq_groupSeries h2, hexpU, ← mul_assoc]
  -- the hypotheses of the core on `ℰ^inter(X')`
  have hr : ∀ p ∈ interPairs X',
      max ‖(c p.1).1 - (c p.1).2‖ ‖(c p.2).1 - (c p.2).2‖ ≤ ε₀ * R := by
    intro p hp
    have h12 := interPairs_subset_pairsOn_biUnion X' hp
    exact max_le (hc _ h12.1) (hc _ h12.2)
  refine abs_sum_odd_even_le hX' hC _ _ _ _ (fun _ => absOddWeight_nonneg _ _ _ _ _ _)
    (fun _ => absEvenWeight_nonneg _ _ _ _ _ _) (fun p hp => ?_) (fun p hp => ?_)
    (fun p hp => ?_) (fun p hp => absEvenWeight_le_absOddWeight hM hlam (hlink p hp))
  · have := (h430 lam ε₀ R M hlam hlamR hM (c p.1) (c p.2) (hr p hp)).1
    rwa [oddBondUnlinked, ite_eq_right (hlink p hp)] at this
  · have := evenBondUnlinked_of_not_linked (β := β) (w := upperBoundInteraction χ lam ε₀ R) hM
      (hlink p hp)
    rw [evenBondUnlinked, ite_eq_right (hlink p hp)] at this
    rw [this, Real.cosh_eq]
    linarith [Real.add_one_le_exp (β * upperBoundInteraction χ lam ε₀ R (c p.1) (c p.2)),
      Real.add_one_le_exp (-(β * upperBoundInteraction χ lam ε₀ R (c p.1) (c p.2)))]
  · have := (h430 lam ε₀ R M hlam hlamR hM (c p.1) (c p.2) (hr p hp)).2.1
    rw [evenBondUnlinked, ite_eq_right (hlink p hp)] at this
    exact (le_abs_self _).trans this

end Bound

end AbsoluteLower

end MultipoleBKT

end
