/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.IntDipole
public import MultipoleBKT.Appendix.MultipoleIntegral.Bounds
public import MultipoleBKT.Limits.DipoleLimit

/-!
# The bound (4.41) on `𝖪^dip_{β,λ}` for `1 < |V| ≤ p*(β)`

Proposition 4.23,
the bound (4.41): for `1 < |V| = k ≤ p*(β)`,
`|𝖪^dip_{β,λ}(V)| ≤ C λ^{2(k-1)} / N^{k-1}` with `C` depending on `β, k` (and `M`, which `𝖪^dip`
does not involve).

**Proof** (proof of Proposition 4.23). `𝖪^dip(V) = ∑_{E ∈ 𝒢_c(V)} I_{dip,∞}(V; E) / (N C_{β,λ})^k`
(`SmallIntegral.dipoleActivity_eq_sum_dipoleIntegral`), Lemma A.5 bounds
`|I_{dip,∞}(V; E)| ≤ C N λ^{(2-β)k + 2(k-1)}` (`SmallIntegral.lemma_A_5`), and
`C_{β,λ} ≥ 𝒵_β λ^{2-β}/2` for `N` large (Lemma 4.12). The number of graphs is bounded in terms of
`k` after relabelling `V` onto `{0, …, k-1}` (`dipoleActivity_congr_card`).

* `dipoleActivity_bound`: (4.41), stated exactly as the third conjunct of the frozen gate
  `MultipoleBKT.proposition_4_23`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BoundedLower

open MeasureTheory Set Finset Filter

/-- **Proposition 4.23, (4.41)** (Proposition 4.23; proof of Proposition 4.23),
in exactly the form of the third conjunct of the frozen gate `MultipoleBKT.proposition_4_23`: for
`2 ≤ k ≤ p*(β)` there are `C > 0` and `λ₀ ∈ (0, 1]` such that for every `λ ∈ (0, λ₀)` there is
`N₀` with `|𝖪^dip_{β,λ}(V)| ≤ C λ^{2(k-1)} / N^{k-1}` for all `N ≥ N₀` and all `V ⊆ [N]` with
`|V| = k`. Here `λ₀ = 1`. -/
theorem dipoleActivity_bound (χ : ℂ → ℝ) (hχ : IsMollifier χ) (β : ℝ) (hβ : 2 < β) :
    ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ V : Finset ℕ, V ⊆ Finset.range N → V.card = k →
            |dipoleActivity χ N β lam V| ≤ C * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
  classical
  intro k hk2 hkp
  have hk1 : 1 ≤ k := by omega
  obtain ⟨CA, hCA, hA⟩ := SmallIntegral.lemma_A_5 hχ hβ hkp
  set W := range k
  set Gs := (Finset.univ : Finset (SimpleGraph W)).filter
    (fun E => E.Connected ∧ E.edgeSet.Nonempty)
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨(Gs.card + 1) * CA * (2 / Z) ^ k, by positivity, 1, one_pos, le_rfl,
    fun lam hlam _ => ?_⟩
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 (eventually_half_le_dipoleNormalization hχ hβ hlam)
  refine ⟨max N₂ 1, fun N hN V _ hVk => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hCN := hN₂ N (le_trans (le_max_left _ _) hN)
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hℓk : (lam ^ (2 - β)) ^ k = lam ^ ((2 - β) * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  set Q := (N : ℝ) * dipoleNormalization χ N β lam
  have hQ : (N : ℝ) * (Z / 2) * lam ^ (2 - β) ≤ Q := by
    simp only [Q, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hNpos.le
    calc Z / 2 * lam ^ (2 - β) = 1 / 2 * Z * lam ^ (2 - β) := by ring
      _ ≤ _ := hCN
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  set T : ℝ := lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1)
  have hT : 0 ≤ T := by positivity
  -- relabel `V` onto `{0, …, k-1}`
  rw [Limits.dipoleActivity_congr_card hχ hlam hN1 (show V.card = W.card by rw [hVk, card_range]),
    SmallIntegral.dipoleActivity_eq_sum_dipoleIntegral hχ hlam hN1 W, card_range]
  -- each graph, by Lemma A.5
  have hterm : ∀ E ∈ Gs, |(Q⁻¹) ^ k * SmallIntegral.dipoleIntegral χ N β lam W E| ≤
      CA * (2 / Z) ^ k * T := by
    intro E hE
    rw [abs_mul, abs_of_nonneg (pow_nonneg (inv_nonneg.2 hQ0.le) k)]
    have hI := hA W (card_range k) E (mem_filter.1 hE).2.1 lam hlam N
    rw [← hℓk] at hI
    have h := MultipoleIntegral.gate_upper_algebra hk1 hNpos hℓ hZ hQ hI (abs_nonneg _)
    refine h.trans_eq ?_
    simp only [T]
    ring
  calc |∑ E ∈ Gs, (Q⁻¹) ^ k * SmallIntegral.dipoleIntegral χ N β lam W E|
      ≤ ∑ E ∈ Gs, |(Q⁻¹) ^ k * SmallIntegral.dipoleIntegral χ N β lam W E| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ E ∈ Gs, CA * (2 / Z) ^ k * T := sum_le_sum hterm
    _ = Gs.card * (CA * (2 / Z) ^ k * T) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Gs.card + 1) * (CA * (2 / Z) ^ k * T) := by
        gcongr
        linarith
    _ = (Gs.card + 1) * CA * (2 / Z) ^ k * lam ^ (2 * (k - 1)) / (N : ℝ) ^ (k - 1) := by
        simp only [T]
        ring

end BoundedLower

end MultipoleBKT

end
