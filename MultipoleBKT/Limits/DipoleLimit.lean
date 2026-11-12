/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.ProfileIndependence
import MultipoleBKT.Limits.RouteDirect.Multipole

/-!
# The limits of the dipole activities, and Lemma 4.26 in the form of Theorems 1 and 2

See Lemma 4.26,
(4.49) and (4.53).

The dipole limit is the displayed sum of the full singleton-averaged integrals,
divided by the power of the single-dipole integral. Translation averaging applies
to each connected graph before the finite sum and normalization.

* `exists_tendsto_dipoleActivity`: (2.34) for every `λ > 0`, as in Theorem 1.
* `exists_tendsto_multipolePartitionFunction_card`: (2.45) for every `λ > 0`, `M ≥ 0`.
* `exists_limits_multipole`: (2.45) and (2.46) for every `λ > 0`, `M ≥ 1`, as in Theorem 2 (1).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter Topology
open scoped ENNReal

variable {χ : ℂ → ℝ} {N : ℕ} {β lam M : ℝ}

/-! ### `𝖪^dip(V)` depends only on `|V|` -/

open scoped Classical in
/-- An order isomorphism of label sets preserves `𝖪^dip` (the same argument as
`multipolePartitionFunction_congr_orderIso`). -/
theorem dipoleActivity_congr_orderIso (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    {V W : Finset ℕ} (e : V ≃o W) :
    dipoleActivity χ N β lam V = dipoleActivity χ N β lam W := by
  have := isProbabilityMeasure_dipoleMeasure hχ hlam β hN
  rw [dipoleActivity_eq_sum, dipoleActivity_eq_sum]
  have hiso : ∀ E : SimpleGraph V, E ≃g Equiv.simpleGraph e.toEquiv E := fun E =>
    { toEquiv := e.toEquiv
      map_rel_iff' := by
        intro a b
        simp }
  refine Finset.sum_equiv (Equiv.simpleGraph e.toEquiv) (fun E => ?_) (fun E _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr (hiso E).connected_iff ?_
    simp only [SimpleGraph.edgeSet_nonempty, ne_eq]
    refine not_congr ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]
      ext a b
      simp
    · ext a b
      have := congrArg (fun G : SimpleGraph W => G.Adj (e a) (e b)) h
      simpa using this
  · have hmp := measurePreserving_piCongrLeft (fun _ : W => dipoleMeasure χ N β lam) e.toEquiv
    refine Eq.trans ?_ (hmp.integral_comp' (dipoleActivityIntegrand χ β lam _))
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    have happ : ∀ v : V, MeasurableEquiv.piCongrLeft (fun _ => ℂ × ℂ) e.toEquiv c (e v) = c v :=
      fun v => by
        simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
    unfold dipoleActivityIntegrand
    refine Fintype.prod_equiv e.toEquiv _ _ fun i => ?_
    refine Fintype.prod_equiv e.toEquiv _ _ fun j => ?_
    simp only [Equiv.simpleGraph_apply, SimpleGraph.comap_adj, Equiv.symm_apply_apply]
    simp only [RelIso.coe_fn_toEquiv, e.lt_iff_lt, happ]

/-- `𝖪^dip(V)` depends only on `|V|` (for `N ≥ 1`). -/
theorem dipoleActivity_congr_card (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    {V W : Finset ℕ} (h : V.card = W.card) :
    dipoleActivity χ N β lam V = dipoleActivity χ N β lam W :=
  dipoleActivity_congr_orderIso hχ hlam hN
    ((V.orderIsoOfFin rfl).symm.trans (W.orderIsoOfFin h.symm))

/-! ### The limit `𝗆` as a function of the size -/

/-- **Lemma 4.26 (𝗆), in the form of Theorem 2 (1).** For `β > 2` and `M ≥ 0` there is
`𝗆 : (0, ∞) × ℕ → ℝ` with `N^{|S|-1} 𝖬_{β,λ}(S) → 𝗆_{β,λ}(|S|)` for every `λ > 0` and every `S`
with `1 ≤ |S| ≤ p*(β)`. -/
theorem exists_tendsto_multipolePartitionFunction_card (hχ : IsMollifier χ) (hβ : 2 < β)
    (hM : 0 ≤ M) :
    ∃ msf : ℝ → ℕ → ℝ, ∀ lam : ℝ, 0 < lam →
      ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
          (𝓝 (msf lam S.card)) := by
  have key : ∀ (lam : ℝ) (k : ℕ), ∃ m : ℝ, 0 < lam → 1 ≤ k → (k : ℕ∞) ≤ pStar β →
      ∀ S : Finset ℕ, S.card = k →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop (𝓝 m) := by
    intro lam k
    by_cases h : 0 < lam ∧ 1 ≤ k ∧ (k : ℕ∞) ≤ pStar β
    · obtain ⟨m, hm⟩ := exists_tendsto_multipolePartitionFunction hχ hβ h.1 hM h.2.1 h.2.2
      exact ⟨m, fun _ _ _ => hm⟩
    · exact ⟨0, fun hlam hk hkp => absurd ⟨hlam, hk, hkp⟩ h⟩
  choose msf hmsf using key
  exact ⟨msf, fun lam hlam S hS hSp => hmsf lam _ hlam hS hSp S rfl⟩

/-! ### The limit `𝗄^dip` -/

/-- **Lemma 4.26 (𝗄^dip), for one label set.** For `β > 2`, `λ > 0` and `2 ≤ |V| ≤ p*(β)`,
`N^{|V|-1} 𝖪^dip_{β,λ}(V)` converges. -/
theorem exists_tendsto_dipoleActivity_of_card (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    {V : Finset ℕ} (hV : 2 ≤ V.card) (hVp : (V.card : ℕ∞) ≤ pStar β) :
    ∃ c : ℝ, Tendsto (fun N : ℕ => (N : ℝ) ^ (V.card - 1) * dipoleActivity χ N β lam V) atTop
      (𝓝 c) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
  have h := RouteDirect.tendsto_dipoleActivity_relative hχ hβ hlam (⟨i, hi⟩ : V) hVp
  rw [← RouteDirect.dipoleCoefficient_eq_relative hχ hβ hlam (⟨i, hi⟩ : V) hVp] at h
  exact ⟨RouteDirect.dipoleCoefficient χ β lam V ⟨i, hi⟩, h⟩

/-- **Lemma 4.26 (𝗄^dip), in the form of Theorem 1.** For `β > 2` there is
`𝗄^dip : (0, ∞) × ℕ → ℝ`, vanishing at `k = 0, 1`, with `N^{k-1} 𝖪^dip_{β,λ}(V) → 𝗄^dip_{β,λ}(k)`
for every `λ > 0`, every `2 ≤ k ≤ p*(β)` and every `V` with `|V| = k`. -/
theorem exists_tendsto_dipoleActivity (hχ : IsMollifier χ) (hβ : 2 < β) :
    ∃ kdip : ℝ → ℕ → ℝ, ∀ lam : ℝ, 0 < lam →
      kdip lam 0 = 0 ∧ kdip lam 1 = 0 ∧
      ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
          (𝓝 (kdip lam k)) := by
  have key : ∀ (lam : ℝ) (k : ℕ), ∃ c : ℝ, (k ≤ 1 → c = 0) ∧ (0 < lam → 2 ≤ k →
      (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
          (𝓝 c)) := by
    intro lam k
    by_cases h : 0 < lam ∧ 2 ≤ k ∧ (k : ℕ∞) ≤ pStar β
    · obtain ⟨hlam, hk, hkp⟩ := h
      have hr : (Finset.range k).card = k := Finset.card_range k
      obtain ⟨c, hc⟩ := exists_tendsto_dipoleActivity_of_card hχ hβ hlam (V := Finset.range k)
        (by rw [hr]; exact hk) (by rw [hr]; exact hkp)
      refine ⟨c, fun h1 => absurd h1 (by omega), fun _ _ _ V hV => ?_⟩
      rw [hr] at hc
      refine hc.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [dipoleActivity_congr_card hχ hlam hN (hr.trans hV.symm)]
    · exact ⟨0, fun _ => rfl, fun hlam hk hkp => absurd ⟨hlam, hk, hkp⟩ h⟩
  choose kdip hkdip0 hkdip using key
  exact ⟨kdip, fun lam hlam => ⟨hkdip0 lam 0 (by omega), hkdip0 lam 1 le_rfl,
    fun k hk hkp V hV => hkdip lam k hlam hk hkp V hV⟩⟩

/-! ### Theorem 2 (1), existence -/

/-- **Lemma 4.26 (𝗆, 𝗄^mult), in the form of Theorem 2 (1).** For `β > 2` and every `M ≥ 1`
there are `𝗆` and `𝗄^mult` such that, for every `λ > 0`, (2.45) holds for `1 ≤ |S| ≤ p*(β)` and
(2.46) holds for every subpartition `X` with `∑_{S ∈ X} |S| ≤ p*(β)`. (Theorem 2 asks this for
`λ ∈ (0, 1)` and `M ≥ M₀` with some `M₀ > 20`; any `M₀ ≥ 1` works.) -/
theorem exists_limits_multipole (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) :
    ∃ msf : ℝ → ℕ → ℝ, ∃ kmult : ℝ → (ℕ →₀ ℕ) → ℝ, ∀ lam : ℝ, 0 < lam →
      (∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
          (𝓝 (msf lam S.card))) ∧
      (∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
        Tendsto (fun N : ℕ =>
            (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
          (𝓝 (kmult lam (blockProfile X)))) := by
  obtain ⟨msf, hmsf⟩ := exists_tendsto_multipolePartitionFunction_card hχ hβ (by linarith)
  obtain ⟨kmult, hkmult⟩ := RouteDirect.exists_tendsto_multipoleActivity_blockProfile hχ hβ hM
  exact ⟨msf, kmult, fun lam hlam => ⟨hmsf lam hlam, hkmult lam hlam⟩⟩

end Limits

end MultipoleBKT

end
