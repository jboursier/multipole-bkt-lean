/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.UpperBoundLDP.Core
public import MultipoleBKT.UpperBound.UpperBoundLDP.RouteNormalization.Entropy

/-!
# Fixed-parameter assembly with the normalization error

The paper: Proposition 5.43. The fixed-choice bound of Lemma 5.16 supplies `N! (N C)^N`.
The logarithmic estimate supplies `K N R̄⁻²`, which the entropy calculation
absorbs into the final coefficient using `R̄⁻² ≤ δ`.
-/

@[expose] public section

open MeasureTheory Finset Filter
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace UpperBoundLDP

open Hierarchical PropFiveFortyFive UpperBound TheoremTwo SetPartition

open scoped Classical in
/-- Internal fixed-parameter assembly after a supplied logarithmic estimate
(Proposition 5.43). -/
theorem bound_at_lambda_upper_of_log_normalization {χ : ℂ → ℝ} (hχ : IsMollifier χ)
    {p₀ : ℕ} {β : ℝ} (hβ : 2 < β)
    {lam M ε₀ t : ℝ} (hlam : 0 < lam) (hM : 0 ≤ M) (hε₀ : 0 < ε₀) (ht : 0 ≤ t)
    {msf : ℕ → ℝ} {kmult : (ℕ →₀ ℕ) → ℝ} {L₀ Cbb t' C₃₈ Kδ KV C K R : ℝ}
    (hb1 : EnergyLowerBound χ L₀)
    (hbb : ∀ {N : ℕ} (V : Finset (Fin N)),
      ∫⁻ Z' in Set.univ.pi (fun _ : V => box N ×ˢ box N),
          ENNReal.ofReal (badWeightZ χ p₀ β lam M ε₀ V (extendBad V Z')) ≤
        ENNReal.ofReal (Real.exp (β * Cbb * V.card)) *
          badPartitionFunction p₀ β lam M ε₀ N V.card)
    (h38 : ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, m ≤ N →
      (N.choose m : ℝ≥0∞) * badPartitionFunction p₀ β lam M ε₀ N m *
          ENNReal.ofReal (Real.exp (t' * m)) ≤
        ENNReal.ofReal ((N * truncatedDipoleNormalization χ N β lam
            (ε₀ * truncationScale p₀ β lam)) ^ m * Real.exp (C₃₈ * N * errorRate p₀ β lam)))
    (ht' : t' = t + β * L₀ + β * Cbb + KV + 1) (hC : C = C₃₈ + Kδ + K + 1)
    (hK : 0 ≤ K) (hRδ : R ≤ errorRate p₀ β lam)
    (hnorm : ∀ᶠ N : ℕ in atTop,
      N * Real.log (cutoffDipoleNormalization χ N p₀ β lam ε₀) -
        (N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)) ≤ K * N * R)
    (hgood : ∀ᶠ N : ℕ in atTop, ∀ n : Fin (pBeta p₀ β) → ℕ,
      ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
      (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
        (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
      ∀ V ∈ (Finset.univ : Finset (Fin N)).powersetCard
          (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i),
        ∀ π ∈ (partitions ((Finset.univ \ V).map Fin.valEmbedding)).filter
            (fun π => (∀ S ∈ π, S.card ≤ pBeta p₀ β) ∧ blockCount (pBeta p₀ β) π = n),
          ∀ Z : Fin N → ℂ × ℂ, AbsoluteUpper.IsFrozenConfig p₀ β lam M ε₀ V Z →
            hatPartitionFunctions χ N p₀ β lam M ε₀ (β * L₀) V Z π *
                clusterSeriesW χ N p₀ β lam M ε₀ (β * L₀) V Z π ≤
              Real.exp (∑ i, (n i : ℝ) * Real.log (msf ((i : ℕ) + 1)) -
                ((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ) - (∑ i, n i : ℕ) : ℝ) *
                  Real.log N -
                N * rateCluster (pBeta p₀ β) kmult (fun i => (n i : ℝ) / N) +
                Kδ * N * errorRate p₀ β lam +
                KV * (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i : ℕ))) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin (pBeta p₀ β) → ℕ,
      ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N →
      (∀ i : Fin (pBeta p₀ β), 1 ≤ (i : ℕ) →
        (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
        ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
            fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
          ENNReal.ofReal (Real.exp (-β * energy χ lam c))
        ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
            + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
            - N * rateFunction (pBeta p₀ β) msf kmult (fun i => (n i : ℝ) / N)
            + C * N * errorRate p₀ β lam)) := by
  have hδ : 0 < errorRate p₀ β lam := TheoremTwo.errorRate_pos hβ hlam
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 + Real.log N ≤ errorRate p₀ β lam * N := by
    filter_upwards [eventually_log_le (errorRate p₀ β lam) hδ 1, eventually_ge_atTop 1]
      with N hN hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hN0 (by linarith)
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (hgood.and (h38.and (hnorm.and (hlogN.and (eventually_ge_atTop 1)))))
  refine ⟨N₀, fun N hN n hn h556 => ?_⟩
  obtain ⟨hgoodN, h38N, hnormN, hlogNN, hN1⟩ := hN₀ N hN
  set N' := ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i with hN'
  have hcut : cutoffDipoleNormalization χ N p₀ β lam ε₀ =
      truncatedDipoleNormalization χ N β lam (ε₀ * truncationScale p₀ β lam) := rfl
  have h38' := h38N (N - N') (Nat.sub_le N N')
  rw [← hcut] at h38'
  have hcore := upper_bound_of_estimates hχ hN1 hβ hlam hM hε₀ hn ht hb1
    (hgoodN n hn h556) hbb h38'
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hCn := cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1
  have hfin := RouteNormalization.upper_entropy_bound_of_log_normalization
    hN1 n hn msf kmult (Kδ := Kδ) (KV := KV)
    (δ := errorRate p₀ β lam) (C₃₈ := C₃₈) (K := K) (R := R) hCn hnormN hK hRδ ht' hlogNN
  rw [hC]
  exact hfin

end UpperBoundLDP

end MultipoleBKT

end
