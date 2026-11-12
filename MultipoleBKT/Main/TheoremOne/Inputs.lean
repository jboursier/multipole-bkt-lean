/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.Inputs
public import MultipoleBKT.Frozen.BoundedBlockPartitions
public import MultipoleBKT.Frozen.TruncatedPartitionWeight
public import MultipoleBKT.Frozen.ConnectionGraph
public import MultipoleBKT.Frozen.Ursell
public import MultipoleBKT.Frozen.MayerTerm
public import MultipoleBKT.Frozen.Mayer

/-!
# Theorem 1 from the gates: the inputs

The proof of Theorem 1 uses Proposition 5.45, Lemma 5.46
, the bound (4.41) of Proposition 4.23 and the existence of the limits `𝗄^dip` (eq. (2.34); Lemma 4.26). The paper uses Theorem 2(2) only inside the proof of
Proposition 5.45, whose frozen statement already carries it, so Theorem 2 is not
an input here.

The types of the frozen statements are restated here to avoid import cycles:

* `MultipoleBKT.TheoremTwo.Prop423Statement` is the type of
 `MultipoleBKT.proposition_4_23`;
* `MultipoleBKT.TheoremOne.Prop545Statement` is the type of
 `MultipoleBKT.proposition_5_45`;
* `MultipoleBKT.TheoremOne.Theorem1Statement` is the type of
 `MultipoleBKT.theorem_1`;
* `MultipoleBKT.TheoremOne.DipoleLimitsExist` is the existence, for every mollifier `χ` and
 `β > 2`, of a coefficient family with the `Tendsto` clauses of (2.34), for every `λ ∈ (0,1)`.
 Lemma 4.26 supplies this input in `MultipoleBKT.TheoremOne.dipoleLimitsExist`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open TwoComponentCoulomb (box)

@[expose] public section

namespace MultipoleBKT

namespace TheoremOne

open scoped Classical in
/-- The type of the frozen statement `MultipoleBKT.proposition_5_45` (verbatim). -/
def Prop545Statement : Prop :=
    ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (p₀ : ℕ), 1 ≤ p₀ → ∀ (β : ℝ), 2 < β →
    let p := pBeta p₀ β
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          let zId : ℝ≥0∞ := ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
              {c | stableMatching c = Equiv.refl (Fin N)},
            ENNReal.ofReal (Real.exp (-β * energy χ lam c))
          let zHat : ℝ := ∑ π ∈ boundedBlockPartitions N p, truncatedPartitionWeight χ N β lam M p π
          0 < zId ∧ zId < ∞ ∧ 0 < zHat ∧
            |Real.log zId.toReal - Real.log zHat| ≤ C * N * errorRate p₀ β lam

open scoped Classical in
/-- The type of the frozen statement `MultipoleBKT.theorem_1` (verbatim). -/
def Theorem1Statement : Prop :=
    ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (p₀ : ℕ), 1 ≤ p₀ → ∀ (β : ℝ), 2 < β →
    ∃ kdip : ℝ → ℕ → ℝ,
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        kdip lam 0 = 0 ∧ kdip lam 1 = 0 ∧
        ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
          Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
            (𝓝 (kdip lam k))) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          let cluster : ℕ+ → ℝ := fun n =>
            1 / (n : ℕ).factorial *
              ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                  (fun V => (connectionGraph V).Connected ∧
                    ∀ i, 2 ≤ (V i).card ∧ (V i).card ≤ pBeta p₀ β),
                (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ)
          0 < partitionFunction χ N β lam ∧ partitionFunction χ N β lam < ∞ ∧
          Summable (fun n => ‖cluster n‖) ∧
          |Real.log (partitionFunction χ N β lam).toReal
              - (2 * N * Real.log N
                + N * ((2 - β) * Real.log lam + Real.log (dipoleConstant χ β) - 1))
              - ∑' n, cluster n|
            ≤ C * N * errorRate p₀ β lam) ∧
      (∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β →
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ → |kdip lam k| ≤ C * lam ^ (2 * (k - 1))) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ →
          Summable (fun nk : ℕ+ × ℕ+ => ‖mayerTerm (pBeta p₀ β) (kdip lam) nk.1 nk.2‖) ∧
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            let cluster : ℕ+ → ℝ := fun n =>
              1 / (n : ℕ).factorial *
                ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                    (fun V => (connectionGraph V).Connected ∧
                      ∀ i, (V i).card ≤ pBeta p₀ β),
                  (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ)
            Summable (fun n => ‖cluster n‖) ∧
            |∑' n, cluster n - (-N * mayer (pBeta p₀ β) (kdip lam))|
              ≤ C * N * errorRate p₀ β lam)

/-- **Existence of the limits `𝗄^dip`** (eq. (2.34); Lemma 4.26, for every `λ ∈ (0,1)`): for every mollifier
`χ` and `β > 2` there is a coefficient family `kdip` with exactly the `Tendsto` clauses of
Theorem 1's limit clause. This is an input of the conditional assembly `theorem_1_of_gates`,
not a gate. -/
def DipoleLimitsExist : Prop :=
  ∀ (χ : ℂ → ℝ), IsMollifier χ → ∀ (β : ℝ), 2 < β →
    ∃ kdip : ℝ → ℕ → ℝ, ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ k : ℕ, 2 ≤ k → (k : ℕ∞) ≤ pStar β → ∀ V : Finset ℕ, V.card = k →
        Tendsto (fun N : ℕ => (N : ℝ) ^ (k - 1) * dipoleActivity χ N β lam V) atTop
          (𝓝 (kdip lam k))

end TheoremOne

end MultipoleBKT

end
