/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKTAudit.Proposition543.Definitions
public import MultipoleBKT.Frozen.Proposition543

/-!
# Proposition 5.43 (large deviations upper bound): the proof

The challenge's statement, proved from `proposition_5_43` of the library. The shared
copied definitions unfold to the library's definitions, so Lean checks the direct
application of the library theorem.

For the nested bad-point definitions, `statementType` gives type ascriptions that
compare the shared functions before applying them. Its local functions expand to
Definitions 5.2–5.5 and the good-multipole count of Proposition 5.43. These ascriptions
erase from the proof term, leaving the direct application of the library theorem.
-/

-- Compare the recursive definitions by ordinary unfolding.
set_option smartUnfolding false

-- Well-founded recursion is marked irreducible by default.
attribute [local semireducible]
  MultipoleBKTAudit.Proposition543.MultipoleBKT.sameSignClustering
  _root_.MultipoleBKT.sameSignClustering

@[expose] public section

namespace MultipoleBKTAudit.Proposition543

open MeasureTheory Filter Topology
open scoped ENNReal
open _root_.MultipoleBKTAudit.Proposition543.TwoComponentCoulomb (box)

namespace MultipoleBKT

private noncomputable def statementType
    (sameSignClustering : {N : ℕ} → ℕ → ℝ → (Fin N → ℂ) → (Fin N → ℝ) →
      Finset (Fin N) → Finset (Finset (Fin N) × ℝ))
    (truncationScale : ℕ → ℝ → ℝ → ℝ)
    (clusterThreshold : ℕ → ℝ → ℕ)
    (pBeta : ℕ → ℝ → ℕ)
    (alphaExponent : ℝ → ℝ)
    (multipoleClassOn : {N : ℕ} → ℝ → ℝ → (Fin N → ℂ × ℂ) →
      Finset (Fin N) → Fin N → Finset (Fin N))
    (stableMatching : {N : ℕ} → (Fin N → ℂ × ℂ) → Equiv.Perm (Fin N))
    (multipoleGraph : {N : ℕ} → ℝ → ℝ → (Fin N → ℂ × ℂ) → SimpleGraph (Fin N))
    (χ : ℂ → ℝ) (p₀ : ℕ) (β : ℝ) : Prop :=
  let badPointsTypeOne {N : ℕ} (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
      Finset (Fin N) :=
    -- `J^{1,±}` for the clustering of the charges `z`
    let J : (Fin N → ℂ) → Finset (Fin N) := fun z =>
      Finset.univ.filter (fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖) ∪
        ((sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam) z
            (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).filter
          (fun Sτ => Sτ.1.card = clusterThreshold p₀ β + 1)).biUnion Prod.fst
    J (fun i => (d i).1) ∪ J (fun i => (d i).2)
  let badPointsTypeTwo {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
      Finset (Fin N) :=
    let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
    -- `I^{2,1}_bad`
    U.filter (fun i => pBeta p₀ β < (multipoleClassOn M lam d U i).card) ∪
      -- `I^{2,2}_bad = ⋃_{k ∈ [p(β)]} I^{2,2,k}_bad`
      (Finset.Icc 1 (pBeta p₀ β)).biUnion fun k =>
        if ε₀ ^ (-alphaExponent β) * N * lam ^ (2 * (k - 1)) <
            ((U.filter fun i => (multipoleClassOn M lam d U i).card = k).card : ℝ)
        then U.filter fun i => (multipoleClassOn M lam d U i).card = k
        else ∅
  let badPointsTypeThree {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
      Finset (Fin N) :=
    let I₁₂ := badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d
    let U := Finset.univ \ badPointsTypeOne p₀ β lam ε₀ d
    -- `J^3_bad`
    let J₃ := (Finset.univ \ I₁₂).filter fun i => ∃ j ∈ I₁₂,
      min (min ‖(d i).1 - (d j).1‖ ‖(d i).1 - (d j).2‖) (min ‖(d i).2 - (d j).1‖ ‖(d i).2 - (d j).2‖)
        ≤ M * max ‖(d i).1 - (d i).2‖ lam
    (Finset.univ \ I₁₂).filter fun i => (multipoleClassOn M lam d U i ∩ J₃).Nonempty
  let badPoints {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
      Finset (Fin N) :=
    badPointsTypeOne p₀ β lam ε₀ d ∪ badPointsTypeTwo p₀ β lam M ε₀ d ∪
      badPointsTypeThree p₀ β lam M ε₀ d
  let goodPoints {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
      Finset (Fin N) :=
    Finset.univ \ badPoints p₀ β lam M ε₀ d
  let goodMultipoleCount {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (c : Fin N → ℂ × ℂ)
      (k : ℕ) : ℕ :=
    Nat.card {C : (multipoleGraph M lam c).ConnectedComponent // Nat.card C.supp = k ∧
      C.supp ⊆ ↑(goodPoints p₀ β lam M ε₀ fun i => ((c i).1, (c (stableMatching c i)).2))}
    let p := pBeta p₀ β
    -- `M` large (`M > max(20, 3^p)`; Proposition 5.20)
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    -- coefficient families pinned by the limits (2.45), (2.46)
    ∀ msf : ℝ → ℕ → ℝ, ∀ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) →
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X)))) →
      -- "for every fixed `t ≥ 1` and for `ε₀, λ` small enough depending on `β, M, p, t`"
      -- `∀ t`, then every `ε₀ ∈ (0, ε₁(t))`, then `C`, `λ₀(ε₀)`, `N₀(λ)`
      ∀ t : ℝ, 1 ≤ t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        -- `O_{β,M,p,ε₀,t}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            -- absolute summability of the series in `ℐ`;
            -- on `⋃_{x ∈ [0,1]} Δ_{p,x}`, the domain on which this gate evaluates
            -- `ℐ` (`n/N ∈ Δ_{p,x}`, `x = 1 - ∑ k n_k/N`)
            (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex p x, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            -- `N₀` uniform in the profile
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N →
              -- (5.56) for `k = i + 1 ∈ {2, …, p}`
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              -- `I_bad` of `c` computed on its matched dipoles
              -- `log ∫ ≤ X` as `∫ ≤ e^X`
              -- the integral as `∫⁻` over `(Λ²)^N ∩ 𝒜`
              -- `ℐ` evaluated at `n/N ∈ Δ_{p,x}` by the formula of Definition 2.15
              ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                  {c | ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
                ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
                    fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c))
                ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                    + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                    - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                    + C * N * errorRate p₀ β lam))

open scoped Classical in
/-- **Proposition 5.43**, for a
profile `n` (`n i = n_{i+1}`) with `n_1 + 2n_2 + ⋯ + p n_p ≤ N` satisfying (5.56), the event
`𝒜 = {𝒩_1^good = n_1, …, 𝒩_p^good = n_p}` and the weight `e^{t|I_bad|}`. -/
theorem proposition_5_43
    -- `χ` and `p₀` outermost
    (χ : ℂ → ℝ) (hχ : IsMollifier χ) (p₀ : ℕ) (hp₀ : 1 ≤ p₀)
    (β : ℝ) (hβ : 2 < β) :
    let p := pBeta p₀ β
    -- `M` large (`M > max(20, 3^p)`; Proposition 5.20)
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
    -- coefficient families pinned by the limits (2.45), (2.46)
    ∀ msf : ℝ → ℕ → ℝ, ∀ kmult : ℝ → (ℕ →₀ ℕ) → ℝ,
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ S : Finset ℕ, 1 ≤ S.card → (S.card : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ (S.card - 1) * multipolePartitionFunction χ N β lam M S) atTop
            (𝓝 (msf lam S.card))) →
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → ((∑ S ∈ X, S.card : ℕ) : ℕ∞) ≤ pStar β →
          Tendsto (fun N : ℕ =>
              (N : ℝ) ^ ((X.card : ℤ) - 1) * multipoleActivity χ N β lam M X) atTop
            (𝓝 (kmult lam (blockProfile X)))) →
      -- "for every fixed `t ≥ 1` and for `ε₀, λ` small enough depending on `β, M, p, t`"
      -- `∀ t`, then every `ε₀ ∈ (0, ε₁(t))`, then `C`, `λ₀(ε₀)`, `N₀(λ)`
      ∀ t : ℝ, 1 ≤ t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ →
        -- `O_{β,M,p,ε₀,t}(Nδ)` as `C`, then `λ₀`, `N₀(λ)`
        ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
          ∀ lam : ℝ, 0 < lam → lam < lam₀ →
            -- absolute summability of the series in `ℐ`;
            -- on `⋃_{x ∈ [0,1]} Δ_{p,x}`, the domain on which this gate evaluates
            -- `ℐ` (`n/N ∈ Δ_{p,x}`, `x = 1 - ∑ k n_k/N`)
            (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ γ ∈ simplex p x, Summable fun nm : ℕ+ × (Fin p → ℕ) =>
              ‖rateSeriesTerm p (kmult lam) γ nm.1 nm.2‖) ∧
            -- `N₀` uniform in the profile
            ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : Fin p → ℕ,
              ∑ i : Fin p, ((i : ℕ) + 1) * n i ≤ N →
              -- (5.56) for `k = i + 1 ∈ {2, …, p}`
              (∀ i : Fin p, 1 ≤ (i : ℕ) →
                (n i : ℝ) ≤ ε₀ ^ (-alphaExponent β) * lam ^ (2 * (i : ℕ)) * N) →
              -- `I_bad` of `c` computed on its matched dipoles
              -- `log ∫ ≤ X` as `∫ ≤ e^X`
              -- the integral as `∫⁻` over `(Λ²)^N ∩ 𝒜`
              -- `ℐ` evaluated at `n/N ∈ Δ_{p,x}` by the formula of Definition 2.15
              ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
                  {c | ∀ i : Fin p, goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i},
                ENNReal.ofReal (Real.exp (t * (badPoints p₀ β lam M ε₀
                    fun i => ((c i).1, (c (stableMatching c i)).2)).card)) *
                  ENNReal.ofReal (Real.exp (-β * energy χ lam c))
                ≤ ENNReal.ofReal (Real.exp (N * Real.log N + Real.log (N.factorial : ℝ)
                    + N * (2 - β) * Real.log lam + N * Real.log (dipoleConstant χ β)
                    - N * rateFunction p (msf lam) (kmult lam) (fun i => (n i : ℝ) / N)
                    + C * N * errorRate p₀ β lam)) :=
  by exact
    (show statementType @sameSignClustering @truncationScale @clusterThreshold @pBeta
        @alphaExponent @multipoleClassOn @stableMatching @multipoleGraph χ p₀ β from
      (show statementType @_root_.MultipoleBKT.sameSignClustering
          @_root_.MultipoleBKT.truncationScale @_root_.MultipoleBKT.clusterThreshold
          @_root_.MultipoleBKT.pBeta @_root_.MultipoleBKT.alphaExponent
          @_root_.MultipoleBKT.multipoleClassOn @_root_.MultipoleBKT.stableMatching
          @_root_.MultipoleBKT.multipoleGraph χ p₀ β from
        _root_.MultipoleBKT.proposition_5_43 χ hχ p₀ hp₀ β hβ))

end MultipoleBKT

end MultipoleBKTAudit.Proposition543

end
