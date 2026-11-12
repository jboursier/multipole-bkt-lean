/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.Relabel
public import MultipoleBKT.Frozen.MultipoleCount

/-!
# The reduction to the identity matching on the event `𝒜` (proof of Proposition 4.62, Step 1)

The proof of Proposition 4.62:
"since labels do not matter,
`∫_𝒜 e^{-βF_λ} dX_N dY_N = N! ∫_𝒜 𝟙_{σ_N = Id} e^{-βF_λ} dX_N dY_N`".

The event `𝒜 = {𝒩_1 = n_1, …, 𝒩_p = n_p} ∩ ⋂ᵢ {|x_i - y_{σ_N(i)}| ≤ ε₀ R̄}` (eq. (4.24)) depends
on a configuration only through its matched dipoles `(x_i, y_{σ_N(i)})ᵢ` (`matchedDipoles`): the
multipole graph does (`multipoleGraph_eq_of_matchedDipoles_eq`), hence so do the counts `𝒩_k`. The
relabeling `T_σ : (x_i, y_i)ᵢ ↦ (x_i, y_{σ(i)})ᵢ` of
`MultipoleBKT.TheoremOne.relabelNeg` maps `{σ_N = σ}` onto `{σ_N = Id}` off a null set and keeps the
matched dipoles. We prove the identity for every event `E` of this kind
(`setLIntegral_inter_eq_factorial_mul`); no measurability of `E` is needed, since the events
`{σ_N = σ}` are measurable and partition the configuration space.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace LowerBoundLDP

open TheoremOne

variable {N : ℕ}

/-- The matched dipoles `(x_i, y_{σ_N(i)})ᵢ` of a configuration. -/
noncomputable def matchedDipoles (c : Fin N → ℂ × ℂ) : Fin N → ℂ × ℂ :=
  fun i => ((c i).1, (c (stableMatching c i)).2)

/-- The multipole graph depends only on the matched dipoles. -/
theorem multipoleGraph_eq_of_matchedDipoles_eq {M lam : ℝ} {c c' : Fin N → ℂ × ℂ}
    (h : matchedDipoles c = matchedDipoles c') : multipoleGraph M lam c = multipoleGraph M lam c' := by
  have h' : ∀ i, ((c i).1, (c (stableMatching c i)).2) = ((c' i).1, (c' (stableMatching c' i)).2) :=
    fun i => congrFun h i
  unfold multipoleGraph
  simp only [h']

/-- The multipole counts `𝒩_k` depend only on the matched dipoles. -/
theorem multipoleCount_eq_of_matchedDipoles_eq {M lam : ℝ} {c c' : Fin N → ℂ × ℂ}
    (h : matchedDipoles c = matchedDipoles c') (k : ℕ) :
    multipoleCount M lam c k = multipoleCount M lam c' k := by
  unfold multipoleCount
  rw [multipoleGraph_eq_of_matchedDipoles_eq h]

/-- On `{σ_N = σ}`, the relabeling `T_σ` keeps the matched dipoles (when `σ_N(T_σ c) = Id`). -/
theorem matchedDipoles_relabelNeg {σ : Equiv.Perm (Fin N)} {c : Fin N → ℂ × ℂ}
    (hσ : stableMatching c = σ) (hId : stableMatching (relabelNeg σ c) = Equiv.refl _) :
    matchedDipoles (relabelNeg σ c) = matchedDipoles c := by
  funext i
  simp only [matchedDipoles, hId, hσ, Equiv.refl_apply, relabelNeg_apply]

/-- Off a null set, `c ∈ {σ_N = σ} ∩ B ∩ E` iff `T_σ c ∈ {σ_N = Id} ∩ B ∩ E`, for `B` the box and an
event `E` that depends only on the matched dipoles. -/
theorem ae_inter_eq_preimage (σ : Equiv.Perm (Fin N)) {E : Set (Fin N → ℂ × ℂ)}
    (hE : ∀ c c', matchedDipoles c = matchedDipoles c' → (c ∈ E ↔ c' ∈ E)) :
    ({c : Fin N → ℂ × ℂ | stableMatching c = σ} ∩
        ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ E)) =ᵐ[volume]
      relabelNeg σ ⁻¹' ({c | stableMatching c = Equiv.refl _} ∩
        ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ E)) := by
  filter_upwards [ae_injective_norm_sub (ι := Fin N)] with c hc
  simp only [eq_iff_iff]
  have hiff := stableMatching_relabelNeg_eq_refl_iff σ hc
  constructor
  · rintro ⟨hσ, hB, hcE⟩
    have hId := hiff.mpr hσ
    refine ⟨hId, (relabelNeg_mem_box_iff σ c).mpr hB, ?_⟩
    exact (hE _ _ (matchedDipoles_relabelNeg hσ hId)).mpr hcE
  · rintro ⟨hId, hB, hcE⟩
    have hσ := hiff.mp hId
    refine ⟨hσ, (relabelNeg_mem_box_iff σ c).mp hB, ?_⟩
    exact (hE _ _ (matchedDipoles_relabelNeg hσ hId)).mp hcE

/-- **The reduction to the identity matching** (proof of Proposition 4.62): for an event
`E` that depends only on the matched dipoles,
`∫_{(Λ²)^N ∩ E} e^{-βF_λ} = N! ∫_{(Λ²)^N ∩ E ∩ {σ_N = Id}} e^{-βF_λ}`. -/
theorem setLIntegral_inter_eq_factorial_mul (χ : ℂ → ℝ) (β lam : ℝ)
    {E : Set (Fin N → ℂ × ℂ)}
    (hE : ∀ c c', matchedDipoles c = matchedDipoles c' → (c ∈ E ↔ c' ∈ E)) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ E,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      (N.factorial : ℝ≥0∞) *
        ∫⁻ c in ((Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ E) ∩
            {c | stableMatching c = Equiv.refl _},
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  set A := (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ E
  set f : (Fin N → ℂ × ℂ) → ℝ≥0∞ := fun c => ENNReal.ofReal (Real.exp (-β * energy χ lam c))
  set B : Equiv.Perm (Fin N) → Set (Fin N → ℂ × ℂ) := fun σ => {c | stableMatching c = σ}
  have hBm : ∀ σ, MeasurableSet (B σ) := fun σ => measurableSet_stableMatching_eq σ
  have hBd : Pairwise (Function.onFun Disjoint B) := by
    intro σ τ hστ
    refine Set.disjoint_left.mpr fun c hcσ hcτ => hστ ?_
    exact hcσ.symm.trans hcτ
  have hBu : (⋃ σ, B σ) = Set.univ := by
    ext c
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨stableMatching c, rfl⟩
  -- the decomposition of `∫_A` along the events `{σ_N = σ}`
  have hdec : volume.restrict A = Measure.sum fun σ => volume.restrict (B σ ∩ A) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := volume.restrict A), ← hBu,
      Measure.restrict_iUnion hBd hBm]
    simp only [Measure.restrict_restrict (hBm _)]
  -- each event carries the integral of `{σ_N = Id}`
  have hσ : ∀ σ : Equiv.Perm (Fin N), ∫⁻ c in B σ ∩ A, f c = ∫⁻ c in B (Equiv.refl _) ∩ A, f c := by
    intro σ
    rw [setLIntegral_congr (ae_inter_eq_preimage σ hE)]
    refine Eq.trans ?_ ((measurePreserving_relabelNeg σ).setLIntegral_comp_preimage_emb
      (relabelNeg σ).measurableEmbedding _ _)
    simp only [f, energy_relabelNeg]
    rfl
  have hsum : ∫⁻ c in A, f c = ∑ σ : Equiv.Perm (Fin N), ∫⁻ c in B σ ∩ A, f c := by
    rw [hdec, lintegral_sum_measure, tsum_fintype]
  rw [hsum, Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, Set.inter_comm (B _)]

end LowerBoundLDP

end MultipoleBKT

end
