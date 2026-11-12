/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Matching.Measurable
public import MultipoleBKT.Gibbs.Basic

/-!
# Theorem 1 from the gates: the relabeling identity `Z = N! ∫_{σ_N = Id} e^{-βF}`

The proofs of Proposition 5.45 and Theorem 1 pass from the partition function `Z_{N,β}^λ` to the integral over the configurations whose
stable matching is the identity "by symmetry"; the identity is never stated in the paper. We
prove it:

  `Z_{N,β}^λ = N! ∫_{(Λ²)^N ∩ {σ_N = Id}} e^{-β F_λ}`

(`MultipoleBKT.TheoremOne.partitionFunction_eq_factorial_mul`).

For a permutation `σ`, the relabeling of the negative charges
`T_σ : (x_i, y_i)_i ↦ (x_i, y_{σ(i)})_i` (`relabelNeg`) preserves Lebesgue measure, the box
`(Λ²)^N` and the energy. When the distances `|x_i - y_j|` are pairwise distinct (almost
everywhere, `MultipoleBKT.ae_injective_norm_sub`), the stable matching is characterized by the
absence of blocking pairs for the distance preferences
(`MultipoleBKT.stableMatching_eq_iff_of_injective`), so `σ_N(c) = σ` iff `σ_N(T_σ c) = Id`.
Hence each of the `N!` events `{σ_N = σ}`, which partition the configuration space, carries the
same integral.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT

namespace TheoremOne

variable {N : ℕ}

/-- The relabeling `T_σ : (x_i, y_i)_i ↦ (x_i, y_{σ(i)})_i` of the negative charges, as a
measurable equivalence (through the coordinates `ι ⊕ ι → ℂ`). -/
noncomputable def relabelNeg (σ : Equiv.Perm (Fin N)) :
    (Fin N → ℂ × ℂ) ≃ᵐ (Fin N → ℂ × ℂ) :=
  (configEquivSum (Fin N)).trans
    ((MeasurableEquiv.piCongrLeft (fun _ => ℂ) (Equiv.sumCongr (Equiv.refl _) σ.symm)).trans
      (configEquivSum (Fin N)).symm)

theorem relabelNeg_apply (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) (i : Fin N) :
    relabelNeg σ c i = ((c i).1, (c (σ i)).2) := by
  simp [relabelNeg, configEquivSum, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    MeasurableEquiv.arrowProdEquivProdArrow, MeasurableEquiv.sumPiEquivProdPi,
    Equiv.arrowProdEquivProdArrow, Equiv.sumPiEquivProdPi, Equiv.sumCongr_symm]

theorem measurePreserving_relabelNeg (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (relabelNeg σ) volume volume :=
  ((measurePreserving_configEquivSum (Fin N)).symm _).comp
    ((volume_measurePreserving_piCongrLeft (fun _ => ℂ) _).comp
      (measurePreserving_configEquivSum (Fin N)))

theorem relabelNeg_mem_box_iff (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) :
    relabelNeg σ c ∈ (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ↔
      c ∈ (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) := by
  simp only [Set.mem_univ_pi, Set.mem_prod, relabelNeg_apply]
  constructor
  · intro h i
    refine ⟨(h i).1, ?_⟩
    have := (h (σ.symm i)).2
    rwa [Equiv.apply_symm_apply] at this
  · intro h i
    exact ⟨(h i).1, (h (σ i)).2⟩

/-- The energy is invariant under the relabeling of the negative charges. -/
theorem energy_relabelNeg (χ : ℂ → ℝ) (lam : ℝ) (σ : Equiv.Perm (Fin N))
    (c : Fin N → ℂ × ℂ) : energy χ lam (relabelNeg σ c) = energy χ lam c := by
  rw [energy_eq_sum_smearedKernel, energy_eq_sum_smearedKernel]
  simp only [relabelNeg_apply]
  congr 2
  set g := smearedKernel χ lam
  have h1 : ∀ i : Fin N, ∑ j, g ((c (σ j)).2 - (c i).1) = ∑ j, g ((c j).2 - (c i).1) := fun i =>
    Equiv.sum_comp σ (fun j => g ((c j).2 - (c i).1))
  have h2 : ∑ i, ∑ j, g ((c j).1 - (c (σ i)).2) = ∑ i, ∑ j, g ((c j).1 - (c i).2) :=
    Equiv.sum_comp σ (fun i => ∑ j, g ((c j).1 - (c i).2))
  have h3 : ∑ i, ∑ j, g ((c (σ j)).2 - (c (σ i)).2) = ∑ i, ∑ j, g ((c j).2 - (c i).2) := by
    rw [Equiv.sum_comp σ (fun i => ∑ j, g ((c (σ j)).2 - (c i).2))]
    exact Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => g ((c j).2 - (c i).2))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h2, h3, Finset.sum_congr rfl fun i _ => h1 i]

/-- Off a null set, `σ_N(c) = σ` iff `σ_N(T_σ c) = Id`. -/
theorem stableMatching_relabelNeg_eq_refl_iff (σ : Equiv.Perm (Fin N)) {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) :
    stableMatching (relabelNeg σ c) = Equiv.refl _ ↔ stableMatching c = σ := by
  have hc' : Function.Injective fun p : Fin N × Fin N =>
      ‖(relabelNeg σ c p.1).1 - (relabelNeg σ c p.2).2‖ := by
    intro p q hpq
    simp only [relabelNeg_apply] at hpq
    have := hc (a₁ := (p.1, σ p.2)) (a₂ := (q.1, σ q.2)) hpq
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at this
    exact Prod.ext this.1 this.2
  rw [stableMatching_eq_iff_of_injective hc', stableMatching_eq_iff_of_injective hc]
  simp only [relabelNeg_apply, Equiv.refl_apply]

/-- The events `{σ_N = σ}` and `T_σ⁻¹ {σ_N = Id}` agree almost everywhere. -/
theorem ae_stableMatching_eq_iff_relabelNeg (σ : Equiv.Perm (Fin N)) :
    {c : Fin N → ℂ × ℂ | stableMatching c = σ} =ᵐ[volume]
      relabelNeg σ ⁻¹' {c | stableMatching c = Equiv.refl _} := by
  filter_upwards [ae_injective_norm_sub (ι := Fin N)] with c hc
  simp only [eq_iff_iff]
  exact (stableMatching_relabelNeg_eq_refl_iff σ hc).symm

/-- Each event `{σ_N = σ}` carries the integral of `{σ_N = Id}`. -/
theorem setLIntegral_stableMatching_eq (χ : ℂ → ℝ) (β lam : ℝ) (σ : Equiv.Perm (Fin N)) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ {c | stableMatching c = σ},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
          {c | stableMatching c = Equiv.refl (Fin N)},
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  set B : Set (Fin N → ℂ × ℂ) := Set.univ.pi fun _ : Fin N => box N ×ˢ box N
  have hB : relabelNeg σ ⁻¹' B = B := by
    ext c
    exact relabelNeg_mem_box_iff σ c
  have hset : B ∩ {c | stableMatching c = σ} =ᵐ[volume]
      relabelNeg σ ⁻¹' (B ∩ {c | stableMatching c = Equiv.refl _}) := by
    rw [Set.preimage_inter, hB]
    exact Filter.EventuallyEqSet.inter (by rfl) (ae_stableMatching_eq_iff_relabelNeg σ)
  rw [setLIntegral_congr hset]
  refine Eq.trans ?_ ((measurePreserving_relabelNeg σ).setLIntegral_comp_preimage_emb
    (relabelNeg σ).measurableEmbedding _ _)
  simp only [energy_relabelNeg]

/-- **The relabeling identity** (used without statement in the proofs of Proposition 5.45 and Theorem 1):
`Z_{N,β}^λ = N! ∫_{(Λ²)^N ∩ {σ_N = Id}} e^{-β F_λ}`. -/
theorem partitionFunction_eq_factorial_mul (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) :
    partitionFunction χ N β lam =
      (N.factorial : ℝ≥0∞) *
        ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩
            {c | stableMatching c = Equiv.refl (Fin N)},
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  set B : Set (Fin N → ℂ × ℂ) := Set.univ.pi fun _ : Fin N => box N ×ˢ box N
  have hcover : B = ⋃ σ : Equiv.Perm (Fin N), B ∩ {c | stableMatching c = σ} := by
    ext c
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨stableMatching c, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hmeas : ∀ σ : Equiv.Perm (Fin N), MeasurableSet (B ∩ {c | stableMatching c = σ}) :=
    fun σ => (measurableSet_pi_box_prod N).inter (measurableSet_stableMatching_eq σ)
  have hdisj : Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin N) =>
      B ∩ {c | stableMatching c = σ}) := by
    intro σ τ hστ
    refine Set.disjoint_left.mpr fun c hcσ hcτ => hστ ?_
    exact hcσ.2.symm.trans hcτ.2
  have hZ : partitionFunction χ N β lam = ∫⁻ c in ⋃ σ : Equiv.Perm (Fin N),
      B ∩ {c | stableMatching c = σ}, ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
    rw [← hcover]
    rfl
  rw [hZ, lintegral_iUnion hmeas hdisj, tsum_fintype]
  rw [Finset.sum_congr rfl fun σ _ => setLIntegral_stableMatching_eq χ β lam σ, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

end TheoremOne

end MultipoleBKT

end
