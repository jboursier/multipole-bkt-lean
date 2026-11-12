/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.RouteExchange.Events

/-!
# The two equal-integral identities

The paper: (5.60) and (5.61). Each fiber has the same Gibbs integral by a measure-preserving
simultaneous relabeling. Only after establishing these equalities do we sum the
disjoint measurable fibers and insert their cardinalities.
-/

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal
open TwoComponentCoulomb (box)

namespace MultipoleBKT.UpperBound.RouteExchange

open Hierarchical Multipole SetPartition TheoremTwo PropFiveFortyFive

variable {N p₀ : ℕ} {χ : ℂ → ℝ} {β lam M ε₀ : ℝ}

private theorem profileEvent_relabel_iff {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (e : Equiv.Perm (Fin N)) (n : Fin (pBeta p₀ β) → ℕ) :
    relabel e c ∈ profileEvent p₀ β lam M ε₀ n ↔ c ∈ profileEvent p₀ β lam M ε₀ n := by
  have hn : ∀ i : Fin (pBeta p₀ β),
      goodMultipoleCount p₀ β lam M ε₀ (relabel e c) ((i : ℕ) + 1) =
        goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) := by
    intro i
    have h := congrArg (fun π => blockCount (pBeta p₀ β) π i)
      (goodBlocks_relabel (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) hc e)
    simpa only [blockCount_mapBlocks, blockCount_goodBlocks] using h
  simp only [profileEvent, Set.mem_ofPred_eq, matching_relabel_iff hc, hn]

private theorem badPoints_relabel {c : Fin N → ℂ × ℂ}
    (hc : Function.Injective fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖)
    (e : Equiv.Perm (Fin N)) :
    badPoints p₀ β lam M ε₀ c = (badPoints p₀ β lam M ε₀ (relabel e c)).map e.toEmbedding := by
  rw [relabel_apply]
  apply BadPointTypes.Permutation.badPoints_permutation
  intro i j hij
  exact congrArg Prod.fst (hc (show
    (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) (i, i) =
      (fun p : Fin N × Fin N => ‖(c p.1).1 - (c p.2).2‖) (j, j) from hij))

private theorem setLIntegral_relabel (e : Equiv.Perm (Fin N))
    {S T : Set (Fin N → ℂ × ℂ)} (h : S =ᵐ[volume] relabel e ⁻¹' T) :
    ∫⁻ c in S, ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      ∫⁻ c in T, ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  rw [setLIntegral_congr h]
  refine Eq.trans ?_ ((measurePreserving_relabel e).setLIntegral_comp_preimage_emb
    (relabel e).measurableEmbedding _ _)
  simp only [energy_relabel]

/-- Equal integrals per fixed bad-label set, proved by simultaneous relabeling
of the configuration rather than by counting sets. -/
theorem badEvent_integral_eq (n : Fin (pBeta p₀ β) → ℕ) {V V' : Finset (Fin N)}
    (hcard : V.card = V'.card) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ badEvent p₀ β lam M ε₀ n V,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ badEvent p₀ β lam M ε₀ n V',
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  classical
  obtain ⟨e, he⟩ := Equiv.Perm.exists_map_finset_eq V V' hcard
  symm
  apply setLIntegral_relabel e
  filter_upwards [ae_injective_norm_sub (ι := Fin N)] with c hc
  simp only [Set.mem_preimage, Set.mem_inter_iff, relabel_mem_box, badEvent,
    profileEvent_relabel_iff hc, Set.mem_ofPred_eq]
  have hbad := badPoints_relabel (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) hc e
  have hiff : badPoints p₀ β lam M ε₀ (relabel e c) = V ↔ badPoints p₀ β lam M ε₀ c = V' := by
    rw [hbad, ← he]
    exact (Finset.map_injective e.toEmbedding).eq_iff.symm
  rw [hiff]

/-- Equal integrals per good partition of a fixed profile. The permutation
preserves the fixed bad-label set and transports the good blocks. -/
theorem choiceEvent_integral_eq {V : Finset (Fin N)} {π π' : Finset (Finset ℕ)}
    {n : Fin (pBeta p₀ β) → ℕ} (hπ : π ∈ choices V (pBeta p₀ β) n)
    (hπ' : π' ∈ choices V (pBeta p₀ β) n) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ choiceEvent p₀ β lam M ε₀ V π,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ choiceEvent p₀ β lam M ε₀ V π',
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  classical
  obtain ⟨e, hV, hπe⟩ := exists_perm_choices hπ hπ'
  symm
  apply setLIntegral_relabel e
  filter_upwards [ae_injective_norm_sub (ι := Fin N)] with c hc
  simp only [Set.mem_preimage, Set.mem_inter_iff, relabel_mem_box, choiceEvent,
    Set.mem_ofPred_eq, matching_relabel_iff hc]
  have hbad := badPoints_relabel (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀) hc e
  have hiff : badPoints p₀ β lam M ε₀ (relabel e c) = V ↔ badPoints p₀ β lam M ε₀ c = V := by
    constructor
    · intro h
      rw [hbad, h, hV]
    · intro h
      apply Finset.map_injective e.toEmbedding
      rw [← hbad, h, hV]
  have hblocks : goodBlocks p₀ β lam M ε₀ (relabel e c) = π ↔
      goodBlocks p₀ β lam M ε₀ c = π' := by
    rw [← goodBlocks_relabel hc e, ← hπe]
    exact (mapBlocks_injective e).eq_iff.symm
  rw [hiff, hblocks]

/-- **Eq. (5.60)**: fixing any bad-label set multiplies its integral by
`binom(N,N')`. -/
theorem eqFcond1 (hM : 0 ≤ M) (n : Fin (pBeta p₀ β) → ℕ)
    (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N)
    (V : Finset (Fin N))
    (hV : V.card = N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ profileEvent p₀ β lam M ε₀ n,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      (N.choose (∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i) : ℝ≥0∞) *
        ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ badEvent p₀ β lam M ε₀ n V,
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  classical
  rw [profileEvent_eq_union hM n, Set.inter_iUnion]
  simp_rw [Set.inter_iUnion]
  rw [lintegral_biUnion_finset]
  · rw [Finset.sum_congr rfl fun V' hV' => badEvent_integral_eq n
      (((mem_powersetCard.1 hV').2).trans hV.symm)]
    simp only [sum_const, nsmul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin]
    rw [Nat.choose_symm hn]
  · intro V' _ V'' _ hne
    exact Set.disjoint_left.2 fun c hc hc' => hne (hc.2.2.symm.trans hc'.2.2)
  · intro V' _
    exact (measurableSet_pi_box_prod N).inter (measurableSet_badEvent n V')

/-- **Eq. (5.61)**: fixing any admissible good partition multiplies its
integral by the literal factorial partition count. -/
theorem eqFcond2 (hM : 0 ≤ M) (n : Fin (pBeta p₀ β) → ℕ)
    (hn : ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i ≤ N)
    (V : Finset (Fin N))
    (hV : V.card = N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i)
    {π : Finset (Finset ℕ)} (hπ : π ∈ choices V (pBeta p₀ β) n) :
    ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ badEvent p₀ β lam M ε₀ n V,
        ENNReal.ofReal (Real.exp (-β * energy χ lam c)) =
      (((∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i).factorial / profileWeight n : ℕ) : ℝ≥0∞) *
        ∫⁻ c in (Set.univ.pi fun _ : Fin N => box N ×ˢ box N) ∩ choiceEvent p₀ β lam M ε₀ V π,
          ENNReal.ofReal (Real.exp (-β * energy χ lam c)) := by
  classical
  rw [badEvent_eq_union hM n V, Set.inter_iUnion]
  simp_rw [Set.inter_iUnion]
  rw [lintegral_biUnion_finset]
  · rw [Finset.sum_congr rfl fun π' hπ' => choiceEvent_integral_eq hπ' hπ]
    simp only [sum_const, nsmul_eq_mul, card_choices hV hn]
  · intro π' _ π'' _ hne
    exact Set.disjoint_left.2 fun c hc hc' => hne (hc.2.2.2.symm.trans hc'.2.2.2)
  · intro π' _
    exact (measurableSet_pi_box_prod N).inter (measurableSet_choiceEvent V π')

end MultipoleBKT.UpperBound.RouteExchange

end
