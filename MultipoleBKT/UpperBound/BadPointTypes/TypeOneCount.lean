/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BadPointTypes.TypeOneIntegral

/-!
# Lemma 5.40: summing over the data

The paper: Lemma 5.40, Step 5. This file retains the scale factorization and the charge-count
identities used by fixed-data integration. The successive combinatorial enumeration and
partition counts of Steps 2–4 and 6 are in `RouteTypeOne/`.
-/

@[expose] public section

namespace MultipoleBKT

namespace BadPointTypes

open Finset
open scoped ENNReal

variable {n : ℕ}

open scoped Classical in
/-- The number of charges of each kind. -/
noncomputable def kindCount (kind : Charge n → Fin 4) (k : Fin 4) : ℕ :=
  (Finset.univ.filter fun v => kind v = k).card

theorem card_charge : Fintype.card (Charge n) = 2 * n := by
  rw [Fintype.card_sum, Fintype.card_fin]
  ring

/-- The four kinds partition the `2n` charges. -/
theorem kindCount_sum (kind : Charge n → Fin 4) :
    kindCount kind 0 + kindCount kind 1 + kindCount kind 2 + kindCount kind 3 = 2 * n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Charge n)))
    (t := (Finset.univ : Finset (Fin 4))) (f := kind) (fun _ _ => mem_univ _)
  rw [Finset.card_univ, card_charge, Fin.sum_univ_four] at h
  rw [h]
  rfl

/-- Valid data have `q` members per overcrowded root and at most `n` good charges. -/
theorem TypeOneValid.counts {q : ℕ} {D : TOData n} (hD : TypeOneValid q D) :
    kindCount D.1 2 = q * kindCount D.1 0 ∧ kindCount D.1 3 ≤ n := by
  classical
  obtain ⟨hV1, -, hV3, hV4, -, -⟩ := hD
  refine ⟨?_, hV4⟩
  unfold kindCount
  rw [Finset.card_eq_sum_card_fiberwise (f := D.2.1)
    (t := Finset.univ.filter fun v => D.1 v = 0)
    (fun v hv => mem_filter.2 ⟨mem_univ _, hV1 v (mem_filter.1 hv).2⟩)]
  rw [Finset.sum_congr rfl (g := fun _ => q) fun r hr => by
      rw [filter_filter]; exact hV3 r (mem_filter.1 hr).2,
    sum_const, smul_eq_mul, mul_comm]

/-- The bound of one overcrowded cluster at the scale index `s`:
`N (64π)^q (λ 2^s)^{q(2-β/2)-β/2}`. -/
noncomputable def crowdTerm (q : ℕ) (β lam : ℝ) (Nₐ : ℕ) (s : ℕ) : ℝ :=
  (Nₐ : ℝ) * (64 * Real.pi) ^ q * dyad lam s ^ clusterExponent q β

open scoped Classical in
/-- The sum over the scale indices factorises over the overcrowded roots. -/
theorem sum_scales (q K : ℕ) (β lam : ℝ) (Nₐ : ℕ) (kind : Charge n → Fin 4) :
    ∑ sc ∈ Fintype.piFinset (fun v => if kind v = 0 then Finset.range (K + 1) else {0}),
      ∏ v ∈ Finset.univ.filter (fun v => kind v = 0), crowdTerm q β lam Nₐ (sc v) =
    (∑ s ∈ Finset.range (K + 1), crowdTerm q β lam Nₐ s) ^ kindCount kind 0 := by
  simp_rw [prod_filter]
  rw [← Finset.prod_univ_sum (t := fun v => if kind v = 0 then Finset.range (K + 1) else {0})
    (f := fun v s => if kind v = 0 then crowdTerm q β lam Nₐ s else 1)]
  rw [Finset.prod_congr rfl (g := fun v => if kind v = 0 then
    ∑ s ∈ Finset.range (K + 1), crowdTerm q β lam Nₐ s else 1) fun v _ => by
      by_cases hv : kind v = 0
      · simp only [hv, ite_true]
      · simp only [hv, ite_false, sum_singleton]]
  rw [← prod_filter, prod_const]
  rfl

open scoped Classical in
theorem typeOneBound_eq (q : ℕ) (β lam h Kg : ℝ) (Nₐ : ℕ) (D : TOData n) :
    typeOneBound q β lam h Kg Nₐ D =
      (∏ v ∈ Finset.univ.filter (fun v => D.1 v = 0), crowdTerm q β lam Nₐ (D.2.2 v)) *
        ((Nₐ : ℝ) * (h / 4) ^ (-(β / 2))) ^ kindCount D.1 1 * Kg ^ kindCount D.1 3 := by
  unfold typeOneBound kindCount crowdTerm
  congr 3

end BadPointTypes

end MultipoleBKT

end
