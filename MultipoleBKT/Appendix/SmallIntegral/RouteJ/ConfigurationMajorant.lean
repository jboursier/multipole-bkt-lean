/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.CoreMajorant

/-!
# The hatted configuration integrand as a retained-tree sum

See Lemma A.4, (A.22) and (A.25).
The near trees retain the separate odd and even families. The odd maximum
tail is passed intact to the joint odd profile.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Finset SimpleGraph
open Multipole SetPartition Limits Hierarchical Peeling BoundedLowerEps
open scoped Classical ENNReal

/-- The hatted core before multiplying the single-dipole densities. -/
noncomputable def hatJCore {X : Finset (Finset ℕ)} (M lam : ℝ) (hX : IsSubpartition X)
    {n : ℕ} (Xs : Fin n → Finset (Finset ℕ)) (Ta : Fin n → Finset (ℕ × ℕ))
    (Tb : Finset (ℕ × ℕ)) (hat : Fin n → X) (c : X.biUnion id → ℂ × ℂ) : ℝ :=
  tailJ (fun i => dipoleLength (c i)) (dipoleDistOn c)
      (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset) *
    (∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
      blockRadius hX (fun i => dipoleLength (c i)) S ^ 2) *
    (∏ e ∈ univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset, keptE M lam c e) *
    (∏ e ∈ (graphOf (X.biUnion id) Tb).edgeFinset, (aSqE M lam c e + linkE M lam c e)) *
    ∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) c) S) then 1 else 0

/-- A retained-tree term with normalized near and even edges and a shared odd tail. -/
noncomputable def retainedTreeTerm {V B : Type*} [Fintype V] [Fintype B]
    [DecidableEq V] [DecidableEq B] [Nonempty V] (blk : V → B)
    (M lam : ℝ) (A E : Finset (Sym2 V)) (R : NearTreeFamily blk) (c : V → ℂ × ℂ) : ℝ≥0∞ :=
  jointOdd (minRad lam c) (maxRad lam c) (fun e : A => (dipoleDistOn c e : ℂ)) *
    (ENNReal.ofReal (radialFactor lam c) *
      ((∏ e ∈ E, ENNReal.ofReal (normalizedEven M lam c e)) *
        ∏ e ∈ nearForest blk (fun b => (R b).val), ENNReal.ofReal (nearE M lam c e)))

/-- The pointwise comparison from the hatted core to retained near-tree
terms. It uses the subpartition radius allocation and one joint odd
profile, with no fractional-power tree term.
See the proof of Lemma A.4. -/
theorem hatJCore_le_retained_sum {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    [Nonempty (X.biUnion id)] {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (hXs : ∀ l, Xs l ⊆ X) (hdisj : ∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l'))
    (Ta : Fin n → Finset (ℕ × ℕ)) (hTa : ∀ l, Ta l ∈ (relTrees (Xs l)).image edgesOf)
    (Tb : Finset (ℕ × ℕ))
    (hTb : Tb ∈ (relTrees₀ (coarsen X ((univ : Finset (Fin n)).image Xs))).image edgesOf)
    (c : X.biUnion id → ℂ × ℂ) (hat : Fin n → X)
    (hhat : ∀ l, hat l ∈ (Xs l).subtype (· ∈ X) ∧
      ∀ S ∈ (Xs l).subtype (· ∈ X),
        blockRadius hX (fun i => dipoleLength (c i)) S ≤
          blockRadius hX (fun i => dipoleLength (c i)) (hat l))
    {M lam : ℝ} (hM : 1 ≤ M) (hlam : 0 < lam) :
    ENNReal.ofReal (hatJCore M lam hX Xs Ta Tb hat c) ≤
      ∑ R : NearTreeFamily (Limits.blockOf X), retainedTreeTerm (Limits.blockOf X) M lam
        (univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset)
        (graphOf (X.biUnion id) Tb).edgeFinset R c := by
  let A := univ.biUnion fun l => (graphOf (X.biUnion id) (Ta l)).edgeFinset
  let E := (graphOf (X.biUnion id) Tb).edgeFinset
  let drop := ∏ l, ∏ S ∈ ((Xs l).subtype (· ∈ X)).erase (hat l),
    blockRadius hX (fun i => dipoleLength (c i)) S ^ 2
  let B := ∏ e ∈ E, (aSqE M lam c e + linkE M lam c e)
  have hdrop : 0 ≤ drop := prod_nonneg fun _ _ => prod_nonneg fun _ _ => sq_nonneg _
  have hB : 0 ≤ B := prod_nonneg fun _ _ => add_nonneg (aSqE_nonneg c _) (linkE_nonneg c _)
  by_cases hm : ∀ S ∈ X, ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) c) S)
  · have hconn : ∀ S : X, ((nearGraph M lam c).induce {i | Limits.blockOf X i = S}).Connected :=
      fun S => connected_induce_of_connOn hX c S.property (hm S S.property)
    obtain ⟨R, hR⟩ := exists_linked_nearTreeFamily (Limits.blockOf X) M lam c hconn
    have hp : (∏ e ∈ nearForest (Limits.blockOf X) (fun S => (R S).val), linkE M lam c e) = 1 := by
      apply prod_eq_one
      intro e he
      induction e using Sym2.ind with
      | h i j => exact ite_eq_left (hR i j he)
    have hnorm := source_normalized_product hX Xs hXs hdisj Ta hTa Tb hTb c hat hhat R hlam M
    rw [hp, mul_one] at hnorm
    have hodd := odd_factor_le_jointOdd hM hlam c A
    have hcore : hatJCore M lam hX Xs Ta Tb hat c =
        (tailJ (fun i => dipoleLength (c i)) (dipoleDistOn c) A * ∏ e ∈ A, keptE M lam c e) *
          (drop * B) := by
      unfold hatJCore
      rw [prod_eq_one (fun S hS => ite_eq_left (hm S hS)), mul_one]
      dsimp only [A, E, drop, B]
      ring
    have hne (e : Sym2 (X.biUnion id)) : 0 ≤ normalizedEven M lam c e :=
      div_nonneg (add_nonneg (aSqE_nonneg c e) (linkE_nonneg c e)) (minSq_pos hlam c e).le
    have hprod : 0 ≤ ∏ e ∈ E, normalizedEven M lam c e := prod_nonneg fun e _ => hne e
    have hrad0 : 0 ≤ radialFactor lam c := by
      unfold radialFactor
      exact mul_nonneg (prod_nonneg fun _ _ => sq_nonneg _)
        (Real.rpow_nonneg (hlam.le.trans (lam_le_maxRad lam c)) _)
    have hbound : ENNReal.ofReal (hatJCore M lam hX Xs Ta Tb hat c) ≤
        retainedTreeTerm (Limits.blockOf X) M lam A E R c := by
      rw [hcore, ENNReal.ofReal_mul' (mul_nonneg hdrop hB)]
      have hn := ENNReal.ofReal_le_ofReal hnorm
      rw [ENNReal.ofReal_mul hrad0, ENNReal.ofReal_mul hprod,
        ENNReal.ofReal_prod_of_nonneg (fun e (_ : e ∈ E) => hne e),
        ENNReal.ofReal_prod_of_nonneg (fun e _ => nearE_nonneg M lam c e)] at hn
      exact mul_le_mul' hodd hn
    exact hbound.trans (single_le_sum
      (f := fun R => retainedTreeTerm (Limits.blockOf X) M lam A E R c)
      (fun _ _ => bot_le) (mem_univ R))
  · push Not at hm
    obtain ⟨S, hS, hn⟩ := hm
    have hp : (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) c) S)
        then (1 : ℝ) else 0) = 0 := prod_eq_zero hS (ite_eq_right hn)
    unfold hatJCore
    rw [hp, mul_zero, ENNReal.ofReal_zero]
    exact bot_le

end MultipoleBKT.SmallIntegral.RouteJ

end
