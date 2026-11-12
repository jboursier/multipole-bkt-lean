/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteCases.AnalyticControls

/-!
# Complete mixed terms with a selected error factor

See (A.55)–(A.58),
(A.60) and case E. These internal multiplication lemmas
keep every correction family while selecting one factor for its sharper bound.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteCases

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : ℝ} {r τ : ι → ℝ} {A B a₁ a₀ b₁ b₀ q : Sym2 ι → ℝ} {u v : ι → ℝ}

omit [Fintype ι] [DecidableEq ι] in
/-- Increasing ordinary geometric majorants preserves all selected controls. -/
theorem InternalControls.mono (H : InternalControls K r τ A B a₁ a₀ b₁ b₀ q u v)
    {A' B' : Sym2 ι → ℝ} (hA : ∀ e, A e ≤ A' e) (hB : ∀ e, B e ≤ B' e) :
    InternalControls K r τ A' B' a₁ a₀ b₁ b₀ q u v := by
  refine { H with odd := ?_, even := ?_ }
  · intro e
    exact ⟨(H.odd e).1.trans (mul_le_mul_of_nonneg_left (hA e) (zero_le_one.trans H.coefficient)),
      (H.odd e).2.trans (mul_le_mul_of_nonneg_left (hA e) (zero_le_one.trans H.coefficient))⟩
  · intro e
    exact ⟨(H.even e).1.trans (mul_le_mul_of_nonneg_left (hB e) (zero_le_one.trans H.coefficient)),
      (H.even e).2.trans (mul_le_mul_of_nonneg_left (hB e) (zero_le_one.trans H.coefficient))⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The same controls with a larger common coefficient. -/
theorem InternalControls.enlarge (H : InternalControls K r τ A B a₁ a₀ b₁ b₀ q u v)
    {K' : ℝ} (hK : K ≤ K') : InternalControls K' r τ A B a₁ a₀ b₁ b₀ q u v := by
  have hKpos : 0 < K := zero_lt_one.trans_le H.coefficient
  have hA0 : ∀ e, 0 ≤ A e := by
    intro e
    have hh := (abs_nonneg (a₀ e)).trans (H.odd e).1
    exact nonneg_of_mul_nonneg_right hh hKpos
  have hB0 : ∀ e, 0 ≤ B e := by
    intro e
    have hh := (abs_nonneg (b₀ e)).trans (H.even e).1
    exact nonneg_of_mul_nonneg_right hh hKpos
  have ht : ∀ i j, 0 ≤ r i * r j / τ i ^ 2 := fun i j =>
    div_nonneg (mul_nonneg (H.radius_nonneg i) (H.radius_nonneg j)) (sq_nonneg _)
  refine ⟨H.coefficient.trans hK, H.radius_nonneg, H.screening_pos,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact ⟨(H.odd e).1.trans (mul_le_mul_of_nonneg_right hK (hA0 e)),
      (H.odd e).2.trans (mul_le_mul_of_nonneg_right hK (hA0 e))⟩
  · intro e
    exact ⟨(H.even e).1.trans (mul_le_mul_of_nonneg_right hK (hB0 e)),
      (H.even e).2.trans (mul_le_mul_of_nonneg_right hK (hB0 e))⟩
  · exact fun e => (H.intra e).trans hK
  · exact fun i => (H.quadratic i).trans hK
  · exact fun i => (H.bad i).trans hK
  · exact fun i j => (H.odd_error i j).trans (mul_le_mul_of_nonneg_right hK (ht i j))
  · exact fun i j => (H.even_error i j).trans (mul_le_mul_of_nonneg_right hK (ht i j))
  · exact fun i j => (H.intra_error i j).trans (mul_le_mul_of_nonneg_right hK (ht i j))
  · exact fun i => (H.quadratic_error i).trans
      (mul_le_mul_of_nonneg_right hK (div_nonneg (sq_nonneg _) (sq_nonneg _)))

variable (H : InternalControls K r τ A B a₁ a₀ b₁ b₀ q u v)
variable (O E I : Finset (Sym2 ι)) (P : FiveSubsets (Sym2 ι) ι)
variable (hP : P ∈ fiveSubsets O E I univ) (G : ℝ)

include H

omit [Fintype ι] in
private theorem ordinary_odd (e : Sym2 ι) : |mixedBond P.1 a₁ a₀ e| ≤ K * A e := by
  unfold mixedBond
  split_ifs
  · exact (H.odd e).2
  · exact (H.odd e).1

omit [Fintype ι] in
private theorem ordinary_even (e : Sym2 ι) : |mixedBond P.2.1 b₁ b₀ e| ≤ K * B e := by
  unfold mixedBond
  split_ifs
  · exact (H.even e).2
  · exact (H.even e).1

include hP

/-- Internal whole-term case B/D estimate before the component reduction. -/
theorem internal_odd_term {i j : ι} (he : s(i,j) ∈ P.1) :
    |G * fiveTerm O E I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O E P *
        ((r i * r j / τ i ^ 2) * (∏ e ∈ O.erase s(i,j), A e) * ∏ e ∈ E, B e) := by
  classical
  have heO := (mem_powerset.1 (mem_product.1 hP).1) he
  have hp := internal_fiveTerm_weighted O E I univ a₁ a₀ b₁ b₀ q u v P hP
    (fun e => if e = s(i,j) then r i * r j / τ i ^ 2 else A e) B (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (zero_le_one.trans H.coefficient)
    (fun e _ => by
      by_cases hm : e = s(i,j)
      · subst e
        simpa only [ite_true, mixedBond, ite_eq_left he] using H.odd_error i j
      · simpa only [ite_eq_right hm] using ordinary_odd H P e)
    (fun e _ => ordinary_even H P e)
    (fun e _ => by simpa only [mul_one] using H.intra e)
    (fun i _ => by simpa only [mul_one] using H.quadratic i)
    (fun i _ => by simpa only [mul_one] using H.bad i) G
  simpa only [weightedFive, internal_selected_product O A heO, prod_const_one, mul_one] using hp

/-- Internal whole-term case C estimate before dropping surplus even edges. -/
theorem internal_even_term {i j : ι} (he : s(i,j) ∈ P.2.1) :
    |G * fiveTerm O E I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O E P *
        ((∏ e ∈ O, A e) * (r i * r j / τ i ^ 2) * ∏ e ∈ E.erase s(i,j), B e) := by
  classical
  have heE := (mem_powerset.1 (mem_product.1 (mem_product.1 hP).2).1) he
  have hp := internal_fiveTerm_weighted O E I univ a₁ a₀ b₁ b₀ q u v P hP
    A (fun e => if e = s(i,j) then r i * r j / τ i ^ 2 else B e) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (zero_le_one.trans H.coefficient)
    (fun e _ => ordinary_odd H P e)
    (fun e _ => by
      by_cases hm : e = s(i,j)
      · subst e
        simpa only [ite_true, mixedBond, ite_eq_left he] using H.even_error i j
      · simpa only [ite_eq_right hm] using ordinary_even H P e)
    (fun e _ => by simpa only [mul_one] using H.intra e)
    (fun i _ => by simpa only [mul_one] using H.quadratic i)
    (fun i _ => by simpa only [mul_one] using H.bad i) G
  simpa only [weightedFive, internal_selected_product E B heE, prod_const_one, mul_one, mul_assoc] using hp

/-- Internal whole-term case A for an intra-block correction. -/
theorem internal_intra_term {i j : ι} (he : s(i,j) ∈ P.2.2.1) :
    |G * fiveTerm O E I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O E P *
        ((∏ e ∈ O, A e) * (∏ e ∈ E, B e) * (r i * r j / τ i ^ 2)) := by
  classical
  have hp := internal_fiveTerm_weighted O E I univ a₁ a₀ b₁ b₀ q u v P hP
    A B (fun e => if e = s(i,j) then r i * r j / τ i ^ 2 else 1)
    (fun _ => 1) (fun _ => 1) (zero_le_one.trans H.coefficient)
    (fun e _ => ordinary_odd H P e) (fun e _ => ordinary_even H P e)
    (fun e _ => by
      by_cases hm : e = s(i,j)
      · subst e
        simpa only [ite_true] using H.intra_error i j
      · simpa only [ite_eq_right hm, mul_one] using H.intra e)
    (fun i _ => by simpa only [mul_one] using H.quadratic i)
    (fun i _ => by simpa only [mul_one] using H.bad i) G
  simpa only [weightedFive, internal_selected_units P.2.2.1 he, prod_const_one, mul_one] using hp

/-- Internal whole-term case A for a quadratic correction. -/
theorem internal_quadratic_term {i : ι} (hi : i ∈ P.2.2.2.1) :
    |G * fiveTerm O E I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O E P *
        ((∏ e ∈ O, A e) * (∏ e ∈ E, B e) * (r i ^ 2 / τ i ^ 2)) := by
  classical
  have hp := internal_fiveTerm_weighted O E I univ a₁ a₀ b₁ b₀ q u v P hP
    A B (fun _ => 1) (fun j => if j = i then r i ^ 2 / τ i ^ 2 else 1)
    (fun _ => 1) (zero_le_one.trans H.coefficient)
    (fun e _ => ordinary_odd H P e) (fun e _ => ordinary_even H P e)
    (fun e _ => by simpa only [mul_one] using H.intra e)
    (fun j _ => by
      by_cases hm : j = i
      · subst j
        simpa only [ite_true] using H.quadratic_error i
      · simpa only [ite_eq_right hm, mul_one] using H.quadratic j)
    (fun i _ => by simpa only [mul_one] using H.bad i) G
  simpa only [weightedFive, internal_selected_units P.2.2.2.1 hi, prod_const_one, mul_one] using hp

/-- Internal whole-term case A for a bad-label correction. The exact indicator
is kept, even when other error subsets are also nonempty. -/
theorem internal_bad_term {i : ι} (hi : i ∈ P.2.2.2.2) :
    |G * fiveTerm O E I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O E P *
        ((∏ e ∈ O, A e) * (∏ e ∈ E, B e) * |v i|) := by
  classical
  have hp := internal_fiveTerm_weighted O E I univ a₁ a₀ b₁ b₀ q u v P hP
    A B (fun _ => 1) (fun _ => 1) (fun j => if j = i then |v i| else 1)
    (zero_le_one.trans H.coefficient)
    (fun e _ => ordinary_odd H P e) (fun e _ => ordinary_even H P e)
    (fun e _ => by simpa only [mul_one] using H.intra e)
    (fun i _ => by simpa only [mul_one] using H.quadratic i)
    (fun j _ => by
      by_cases hm : j = i
      · subst j
        simpa only [ite_true, one_mul] using mul_le_mul_of_nonneg_right H.coefficient (abs_nonneg (v i))
      · simpa only [ite_eq_right hm, mul_one] using H.bad j) G
  simpa only [weightedFive, internal_selected_units P.2.2.2.2 hi, prod_const_one, mul_one] using hp

/-- Internal whole-term case E. Its distinguished even kernel survives the
multiplication of all other five-family factors. -/
theorem internal_marked_even_term {i j : ι} (he : s(i,j) ∈ P.2.1) {kernel : ℝ}
    (hmark : |b₁ s(i,j) - b₀ s(i,j)| ≤ K * kernel) :
    |G * fiveTerm O E I a₁ a₀ b₁ b₀ q u v P| ≤
      |G| * K ^ factorCount O E P *
        ((∏ e ∈ O, A e) * kernel * ∏ e ∈ E.erase s(i,j), B e) := by
  classical
  have heE := (mem_powerset.1 (mem_product.1 (mem_product.1 hP).2).1) he
  have hp := internal_fiveTerm_weighted O E I univ a₁ a₀ b₁ b₀ q u v P hP
    A (fun e => if e = s(i,j) then kernel else B e) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (zero_le_one.trans H.coefficient)
    (fun e _ => ordinary_odd H P e)
    (fun e _ => by
      by_cases hm : e = s(i,j)
      · subst e
        simpa only [ite_true, mixedBond, ite_eq_left he] using hmark
      · simpa only [ite_eq_right hm] using ordinary_even H P e)
    (fun e _ => by simpa only [mul_one] using H.intra e)
    (fun i _ => by simpa only [mul_one] using H.quadratic i)
    (fun i _ => by simpa only [mul_one] using H.bad i) G
  simpa only [weightedFive, internal_selected_product E B heE, prod_const_one, mul_one, mul_assoc] using hp

end MultipoleBKT.ExpansionK.RouteCases

end
