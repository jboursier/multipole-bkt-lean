/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Gibbs.Activities

/-!
# Theorem 1 from the gates: exchangeability of the dipole activity

The dipole activity `𝖪^dip_{β,λ}(V)` (Definition 2.5) depends on the label set `V` only through `|V|`: the integral is against the product
measure `μ_{β,λ}^{⊗V}` and the integrand is invariant under an order-preserving relabeling. The
paper uses this silently when it writes `𝖪^dip(V_i) = N^{1-|V_i|}(𝗄^dip(|V_i|) + o(1))` and sums
over the union `V_1 ∪ ⋯ ∪ V_n` in (5.167).

* `dipoleActivity_congr_orderIso`, `dipoleActivity_congr_card`: `𝖪^dip(V) = 𝖪^dip(W)` when
  `|V| = |W|` (for `N ≥ 1`);
* `dipoleActivity_eq_range_card`: `𝖪^dip(V) = 𝖪^dip({0, …, |V| - 1})`.
-/

@[expose] public section

open MeasureTheory Filter

namespace MultipoleBKT

namespace TheoremOne

variable {χ : ℂ → ℝ} {β lam : ℝ} {N : ℕ}

open scoped Classical in
/-- An order isomorphism of label sets preserves `𝖪^dip`. -/
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

/-- `𝖪^dip(V) = 𝖪^dip({0, …, |V| - 1})` (for `N ≥ 1`). -/
theorem dipoleActivity_eq_range_card (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (V : Finset ℕ) :
    dipoleActivity χ N β lam V = dipoleActivity χ N β lam (Finset.range V.card) :=
  dipoleActivity_congr_card hχ hlam hN (Finset.card_range _).symm

end TheoremOne

end MultipoleBKT

end
