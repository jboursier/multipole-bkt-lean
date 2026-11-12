/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.BaselineUniform

/-!
# Literal closed tail domains and the nonempty cutoff expansion

See (A.52)
and (A.53). Circles have zero planar measure.
Consequently every literal closed tail product agrees almost everywhere
with its strict version before the finite nonempty subset expansion.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteAssembly

open MeasureTheory Set Finset Limits Hierarchical Multipole Parity RouteCases RouteSpatial
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Fintype B] [DecidableEq B]

/-- The signed tail product appearing literally in (A.53). -/
noncomputable def tailProduct (closed : Bool) (h : ℝ) (U : Finset I) (c : I → ℂ × ℂ) : ℝ :=
  ∏ i ∈ U, -(if (if closed then h ≤ ‖(c i).1-(c i).2‖ else h < ‖(c i).1-(c i).2‖) then 1 else 0)

omit [DecidableEq I] [LinearOrder I] in
/-- The radial boundary of each dipole coordinate is null. -/
theorem ae_all_length_ne (h : ℝ) : ∀ᵐ c : I → ℂ × ℂ ∂volume, ∀ i, ‖(c i).1-(c i).2‖ ≠ h := by
  have hp : ∀ᵐ d : ℂ × ℂ ∂volume, ‖d.1-d.2‖ ≠ h := by
    change ∀ᵐ d : ℂ × ℂ ∂(volume : Measure ℂ).prod volume, ‖d.1-d.2‖ ≠ h
    apply (Measure.ae_prod_iff_ae_ae (show MeasurableSet {d : ℂ × ℂ | ‖d.1-d.2‖ ≠ h} by measurability)).2
    apply Filter.Eventually.of_forall
    intro x
    have hs : ∀ᵐ y : ℂ ∂volume, y ∉ Metric.sphere x h := by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using Measure.addHaar_sphere volume x h
    filter_upwards [hs] with y hy
    simpa only [Metric.mem_sphere,dist_eq_norm,norm_sub_rev] using hy
  rw [ae_all_iff]
  intro i
  rw [volume_pi]
  exact (Measure.quasiMeasurePreserving_eval (fun _ : I => (volume : Measure (ℂ × ℂ))) i).ae hp

omit [DecidableEq I] [LinearOrder I] in
/-- The closed and strict tail products coincide off the null circles. -/
theorem tailProduct_closed_ae (h : ℝ) (U : Finset I) :
    tailProduct true h U =ᵐ[volume] tailProduct false h U := by
  filter_upwards [ae_all_length_ne (I := I) h] with c hc
  unfold tailProduct
  apply prod_congr rfl
  intro i _
  change (-(if h ≤ ‖(c i).1-(c i).2‖ then (1 : ℝ) else 0)) =
    -(if h < ‖(c i).1-(c i).2‖ then 1 else 0)
  simp only [le_iff_lt_or_eq,or_iff_left (Ne.symm (hc i))]

omit [LinearOrder I] in
/-- The literal finite nonempty-U₀ expansion, away from the null boundary. -/
theorem cutoff_nonempty_expansion_ae (h : ℝ) :
    (fun c : I → ℂ × ℂ => cutInd h c - 1) =ᵐ[volume]
      (fun c => ∑ U ∈ (univ : Finset I).powerset.erase ∅, tailProduct true h U c) := by
  filter_upwards [ae_all_length_ne (I := I) h] with c hc
  have hi (i : I) : (if ‖(c i).1-(c i).2‖ ≤ h then (1 : ℝ) else 0) =
      (-(if h ≤ ‖(c i).1-(c i).2‖ then 1 else 0)) + 1 := by
    by_cases hi : ‖(c i).1-(c i).2‖ ≤ h
    · have hlt := lt_of_le_of_ne hi (hc i)
      simp only [ite_eq_left hi,ite_eq_right (not_le.2 hlt)]
      norm_num
    · have hgt := lt_of_not_ge hi
      simp only [ite_eq_right hi,ite_eq_left hgt.le]
      norm_num
  have he := prod_add_one (f := fun i : I => -(if h ≤ ‖(c i).1-(c i).2‖ then (1 : ℝ) else 0)) univ
  have hm : (∅ : Finset I) ∈ (univ : Finset I).powerset := mem_powerset.2 (empty_subset _)
  rw [← add_sum_erase _ _ hm] at he
  simp only [Finset.prod_empty] at he
  change (∏ i : I, if ‖(c i).1-(c i).2‖ ≤ h then (1 : ℝ) else 0)-1 = _
  simp_rw [hi]
  change (∏ i : I, ((-(if h ≤ ‖(c i).1-(c i).2‖ then (1 : ℝ) else 0))+1))-1 =
    ∑ U ∈ (univ : Finset I).powerset.erase ∅, ∏ i ∈ U, -(if h ≤ ‖(c i).1-(c i).2‖ then 1 else 0)
  linarith [he]

end MultipoleBKT.ExpansionK.RouteAssembly

end
