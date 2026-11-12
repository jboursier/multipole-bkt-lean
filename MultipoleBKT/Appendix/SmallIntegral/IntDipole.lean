/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.DipoleBound
public import MultipoleBKT.Limits.Relabel
public import MultipoleBKT.Frozen.DipoleActivity

/-!
# Lemma A.5: the integrals of the dipole clusters

See (A.28) and
Lemma A.5. For each connected graph with an edge,
`|I_{dip,∞}(V; E)| ≤ C N λ^{(4-β)|V|-2}` for every positive λ.

Take `M=30` and expand in near and far edges. Reverse the merged near
components, apply the separate odd and even trees, and integrate the joint
odd tail and even annuli through the logarithmic formulas. Order the radii
and integrate the resulting logarithmic moments in the three β regimes.
The root costs `N`. Relabelling and a finite graph sum make the coefficient
depend only on the number of labels. The frozen statement also allows
one vertex with no edge, which retains a scalar integral estimate.

* `dipoleIntegral`: `I_{dip,∞}(V; E)`.
* `dipoleActivity_eq_sum_dipoleIntegral`: `𝖪^dip_{β,λ}(V) = ∑_{E ∈ 𝒢_c(V)} I_{dip,∞}(V; E) /
  (N C_{β,λ})^{|V|}` (A.28).
* `lemma_A_5`: Lemma A.5.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open MeasureTheory Set Finset SimpleGraph Filter
open Limits BoundedLower

variable {χ : ℂ → ℝ} {N : ℕ} {β lam : ℝ}

open scoped Classical in
/-- **The dipole integral** `I_{dip,∞}(V; E)` (eq. (A.28), with
`ε₀ = ∞`): `∫_{(Λ²)^{|V|}} ∏_{ij ∈ E} f_ij^v ∏_{i ∈ V} e^{β g_λ(x_i - y_i)} dx_i dy_i`, where
`f_ij^v = e^{-β v_ij} 𝟙_{𝒜_ij} - 1` is evaluated with `i < j` (as in `dipoleActivity`). -/
noncomputable def dipoleIntegral (χ : ℂ → ℝ) (N : ℕ) (β lam : ℝ) (V : Finset ℕ)
    (E : SimpleGraph V) : ℝ :=
  ∫ c in boxConfig V N, dipoleActivityIntegrand χ β lam E c * ∏ i, pairDensity χ β lam (c i)

theorem dipoleIntegral_eq_dipBox (V : Finset ℕ) (E : SimpleGraph V) :
    dipoleIntegral χ N β lam V E = ∫ c in boxConfig V N, dipBox χ β lam E c := rfl

open scoped Classical in
/-- `𝖪^dip_{β,λ}(V) = ∑_{E ∈ 𝒢_c(V)} I_{dip,∞}(V; E) / (N C_{β,λ})^{|V|}` (A.28),
for `N ≥ 1` and `λ > 0`. -/
theorem dipoleActivity_eq_sum_dipoleIntegral (hχ : IsMollifier χ) (hlam : 0 < lam) (hN : 1 ≤ N)
    (V : Finset ℕ) :
    dipoleActivity χ N β lam V =
      ∑ E ∈ (Finset.univ : Finset (SimpleGraph V)).filter
          (fun E => E.Connected ∧ E.edgeSet.Nonempty),
        ((N : ℝ) * dipoleNormalization χ N β lam)⁻¹ ^ V.card * dipoleIntegral χ N β lam V E := by
  rw [dipoleActivity_eq_sum]
  refine sum_congr (by ext E; simp) fun E _ => ?_
  rw [integral_pi_dipoleMeasure hχ hlam β hN, Fintype.card_coe]
  rfl

open scoped Classical in
/-- An order isomorphism of label sets preserves the dipole integrals. -/
theorem dipoleIntegral_congr_orderIso {V W : Finset ℕ} (e : V ≃o W) (E : SimpleGraph V) :
    dipoleIntegral χ N β lam V E =
      dipoleIntegral χ N β lam W (Equiv.simpleGraph e.toEquiv E) := by
  unfold dipoleIntegral
  rw [← integral_boxConfig_comp_equiv e.toEquiv]
  refine setIntegral_congr_fun (measurableSet_boxConfig N) fun c _ => ?_
  unfold dipoleActivityIntegrand
  congr 1
  · refine Fintype.prod_equiv e.toEquiv _ _ fun i => ?_
    refine Fintype.prod_equiv e.toEquiv _ _ fun j => ?_
    simp only [Equiv.simpleGraph_apply, SimpleGraph.comap_adj, RelIso.coe_fn_toEquiv,
      e.lt_iff_lt, OrderIso.coe_symm_toEquiv, OrderIso.symm_apply_apply]
  · exact Fintype.prod_equiv e.toEquiv _ _ fun i => by
      simp only [RelIso.coe_fn_toEquiv, OrderIso.coe_symm_toEquiv, OrderIso.symm_apply_apply]

theorem rpow_sub_two_eq (hlam : 0 < lam) (β : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    lam ^ ((4 - β) * k - 2) = lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  rw [← Real.rpow_natCast lam (2 * (k - 1)), ← Real.rpow_add hlam]
  congr 1
  rw [Nat.cast_mul, Nat.cast_sub hk]
  push_cast
  ring

open scoped Classical in
/-- **Lemma A.5**: for `β > 2` and
`k ≤ p*(β)` there is `C > 0` (depending on `χ, β, k`) such that for every `V` with `|V| = k`, every
connected edge set `E` on `V`, every `λ > 0` and every `N`,
`|I_{dip,∞}(V; E)| ≤ C N λ^{(2-β)k} λ^{2(k-1)}`. -/
theorem lemma_A_5 (hχ : IsMollifier χ) (hβ : 2 < β) {k : ℕ} (hk : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Finset ℕ, V.card = k → ∀ E : SimpleGraph V, E.Connected →
      ∀ lam : ℝ, 0 < lam → ∀ N : ℕ,
        |dipoleIntegral χ N β lam V E| ≤ C * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by
  set W := range k
  have hW : W.card = k := card_range k
  have hF : ∀ E₀ ∈ (univ : Finset (SimpleGraph W)).filter SimpleGraph.Connected,
      ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → ∀ N : ℕ,
        |∫ c in boxConfig W N, dipBox χ β lam E₀ c| ≤ A * (N * lam ^ ((4 - β) * k - 2)) := by
    intro E₀ hE₀
    have hconn := (mem_filter.1 hE₀).2
    have : Nonempty W := hconn.nonempty
    have hkW : (Fintype.card W : ℕ∞) ≤ pStar β := by rwa [Fintype.card_coe, hW]
    by_cases hW2 : 2 ≤ Fintype.card W
    · obtain ⟨A, hA0, hA⟩ := exists_abs_integral_dipBox_log_le hχ hβ hW2 hkW E₀ hconn
      rw [Fintype.card_coe, hW] at hA
      exact ⟨A, hA0, hA⟩
    · obtain ⟨A, hA0, hA⟩ := exists_abs_integral_dipBox_le hχ hβ hkW E₀ hconn
      rw [Fintype.card_coe, hW] at hA
      exact ⟨A, hA0, hA⟩
  choose! A hA0 hA using hF
  set Atot := ∑ E₀ ∈ (univ : Finset (SimpleGraph W)).filter SimpleGraph.Connected, A E₀
  have hAtot0 : 0 ≤ Atot := sum_nonneg fun E₀ hE₀ => hA0 E₀ hE₀
  refine ⟨Atot + 1, by linarith, fun V hV E hE lam hlam N => ?_⟩
  have hk1 : 1 ≤ k := by
    obtain ⟨v⟩ := hE.nonempty
    rw [← hV]
    exact card_pos.2 ⟨v, v.2⟩
  set e : V ≃o W := (V.orderIsoOfFin hV).symm.trans (W.orderIsoOfFin hW)
  set E₀ := Equiv.simpleGraph e.toEquiv E
  have hiso : E ≃g E₀ :=
    { toEquiv := e.toEquiv
      map_rel_iff' := by
        intro a b
        simp [E₀] }
  have hE₀ : E₀ ∈ (univ : Finset (SimpleGraph W)).filter SimpleGraph.Connected :=
    mem_filter.2 ⟨mem_univ _, hiso.connected_iff.1 hE⟩
  rw [dipoleIntegral_congr_orderIso e E, dipoleIntegral_eq_dipBox]
  refine (hA E₀ hE₀ lam hlam N).trans ?_
  rw [rpow_sub_two_eq hlam β hk1]
  have hAle : A E₀ ≤ Atot + 1 :=
    (single_le_sum (f := A) (fun Y hY => hA0 Y hY) hE₀).trans (by linarith)
  have hpos : 0 ≤ (N : ℝ) * (lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))) := by positivity
  calc A E₀ * (N * (lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1))))
      ≤ (Atot + 1) * (N * (lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)))) :=
        mul_le_mul_of_nonneg_right hAle hpos
    _ = (Atot + 1) * N * lam ^ ((2 - β) * k) * lam ^ (2 * (k - 1)) := by ring

end SmallIntegral

end MultipoleBKT

end
