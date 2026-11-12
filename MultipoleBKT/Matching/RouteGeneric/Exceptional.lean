/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Matching.Measurable

/-!
# The full finite exceptional set for clustering

Section 4.1 of the paper. Fix the matching
permutation first, square the contact equalities, and take the finite union over
permutations and labels. Both signs and both stopping thresholds are included.
-/

@[expose] public section

open MeasureTheory MvPolynomial

namespace MultipoleBKT.RouteGeneric

variable {ι : Type*} [Fintype ι]

/-- No same-sign contact time equals a dipole stopping time or the final cutoff,
for any fixed matching permutation. The quantifier over permutations also covers
the configuration-dependent stable matching. -/
def NoStoppingCoincidences (h : ℝ) (c : ι → ℂ × ℂ) : Prop :=
  ∀ (σ : Equiv.Perm ι) (i j k : ι), i ≠ j →
    ‖(c i).1 - (c j).1‖ / 2 ≠ ‖(c k).1 - (c (σ k)).2‖ / 4 ∧
    ‖(c i).2 - (c j).2‖ / 2 ≠ ‖(c k).1 - (c (σ k)).2‖ / 4 ∧
    ‖(c i).1 - (c j).1‖ / 2 ≠ h ∧ ‖(c i).2 - (c j).2‖ / 2 ≠ h

private theorem volume_contact_stop (σ : Equiv.Perm ι) (i j k : ι) :
    volume {c : ι → ℂ × ℂ |
      ‖(c i).1 - (c j).1‖ / 2 = ‖(c k).1 - (c (σ k)).2‖ / 4} = 0 ∧
    volume {c : ι → ℂ × ℂ |
      ‖(c i).2 - (c j).2‖ / 2 = ‖(c k).1 - (c (σ k)).2‖ / 4} = 0 := by
  have hn : ∀ (a b : ι ⊕ ι),
      C 4 * squaredDistance a b - squaredDistance (Sum.inl k) (Sum.inr (σ k)) ≠ 0 →
      volume {c : ι → ℂ × ℂ | ‖configEquivSum ι c a - configEquivSum ι c b‖ / 2 =
        ‖(c k).1 - (c (σ k)).2‖ / 4} = 0 := by
    intro a b hp
    let P := C 4 * squaredDistance a b - squaredDistance (Sum.inl k) (Sum.inr (σ k))
    let e := (configEquivSum ι).trans (realCoordinates (ι ⊕ ι))
    have he : MeasurePreserving e volume volume :=
      (measurePreserving_realCoordinates (ι := ι ⊕ ι)).comp
        (measurePreserving_configEquivSum ι)
    have hm := he.measure_preimage_equiv {x | eval x P = 0}
    refine measure_mono_null (fun c hc => ?_) (hm.trans (volume_polynomial_zero P hp))
    change eval (realCoordinates (ι ⊕ ι) (configEquivSum ι c)) P = 0
    simp only [P, map_sub, map_mul, eval_C, eval_squaredDistance,
      configEquivSum_apply_inl, configEquivSum_apply_inr]
    change ‖configEquivSum ι c a - configEquivSum ι c b‖ / 2 =
      ‖(c k).1 - (c (σ k)).2‖ / 4 at hc
    have hnorm : ‖(c k).1 - (c (σ k)).2‖ =
        2 * ‖configEquivSum ι c a - configEquivSum ι c b‖ := by linarith
    rw [hnorm]
    ring
  exact ⟨hn _ _ (contactStop_ne_zero σ i j k), hn _ _ (contactStopMinus_ne_zero σ i j k)⟩

/-- The finite union over fixed matchings and labels is null, including the
contact coincidences with `r_k/4` and with `h = ε₀ R̄`. -/
theorem ae_noStoppingCoincidences (h : ℝ) :
    ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)), NoStoppingCoincidences h c := by
  classical
  simp only [NoStoppingCoincidences, ae_all_iff]
  intro σ i j k hij
  have hc : ∀ (e : ι → ι ⊕ ι), Function.Injective e →
      volume {c : ι → ℂ × ℂ |
        ‖configEquivSum ι c (e i) - configEquivSum ι c (e j)‖ / 2 = h} = 0 := by
    intro e he
    exact ((measurePreserving_configEquivSum ι).measure_preimage_equiv _).trans
      (volume_contact_cutoff (he.ne hij) h)
  have h1 : ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)),
      ‖(c i).1 - (c j).1‖ / 2 ≠ ‖(c k).1 - (c (σ k)).2‖ / 4 := by
    apply ae_iff.2
    simpa only [not_not] using (volume_contact_stop σ i j k).1
  have h2 : ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)),
      ‖(c i).2 - (c j).2‖ / 2 ≠ ‖(c k).1 - (c (σ k)).2‖ / 4 := by
    apply ae_iff.2
    simpa only [not_not] using (volume_contact_stop σ i j k).2
  have h3 : ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)), ‖(c i).1 - (c j).1‖ / 2 ≠ h := by
    apply ae_iff.2
    simpa only [not_not, configEquivSum_apply_inl] using hc Sum.inl Sum.inl_injective
  have h4 : ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)), ‖(c i).2 - (c j).2‖ / 2 ≠ h := by
    apply ae_iff.2
    simpa only [not_not, configEquivSum_apply_inr] using hc Sum.inr Sum.inr_injective
  filter_upwards [h1, h2, h3, h4] with c h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩

/-- The single exceptional set of Section 4.1: opposite-sign ties, same-sign ties,
and stopping coincidences. All its defining families are finite. -/
def OutsideExceptional (h : ℝ) (c : ι → ℂ × ℂ) : Prop :=
  (Function.Injective fun p : ι × ι => ‖(c p.1).1 - (c p.2).2‖) ∧
  (∀ i j k l : ι, i ≠ j → k ≠ l →
    ‖(c i).1 - (c j).1‖ = ‖(c k).1 - (c l).1‖ →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧
  (∀ i j k l : ι, i ≠ j → k ≠ l →
    ‖(c i).2 - (c j).2‖ = ‖(c k).2 - (c l).2‖ →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k)) ∧ NoStoppingCoincidences h c

/-- The exceptional set in the paper has measure zero. -/
theorem ae_outsideExceptional (h : ℝ) :
    ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)), OutsideExceptional h c := by
  have hs : ∀ (e : ι → ι ⊕ ι), Function.Injective e →
      ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)), ∀ i j k l : ι, i ≠ j → k ≠ l →
        ‖configEquivSum ι c (e i) - configEquivSum ι c (e j)‖ =
          ‖configEquivSum ι c (e k) - configEquivSum ι c (e l)‖ →
        (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    intro e he
    simp only [ae_all_iff]
    intro i j k l hij hkl
    by_cases hsame : (i = k ∧ j = l) ∨ (i = l ∧ j = k)
    · exact Filter.Eventually.of_forall fun _ _ => hsame
    have hn := volume_distance_eq (he.ne hij) (he.ne hkl) (by
      simpa only [he.eq_iff] using hsame)
    have hn' := (measurePreserving_configEquivSum ι).measure_preimage_equiv
      {z | ‖z (e i) - z (e j)‖ = ‖z (e k) - z (e l)‖}
    have ha : ∀ᵐ c ∂(volume : Measure (ι → ℂ × ℂ)),
        ‖configEquivSum ι c (e i) - configEquivSum ι c (e j)‖ ≠
        ‖configEquivSum ι c (e k) - configEquivSum ι c (e l)‖ := by
      apply ae_iff.2
      simpa only [not_not, Set.preimage_ofPred_eq] using hn'.trans hn
    exact ha.mono fun _ hc heq => (hc heq).elim
  filter_upwards [ae_injective_norm_sub, hs Sum.inl Sum.inl_injective,
    hs Sum.inr Sum.inr_injective, ae_noStoppingCoincidences h] with c hc hplus hminus hstop
  exact ⟨hc, hplus, hminus, hstop⟩

end MultipoleBKT.RouteGeneric

end
