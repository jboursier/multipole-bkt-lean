/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.RouteJ.VectorRadial
public import MultipoleBKT.Limits.RouteBase.Integrand

/-!
# The final logarithmic absorption in the limiting integrals

See Lemma 4.26 of the paper. Spatial integration is completed before choosing a small
positive power. The remaining logarithmic radial integral then factorizes.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set
open SmallIntegral SmallIntegral.RouteJ
open scoped ENNReal

/-- A logarithmic power is bounded by any positive power at infinity.
The coefficient is explicit and independent of the radii and of λ. -/
theorem one_add_log_pow_le {η : ℝ} (hη : 0 < η) (q : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (1 + Real.log x) ^ q ≤ (1 + (q : ℝ) / η) ^ q * x ^ η := by
  by_cases hq : q = 0
  · subst q
    simpa using Real.one_le_rpow hx hη.le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have he : 0 < η / q := div_pos hη hq0
  have hlog := Real.log_le_rpow_div hx0.le he
  have hp : 1 ≤ x ^ (η / q) := Real.one_le_rpow hx he.le
  have hbase : 1 + Real.log x ≤ (1 + (q : ℝ) / η) * x ^ (η / q) := by
    have hid : x ^ (η / q) / (η / q) = (q : ℝ) / η * x ^ (η / q) := by field_simp
    rw [hid] at hlog
    nlinarith
  have hpow : (x ^ (η / q)) ^ q = x ^ η := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    field_simp
  calc
    _ ≤ ((1 + (q : ℝ) / η) * x ^ (η / q)) ^ q :=
      pow_le_pow_left₀ (by linarith [Real.log_nonneg hx]) hbase q
    _ = _ := by rw [mul_pow, hpow]

/-- The precise product-power absorption used after the spatial logarithms.
Here `R` and `m` are the largest and smallest regularized radii. -/
theorem logarithm_absorption {I : Type*} [Fintype I] [Nonempty I]
    (ρ : I → ℝ) {lam R m η : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hρ : ∀ i, lam ≤ ρ i) (hm : lam ≤ m) (hmR : m ≤ R)
    (hR : ∃ i, ρ i = R) (q : ℕ) :
    (1 + Real.log (R / m)) ^ q ≤
      (1 + (q : ℝ) / η) ^ q * ∏ i, (ρ i / lam) ^ η := by
  classical
  have hm0 : 0 < m := hlam.trans_le hm
  have hR0 : 0 < R := hm0.trans_le hmR
  have hquot : 1 ≤ R / m := (one_le_div hm0).mpr hmR
  obtain ⟨i₀, hi₀⟩ := hR
  have hratio : (R / m) ^ η ≤ (ρ i₀ / lam) ^ η := by
    apply Real.rpow_le_rpow (by positivity) _ hη.le
    rw [hi₀]
    exact div_le_div_of_nonneg_left hR0.le hlam hm
  have hprod : (ρ i₀ / lam) ^ η ≤ ∏ i, (ρ i / lam) ^ η := by
    rw [← mul_prod_erase univ (fun i => (ρ i / lam) ^ η) (mem_univ i₀)]
    apply le_mul_of_one_le_right (Real.rpow_nonneg (div_nonneg (hlam.trans_le (hρ i₀)).le hlam.le) _)
    exact Finset.one_le_prod₀ (fun i _ => Real.one_le_rpow ((one_le_div hlam).mpr (hρ i)) hη.le)
  exact (one_add_log_pow_le hη q hquot).trans
    (mul_le_mul_of_nonneg_left (hratio.trans hprod) (by positivity))

/-- Absorb the logarithms and distribute the inverse square of the largest
radius. This is the pointwise factorization in Lemma 4.26. -/
theorem logRadialWeight_le_product {I : Type*} [Fintype I] [Nonempty I]
    {β lam η : ℝ} (hlam : 0 < lam) (hη : 0 < η) (q : ℕ) (u : I → ℂ) :
    logRadialWeight β lam q u ≤
      ((1 + (q : ℝ) / η) ^ q * lam ^ (-η * Fintype.card I)) *
        ∏ i, rho lam (u i) ^ (2 - 2 / (Fintype.card I : ℝ) + η - β) := by
  classical
  let k := Fintype.card I
  let a := 2 - 2 / (k : ℝ) + η - β
  let ρ := fun i => rho lam (u i)
  let R := maxRho lam u
  have hρ : ∀ i, 0 < ρ i := fun i => rho_pos hlam _
  have hR : ∀ i, ρ i ≤ R := fun i => rho_le_maxRho lam u i
  have hRm : minRho lam u ≤ R := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (minRho_le_rho lam u i).trans (hR i)
  have hmax : ∃ i, ρ i = R := by
    obtain ⟨i, _, hi⟩ := exists_max_image univ ρ univ_nonempty
    refine ⟨i, le_antisymm (hR i) ?_⟩
    exact (fold_max_le _).mpr ⟨(lam_le_rho lam (u i)), fun j hj => hi j hj⟩
  have hlog := logarithm_absorption ρ hlam hη (fun i => lam_le_rho lam (u i))
    (lam_le_minRho lam u) hRm hmax q
  have hord := prod_rpow_mul_rpow_neg_le ρ hρ hR (by norm_num : (0 : ℝ) ≤ 2)
  have hrad : R ^ (-2 : ℝ) * ∏ i, ρ i ^ (2 - β) ≤ ∏ i, ρ i ^ (2 - 2 / (k : ℝ) - β) := by
    have h := mul_le_mul_of_nonneg_right hord
      (prod_nonneg (s := (Finset.univ : Finset I))
        (fun i _ => Real.rpow_nonneg (hρ i).le (-β)))
    rw [mul_assoc, ← prod_mul_distrib, ← prod_mul_distrib] at h
    simpa only [← Real.rpow_add (hρ _), show (2 : ℝ) + -β = 2 - β by ring,
      show 2 - 2 / (Fintype.card I : ℝ) + -β = 2 - 2 / (k : ℝ) - β by rfl] using h
  have heq : (∏ i, (ρ i / lam) ^ η) * (∏ i, ρ i ^ (2 - 2 / (k : ℝ) - β)) =
      lam ^ (-η * k) * ∏ i, ρ i ^ a := by
    simp_rw [Real.div_rpow (hρ _).le hlam.le, div_eq_mul_inv,
      ← Real.rpow_neg hlam.le]
    rw [Finset.prod_mul_distrib, Finset.prod_const, card_univ,
      ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    rw [mul_assoc, mul_comm (∏ i, ρ i ^ η), mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply prod_congr rfl
    intro i _
    rw [← Real.rpow_add (hρ i)]
    congr 1
    dsimp only [a]
    ring
  change (1 + Real.log (R / minRho lam u)) ^ q *
    (R ^ (-2 : ℝ) * ∏ i, ρ i ^ (2 - β)) ≤ _
  calc
    _ ≤ ((1 + (q : ℝ) / η) ^ q * ∏ i, (ρ i / lam) ^ η) *
        ∏ i, ρ i ^ (2 - 2 / (k : ℝ) - β) :=
      mul_le_mul hlog hrad
        (mul_nonneg (Real.rpow_nonneg (maxRho_pos hlam u).le _)
          (prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _))
        (mul_nonneg (pow_nonneg (by positivity) _)
          (prod_nonneg fun i _ => Real.rpow_nonneg (div_nonneg (hρ i).le hlam.le) _))
    _ = _ := by rw [mul_assoc, heq]; dsimp only [ρ]; ring

/-- The full logarithmic radial majorant is integrable at every positive λ.
This is the final small-power step of Lemma 4.26, with all radii present. -/
theorem lintegral_logRadialWeight_lt_top {I : Type*} [Fintype I] [Nonempty I]
    {β lam : ℝ} (_hβ : 2 < β) (hlam : 0 < lam)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (q : ℕ) :
    ∫⁻ u : I → ℂ, ENNReal.ofReal (logRadialWeight β lam q u) < ∞ := by
  classical
  let k := Fintype.card I
  have hgap := two_sub_two_div_lt_of_le_pStar (Fintype.card_pos (α := I)) hk
  let η := (β - 4 + 2 / (k : ℝ)) / 2
  have hη : 0 < η := by dsimp only [η, k]; linarith
  let a := 2 - 2 / (k : ℝ) + η - β
  have ha : a < -2 := by dsimp only [a, η, k]; linarith
  let C := (1 + (q : ℝ) / η) ^ q * lam ^ (-η * k)
  have hpoint (u : I → ℂ) : logRadialWeight β lam q u ≤ C * ∏ i, rho lam (u i) ^ a :=
    logRadialWeight_le_product hlam hη q u
  have hint : Integrable (fun u : I → ℂ => C * ∏ i, rho lam (u i) ^ a) := by
    apply Integrable.const_mul
    rw [volume_pi]
    exact Integrable.fintype_prod (fun _ => integrable_rpow_rho hlam ha)
  exact (lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hpoint u)).trans_lt hint.lintegral_lt_top

end MultipoleBKT.Limits.RouteDirect

end
