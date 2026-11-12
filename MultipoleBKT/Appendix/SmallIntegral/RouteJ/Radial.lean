/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.API
public import MultipoleBKT.Appendix.RadialIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Ordered logarithmic radial integrals for J

See Lemma A.4. The integral below includes the core where the largest radius
is below λ. We compare that integral to the separated-core majorant before
using the logarithmic moments. The infinite-cutoff estimates integrate the
logarithmic moments directly.
-/

@[expose] public section

namespace MultipoleBKT.SmallIntegral.RouteJ

open MeasureTheory Set Finset
open MultipoleBKT.RouteLog
open scoped ENNReal

/-- The inner radii in (A.26), after fixing the largest radius `u`.
The logarithm uses the regularized largest and smallest radii. -/
noncomputable def innerRadial (β lam : ℝ) (k q : ℕ) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
    ENNReal.ofReal ((1 + Real.log (max u lam / minimumRadius lam r)) ^ q) *
      ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))

/-- The scalar radial integral of (A.26) for `k+2` dipoles, with one
specified largest-radius index. Angular factors are kept outside this integral. -/
noncomputable def orderedRadial (β lam h : ℝ) (k q : ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Ioc 0 h, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u

/-- The same ordered radial integral without a radial cutoff. -/
noncomputable def orderedRadialInfinity (β lam : ℝ) (k q : ℕ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi 0, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u

private theorem innerRadial_core_le {lam u : ℝ} (hlam : 0 < lam) (hu : u ≤ lam)
    (β : ℝ) (k q : ℕ) :
    innerRadial β lam k q u ≤ ENNReal.ofReal (lam ^ (4 - β) / 2) ^ (k + 1) := by
  have hsmall (r : Fin (k + 1) → ℝ)
      (hr : r ∈ Set.univ.pi (fun _ => Ioc 0 u)) :
      minimumRadius lam r = lam := by
    unfold minimumRadius
    apply le_antisymm
    · exact (inf'_le _ (mem_univ 0)).trans_eq (max_eq_right ((mem_univ_pi.mp hr 0).2.trans hu))
    · exact (le_inf'_iff _ _).mpr fun i _ => le_max_right _ _
  have he : innerRadial β lam k q u =
      ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β)) := by
    unfold innerRadial
    apply setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ioc)
    intro r hr
    dsimp only
    rw [hsmall r hr, max_eq_right hu, div_self hlam.ne', Real.log_one]
    simp
  rw [he]
  calc
    _ ≤ ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 lam),
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β)) :=
      lintegral_mono_set (Set.pi_mono fun _ _ => Ioc_subset_Ioc_right hu)
    _ = ENNReal.ofReal (lam ^ (4 - β) / 2) ^ (k + 1) := by
      change (∫⁻ r : Fin (k + 1) → ℝ, ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))
        ∂((Measure.pi fun _ => (volume : Measure ℝ)).restrict (Set.univ.pi fun _ => Ioc 0 lam))) = _
      rw [Measure.restrict_pi_pi,
        TwoComponentCoulomb.lintegral_fin_prod_eq_prod (fun _ => volume.restrict (Ioc 0 lam))
          (fun _ t => ENNReal.ofReal (t * max t lam ^ (2 - β))) (fun _ => by fun_prop)]
      have hscalar : (∫⁻ t in Ioc 0 lam, ENNReal.ofReal (t * max t lam ^ (2 - β))) =
          ENNReal.ofReal (lam ^ (4 - β) / 2) := by
        have h := lintegral_radialLogMoment (4 - β) 0 hlam le_rfl
        rw [radialLogMoment_split (4 - β) 0 hlam le_rfl] at h
        simpa only [show 4 - β - 2 = 2 - β by ring, pow_zero, mul_one,
          intervalIntegral.integral_same, add_zero] using h
      simp_rw [hscalar]
      simp

private theorem radial_core_le (β : ℝ) (k q : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    (∫⁻ u in Ioc 0 lam, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u) ≤
      ENNReal.ofReal (lam ^ ((4 - β) * (k + 2) - 2)) := by
  have hscalar : (∫⁻ u in Ioc 0 lam, ENNReal.ofReal (u * max u lam ^ (-β))) =
      ENNReal.ofReal (lam ^ (2 - β) / 2) := by
    have h := lintegral_radialLogMoment (2 - β) 0 hlam le_rfl
    rw [radialLogMoment_split (2 - β) 0 hlam le_rfl] at h
    simpa only [show 2 - β - 2 = -β by ring, pow_zero, mul_one,
      intervalIntegral.integral_same, add_zero] using h
  calc
    _ ≤ ∫⁻ u in Ioc 0 lam, ENNReal.ofReal (u * max u lam ^ (-β)) *
        ENNReal.ofReal (lam ^ (4 - β) / 2) ^ (k + 1) := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro u hu
      exact mul_le_mul_right (innerRadial_core_le hlam hu.2 β k q) _
    _ = ENNReal.ofReal (lam ^ (2 - β) / 2) *
        ENNReal.ofReal (lam ^ (4 - β) / 2) ^ (k + 1) := by
      rw [lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top), hscalar]
    _ ≤ ENNReal.ofReal (lam ^ (2 - β)) * ENNReal.ofReal (lam ^ (4 - β)) ^ (k + 1) := by
      gcongr <;> exact div_le_self (Real.rpow_nonneg hlam.le _) (by norm_num)
    _ = _ := by
      rw [← ENNReal.ofReal_pow (Real.rpow_nonneg hlam.le _),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hlam.le _),
        ← Real.rpow_natCast, ← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
      congr 2
      push_cast
      ring

private theorem outer_integrand_eq {lam u : ℝ} (hlam : 0 < lam) (hu : lam ≤ u)
    (β : ℝ) (k q : ℕ) :
    ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u =
      ENNReal.ofReal (u ^ (1 - β)) *
        ∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
          ENNReal.ofReal ((1 + Real.log (u / minimumRadius lam r)) ^ q) *
            ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β)) := by
  unfold innerRadial
  rw [max_eq_left hu]
  congr 2
  rw [mul_comm, ← Real.rpow_add_one (hlam.trans_le hu).ne']
  congr 1
  ring

/-- Comparison with the majorant, including the core below λ.
See (A.26). -/
theorem orderedRadial_le_orderedLogIntegral {lam h : ℝ} (hlam : 0 < lam) (hlh : lam ≤ h)
    (β : ℝ) (k q : ℕ) :
    orderedRadial β lam h k q ≤ orderedLogIntegral β lam h k q := by
  have hsplit : Ioc (0 : ℝ) h = Ioc 0 lam ∪ Ioc lam h := by
    ext u
    simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · rintro ⟨hu, huh⟩
      by_cases hul : u ≤ lam
      · exact Or.inl ⟨hu, hul⟩
      · exact Or.inr ⟨lt_of_not_ge hul, huh⟩
    · rintro (⟨hu, hul⟩ | ⟨hul, huh⟩)
      · exact ⟨hu, hul.trans hlh⟩
      · exact ⟨hlam.trans hul, huh⟩
  unfold orderedRadial orderedLogIntegral
  rw [hsplit]
  calc
    _ ≤ (∫⁻ u in Ioc 0 lam, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u) +
        ∫⁻ u in Ioc lam h, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u :=
      lintegral_union_le _ _ _
    _ ≤ _ := by
      apply add_le_add (radial_core_le β k q hlam)
      apply le_of_eq
      exact setLIntegral_congr_fun measurableSet_Ioc fun u hu => outer_integrand_eq hlam hu.1.le β k q

/-- The literal ordered logarithmic integral for `2 < β < 4` reduces to the
single power integral used by Lemma A.2. No positive power replaces a logarithm.
See the proof of Lemma A.4. -/
theorem orderedRadial_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam h k q ≤ ENNReal.ofReal (C *
        (lam ^ ((4 - β) * (k + 2) - 2) + ∫ u in lam..h, u ^ ((4 - β) * (k + 2) - 3))) := by
  obtain ⟨C, hC, hbound⟩ := ordered_radial_lt_four hβ hβ4 k q
  exact ⟨C, hC, fun lam h hlam hlh =>
    (orderedRadial_le_orderedLogIntegral hlam hlh β k q).trans (hbound lam h hlam hlh)⟩

/-- The critical and supercritical logarithmic bound for the literal ordered
integral. See the proof of Lemma A.4. -/
theorem orderedRadial_ge_four {β : ℝ} (hβ : 4 ≤ β) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam h : ℝ, 0 < lam → lam ≤ h →
      orderedRadial β lam h k q ≤ ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  obtain ⟨C, hC, hbound⟩ := ordered_radial_ge_four_bound hβ k q
  exact ⟨C, hC, fun lam h hlam hlh =>
    (orderedRadial_le_orderedLogIntegral hlam hlh β k q).trans (hbound lam h hlam hlh)⟩

private theorem infinite_bound_from_inner (β : ℝ) (k q l : ℕ) (A σ τ : ℝ)
    (hA : 0 < A) (hp : 0 < β - 2 - τ)
    (hE : σ + (2 - β + τ) = (4 - β) * (k + 2) - 2)
    (hinner : ∀ lam u : ℝ, 0 < lam → lam ≤ u →
      innerRadial β lam k q u ≤
        ENNReal.ofReal (A * lam ^ σ * u ^ τ * (1 + Real.log (u / lam)) ^ l)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedRadialInfinity β lam k q ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  let p := β - 2 - τ
  let C := 1 + A * momentConstant p l
  have hC : 0 < C := by
    dsimp only [C]
    have := momentConstant_pos hp l
    positivity
  refine ⟨C, hC, fun lam hlam => ?_⟩
  let E := (4 - β) * ((k : ℝ) + 2) - 2
  have htail : (∫⁻ u in Ioi lam,
      ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u) ≤
      ENNReal.ofReal (A * momentConstant p l * lam ^ E) := by
    calc
      _ ≤ ∫⁻ u in Ioi lam, ENNReal.ofReal (A * lam ^ σ) *
          ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / lam)) ^ l) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro u hu
        have hu0 : 0 < u := hlam.trans hu
        calc
          _ ≤ ENNReal.ofReal (u * max u lam ^ (-β)) *
              ENNReal.ofReal (A * lam ^ σ * u ^ τ * (1 + Real.log (u / lam)) ^ l) :=
            mul_le_mul_right (hinner lam u hlam hu.le) _
          _ = _ := by
            rw [max_eq_left hu.le,
              ← ENNReal.ofReal_mul (mul_nonneg hu0.le (Real.rpow_nonneg hu0.le _)),
              ← ENNReal.ofReal_mul (mul_nonneg hA.le (Real.rpow_nonneg hlam.le _))]
            congr 1
            have he : u * u ^ (-β) * u ^ τ = u ^ (-p - 1) := by
              rw [mul_comm u, ← Real.rpow_add_one hu0.ne', ← Real.rpow_add hu0]
              congr 1
              dsimp only [p]
              ring
            calc
              _ = (A * lam ^ σ) * ((u * u ^ (-β) * u ^ τ) *
                  (1 + Real.log (u / lam)) ^ l) := by ring
              _ = _ := by rw [he]
      _ = ENNReal.ofReal (A * lam ^ σ) *
          ∫⁻ u in Ioi lam, ENNReal.ofReal (u ^ (-p - 1) * (1 + Real.log (u / lam)) ^ l) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (A * lam ^ σ) *
          ENNReal.ofReal (lam ^ (-p) * momentConstant p l) :=
        mul_le_mul_right (lintegral_logarithmic_tail_scaled hp hlam l) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hA.le (Real.rpow_nonneg hlam.le _))]
        congr 1
        have he : σ + -p = E := by dsimp only [p, E]; linarith [hE]
        calc
          _ = A * momentConstant p l * (lam ^ σ * lam ^ (-p)) := by ring
          _ = _ := by rw [← Real.rpow_add hlam, he]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 lam ∪ Ioi lam := by
    ext u
    simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro hu
      by_cases h : u ≤ lam
      · exact Or.inl ⟨hu, h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨hu, _⟩ | hu)
      · exact hu
      · exact hlam.trans hu
  unfold orderedRadialInfinity
  rw [hsplit]
  calc
    _ ≤ (∫⁻ u in Ioc 0 lam, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u) +
        ∫⁻ u in Ioi lam, ENNReal.ofReal (u * max u lam ^ (-β)) * innerRadial β lam k q u :=
      lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (lam ^ E) + ENNReal.ofReal (A * momentConstant p l * lam ^ E) :=
      add_le_add (radial_core_le β k q hlam) htail
    _ = _ := by
      rw [← ENNReal.ofReal_add (Real.rpow_nonneg hlam.le _) (by
        exact mul_nonneg (mul_nonneg hA.le (momentConstant_pos hp l).le) (Real.rpow_nonneg hlam.le _))]
      congr 1
      dsimp only [C, E]
      ring

/-- Infinite-cutoff logarithmic convergence below the critical temperature.
The size condition is exactly the strict decay exponent in the outer integral.
See the proof of Lemma A.4. -/
theorem orderedRadialInfinity_lt_four {β : ℝ} (hβ : 2 < β) (hβ4 : β < 4)
    (k q : ℕ) (hsize : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedRadialInfinity β lam k q ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  have ha : 0 < 4 - β := by linarith
  have hneg : (4 - β) * ((k : ℝ) + 2) - 2 < 0 := by
    have h := (Appendix.transitionBeta_lt_iff (by omega : 1 ≤ k + 2) β).mp
      ((Appendix.le_pStar_iff (by omega : 1 ≤ k + 2)).mp hsize)
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  let A := ((k : ℝ) + 1) * momentConstant (4 - β) q * momentConstant (4 - β) 0 ^ k
  apply infinite_bound_from_inner β k q 0 A 0 ((4 - β) * (k + 1))
    (by dsimp only [A]; have := momentConstant_pos ha q; have := momentConstant_pos ha 0; positivity)
    (by nlinarith) (by ring)
  intro lam u hlam hlu
  have hb := ordered_inner_log_moment hβ hβ4 k q hlam hlu
  simpa only [innerRadial, max_eq_left hlu, Real.rpow_zero, pow_zero, mul_one] using hb

/-- Infinite-cutoff logarithmic convergence at and above the critical temperature.
The critical inner moment retains its logarithm. Above four the inner zeroth
moment is bounded, and the outer logarithmic moment converges in both cases.
See the proof of Lemma A.4. -/
theorem orderedRadialInfinity_ge_four {β : ℝ} (hβ : 4 ≤ β) (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedRadialInfinity β lam k q ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  by_cases heq : β = 4
  · subst β
    let A := ((k : ℝ) + 1) * (1 / 2 + 1 / ((q : ℝ) + 1)) * (3 / 2 : ℝ) ^ k
    apply infinite_bound_from_inner 4 k q (k + 1 + q) A 0 0
      (by dsimp only [A]; positivity) (by norm_num) (by ring)
    intro lam u hlam hlu
    have hb := lintegral_minimum_log_le_zero (k := k) q hlam hlu
    have hL : 0 ≤ 1 + Real.log (u / lam) := by
      have := Real.log_nonneg ((one_le_div hlam).mpr hlu)
      linarith
    convert hb using 1
    · simp only [innerRadial, max_eq_left hlu]
      norm_num
    · dsimp only [A]
      simp (disch := positivity) only [Real.rpow_zero, mul_one, ENNReal.ofReal_mul,
        ENNReal.ofReal_pow, ENNReal.ofReal_add, ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  · have hgt : 4 < β := lt_of_le_of_ne hβ (Ne.symm heq)
    let a := 4 - β
    have ha : a < 0 := by dsimp only [a]; linarith
    let c := 1 / 2 + 1 / (-a)
    have hc : 0 < c := by dsimp only [c]; have : 0 < -a := neg_pos.mpr ha; positivity
    let A := ((k : ℝ) + 1) * c ^ (k + 1)
    apply infinite_bound_from_inner β k q q A (a * (k + 1)) 0
      (by dsimp only [A]; positivity) (by linarith) (by dsimp only [a]; ring)
    intro lam u hlam hlu
    have hb := lintegral_minimum_log_le_of_neg (k := k) ha q hlam hlu
    have hL : 0 ≤ 1 + Real.log (u / lam) := by
      have := Real.log_nonneg ((one_le_div hlam).mpr hlu)
      linarith
    have he : a - 2 = 2 - β := by dsimp only [a]; ring
    rw [he] at hb
    change (∫⁻ r in Set.univ.pi (fun _ : Fin (k + 1) => Ioc 0 u),
      ENNReal.ofReal ((1 + Real.log (max u lam / minimumRadius lam r)) ^ q) *
        ∏ i, ENNReal.ofReal (r i * max (r i) lam ^ (2 - β))) ≤ _
    rw [max_eq_left hlu]
    refine hb.trans (le_of_eq ?_)
    have hpow : lam ^ (a * (k + 1)) = (lam ^ a) ^ (k + 1) := by
      rw [Real.rpow_mul hlam.le,
        show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast]
    rw [hpow]
    dsimp only [A, c]
    simp (disch := positivity) only [Real.rpow_zero, mul_one, ENNReal.ofReal_mul,
      ENNReal.ofReal_pow, ENNReal.ofReal_add, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

/-- The radius restriction asserted for `Ĵ_∞` gives a finite logarithmic
radial majorant, with the stated λ exponent, in all temperature regimes.
See Lemma A.4. -/
theorem orderedRadialInfinity_bound {β : ℝ} (hβ : 2 < β) (k q : ℕ)
    (hsize : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam →
      orderedRadialInfinity β lam k q ≤
        ENNReal.ofReal (C * lam ^ ((4 - β) * (k + 2) - 2)) := by
  rcases lt_or_ge β 4 with hβ4 | hβ4
  · exact orderedRadialInfinity_lt_four hβ hβ4 k q hsize
  · exact orderedRadialInfinity_ge_four hβ4 k q

/-- The ordered logarithmic radial bound in the normalization of (A.27).
Below four, this invokes Lemma A.2 only after the logarithmic integration. -/
theorem orderedRadial_bound {β eps : ℝ} (hβ : 2 < β) (heps : 0 < eps) (heps1 : eps < 1)
    (k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam ≤ Appendix.lamBound eps (k + 2) →
      orderedRadial β lam (eps * truncationScale p₀ β lam) k q ≤
        ENNReal.ofReal (C * (lam ^ ((2 - β) * (k + 2)) * Appendix.gammaBeta p₀ β lam (k + 2))) := by
  rcases lt_or_ge β 4 with hβ4 | hβ4
  · obtain ⟨C, hC, hbound⟩ := orderedRadial_lt_four hβ hβ4 k q
    refine ⟨C * Appendix.radialConst β (k + 2) eps,
      mul_pos hC (Appendix.radialConst_pos (by omega) heps), fun p₀ lam hlam hlamB => ?_⟩
    obtain ⟨hlam12, hlameps, _⟩ := Appendix.le_of_le_lamBound hlamB
    have hlh : lam ≤ eps * truncationScale p₀ β lam := by
      exact hlameps.trans (le_mul_of_one_le_right heps.le
        (Appendix.one_le_truncationScale hβ hlam (by linarith)))
    have heq : lam ^ ((4 - β) * (k + 2) - 2) +
        (∫ u in lam..(eps * truncationScale p₀ β lam), u ^ ((4 - β) * (k + 2) - 3)) =
          Appendix.radialIntegral p₀ β lam (k + 2) eps := by
      rw [Appendix.radialIntegral_eq, Appendix.integral_indicator_Iic,
        Appendix.integral_Ioc_max_rpow hlam hlh]
      have he : ((4 - β) * ((k + 2 : ℕ) : ℝ) - 2) - 1 =
          (4 - β) * ((k : ℝ) + 2) - 3 := by push_cast; ring
      rw [he]
      simp only [show (4 - β) * ((k : ℝ) + 2) - 3 + 1 =
        (4 - β) * ((k : ℝ) + 2) - 2 by ring]
    have hb := hbound lam _ hlam hlh
    rw [heq] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hu := (Appendix.lemsupplapp_two_sided p₀ hβ (by omega : 1 ≤ k + 2) heps heps1 lam hlam hlamB).2.2
    calc
      C * Appendix.radialIntegral p₀ β lam (k + 2) eps ≤
          C * (Appendix.radialConst β (k + 2) eps *
            (lam ^ ((2 - β) * ((k + 2 : ℕ) : ℝ)) * Appendix.gammaBeta p₀ β lam (k + 2))) :=
        mul_le_mul_of_nonneg_left hu hC.le
      _ = _ := by push_cast; ring
  · obtain ⟨C, hC, hbound⟩ := orderedRadial_ge_four hβ4 k q
    refine ⟨C, hC, fun p₀ lam hlam hlamB => ?_⟩
    obtain ⟨hlam12, hlameps, _⟩ := Appendix.le_of_le_lamBound hlamB
    have hlh : lam ≤ eps * truncationScale p₀ β lam :=
      hlameps.trans (le_mul_of_one_le_right heps.le
        (Appendix.one_le_truncationScale hβ hlam (by linarith)))
    have hneg : (4 - β) * ((k + 2 : ℕ) : ℝ) - 2 < 0 := by
      have hk : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have heq := Appendix.target_neg (p₀ := p₀) hlam (by omega : 1 ≤ k + 2) hneg
    have hb := hbound lam _ hlam hlh
    simp only [Nat.cast_add, Nat.cast_ofNat] at heq
    rw [heq]
    exact hb

/-- The infinite ordered logarithmic bound in the γ notation, with its size
restriction explicit. See Lemma A.4. -/
theorem orderedRadialInfinity_gamma {β : ℝ} (hβ : 2 < β) (k q : ℕ)
    (hsize : ((k + 2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam →
      orderedRadialInfinity β lam k q ≤
        ENNReal.ofReal (C * (lam ^ ((2 - β) * (k + 2)) * Appendix.gammaBeta p₀ β lam (k + 2))) := by
  obtain ⟨C, hC, hbound⟩ := orderedRadialInfinity_bound hβ k q hsize
  refine ⟨C, hC, fun p₀ lam hlam => ?_⟩
  have hneg := (Appendix.transitionBeta_lt_iff (by omega : 1 ≤ k + 2) β).mp
    ((Appendix.le_pStar_iff (by omega : 1 ≤ k + 2)).mp hsize)
  have heq := Appendix.target_neg (p₀ := p₀) hlam (by omega : 1 ≤ k + 2) hneg
  have hb := hbound lam hlam
  simp only [Nat.cast_add, Nat.cast_ofNat] at heq
  rw [heq]
  exact hb

end MultipoleBKT.SmallIntegral.RouteJ

end
