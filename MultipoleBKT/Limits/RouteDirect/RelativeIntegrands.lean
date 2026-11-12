/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteDirect.Dipole
public import MultipoleBKT.Limits.RouteDirect.Coordinates
public import MultipoleBKT.Limits.RouteDirect.BlockIntegrable

/-!
# The specified limiting integrands on the domains used in the paper

See (4.48), (4.50),
(4.49), and Lemma 4.26.
The full singleton and block averages are restricted to a fixed origin.
-/

@[expose] public section

namespace MultipoleBKT.Limits.RouteDirect

open MeasureTheory Finset Set SimpleGraph Filter Topology SmallIntegral
open scoped Classical ENNReal

variable {I B : Type*} [Fintype I] [ordI : LinearOrder I] [Fintype B] [DecidableEq B]
variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-- The full specified `G'`, with `x_root=0` and all remaining endpoints free. -/
noncomputable def Gprime (χ : ℂ → ℝ) (β lam : ℝ) (E : SimpleGraph I) (root : I)
    (p : RelativeCoordinates root) : ℝ := singletonBox χ β lam E (relativeLift root p)

/-- The full specified `G''`, averaged over the original blocks. -/
noncomputable def GdoublePrime [DecidableEq I] (χ : ℂ → ℝ) (β lam M : ℝ) (blk : I → B)
    (E : SimpleGraph I) (root : I) (p : RelativeCoordinates root) : ℝ :=
  symBox χ β lam M blk E (relativeLift root p)

/-- The pointwise fixed-origin identity (4.48). -/
theorem Gprime_representation (E : SimpleGraph I) (root : I) (c : I → ℂ × ℂ) :
    singletonBox χ β lam E c = Gprime χ β lam E root (relativeEndpoints root c) := by
  unfold Gprime
  rw [relativeLift_relativeEndpoints, singletonBox_translate]

/-- The pointwise fixed-origin identity (4.50). -/
theorem GdoublePrime_representation [DecidableEq I] (blk : I → B) (E : SimpleGraph I)
    (root : I) (c : I → ℂ × ℂ) :
    symBox χ β lam M blk E c = GdoublePrime χ β lam M blk E root (relativeEndpoints root c) := by
  unfold GdoublePrime
  rw [relativeLift_relativeEndpoints, symBox_translate]

/-- The original block average absorbs the average over every merger of
those blocks. This is the subgroup identity in Lemma 4.26. -/
theorem symBox_subgroup [DecidableEq I] {C : Type*} [Fintype C] [DecidableEq C]
    (blk : I → B) (q : B → C) (E : SimpleGraph I) (c : I → ℂ × ℂ) :
    reversalAverage blk (reversalAverage (q ∘ blk) (multBox χ β lam M blk E)) c =
      symBox χ β lam M blk E c := reversalAverage_subgroup blk q _ c

/-- Well-definedness of the full `G'` integral in (4.49). -/
theorem integrable_Gprime (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (E : SimpleGraph I) (hE : E.Connected) (root : I) :
    Integrable (Gprime χ β lam E root) := by
  have : Nonempty I := ⟨root⟩
  exact integrable_relative root (measurable_singletonBox hχ hlam E) (singletonBox_translate E)
    (integrable_anchor_singletonBox hχ hβ hlam hk E hE root)

/-- Well-definedness of the full `G''` integral in (4.51). -/
theorem integrable_GdoublePrime [DecidableEq I] (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 1 ≤ M) (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b') (root : I) :
    Integrable (GdoublePrime χ β lam M blk E root) := by
  have : Nonempty I := ⟨root⟩
  exact integrable_relative root (measurable_symBox hχ hlam blk E) (symBox_translate blk E)
    (integrable_anchor_symBox_log hχ hβ hlam hM hk blk hblk E hinter hconn root)

/-- Identification of each displayed `G''` integral, with the original
block average and the literal relative-coordinate carrier. -/
theorem integral_symBox_eq_GdoublePrime [DecidableEq I]
    (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam) (hM : 1 ≤ M)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β)
    (blk : I → B) (hblk : Function.Surjective blk) (E : SimpleGraph I)
    (hinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hconn : ∀ b b', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable b b') (root : I) :
    (∫ c, anchorR root c * symBox χ β lam M blk E c) =
      ∫ p : RelativeCoordinates root, GdoublePrime χ β lam M blk E root p := by
  have : Nonempty I := ⟨root⟩
  exact integral_anchor_eq_relative root (measurable_symBox hχ hlam blk E) (symBox_translate blk E)
    (integrable_anchor_symBox_log hχ hβ hlam hM hk blk hblk E hinter hconn root)

/-- The single-block integrand `G_S` on the same fixed-origin coordinates. -/
noncomputable def Gsingle (χ : ℂ → ℝ) (β lam M : ℝ) (root : I)
    (p : RelativeCoordinates root) : ℝ := multipoleBox χ β lam M (relativeLift root p)

/-- The pointwise fixed-origin identity (4.46). -/
theorem Gsingle_representation (root : I) (c : I → ℂ × ℂ) :
    multipoleBox χ β lam M c = Gsingle χ β lam M root (relativeEndpoints root c) := by
  unfold Gsingle
  rw [relativeLift_relativeEndpoints, translationInvariant_multipoleBox]

/-- Identification of the denominator integrals in (4.51). -/
theorem integral_multipoleBox_eq_Gsingle (hχ : IsMollifier χ) (hβ : 2 < β)
    (hlam : 0 < lam) (hM : 0 ≤ M) (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (root : I) :
    (∫ c, anchorR root c * multipoleBox χ β lam M c) =
      ∫ p : RelativeCoordinates root, Gsingle χ β lam M root p := by
  have : Nonempty I := ⟨root⟩
  exact integral_anchor_eq_relative root (measurable_multipoleBox hχ hlam β M)
    translationInvariant_multipoleBox (integrable_anchor_multipoleBox hχ hβ hlam hM hk root)

/-- Identification of each displayed `G'` integral. -/
theorem integral_singletonBox_eq_Gprime (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hk : (Fintype.card I : ℕ∞) ≤ pStar β) (E : SimpleGraph I) (hE : E.Connected) (root : I) :
    (∫ c, anchorR root c * singletonBox χ β lam E c) =
      ∫ p : RelativeCoordinates root, Gprime χ β lam E root p := by
  have : Nonempty I := ⟨root⟩
  exact integral_anchor_eq_relative root (measurable_singletonBox hχ hlam E)
    (singletonBox_translate E) (integrable_anchor_singletonBox hχ hβ hlam hk E hE root)

/-- The full `G'` coefficient is the literal displayed sum of fixed-origin
integrals, with the single-dipole integral in the denominator. -/
theorem dipoleCoefficient_eq_relative (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    {V : Finset ℕ} (root : V) (hk : (V.card : ℕ∞) ≤ pStar β) :
    dipoleCoefficient χ β lam V root =
      (∑ E ∈ (univ : Finset (SimpleGraph V)).filter (fun E => E.Connected ∧ E.edgeSet.Nonempty),
        ∫ p : RelativeCoordinates root, Gprime χ β lam E root p) /
          (∫ z : ℂ, Real.exp (β * smearedKernel χ lam z)) ^ V.card := by
  have hk' : (Fintype.card V : ℕ∞) ≤ pStar β := by simpa only [Fintype.card_coe] using hk
  unfold dipoleCoefficient
  apply congrArg (fun x : ℝ => x / (∫ z : ℂ, Real.exp (β * smearedKernel χ lam z)) ^ V.card)
  apply sum_congr rfl
  intro E hE
  convert integral_singletonBox_eq_Gprime hχ hβ hlam hk' E (mem_filter.mp hE).2.1 root using 1
  congr 3
  congr 1
  exact Subsingleton.elim _ _

/-- Direct identification of the dipole limit with the displayed `G'` integral. -/
theorem tendsto_dipoleActivity_relative (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    {V : Finset ℕ} (root : V) (hk : (V.card : ℕ∞) ≤ pStar β) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (V.card - 1) * dipoleActivity χ N β lam V) atTop
      (𝓝 ((∑ E ∈ (univ : Finset (SimpleGraph V)).filter (fun E => E.Connected ∧ E.edgeSet.Nonempty),
        ∫ p : RelativeCoordinates root, Gprime χ β lam E root p) /
          (∫ z : ℂ, Real.exp (β * smearedKernel χ lam z)) ^ V.card)) := by
  rw [← dipoleCoefficient_eq_relative hχ hβ hlam root hk]
  exact tendsto_dipoleActivity_integral hχ hβ hlam root hk

end MultipoleBKT.Limits.RouteDirect

end
