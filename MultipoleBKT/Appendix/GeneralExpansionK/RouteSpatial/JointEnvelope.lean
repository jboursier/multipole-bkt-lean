/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailRelabel
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.BaselineSource

/-!
# Finite tree integration in case F

See Step 4 of
the proof of Lemma A.7. The near, odd and even
edge families remain a disjoint partition of one original tree. All shape
choices are summed before their logarithmic configuration integrals.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral SmallIntegral.RouteJ
open scoped Classical ENNReal

/-- The complete finite tree shape, including its three separate edge families. -/
structure JointShape (W : Type*) [Fintype W] [DecidableEq W] where
  tree : SimpleGraph W
  odd : Finset (Sym2 W)
  even : Finset (Sym2 W)
  near : Finset (Sym2 W)
  isTree : tree.IsTree
  partition : odd ∪ (even ∪ near) = tree.edgeFinset
  disjoint_odd : Disjoint odd (even ∪ near)
  disjoint_even : Disjoint even near

instance {W : Type*} [Fintype W] [DecidableEq W] : Finite (JointShape W) := by
  apply Finite.of_injective (fun s : JointShape W => (s.tree,s.odd,s.even,s.near))
  intro s t he
  cases s
  cases t
  cases he
  rfl

noncomputable instance {W : Type*} [Fintype W] [DecidableEq W] : Fintype (JointShape W) := Fintype.ofFinite _

/-- All choices are bounded uniformly in the number of labels. -/
theorem card_jointShape_le {W : Type*} [Fintype W] [DecidableEq W] :
    Fintype.card (JointShape W) ≤ (2 ^ ((Fintype.card W+1).choose 2)) ^ 4 := by
  have hi : Function.Injective (fun s : JointShape W => (s.tree.edgeFinset,s.odd,s.even,s.near)) := by
    intro s t he
    have ht : s.tree = t.tree := edgeFinset_inj.1 (congrArg Prod.fst he)
    cases s
    cases t
    simp only [Prod.mk.injEq] at he
    cases ht
    rcases he with ⟨-,rfl,rfl,rfl⟩
    rfl
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_prod,Fintype.card_finset,Sym2.card,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hc

/-- The full finite envelope for the unbounded original trees. -/
noncomputable def jointEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam : ℝ) (c : W → ℂ × ℂ) : ℝ≥0∞ :=
  ∑ s : JointShape W, jointTreeDensity χ β M lam s.odd s.even s.near c

/-- A selected complete original shape is one summand of the fixed envelope. -/
theorem le_jointEnvelope {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (χ : ℂ → ℝ) (β M lam : ℝ) (s : JointShape W) (c : W → ℂ × ℂ) :
    jointTreeDensity χ β M lam s.odd s.even s.near c ≤ jointEnvelope χ β M lam c := by
  unfold jointEnvelope
  exact single_le_sum (f := fun s : JointShape W => jointTreeDensity χ β M lam s.odd s.even s.near c)
    (fun _ _ => bot_le) (mem_univ s)

/-- Case F for the finite envelope on any original-label carrier. -/
theorem caseF_jointEnvelope_bound {χ : ℂ → ℝ} {β M : ℝ}
    (hχ : IsMollifier χ) (hβ : 2 < β) (hM : 1 ≤ M) (p₀ k : ℕ)
    (hkp : ((k+2 : ℕ) : ℕ∞) ≤ pStar β) :
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ lam : ℝ, 0 < lam → lam ≤ eps →
      ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W], Fintype.card W = k+2 →
      ∀ n : ℕ, (∫⁻ c in boxConfig W n ∩
          {c : W → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
        jointEnvelope χ β M lam c) ≤
        ENNReal.ofReal (C * n * lam ^ ((2-β)*(k+2)) * truncationScale p₀ β lam ^ (-2 : ℝ)) := by
  intro eps heps heps1
  obtain ⟨A,hA,ha⟩ := jointTree_tail_le_radial_any hχ (by linarith : 0 ≤ β) hM k
  obtain ⟨B,hB,hb⟩ := caseF_vector_bound_any hβ p₀ k hkp eps heps heps1
  let D : ℝ := ((2 ^ ((k+2+1).choose 2)) ^ 4 + 1 : ℕ)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D*(A*B),by positivity,?_⟩
  intro lam hlam hle W _ _ _ hW n
  unfold jointEnvelope
  rw [lintegral_finsetSum _ (fun s _ => measurable_jointTreeDensity hχ β M hlam s.odd s.even s.near)]
  let V := A * B * n * lam ^ ((2-β)*(k+2)) * truncationScale p₀ β lam ^ (-2 : ℝ)
  have hV : 0 ≤ V := by
    have ht := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
    dsimp [V]
    positivity
  have hterm (s : JointShape W) : (∫⁻ c in boxConfig W n ∩
      {c : W → ℂ × ℂ | eps * truncationScale p₀ β lam < maxRad lam c},
      jointTreeDensity χ β M lam s.odd s.even s.near c) ≤ ENNReal.ofReal V := by
    have hs := ha W hW lam (eps * truncationScale p₀ β lam) hlam s.tree s.isTree
      s.odd s.even s.near s.partition s.disjoint_odd s.disjoint_even n
    refine hs.trans ((mul_le_mul' le_rfl (hb lam hlam hle W hW)).trans_eq ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg hA.le (Nat.cast_nonneg _))]
    congr 1
    dsimp [V]
    ring
  calc
    _ ≤ ∑ _s : JointShape W, ENNReal.ofReal V := sum_le_sum fun s _ => hterm s
    _ = ENNReal.ofReal ((Fintype.card (JointShape W) : ℝ)*V) := by
      rw [sum_const,card_univ,nsmul_eq_mul,← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (D*V) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by
      have hc := card_jointShape_le (W := W)
      rw [hW] at hc
      dsimp [D]
      exact_mod_cast (hc.trans (Nat.le_add_right _ 1))) hV)
    _ = _ := by congr 1; dsimp [V]; ring

end MultipoleBKT.ExpansionK.RouteSpatial

end
