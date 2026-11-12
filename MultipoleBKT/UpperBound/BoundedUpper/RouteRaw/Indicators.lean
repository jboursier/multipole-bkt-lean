/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Components

/-!
# Full separation within odd components

The paper: Proposition 5.18. These are the complete inter-block separation products,
including pairs absent from the odd graph. They remain in the integrand
until each component's replacement-tree tail has been established.
-/

@[expose] public section

namespace MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

open MeasureTheory Finset Hierarchical Multipole Parity SetPartition
open scoped Classical

/-- All inter-block pairs in one odd component are separated. -/
noncomputable def componentSeparation (M lam : ℝ) (Y : Finset (Finset ℕ))
    (c : ℕ → ℂ × ℂ) : ℝ :=
  ∏ p ∈ interPairs Y, if MultipoleLinked M lam (c p.1) (c p.2) then 0 else 1

/-- The full separation product over the nontrivial odd components. -/
noncomputable def oddSeparation (M lam : ℝ) (X : Finset (Finset ℕ))
    (E₁ : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  ∏ Y ∈ oddComponents X E₁, componentSeparation M lam Y c

theorem componentSeparation_nonneg (M lam : ℝ) (Y : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    0 ≤ componentSeparation M lam Y c :=
  prod_nonneg fun _ _ => by split_ifs <;> norm_num

theorem componentSeparation_le_one (M lam : ℝ) (Y : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) :
    componentSeparation M lam Y c ≤ 1 :=
  prod_le_one₀ (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)

theorem oddSeparation_nonneg (M lam : ℝ) (X : Finset (Finset ℕ))
    (E₁ : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : 0 ≤ oddSeparation M lam X E₁ c :=
  prod_nonneg fun Y _ => componentSeparation_nonneg M lam Y c

theorem oddSeparation_le_one (M lam : ℝ) (X : Finset (Finset ℕ))
    (E₁ : Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) : oddSeparation M lam X E₁ c ≤ 1 :=
  prod_le_one₀ (fun Y _ => componentSeparation_nonneg M lam Y c)
    (fun Y _ => componentSeparation_le_one M lam Y c)

theorem measurable_oddSeparation (M lam : ℝ) (X : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) :
    Measurable (oddSeparation M lam X E₁) :=
  Finset.measurable_prod _ fun _Y _ =>
    measurable_prod_pair (g := fun d e => if MultipoleLinked M lam d e then (0 : ℝ) else 1)
      (measurable_unlinkedIndicator M lam)

theorem boundedOn_oddSeparation (M lam : ℝ) (X : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ))
    (K : Set (ℂ × ℂ)) : BoundedOn K (oddSeparation M lam X E₁) :=
  ⟨1, fun c _ => (abs_of_nonneg (oddSeparation_nonneg M lam X E₁ c)).le.trans
    (oddSeparation_le_one M lam X E₁ c)⟩

theorem dependsOn_oddSeparation (M lam : ℝ) (X : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) :
    DependsOn (oddSeparation M lam X E₁) ((X.biUnion id : Finset ℕ) : Set ℕ) := by
  intro c c' hcc'
  apply prod_congr rfl
  intro Y hY
  apply prod_congr rfl
  intro p hp
  have hpY := mem_pairsOn.1 (interPairs_subset_pairsOn hp)
  have hYX := biUnion_subset_biUnion_of_subset_left id
    (subset_of_mem_relComponents (oddComponents_subset _ hY))
  rw [hcc' p.1 (hYX hpY.1), hcc' p.2 (hYX hpY.2.1)]

/-- The separated envelope is integrable under the original hierarchical model. -/
theorem integrable_abs_reduced_mul_oddSeparation {N p₀ : ℕ} {χ : ℂ → ℝ}
    {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}
    (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
    {X : Finset (Finset ℕ)} {E E₁ : Finset (ℕ × ℕ)} {U₁ : Finset ℕ}
    (hE : E ⊆ interPairs X) (hE₁ : E₁ ⊆ E) (hU₁ : U₁ ⊆ X.biUnion id) :
    Integrable (fun y => |reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁
        (extendConfig (X.biUnion id) y)| * oddSeparation M lam X E₁ (extendConfig (X.biUnion id) y))
      (plusModel χ N p₀ β lam M ε₀ L V Z X) := by
  have h := modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L)
    (V := V) (Z := Z) hχ hlam hε₀ hN
  let f := fun c => |reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁ c| * oddSeparation M lam X E₁ c
  have hm : Measurable f := (continuous_abs.measurable.comp (measurable_reducedTerm hχ hlam X E E₁ U₁)).mul
    (measurable_oddSeparation M lam X E₁)
  have hbabs : BoundedOn (supportSet N p₀ β lam ε₀) fun c =>
      |reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ U₁ c| := by
    obtain ⟨B, hB⟩ := boundedOn_reducedTerm (p₀ := p₀) (β := β) (M := M)
      (ε₀ := ε₀) (V := V) (Z := Z) hχ hlam X E E₁ U₁
    exact ⟨B, fun c hc => by simpa only [abs_abs] using hB c hc⟩
  have hb : BoundedOn (supportSet N p₀ β lam ε₀) f := hbabs.mul
    (boundedOn_oddSeparation M lam X E₁ (supportSet N p₀ β lam ε₀))
  apply h.integrable_comp_extendConfig hm hb
  intro c c' hcc'
  dsimp only [f]
  rw [(dependsOn_reducedTerm hE hE₁ hU₁) hcc', dependsOn_oddSeparation M lam X E₁ hcc']

end MultipoleBKT.UpperBound.BoundedUpper.RouteRaw

end
