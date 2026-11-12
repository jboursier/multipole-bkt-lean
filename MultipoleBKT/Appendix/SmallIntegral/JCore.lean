/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.TreeMajorant
public import MultipoleBKT.Appendix.OrderingTree

/-!
# Edge weights and radius products for Lemma A.4

See Lemma A.4. The logarithmic proof uses the
kept odd weight, the squared hatted weight and the near indicator separately.
Dropping a largest radius gives the radius-product comparison at (A.25).
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open Finset SimpleGraph
open Limits

variable {M lam : ℝ}

/-! ### The weights -/

section Weights

variable {ι : Type*}

open scoped Classical in
/-- The weight `d_ij^{-2} 𝟙_{𝓑_ij^c}` of an edge of `T^a`. -/
noncomputable def keptE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 0 else
    (dipoleDist (c i) (c j) ^ 2)⁻¹)
    fun i j => by rw [dipoleDist_comm]; exact if_congr multipoleLinked_comm rfl rfl

open scoped Classical in
/-- The weight `â_ij² 𝟙_{𝓑_ij^c}`. -/
noncomputable def aSqE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 0 else ahat (c i) (c j) ^ 2)
    fun i j => by rw [ahat_comm]; exact if_congr multipoleLinked_comm rfl rfl

open scoped Classical in
/-- The indicator `𝟙_{𝓑_ij}`. -/
noncomputable def linkE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 1 else 0)
    fun _ _ => if_congr multipoleLinked_comm rfl rfl

theorem keptE_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ keptE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show 0 ≤ (if MultipoleLinked M lam (c i) (c j) then 0 else (dipoleDist (c i) (c j) ^ 2)⁻¹)
    split_ifs
    · exact le_rfl
    · positivity

theorem aSqE_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ aSqE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show 0 ≤ (if MultipoleLinked M lam (c i) (c j) then 0 else ahat (c i) (c j) ^ 2)
    split_ifs
    · exact le_rfl
    · positivity

theorem linkE_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ linkE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show 0 ≤ (if MultipoleLinked M lam (c i) (c j) then (1 : ℝ) else 0)
    split_ifs <;> norm_num

end Weights

/-! ### Generic lemmas -/

section Generic

/-- **Dropping a largest factor gives the smallest product**: if `f b ≤ f a`, then
`∏_{s ∖ {a}} f ≤ ∏_{s ∖ {b}} f` (for `f ≥ 0` on `s`). -/
theorem prod_erase_le_prod_erase {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : f b ≤ f a) :
    ∏ x ∈ s.erase a, f x ≤ ∏ x ∈ s.erase b, f x := by
  by_cases h : a = b
  · rw [h]
  have hb' : b ∈ s.erase a := mem_erase.2 ⟨Ne.symm h, hb⟩
  have ha' : a ∈ s.erase b := mem_erase.2 ⟨h, ha⟩
  rw [← mul_prod_erase _ f hb', ← mul_prod_erase _ f ha', erase_right_comm]
  exact mul_le_mul_of_nonneg_right hab
    (prod_nonneg fun x hx => hf x (mem_of_mem_erase (mem_of_mem_erase hx)))

end Generic

end SmallIntegral

end MultipoleBKT

end
