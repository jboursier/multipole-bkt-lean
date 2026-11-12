/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Compact
public import MultipoleBKT.LowerBound.Hierarchical.ExpE11

/-!
# The parity reduction with external marks (Corollary 5.24)

The paper: Corollary 5.24 and
its use in the proof of Proposition 5.18: expanding the bonds
`u_ij = a^{v^Z}_ij 𝟙_{𝓑^c} + (b^{v^Z}_ij 𝟙_{𝓑^c} - 𝟙_𝓑)` (odd + even in each dipole) and the external
factors `1 + f_{i∞} = e^{-β S_i} = -sinh(β S_i) + cosh(β S_i)` (`S_i = ∑_{j ∈ V_bad} v^Z_ij`, odd +
even), only the terms with `E₁ ∈ Eul^X(V₁)` survive: `deg_{E₁}(S) + |S ∩ V₁|` even for every
`S ∈ X` (Definition 5.23). The reversal of the dipoles of a block `S₀ ∈ X` preserves
`𝖯^{+,ε₀,Z}_X` (`measurePreserving_flipOn_modelHierarchical`) and multiplies such a
term by `(-1)^{deg_{E₁}(S₀) + |S₀ ∩ V₁|}`.

* `reducedTerm X E E₁ V₁ c = ∏_{E₁} a^{v^Z}𝟙_{𝓑^c} ∏_{E ∖ E₁} (b^{v^Z}𝟙_{𝓑^c} - 𝟙_𝓑)
  ∏_{V₁} (-sinh(β S_i)) ∏_{V_X ∖ V₁} cosh(β S_i)`.
* `IsParityPair X E₁ V₁`: `deg_{E₁}(S) + |S ∩ V₁|` even for every `S ∈ X`.
* `abs_plusActivity_le` is preserved in `RouteRaw.Legacy`. Its proof starts
  with the nested raw expansion, cancels parity there and only then regroups
  the surviving terms to retain its original coefficient-one interface.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Multipole Parity

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)}
  {Z : Fin N → ℂ × ℂ}

/-- `S_e = ∑_{j ∈ V_bad} v^Z(e, Z_j)`. -/
noncomputable def extSumZ (χ : ℂ → ℝ) (p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (e : ℂ × ℂ) : ℝ :=
  ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V Z e j

theorem extSumZ_swap (e : ℂ × ℂ) :
    extSumZ χ p₀ β lam ε₀ V Z e.swap = -extSumZ χ p₀ β lam ε₀ V Z e := by
  unfold extSumZ
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => interactionExtZ_swap e j

theorem one_add_externalBondZ_eq (e : ℂ × ℂ) :
    1 + externalBondZ χ p₀ β lam ε₀ V Z e =
      -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z e) + Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z e) := by
  have h : ∑ j ∈ V, -β * interactionExtZ χ p₀ β lam ε₀ V Z e j =
      -(β * extSumZ χ p₀ β lam ε₀ V Z e) := by
    rw [extSumZ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [one_add_externalBondZ, ← Real.exp_sum, h, ← Real.cosh_sub_sinh]
  ring

theorem measurable_extSumZ (hχ : IsMollifier χ) (hlam : 0 < lam) :
    Measurable (extSumZ χ p₀ β lam ε₀ V Z) :=
  Finset.measurable_sum _ fun j _ => measurable_interactionExtZ p₀ β lam ε₀ V Z hχ hlam j

/-- The reduced term of Corollary 5.24 for the edge set `E`, its odd edges `E₁ ⊆ E` and the
marks `V₁ ⊆ V_X`. -/
noncomputable def reducedTerm (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (X : Finset (Finset ℕ)) (E E₁ : Finset (ℕ × ℕ)) (V₁ : Finset ℕ)
    (c : ℕ → ℂ × ℂ) : ℝ :=
  (∏ p ∈ E₁, oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)) *
    (∏ p ∈ E \ E₁, evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2)) *
    (∏ i ∈ V₁, -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))) *
    ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))

/-- `E₁ ∈ Eul^X(V₁)` in the edge-set form: `deg_{E₁}(S) + |S ∩ V₁|` is even for every `S ∈ X`
(Definition 5.23). -/
def IsParityPair (X : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ)) (V₁ : Finset ℕ) : Prop :=
  ∀ S ∈ X, Even (blockDeg E₁ S + (S ∩ V₁).card)

/-- Reversing the dipoles of `S` turns `∏_{i ∈ V₁} u(c_i)` into `(-1)^{|V₁ ∩ S|} ∏_{i ∈ V₁} u(c_i)`
for `u` odd. -/
theorem prod_flipOn_vertex_odd {u : ℂ × ℂ → ℝ} (hu : ∀ d, u d.swap = -u d) (V₁ S : Finset ℕ)
    (c : ℕ → ℂ × ℂ) :
    ∏ i ∈ V₁, u (flipOn Prod.swap S c i) = (-1) ^ (S ∩ V₁).card * ∏ i ∈ V₁, u (c i) := by
  classical
  have hpt : ∀ i, u (flipOn Prod.swap S c i) = (if i ∈ S then (-1 : ℝ) else 1) * u (c i) := by
    intro i
    rw [flipOn_apply]
    split_ifs <;> simp [hu]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite,
    Finset.prod_const_one, Finset.prod_const, mul_one, Finset.filter_mem_eq_inter,
    Finset.inter_comm]

theorem prod_flipOn_vertex_even {v : ℂ × ℂ → ℝ} (hv : ∀ d, v d.swap = v d) (W S : Finset ℕ)
    (c : ℕ → ℂ × ℂ) : ∏ i ∈ W, v (flipOn Prod.swap S c i) = ∏ i ∈ W, v (c i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [flipOn_apply]
  split_ifs <;> simp [hv]

/-- The reduced term at the configuration with the dipoles of `S` reversed. -/
theorem reducedTerm_flipOn (hM : 1 ≤ M) (X : Finset (Finset ℕ)) (E E₁ : Finset (ℕ × ℕ))
    (V₁ S : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ (flipOn Prod.swap S c) =
      (-1) ^ (blockDeg E₁ S + (S ∩ V₁).card) * reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁ c := by
  unfold reducedTerm
  rw [prod_flipOn_of_odd' (fun d e => oddBondUnlinked_swap_left hM
      (fun d e => interactionGoodZ_swap_left d e) d e)
      (fun d e => oddBondUnlinked_swap_right hM (fun d e => interactionGoodZ_swap_right d e) d e),
    prod_flipOn_of_even' (fun d e => evenBondMult_swap_left hM
      (fun d e => interactionGoodZ_swap_left d e) d e)
      (fun d e => evenBondMult_swap_right hM (fun d e => interactionGoodZ_swap_right d e) d e),
    prod_flipOn_vertex_odd (u := fun d => -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z d))
      (fun d => by simp only [extSumZ_swap, mul_neg, Real.sinh_neg, neg_neg]),
    prod_flipOn_vertex_even (v := fun d => Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z d))
      (fun d => by simp only [extSumZ_swap, mul_neg, Real.cosh_neg]), pow_add]
  ring

/-- `cosh x ≤ e^{|x|}`. -/
theorem cosh_le_exp_abs' (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 : Real.exp (-|x|) ≤ Real.exp |x| := Real.exp_le_exp.2 (by linarith [abs_nonneg x])
  linarith

/-- `|sinh x| ≤ e^{|x|}`. -/
theorem abs_sinh_le_exp_abs (x : ℝ) : |Real.sinh x| ≤ Real.exp |x| := by
  have h : |Real.sinh x| ≤ Real.cosh x := by
    rw [Real.sinh_eq, Real.cosh_eq, abs_le]
    have h1 := Real.exp_pos x
    have h2 := Real.exp_pos (-x)
    constructor <;> linarith
  exact h.trans (cosh_le_exp_abs' x)

section Integral

variable (hχ : IsMollifier χ) (hlam : 0 < lam) (hε₀ : 0 < ε₀) (hN : 1 ≤ N)
include hχ hlam hε₀ hN

omit hε₀ hN in
theorem measurable_reducedTerm (X : Finset (Finset ℕ)) (E E₁ : Finset (ℕ × ℕ)) (V₁ : Finset ℕ) :
    Measurable (reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁) := by
  have hw := measurable_interactionGoodZ p₀ β lam ε₀ V Z hχ hlam
  have hodd := measurable_oddBondUnlinked hw β M lam
  have heven : Measurable fun q : (ℂ × ℂ) × (ℂ × ℂ) =>
      evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam q.1 q.2 := by
    unfold evenBondMult
    exact (measurable_evenBondUnlinked hw β M lam).sub (Measurable.ite
      (measurableSet_multipoleLinked M lam) measurable_const measurable_const)
  have hS := measurable_extSumZ (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V) (Z := Z) hχ hlam
  unfold reducedTerm
  refine (((Finset.measurable_prod _ fun p _ => measurable_pairWeight hodd p).mul
    (Finset.measurable_prod _ fun p _ => measurable_pairWeight heven p)).mul
    (Finset.measurable_prod _ fun i _ => ?_)).mul (Finset.measurable_prod _ fun i _ => ?_)
  · exact (Real.continuous_sinh.measurable.comp (measurable_const.mul
      (hS.comp (measurable_pi_apply i)))).neg
  · exact Real.continuous_cosh.measurable.comp (measurable_const.mul
      (hS.comp (measurable_pi_apply i)))

omit hε₀ hN in
theorem boundedOn_reducedTerm (X : Finset (Finset ℕ)) (E E₁ : Finset (ℕ × ℕ)) (V₁ : Finset ℕ) :
    BoundedOn (supportSet N p₀ β lam ε₀) (reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁) := by
  classical
  obtain ⟨Bw, hBw⟩ := exists_abs_interactionGoodZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
    (Z := Z) hχ hlam
  obtain ⟨Bo, hBo⟩ := exists_abs_oddBondUnlinked_le (K := supportSet N p₀ β lam ε₀)
    ⟨Bw, hBw⟩ β M lam
  obtain ⟨Be, hBe⟩ := exists_abs_evenBondUnlinked_le (K := supportSet N p₀ β lam ε₀)
    ⟨Bw, hBw⟩ β M lam
  obtain ⟨Bx, hBx⟩ := exists_abs_interactionExtZ_le (p₀ := p₀) (β := β) (ε₀ := ε₀) (V := V)
    (Z := Z) hχ hlam
  have hS : ∀ d ∈ supportSet N p₀ β lam ε₀, |β * extSumZ χ p₀ β lam ε₀ V Z d| ≤
      |β| * ∑ _j ∈ V, Bx := by
    intro d hd
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => hBx d hd j hj)) (abs_nonneg β)
  have h1 : BoundedOn (supportSet N p₀ β lam ε₀) fun c : ℕ → ℂ × ℂ =>
      ∏ p ∈ E₁, oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2) :=
    BoundedOn.prod _ fun (p : ℕ × ℕ) _ =>
      BoundedOn.pair (φ := oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam)
        ⟨Bo, hBo⟩ p.1 p.2
  have h2 : BoundedOn (supportSet N p₀ β lam ε₀) fun c : ℕ → ℂ × ℂ =>
      ∏ p ∈ E \ E₁, evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c p.1) (c p.2) := by
    refine BoundedOn.prod _ fun (p : ℕ × ℕ) _ =>
      BoundedOn.pair (φ := evenBondMult β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam)
        ⟨Be + 1, fun d hd e he => ?_⟩ p.1 p.2
    unfold evenBondMult
    have := hBe d hd e he
    calc |evenBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e -
          (if MultipoleLinked M lam d e then 1 else 0)|
        ≤ |evenBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam d e| +
          |(if MultipoleLinked M lam d e then (1 : ℝ) else 0)| := abs_sub _ _
      _ ≤ Be + 1 := by
          gcongr
          split_ifs <;> norm_num
  have h3 : BoundedOn (supportSet N p₀ β lam ε₀) fun c : ℕ → ℂ × ℂ =>
      ∏ i ∈ V₁, -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) := by
    refine BoundedOn.prod _ fun i _ => BoundedOn.single
      (ψ := fun d => -Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z d))
      ⟨Real.exp (|β| * ∑ _j ∈ V, Bx), fun d hd => ?_⟩ i
    simp only [abs_neg]
    exact (abs_sinh_le_exp_abs _).trans (Real.exp_le_exp.2 (hS d hd))
  have h4 : BoundedOn (supportSet N p₀ β lam ε₀) fun c : ℕ → ℂ × ℂ =>
      ∏ i ∈ X.biUnion id \ V₁, Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z (c i)) := by
    refine BoundedOn.prod _ fun i _ => BoundedOn.single
      (ψ := fun d => Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z d))
      ⟨Real.exp (|β| * ∑ _j ∈ V, Bx), fun d hd => ?_⟩ i
    rw [abs_of_pos (Real.cosh_pos _)]
    exact (cosh_le_exp_abs' _).trans (Real.exp_le_exp.2 (hS d hd))
  unfold reducedTerm
  exact ((h1.mul h2).mul h3).mul h4

omit hχ hlam hε₀ hN in
theorem dependsOn_reducedTerm {X : Finset (Finset ℕ)} {E E₁ : Finset (ℕ × ℕ)} {V₁ : Finset ℕ}
    (hE : E ⊆ interPairs X) (hE₁ : E₁ ⊆ E) (hV₁ : V₁ ⊆ X.biUnion id) :
    DependsOn (reducedTerm χ p₀ β lam M ε₀ V Z X E E₁ V₁) ((X.biUnion id : Finset ℕ) : Set ℕ) := by
  intro c c' hcc'
  have hEV : ∀ p ∈ E, p.1 ∈ X.biUnion id ∧ p.2 ∈ X.biUnion id := by
    intro p hp
    have hpI := hE hp
    rw [interPairs, Finset.mem_sdiff, mem_pairsOn] at hpI
    exact ⟨hpI.1.1, hpI.1.2.1⟩
  have hc : ∀ i ∈ X.biUnion id, c i = c' i := fun i hi => hcc' i (Finset.mem_coe.2 hi)
  unfold reducedTerm
  congr 1
  · congr 1
    · congr 1
      · exact Finset.prod_congr rfl fun p hp => by
          rw [hc p.1 (hEV p (hE₁ hp)).1, hc p.2 (hEV p (hE₁ hp)).2]
      · exact Finset.prod_congr rfl fun p hp => by
          rw [hc p.1 (hEV p (Finset.mem_sdiff.1 hp).1).1, hc p.2 (hEV p (Finset.mem_sdiff.1 hp).1).2]
    · exact Finset.prod_congr rfl fun i hi => by rw [hc i (hV₁ hi)]
  · exact Finset.prod_congr rfl fun i hi => by rw [hc i (Finset.mem_sdiff.1 hi).1]


end Integral

end BoundedUpper

end UpperBound

end MultipoleBKT

end
