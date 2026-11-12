/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.BoundedUpper.Inputs
public import MultipoleBKT.UpperBound.Quadratic.Instance
public import MultipoleBKT.LowerBound.Parity.MayerBond
public import MultipoleBKT.LowerBound.Hierarchical.Activity
public import MultipoleBKT.Appendix.RadialIntegral

/-!
# The integral `J` of Lemma A.4 (eq. (A.17)) and the input (A.19)

The paper: Lemma A.4: for a
subpartition `X` with `|X| ≥ 2`, disjoint `X_1, …, X_n ⊂ X`, trees `T_l^a ∈ 𝖳^{X_l}` and
`T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}`, with `T^a = ⋃_l T_l^a` and `Ŝ_l ∈ X_l` of maximal radius,

`J = ∫_{(Λ²)^{|V_X|}} min(max_{i ∈ V_X} r_i / max_{e ∈ T^a} d_e, 1)² (∏_l ∏_{S ∈ X_l, S ≠ Ŝ_l} r_S²)
  (∏_{ij ∈ T^a} d_ij^{-2} 𝟙_{d_ij ≤ 17 ε₀ R̄} 𝟙_{𝓑_ij^c}) ∏_{ij ∈ T^b} b^abs_ij ∏_{S ∈ X} 𝟙_{𝓑_S}
  ∏_{i ∈ V_X} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄} dx_i dy_i`

(eq. (A.17)), with the convention `max_{e ∈ T^a} d_e = 0⁺` if `T^a = ∅`, and (A.19):
`J ≤ C N λ^{(2-β)|V_X|} γ_{β,λ,|V_X|}`, `C` depending on `β, M, ε₀, |V_X|`.

Formalization (`c : ℕ → ℂ × ℂ` a configuration of all labels, `r_i = |x_i - y_i|`):

* `blockRad c S = max_{i ∈ S} r_i` (Definition 4.42, `r_S`; `0` for `S = ∅`);
* `radialExceptMax c Y = (∏_{S ∈ Y} r_S²) / (max_{S ∈ Y} r_S)²`, which is
  `∏_{S ∈ Y, S ≠ Ŝ} r_S²` for any `Ŝ ∈ Y` of maximal radius when that radius is positive
  (`radialExceptMax_eq`); for `|Y| ≥ 2` (the case of `Y = X_l` with `𝖳^{X_l} ≠ ∅`) both vanish when
  it is `0`;
* `jTail c X Ta = (max_{i ∈ V_X} r_i / max(max_{e ∈ T^a} d_e, max_{i ∈ V_X} r_i))²`: this is
  `min(max r / max_{T^a} d, 1)²` with the convention `max_{∅} d = 0⁺`, except on the null set
  where `max r = max_{T^a} d = 0` and `T^a ≠ ∅` (where the paper's expression `0/0` is undefined);
* `keptLift`, `absEvenLift`: the weights `d_ij^{-2} 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R̄}` (`keptWeight` with
  `cutOn` of `MultipoleBKT.UpperBound.Quadratic.Instance`) and `b^abs_ij` (`Parity.absEvenWeight`) on
  unordered pairs;
* `jIntegrand`, `jFullIntegrand`, `jIntegral`: the integrand of `J` without the factors
  `∏_S 𝟙_{𝓑_S}` and the dipole densities, the full integrand, and `J`, the Lebesgue integral of a
  nonnegative function, with values in `[0, ∞]`;
* `LemmaA6J`: the input (A.19), for fixed `p₀`, `β`, `M`, `ε₀`, with `λ` small and `N` large
  (the paper's standing convention); it is derived from `MultipoleBKT.SmallIntegral.lemma_A6` in `MultipoleBKT.UpperBound.BoundedUpper.LemmaA6Bridge`
  (`RouteRaw.lemmaA6J_source_holds`).

The trees are simple graphs on the vertex types `(X_l).biUnion id` and
`(Coarse_X(X_1, …, X_n)).biUnion id`, as in `MultipoleBKT.relTrees` and `MultipoleBKT.relTrees₀`.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)
open scoped NNReal ENNReal

namespace MultipoleBKT

namespace UpperBound

namespace BoundedUpper

open Hierarchical Parity Quadratic Peeling Multipole

/-! ### Radii -/

section Radii

/-- `r_S = max_{i ∈ S} |x_i - y_i|` (Definition 4.42), as a real number. -/
noncomputable def blockRad (c : ℕ → ℂ × ℂ) (S : Finset ℕ) : ℝ :=
  ((S.sup fun i => ‖(c i).1 - (c i).2‖₊ : ℝ≥0) : ℝ)

theorem blockRad_nonneg (c : ℕ → ℂ × ℂ) (S : Finset ℕ) : 0 ≤ blockRad c S :=
  NNReal.coe_nonneg _

theorem le_blockRad (c : ℕ → ℂ × ℂ) {S : Finset ℕ} {i : ℕ} (hi : i ∈ S) :
    ‖(c i).1 - (c i).2‖ ≤ blockRad c S := by
  unfold blockRad
  have : ‖(c i).1 - (c i).2‖₊ ≤ S.sup fun i => ‖(c i).1 - (c i).2‖₊ :=
    Finset.le_sup (f := fun i => ‖(c i).1 - (c i).2‖₊) hi
  exact_mod_cast this

theorem blockRad_le {c : ℕ → ℂ × ℂ} {S : Finset ℕ} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i ∈ S, ‖(c i).1 - (c i).2‖ ≤ a) : blockRad c S ≤ a := by
  unfold blockRad
  have : (S.sup fun i => ‖(c i).1 - (c i).2‖₊) ≤ ⟨a, ha⟩ :=
    Finset.sup_le fun i hi => by
      show (‖(c i).1 - (c i).2‖₊ : ℝ) ≤ a
      exact h i hi
  exact_mod_cast this

/-- There is a label of `S` realizing `r_S` (for `S` nonempty). -/
theorem exists_blockRad_eq (c : ℕ → ℂ × ℂ) {S : Finset ℕ} (hS : S.Nonempty) :
    ∃ i ∈ S, blockRad c S = ‖(c i).1 - (c i).2‖ := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup S hS fun i => ‖(c i).1 - (c i).2‖₊
  refine ⟨i, hi, ?_⟩
  unfold blockRad
  rw [h]
  rfl

theorem blockRad_mono (c : ℕ → ℂ × ℂ) {S T : Finset ℕ} (h : S ⊆ T) :
    blockRad c S ≤ blockRad c T :=
  blockRad_le (blockRad_nonneg c T) fun _ hi => le_blockRad c (h hi)

/-- `(∏_{S ∈ Y} r_S²) / (max_{S ∈ Y} r_S)²`, i.e. `∏_{S ∈ Y, S ≠ Ŝ} r_S²` for `Ŝ` of maximal radius
(`radialExceptMax_eq`). -/
noncomputable def radialExceptMax (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) : ℝ :=
  (∏ S ∈ Y, blockRad c S ^ 2) / blockRad c (Y.biUnion id) ^ 2

theorem radialExceptMax_nonneg (c : ℕ → ℂ × ℂ) (Y : Finset (Finset ℕ)) :
    0 ≤ radialExceptMax c Y :=
  div_nonneg (prod_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

/-- For `Ŝ ∈ Y` of maximal radius `r_Ŝ = max_{S ∈ Y} r_S > 0`,
`radialExceptMax c Y = ∏_{S ∈ Y, S ≠ Ŝ} r_S²`. -/
theorem radialExceptMax_eq {c : ℕ → ℂ × ℂ} {Y : Finset (Finset ℕ)} {Ŝ : Finset ℕ} (hŜ : Ŝ ∈ Y)
    (hmax : blockRad c Ŝ = blockRad c (Y.biUnion id)) (hpos : 0 < blockRad c Ŝ) :
    radialExceptMax c Y = ∏ S ∈ Y.erase Ŝ, blockRad c S ^ 2 := by
  unfold radialExceptMax
  rw [← Finset.mul_prod_erase Y _ hŜ, ← hmax]
  field_simp

end Radii

/-! ### The weights on trees -/

section Weights

variable {W : Finset ℕ}

theorem absOddWeight_comm (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) :
    absOddWeight M lam ε₀ R d e = absOddWeight M lam ε₀ R e d := by
  classical
  unfold absOddWeight
  rw [dipoleDist_comm, max_comm ‖d.1 - d.2‖, mul_comm ‖d.1 - d.2‖]
  congr 2
  exact if_congr Quadratic.multipoleLinked_comm rfl rfl

theorem absEvenWeight_comm (M lam ε₀ R : ℝ) (d e : ℂ × ℂ) :
    absEvenWeight M lam ε₀ R d e = absEvenWeight M lam ε₀ R e d := by
  classical
  unfold absEvenWeight
  rw [absOddWeight_comm]
  congr 1
  exact if_congr Quadratic.multipoleLinked_comm rfl rfl

/-- `b^abs_ij` on unordered pairs of labels of `W`. -/
noncomputable def absEvenLift (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) : Sym2 W → ℝ :=
  Sym2.lift ⟨fun i j => absEvenWeight M lam ε₀ R (c i) (c j), fun _ _ => absEvenWeight_comm _ _ _ _ _ _⟩

/-- `d_ij^{-2} 𝟙_{𝓑_ij^c} 𝟙_{d_ij ≤ 17 ε₀ R}` on unordered pairs of labels of `W`. -/
noncomputable def keptLift (M lam ε₀ R : ℝ) (c : ℕ → ℂ × ℂ) : Sym2 W → ℝ :=
  keptWeight (distOn fun i : W => c i) (cutOn M lam ε₀ R fun i : W => c i)

/-- `max_{e ∈ T} d_e` (`0` for `T = ∅`). -/
noncomputable def maxEdgeDist (c : ℕ → ℂ × ℂ) (T : SimpleGraph W) [DecidableRel T.Adj] : ℝ≥0 :=
  T.edgeFinset.sup fun e => (distOn (fun i : W => c i) e).toNNReal

end Weights

/-! ### The integrand and the integral `J` -/

section J

variable (M lam ε₀ R : ℝ)

open scoped Classical in
/-- The tail `min(max_{i ∈ V_X} r_i / max_{e ∈ T^a} d_e, 1)²` of (A.17), written
`(max r / max(max_{T^a} d, max r))²`. -/
noncomputable def jTail (c : ℕ → ℂ × ℂ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id)) : ℝ :=
  (blockRad c (X.biUnion id) /
    max ((Finset.univ.sup fun l => maxEdgeDist c (Ta l) : ℝ≥0) : ℝ) (blockRad c (X.biUnion id))) ^ 2

open scoped Classical in
/-- The integrand of `J` (eq. (A.17)) without the factors `∏_{S ∈ X} 𝟙_{𝓑_S}` and the dipole
densities: `tail ∏_l ∏_{S ∈ X_l, S ≠ Ŝ_l} r_S² ∏_l ∏_{ij ∈ T_l^a} d_ij^{-2} 𝟙 𝟙_{𝓑^c}
∏_{ij ∈ T^b} b^abs_ij`. -/
noncomputable def jIntegrand (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) (c : ℕ → ℂ × ℂ) : ℝ :=
  jTail c X Xs Ta * (∏ l, radialExceptMax c (Xs l)) *
    (∏ l, ∏ e ∈ (Ta l).edgeFinset, keptLift M lam ε₀ R c e) *
    ∏ e ∈ Tb.edgeFinset, absEvenLift M lam ε₀ R c e

open scoped Classical in
/-- The integrand of `J` (eq. (A.17)) on `(Λ²)^{V_X}`: `jIntegrand` times `∏_{S ∈ X} 𝟙_{𝓑_S}` and
`∏_{i ∈ V_X} e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R}`. -/
noncomputable def jFullIntegrand (χ : ℂ → ℝ) (β : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id))
    (y : X.biUnion id → ℂ × ℂ) : ℝ :=
  jIntegrand M lam ε₀ R X Xs Ta Tb (extendConfig (X.biUnion id) y) *
    (∏ S ∈ X, if ConnOn S (linkedPairs M lam (extendConfig (X.biUnion id) y) S) then 1 else 0) *
    ∏ i : X.biUnion id, (Real.exp (β * smearedKernel χ lam ((y i).1 - (y i).2)) *
      (Metric.closedBall (0 : ℂ) (ε₀ * R)).indicator 1 ((y i).1 - (y i).2))

/-- **The integral `J`** of Lemma A.4 (eq. (A.17)), with `R` standing for
`R̄_{β,λ}`: the integral over `(Λ²)^{V_X}` of the nonnegative function `jFullIntegrand`, a value in
`[0, ∞]` (the Lebesgue integral of the paper; (A.19) asserts in particular that it is
finite). -/
noncomputable def jIntegral (χ : ℂ → ℝ) (N : ℕ) (β : ℝ) (X : Finset (Finset ℕ)) {n : ℕ}
    (Xs : Fin n → Finset (Finset ℕ)) (Ta : ∀ l, SimpleGraph ((Xs l).biUnion id))
    (Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id)) : ℝ≥0∞ :=
  ∫⁻ y in Set.univ.pi (fun _ : X.biUnion id => box N ×ˢ box N),
    ENNReal.ofReal (jFullIntegrand M lam ε₀ R χ β X Xs Ta Tb y)

end J

/-- **Lemma A.4, eq. (A.19)** (Lemma A.4), for
fixed `p₀`, `β`, `M`, `ε₀`: for every `k ≥ 1` there is `C > 0` such that for `λ` small and `N`
large, for every subpartition `X` with `|X| ≥ 2` and `|V_X| = k`, all disjoint `X_1, …, X_n ⊂ X`,
`T_l^a ∈ 𝖳^{X_l}` and `T^b ∈ 𝖳_0^{Coarse_X(X_1, …, X_n)}`,
`J ≤ C N λ^{(2-β)k} γ_{β,λ,k}` (as an inequality in `[0, ∞]`). -/
def LemmaA6J (χ : ℂ → ℝ) (p₀ : ℕ) (β M ε₀ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Finset (Finset ℕ), IsSubpartition X → 2 ≤ X.card →
      (X.biUnion id).card = k → ∀ (n : ℕ) (Xs : Fin n → Finset (Finset ℕ)), (∀ l, Xs l ⊆ X) →
      (∀ l l', l ≠ l' → Disjoint (Xs l) (Xs l')) →
      ∀ Ta : ∀ l, SimpleGraph ((Xs l).biUnion id), (∀ l, IsRelTree (Xs l) (Ta l)) →
      ∀ Tb : SimpleGraph ((coarsen X (Finset.univ.image Xs)).biUnion id),
        IsRelTree₀ (coarsen X (Finset.univ.image Xs)) Tb →
        jIntegral M lam ε₀ (truncationScale p₀ β lam) χ N β X Xs Ta Tb ≤
          ENNReal.ofReal (C * N * (lam ^ ((2 - β) * (k : ℝ)) * Appendix.gammaBeta p₀ β lam k))

end BoundedUpper

end UpperBound

end MultipoleBKT

end
