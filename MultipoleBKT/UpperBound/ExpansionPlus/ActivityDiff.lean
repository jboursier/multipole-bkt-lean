/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.Inputs

/-!
# The upper activity comparison from fixed expectation errors

The paper: Proposition 5.19, especially (5.107) and the reference to (4.81).

Split the marks using `plusActivity_eq` and bound the nonempty marks by the
claim (5.106). For each unmarked datum, compare its numerator using Lemma A.7,
then multiply the bound (4.80) by the reciprocal-product error as in Section 4.
`activity_diff_of_blocks` sums only the resulting fixed expectation errors.
Finally apply (4.45) and compare the block denominators.

The coefficients of `ε₀^(αk) |V_bad| / N` are chosen before `ε₀`.
The existential threshold can be `M₀ = 21`, together with the
separate hypothesis `3^(pBeta p₀ β) ≤ M`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset Filter
open Hierarchical BoundedUpper ExpansionErrors Multipole SetPartition MultipoleIntegral Limits

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ L : ℝ} {V : Finset (Fin N)} {Z : Fin N → ℂ × ℂ}

open scoped Classical in
/-- **The split of `𝖪^{+,Z}_{ε₀}` according to the marks** (Definition 5.15, eq. (5.107)): for
`|X| ≥ 2`, `𝖪^{+,Z}_{ε₀}(X)` is the activity of the model `(μ_{β,λ,ε₀}, v^Z, ψ^Z)` without marks
plus the sum over the nonempty marks `V^∞ ⊆ V_X` of the finite sums of the marked terms. -/
theorem plusActivity_eq {X : Finset (Finset ℕ)} (h2 : 2 ≤ X.card) :
    plusActivity χ N p₀ β lam M ε₀ L V Z X =
      modelActivity (cutoffDipoleMeasure χ N p₀ β lam ε₀) β (interactionGoodZ χ p₀ β lam ε₀ V Z)
          (dipoleWeightZ p₀ β lam M ε₀ L V Z) M lam X +
        ∑ U ∈ (X.biUnion id).powerset.erase ∅, clusterSum X fun _ Xs Es F =>
          ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
              (extendConfig (X.biUnion id) y) *
            ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
            ∂plusModel χ N p₀ β lam M ε₀ L V Z X := by
  have hfin : ∀ (f : ∀ n : ℕ, (Fin n → Finset (Finset ℕ)) → (Fin n → Finset (ℕ × ℕ)) →
      Finset (ℕ × ℕ) → ℝ),
      ∑' n : ℕ, 1 / (n.factorial : ℝ) *
        ∑ Xs ∈ (Fintype.piFinset fun _ : Fin n => X.powerset).filter
            (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
          ∑ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
            ∑ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), f n Xs Es F =
        clusterSum X f := by
    intro f
    refine tsum_eq_sum fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [sum_piFinset_relEdgeSets_eq_zero (by omega), mul_zero]
  rw [plusActivity, ite_eq_right (by omega : ¬ X.card ≤ 1),
    ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  congr 1
  · simp only [Finset.prod_empty, mul_one]
    rw [modelActivity, ite_eq_right (by omega : ¬ X.card ≤ 1)]
    rfl
  · exact Finset.sum_congr rfl fun U _ => hfin _

/-! ### Arithmetic -/

/-- `∏_{S ∈ X} f(S) ≤ C^k ∏_{S ∈ X} g(S)` from `0 ≤ f ≤ C g` blockwise, `g > 0`, `C ≥ 1`,
`|X| ≤ k`. -/
theorem prod_le_pow_mul_prod {X : Finset (Finset ℕ)} {f g : Finset ℕ → ℝ} {C : ℝ} {k : ℕ}
    (hC : 1 ≤ C) (hk : X.card ≤ k) (hf : ∀ S ∈ X, 0 ≤ f S) (hg : ∀ S ∈ X, 0 < g S)
    (hfg : ∀ S ∈ X, f S ≤ C * g S) : ∏ S ∈ X, f S ≤ C ^ k * ∏ S ∈ X, g S := by
  have hP : 0 ≤ ∏ S ∈ X, g S := prod_nonneg fun S hS => (hg S hS).le
  calc ∏ S ∈ X, f S ≤ ∏ S ∈ X, (C * g S) := prod_le_prod₀ hf hfg
    _ = C ^ X.card * ∏ S ∈ X, g S := by rw [prod_mul_distrib, prod_const]
    _ ≤ C ^ k * ∏ S ∈ X, g S := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hk) hP

/-- `a / (P T) ≤ B a / (Q T)` from `Q ≤ B P`, `P, Q, T > 0`, `a ≥ 0`. -/
theorem div_le_div_of_le_mul {a P Q T B : ℝ} (ha : 0 ≤ a) (hP : 0 < P) (hQ : 0 < Q) (hT : 0 < T)
    (hQP : Q ≤ B * P) : a / (P * T) ≤ B * a / (Q * T) := by
  have hB : 0 < B := by
    by_contra h
    push Not at h
    nlinarith
  rw [div_le_div_iff₀ (mul_pos hP hT) (mul_pos hQ hT)]
  have : a * (Q * T) ≤ a * (B * P * T) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQP hT.le) ha
  nlinarith

/-- **The combination** (eq. (5.107) and the paper): from the bound on the marked terms (against
`𝖬^{+,Z}_{ε₀}(X)`), the unmarked comparison with `𝖪^0_∞` and (4.45) (against `𝖬^0_∞(X)`), and
`𝖬^0_{ε₀}(X) ≤ B 𝖬^{+,Z}_{ε₀}(X)`, `𝖬^0_{ε₀}(X) ≤ B 𝖬^0_∞(X)`. -/
theorem combine_le {Kp Ke Kz Ki Sg Pp P₀ Pz T η A₁ A₂ A₃ B : ℝ} (hKp : Kp = Ke + Sg)
    (hPp : 0 < Pp) (hP₀ : 0 < P₀) (hPz : 0 < Pz) (hT : 0 < T) (hη : 0 ≤ η) (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃) (hSg : |Sg| ≤ A₁ * η / (Pp * T))
    (hKe : |Ke - Ki| ≤ A₂ * η / (P₀ * T)) (hz : |Kz - Ki| ≤ A₃ * η / (P₀ * T))
    (hBp : Pz ≤ B * Pp) (hB₀ : Pz ≤ B * P₀) :
    |Kp - Kz| ≤ (A₁ + A₂ + A₃) * B * η / (T * Pz) := by
  have e : Kp - Kz = Sg + (Ke - Ki) - (Kz - Ki) := by rw [hKp]; ring
  have h1 := div_le_div_of_le_mul (mul_nonneg hA₁ hη) hPp hPz hT hBp
  have h2 := div_le_div_of_le_mul (mul_nonneg hA₂ hη) hP₀ hPz hT hB₀
  have h3 := div_le_div_of_le_mul (mul_nonneg hA₃ hη) hP₀ hPz hT hB₀
  calc |Kp - Kz| ≤ |Sg| + |Ke - Ki| + |Kz - Ki| := by
        rw [e]
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ B * (A₁ * η) / (Pz * T) + B * (A₂ * η) / (Pz * T) + B * (A₃ * η) / (Pz * T) :=
        add_le_add (add_le_add (hSg.trans h1) (hKe.trans h2)) (hz.trans h3)
    _ = (A₁ + A₂ + A₃) * B * η / (T * Pz) := by
        rw [mul_comm T Pz]
        ring

theorem zeroPartitionFunction_eq_prod' {N p₀ : ℕ} {β lam M ε₀ : ℝ} (X : Finset (Finset ℕ)) :
    zeroPartitionFunction χ N p₀ β lam M ε₀ X =
      ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
  unfold zeroPartitionFunction
  exact Finset.prod_congr rfl fun S _ => (Finset.prod_singleton _ S).symm

theorem goodLabels_subset_range {N : ℕ} (V : Finset (Fin N)) : goodLabels V ⊆ Finset.range N := by
  intro n hn
  obtain ⟨h, -⟩ := mem_goodLabels.1 hn
  exact Finset.mem_range.2 h

/-! ### Arithmetic of the terms -/

/-- The two estimates of Lemma A.7 combine into the bound `D N λ^{(2-β)k} η` of
`activity_diff_of_blocks`, `η = C_t R̄^{-2} + ε₀^{αk} |V|/N`. -/
theorem term_arith {x y z Λ N R e Vc Cε8 C8 Cbis Ct D : ℝ} (hΛ : 0 ≤ Λ) (hN : 0 < N)
    (hR : 0 ≤ R) (he : 0 ≤ e) (hVc : 0 ≤ Vc) (hCt : 0 ≤ Ct) (h1 : Cε8 + Cbis ≤ Ct)
    (hD1 : 1 ≤ D) (hD8 : C8 ≤ D)
    (ha : |x - y| ≤ Λ * (Cε8 * N * R + C8 * e * Vc)) (hb : |y - z| ≤ Cbis * N * (Λ * R)) :
    |x - z| ≤ D * N * (Λ * (Ct * R + e * (Vc / N))) := by
  have hsum : (Cε8 + Cbis) * N * R ≤ D * Ct * N * R := by
    have h2 : Ct ≤ D * Ct := le_mul_of_one_le_left hCt hD1
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h1.trans h2) hN.le) hR
  have hC8 : C8 * e * Vc ≤ D * e * Vc :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD8 he) hVc
  calc |x - z| ≤ |x - y| + |y - z| := abs_sub_le _ _ _
    _ ≤ Λ * (Cε8 * N * R + C8 * e * Vc) + Cbis * N * (Λ * R) := add_le_add ha hb
    _ = Λ * ((Cε8 + Cbis) * N * R + C8 * e * Vc) := by ring
    _ ≤ Λ * (D * Ct * N * R + D * e * Vc) := mul_le_mul_of_nonneg_left (add_le_add hsum hC8) hΛ
    _ = D * N * (Λ * (Ct * R + e * (Vc / N))) := by
        field_simp

/-- `C R ≤ m (C_t R + e v)` for `C ≤ C_t`, `1 ≤ m`, `R, e, v, C_t ≥ 0`, and
`C R + C' e v ≤ max 1 C' (C_t R + e v)`. -/
theorem eta_arith {C C' Ct R e v : ℝ} (hR : 0 ≤ R) (he : 0 ≤ e) (hv : 0 ≤ v) (hCt : 0 ≤ Ct)
    (hC : C ≤ Ct) : C * R + C' * e * v ≤ max 1 C' * (Ct * R + e * v) := by
  have h2 : Ct ≤ max 1 C' * Ct := le_mul_of_one_le_left hCt (le_max_left _ _)
  have h3 := mul_le_mul_of_nonneg_right (hC.trans h2) hR
  have h4 : C' * e * v ≤ max 1 C' * e * v :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) he) hv
  calc C * R + C' * e * v ≤ max 1 C' * Ct * R + max 1 C' * e * v := add_le_add h3 h4
    _ = max 1 C' * (Ct * R + e * v) := by ring

/-! ### The marked terms -/

open scoped Classical in
/-- **The marked terms** (eq. (5.107)): if every marked term is at most `Q ≥ 0` in absolute value,
the sum over the nonempty marks of the finite sums is at most `2^k countBound(k) Q`. -/
theorem marked_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {k : ℕ}
    (hXk : (X.biUnion id).card = k) {Q : ℝ} (hQ : 0 ≤ Q)
    (f : Finset ℕ → ∀ n : ℕ, (Fin n → Finset (Finset ℕ)) → (Fin n → Finset (ℕ × ℕ)) →
      Finset (ℕ × ℕ) → ℝ)
    (hf : ∀ U ∈ (X.biUnion id).powerset.erase ∅, ∀ n (Xs : Fin n → Finset (Finset ℕ)),
      (∀ l, Xs l ⊆ X) → (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) →
      ∀ Es ∈ Fintype.piFinset (fun l => relEdgeSets (Xs l)),
      ∀ F ∈ relEdgeSets₀ (coarsen X (Finset.univ.image Xs)), |f U n Xs Es F| ≤ Q) :
    |∑ U ∈ (X.biUnion id).powerset.erase ∅, clusterSum X (f U)| ≤
      (2 : ℝ) ^ k * countBound k * Q := by
  have hU : ∀ U ∈ (X.biUnion id).powerset.erase ∅, |clusterSum X (f U)| ≤ countBound k * Q :=
    fun U hU => by
      have := abs_clusterSum_le hX hQ (hf U hU)
      rwa [hXk] at this
  have hcardU : ((X.biUnion id).powerset.erase ∅).card ≤ 2 ^ k := by
    refine (Finset.card_erase_le).trans ?_
    rw [Finset.card_powerset, hXk]
  calc _ ≤ ∑ U ∈ (X.biUnion id).powerset.erase ∅, |clusterSum X (f U)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _U ∈ (X.biUnion id).powerset.erase ∅, countBound k * Q := Finset.sum_le_sum hU
    _ = ((X.biUnion id).powerset.erase ∅).card * (countBound k * Q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ k * (countBound k * Q) := by
        gcongr
        exact_mod_cast hcardU
    _ = (2 : ℝ) ^ k * countBound k * Q := by ring

/-! ### Eq. (5.69) for `𝖪^{+,Z}_{ε₀}` -/

open scoped Classical in
/-- Internal estimate (5.69) from Lemma A.7 and the nonempty-mark claim.
The paper: Proposition 5.19.
The unmarked comparison follows the fixed-term argument of (4.81).
The coefficients of the bad-point term are independent of `ε₀`. -/
theorem eq_K_plus_diff_of_inputs (hχ : IsMollifier χ) (hβ : 2 < β) (L : ℝ) (p₀ : ℕ) {k : ℕ}
    (hk : 2 ≤ k) (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      LemmaA8PlusStatement χ β M L p₀ k → LemmaA8BisStatement χ β M p₀ k →
      NonEmptyMarksStatement χ β M L p₀ k →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
          (X.biUnion id).card = k →
          |plusActivity χ N p₀ β lam M ε₀ L V Z X - zeroActivity χ N p₀ β lam M ε₀ X| ≤
            (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
              ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
  refine ⟨21, by norm_num, fun M hM hMp hA8 hA8b hNE => ?_⟩
  have hM20 : 20 < M := by linarith
  obtain ⟨CK, hCK, hborn⟩ := bornI2 hχ hβ (by linarith : 1 ≤ M) k hkp
  have hK0' := internal_K_diff0_at_M_of_lemma_A8 hχ hβ hk hkp p₀ M hM20 hA8b
  obtain ⟨CB, hCB, hblocks⟩ := plus_blocks (χ := χ) hχ hβ L hM20 hMp hkp
  obtain ⟨C8, hC8, h8⟩ := hA8
  obtain ⟨Cne, hCne, hne⟩ := hNE
  set Zc := dipoleConstant χ β
  have hZ : 0 < Zc := dipoleConstant_pos hχ hβ
  set CB' := max CB 1
  have hCB' : 1 ≤ CB' := le_max_right _ _
  set D := max 1 C8
  have hD : 0 ≤ D := zero_le_one.trans (le_max_left _ _)
  set K₁ := countBound k * (D * (2 / Zc) ^ k * CB' ^ k + CK * (2 / Zc) ^ k * (CB' ^ k * (k * CB')))
  have hK₁ : 0 ≤ K₁ := by positivity
  set A₁ := (2 : ℝ) ^ k * countBound k * max 1 Cne
  have hA₁ : 0 ≤ A₁ := by positivity
  set Ctot := (A₁ + K₁ + 1) * CB' ^ k
  have hCtot : 0 < Ctot := by positivity
  refine ⟨Ctot, hCtot, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cεb, hCεb, lb, hlb, hb⟩ := hblocks ε₀ hε₀ hε₁
  obtain ⟨Cε8, hCε8, l8, hl8, h8'⟩ := h8 ε₀ hε₀ hε₁
  obtain ⟨Cbis, hCbis, lbis, hlbis, hbis⟩ := hA8b ε₀ hε₀ hε₁
  obtain ⟨C0, hC0, l0, hl0, -, hK0''⟩ := hK0' ε₀ hε₀ hε₁
  obtain ⟨Cεne, hCεne, lne, hlne, hne'⟩ := hne ε₀ hε₀ hε₁
  set Cεt := Cεb + Cε8 + Cbis + C0 + Cεne
  have hCεt : 0 < Cεt := by positivity
  refine ⟨Ctot * Cεt, by positivity, min (min (min lb l8) (min lbis l0)) (min lne (1 : ℝ)),
    lt_min (lt_min (lt_min hlb hl8) (lt_min hlbis hl0)) (lt_min hlne one_pos), fun lam hlam hlt => ?_⟩
  have hltb : lam < lb := hlt.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hlt8 : lam < l8 := hlt.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hltbis : lam < lbis := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hlt0 : lam < l0 := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hltne : lam < lne := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨Nb, hNb⟩ := hb lam hlam hltb
  obtain ⟨N8, hN8⟩ := h8' lam hlam hlt8
  obtain ⟨Nbis, hNbis⟩ := hbis lam hlam hltbis
  obtain ⟨N0, hN0⟩ := hK0'' lam hlam hlt0
  obtain ⟨Nne, hNne⟩ := hne' lam hlam hltne
  obtain ⟨Nh, hNh⟩ := eventually_atTop.1 (eventually_half_le_dipoleNormalization hχ hβ hlam)
  refine ⟨max (max (max Nb N8) (max Nbis N0)) (max (max Nne 1) (max Nh 1)),
    fun N hN V Z hV X hX hXV hXk => ?_⟩
  have hNb' : Nb ≤ N := le_trans ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_left _ _))) hN
  have hN8' : N8 ≤ N := le_trans ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_left _ _))) hN
  have hNbis' : Nbis ≤ N := le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_left _ _))) hN
  have hN0' : N0 ≤ N := le_trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_left _ _))) hN
  have hNne' : Nne ≤ N := le_trans ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _))) hN
  have hNh' : Nh ≤ N := le_trans ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _))) hN
  have hN1 : 1 ≤ N := le_trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _))) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT : (0 : ℝ) < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set e := ε₀ ^ (alphaExponent β * k)
  have he : 0 ≤ e := by positivity
  set v : ℝ := V.card / N
  have hv : 0 ≤ v := by positivity
  set η := Cεt * R + e * v with hη_def
  have hη : 0 ≤ η := by positivity
  have hXN : X.biUnion id ⊆ Finset.range N := hXV.trans (goodLabels_subset_range V)
  -- the trivial case `|X| ≤ 1`
  by_cases h2 : 2 ≤ X.card
  swap
  · have h1 : X.card ≤ 1 := by omega
    rw [plusActivity_eq_zero_of_card_le_one χ p₀ β lam M ε₀ L V Z h1, zeroActivity,
      modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ h1, sub_zero, abs_zero]
    refine div_nonneg (by positivity) (mul_nonneg hT.le ?_)
    unfold zeroPartitionFunction
    exact prod_nonneg fun S _ =>
      (modelHyp_zero (p₀ := p₀) hχ hlam β hε₀ hN1).modelPartitionFunction_nonneg M lam S
  -- the blocks
  have hblk : ∀ S ∈ X, PlusBlockFacts χ N p₀ β lam M ε₀ L k S.card CB Cεb := fun S hS =>
    hNb N hNb' S.card (card_block_mem hX hS).1 (hXk ▸ (card_block_mem hX hS).2)
  have hηb : Cεb * R + e * v ≤ η := by
    have : Cεb ≤ Cεt := by simp only [Cεt]; linarith
    have := mul_le_mul_of_nonneg_right this hR0
    linarith
  have hXk' : X.card ≤ k := hXk ▸ card_le_card_biUnion hX
  set Pp := ∏ S ∈ X, plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S
  set P₀ := ∏ S ∈ X, multipolePartitionFunction χ N β lam M S
  set Pz := zeroPartitionFunction χ N p₀ β lam M ε₀ X
  have hPz_eq : Pz = ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} :=
    zeroPartitionFunction_eq_prod' X
  have hPp : 0 < Pp := prod_pos fun S hS => (hblk S hS V Z hV S rfl).2.1
  have hP₀ : 0 < P₀ := prod_pos fun S hS => (hblk S hS V Z hV S rfl).2.2.1
  have hPz : 0 < Pz := by
    rw [hPz_eq]; exact prod_pos fun S hS => (hblk S hS V Z hV S rfl).2.2.2.1
  have hBp : Pz ≤ CB' ^ k * Pp := by
    rw [hPz_eq]
    exact prod_le_pow_mul_prod hCB' hXk' (fun S hS => (hblk S hS V Z hV S rfl).2.2.2.1.le)
      (fun S hS => (hblk S hS V Z hV S rfl).2.1) fun S hS =>
        ((hblk S hS V Z hV S rfl).2.2.2.2.1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (hblk S hS V Z hV S rfl).2.1.le)
  have hB₀ : Pz ≤ CB' ^ k * P₀ := by
    rw [hPz_eq]
    exact prod_le_pow_mul_prod hCB' hXk' (fun S hS => (hblk S hS V Z hV S rfl).2.2.2.1.le)
      (fun S hS => (hblk S hS V Z hV S rfl).2.2.1) fun S hS =>
        ((hblk S hS V Z hV S rfl).2.2.2.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (hblk S hS V Z hV S rfl).2.2.1.le)
  -- (a) Bound each unmarked expectation before summing, as in (4.81).
  have hCε8bis : Cε8 + Cbis ≤ Cεt := by simp only [Cεt]; linarith
  have hCe0 : 0 < (N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀ :=
    natCast_mul_cutoffDipoleNormalization_pos (p₀ := p₀) hχ hlam β hε₀ hN1
  have hC' : Zc / 2 * lam ^ (2 - β) ≤ dipoleNormalization χ N β lam := by
    have := hNh N hNh'
    linarith
  have hΛ : 0 < lam ^ ((2 - β) * (k : ℝ)) := Real.rpow_pos_of_pos hlam _
  have hunmarked := activity_diff_of_blocks (M := M) hχ hlam hN1 (by linarith) hX h2 hXk
    (modelHyp_plus (p₀ := p₀) (β := β) (M := M) (L := L) (V := V) (Z := Z) hχ hlam hε₀ hN1)
    (a := ((N : ℝ) * cutoffDipoleNormalization χ N p₀ β lam ε₀)⁻¹) (inv_pos.2 hCe0)
    (dens := cutoffWeight χ β lam (ε₀ * truncationScale p₀ β lam))
    (I₁ := fun S => multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S)
    (fun S _ => plusPartitionFunction_eq_multipoleIntegralPlus hχ hlam hε₀ hN1 S)
    (fun Φ hΦ hdep => integral_labelField_cutoff hχ hlam β hε₀ hN1 hΦ hdep) hCB'
    (pow_pos hlam _) (η := η)
    (fun S hS => (blockComparison_mono_eta hηb (blockComparison_nonneg (hblk S hS V Z hV S rfl).1)
      (hblk S hS V Z hV S rfl).1).mono (le_max_left _ _))
    hD
    (fun n Xs hXs hdisj Es hEs F hF =>
      term_arith hΛ.le hNpos hR0 he (Nat.cast_nonneg _) hCεt.le hCε8bis (le_max_left _ _)
        (le_max_right _ _)
        (hN8 N hN8' hMp V Z hV X hX hXV h2 hXk n Xs hXs hdisj Es hEs F hF)
        (hNbis N hNbis' X hX hXN h2 hXk n Xs hXs hdisj Es hEs F hF))
    hZ hC' hCK.le (fun n Xs hXs hdisj Es hEs F hF =>
      hborn lam hlam N hN1 X hX h2 hXk Xs hXs hdisj Es hEs F hF)
  -- (b) (4.45)
  have hzero := hN0 N hN0' X hX hXN h2 hXk
  have hzero' : |zeroActivity χ N p₀ β lam M ε₀ X - zeroActivityInf χ N β lam M X| ≤
      1 * η / (P₀ * (N : ℝ) ^ (k - 1)) := by
    refine hzero.trans (div_le_div_of_nonneg_right ?_ (mul_pos hP₀ hT).le)
    have h1 : C0 ≤ Cεt := by simp only [Cεt]; linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hR0
    have h3 : 0 ≤ e * v := mul_nonneg he hv
    rw [one_mul, hη_def]
    linarith
  -- (c) the marked terms (the claim (5.106))
  have hθη : Cεne * R + Cne * e * v ≤ max 1 Cne * η :=
    eta_arith hR0 he hv hCεt.le (by simp only [Cεt]; linarith)
  have hmarked := marked_le hX hXk (Q := max 1 Cne * η / (Pp * (N : ℝ) ^ (k - 1)))
    (div_nonneg (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hη) (mul_pos hPp hT).le)
    (fun U _ Xs Es F => ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
          (extendConfig (X.biUnion id) y) *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X)
    (fun U hU n Xs hXs hdisj Es hEs F hF => by
      obtain ⟨hU0, hUX⟩ := Finset.mem_erase.1 hU
      exact (hNne N hNne' hMp V Z hV X hX hXV h2 hXk U (Finset.mem_powerset.1 hUX)
        (Finset.nonempty_iff_ne_empty.2 hU0) n Xs hXs hdisj Es hEs F hF).trans
          (div_le_div_of_nonneg_right hθη (mul_pos hPp hT).le))
  have hmarked' : |∑ U ∈ (X.biUnion id).powerset.erase ∅, clusterSum X fun _ Xs Es F =>
      ∫ y, clusterTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Xs Es F
          (extendConfig (X.biUnion id) y) *
        ∏ i ∈ U, externalBondZ χ p₀ β lam ε₀ V Z (extendConfig (X.biUnion id) y i)
        ∂plusModel χ N p₀ β lam M ε₀ L V Z X| ≤ A₁ * η / (Pp * (N : ℝ) ^ (k - 1)) := by
    refine hmarked.trans (le_of_eq ?_)
    simp only [A₁]
    ring
  -- the combination
  have hfin := combine_le (plusActivity_eq h2) hPp hP₀ hPz hT hη hA₁ hK₁ zero_le_one hmarked'
    hunmarked hzero' hBp hB₀
  refine hfin.trans (le_of_eq ?_)
  simp only [Ctot, hη_def]
  ring

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
