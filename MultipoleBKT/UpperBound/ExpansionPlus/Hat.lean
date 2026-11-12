/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.ActivityDiff
public import MultipoleBKT.LowerBound.BoundedLower.MultipoleActivity

/-!
# Proposition 5.19, eq. (5.69) for `𝖪̂^{+,Z}_{ε₀}`

The paper: the hatted bound following Proposition 5.19 and its proof:

"Finally, by (5.101), `|𝖪̂^{+,Z}_{ε₀}(X) - 𝖪^0_{ε₀}(X)| ≤ |𝖪^{+,Z}_{ε₀}(X) - 𝖪^0_{ε₀}(X)|
+ |𝖪^0_{ε₀}(X)| ∑_{S ∈ X} (g^Z_{ε₀}(S) - 1)`. Since `k = |V_X| ≤ p(β)`, Proposition 4.23 and
(5.105) bound the last term by `C θ_k / (𝖬^0_{ε₀}(X) N^{k-1})`."

**On the constant.** Proposition 4.23 bounds `|𝖪^0_{ε₀}(X)|` with a constant depending on `ε₀`
(eq. (4.40)), which would put an `ε₀`-dependent constant in front of
`ε₀^{α(β)k} |V_bad| / N`. Here `|𝖪^0_{ε₀}(X)| ≤ |𝖪^0_∞(X)| + |𝖪^0_{ε₀}(X) - 𝖪^0_∞(X)|`: the first term
is bounded by (4.40) for `𝖪^0_∞ = 𝖪^mult` (Proposition 4.23, `ε₀`-free, for
`k ≤ p*(β)`), the second by Proposition 4.24, eq. (4.45) (`C_{ε₀} R̄^{-2}`), times
`∏ g - 1 ≤ C` (eq. (5.101)); so the constant of the `|V_bad|` term is independent of
`ε₀`, as stated. The product `∏_{S ∈ X} g^Z_{ε₀}(S) - 1` replaces the paper's sum (they agree up to
a constant, `abs_prod_sub_one_le`).

* `hat_arith`: `|𝖪/G - 𝖪^0| ≤ |𝖪 - 𝖪^0| + |𝖪^0| (G - 1)` for `G ≥ 1`;
* `external_uniform`: eq. (5.105) for all sizes `1 ≤ s ≤ k`, uniformly;
* `zeroActivity_mul_external_le` (internal): the bound on `|𝖪^0_{ε₀}(X)| (∏_S g^Z_{ε₀}(S) - 1)`;
* `eq_K_hat_diff_of_inputs` (internal): **eq. (5.69) for `𝖪̂^{+,Z}_{ε₀}`** from the inputs.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset Filter
open Hierarchical BoundedUpper ExpansionErrors Multipole SetPartition MultipoleIntegral

variable {χ : ℂ → ℝ} {β M : ℝ}

/-- `|K/G - K₀| ≤ |K - K₀| + |K₀| (G - 1)` for `G ≥ 1`. -/
theorem hat_arith {K K₀ G : ℝ} (hG : 1 ≤ G) : |K / G - K₀| ≤ |K - K₀| + |K₀| * (G - 1) := by
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have e : K / G - K₀ = (K - K₀) / G + K₀ * ((1 - G) / G) := by field_simp; ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos hG0]
    exact div_le_self (abs_nonneg _) hG
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_div, abs_of_pos hG0, abs_of_nonpos (by linarith), neg_sub]
    exact div_le_self (by linarith) hG

/-- **Eq. (5.105) for all sizes `1 ≤ s ≤ k ≤ p(β)`**, with an `ε₀`-independent
constant, and `g^Z_{ε₀}(S) ≤ C` (eq. (5.101)). -/
theorem external_uniform (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀) (L : ℝ)
    (hM : 20 < M) (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k : ℕ} (hkp : k ≤ pBeta p₀ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s, 1 ≤ s → s ≤ k →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ S : Finset ℕ, S.card = s →
          0 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ∧
          externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ≤
            (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
              C * ε₀ ^ (alphaExponent β * s) * (V.card / N)) / lam ^ (2 * (s - 1)) := by
  refine exists_uniform_eps (fun s C ε₀ Cε lam N =>
      ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ S : Finset ℕ, S.card = s →
          0 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ∧
          externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ≤
            (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
              C * ε₀ ^ (alphaExponent β * s) * (V.card / N)) / lam ^ (2 * (s - 1)))
    (fun s C C' ε₀ Cε Cε' lam N hε₀ hlam hC hCε h V Z hV S hS => ?_) k
    fun s hs hsk => external_factor_bound hχ hβ hp₀ L hM hMp hs (hsk.trans hkp)
  obtain ⟨h0, h1⟩ := h V Z hV S hS
  refine ⟨h0, h1.trans (div_le_div_of_nonneg_right ?_ (pow_pos hlam _).le)⟩
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  have h1 : 0 ≤ truncationScale p₀ β lam ^ (-2 : ℝ) := (Real.rpow_pos_of_pos hR _).le
  have h2 : 0 ≤ ε₀ ^ (alphaExponent β * s) * ((V.card : ℝ) / N) :=
    mul_nonneg (Real.rpow_nonneg hε₀.le _) (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hCε h1
  have h4 := mul_le_mul_of_nonneg_right hC h2
  linarith

/-- `(A + B ε₀^{αs}) / λ^{2(s-1)} ≤ (A + B ε₀^{αk}) / λ^{2(k-1)}` for `1 ≤ s ≤ k`,
`0 < λ ≤ min(1, ε₀^α)` (proof of Proposition 5.19: `λ^{2(k-s)} θ_s ≤ θ_k`). -/
theorem size_shift_le {lam ε₀ α A B : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamα : lam ≤ ε₀ ^ α) (hε₀ : 0 < ε₀) (hA : 0 ≤ A) (hB : 0 ≤ B) {s k : ℕ} (hs : 1 ≤ s)
    (hsk : s ≤ k) :
    (A + B * ε₀ ^ (α * s)) / lam ^ (2 * (s - 1)) ≤
      (A + B * ε₀ ^ (α * k)) / lam ^ (2 * (k - 1)) := by
  have hsplit : lam ^ (2 * (k - 1)) = lam ^ (2 * (s - 1)) * lam ^ (2 * (k - s)) := by
    rw [← pow_add]; congr 1; omega
  have hp1 : 0 < lam ^ (2 * (s - 1)) := pow_pos hlam _
  have hp2 : 0 < lam ^ (2 * (k - s)) := pow_pos hlam _
  have h1 : lam ^ (2 * (k - s)) ≤ 1 := pow_le_one₀ hlam.le hlam1
  have h2 := pow_mul_rpow_le hlam hlam1 hlamα hε₀ hsk
  rw [div_le_div_iff₀ hp1 (pow_pos hlam _), hsplit]
  have key : (A + B * ε₀ ^ (α * s)) * lam ^ (2 * (k - s)) ≤ A + B * ε₀ ^ (α * k) := by
    have e : (A + B * ε₀ ^ (α * s)) * lam ^ (2 * (k - s)) =
        A * lam ^ (2 * (k - s)) + B * (lam ^ (2 * (k - s)) * ε₀ ^ (α * s)) := by ring
    rw [e]
    exact add_le_add (mul_le_of_le_one_right hA h1) (mul_le_mul_of_nonneg_left h2 hB)
  calc (A + B * ε₀ ^ (α * s)) * (lam ^ (2 * (s - 1)) * lam ^ (2 * (k - s)))
      = lam ^ (2 * (s - 1)) * ((A + B * ε₀ ^ (α * s)) * lam ^ (2 * (k - s))) := by ring
    _ ≤ lam ^ (2 * (s - 1)) * (A + B * ε₀ ^ (α * k)) := mul_le_mul_of_nonneg_left key hp1.le
    _ = (A + B * ε₀ ^ (α * k)) * lam ^ (2 * (s - 1)) := by ring

/-- The arithmetic of the hatted correction: with `|K_∞| ≤ C_K Λ / (P T)`,
`|K_0 - K_∞| ≤ C_0 R / (P T)`, `0 ≤ G - 1 ≤ C_g^k k η'`, `G - 1 ≤ C_g^k`, `Λ η' = A`,
`P_z ≤ B P`: `|K_0| (G - 1) ≤ B (C_K C_g^k k A + C_0 C_g^k R) / (T P_z)`. -/
theorem hat_correction_arith {K₀ Ki G P Pz T CK C0 Cg R A η' Λ B : ℝ} {k : ℕ}
    (hP : 0 < P) (hPz : 0 < Pz) (hT : 0 < T) (hCK : 0 ≤ CK) (hC0 : 0 ≤ C0) (hCg : 1 ≤ Cg)
    (hR : 0 ≤ R) (hΛ : 0 ≤ Λ) (hη' : 0 ≤ η') (hG1 : 0 ≤ G - 1)
    (hGη : G - 1 ≤ Cg ^ k * (k * η')) (hGC : G - 1 ≤ Cg ^ k) (hA : Λ * η' = A)
    (hKi : |Ki| ≤ CK * Λ / (P * T)) (hK0 : |K₀ - Ki| ≤ C0 * R / (P * T)) (hB : Pz ≤ B * P) :
    |K₀| * (G - 1) ≤ B * (CK * Cg ^ k * k * A + C0 * Cg ^ k * R) / (T * Pz) := by
  have hPT : 0 < P * T := mul_pos hP hT
  have hCgk : 0 ≤ Cg ^ k := by positivity
  have hA0 : 0 ≤ A := hA ▸ mul_nonneg hΛ hη'
  have h1 : |Ki| * (G - 1) ≤ CK * Cg ^ k * k * A / (P * T) := by
    calc |Ki| * (G - 1) ≤ CK * Λ / (P * T) * (Cg ^ k * (k * η')) :=
          mul_le_mul hKi hGη hG1 (by positivity)
      _ = CK * Cg ^ k * k * A / (P * T) := by rw [← hA]; ring
  have h2 : |K₀ - Ki| * (G - 1) ≤ C0 * Cg ^ k * R / (P * T) := by
    calc |K₀ - Ki| * (G - 1) ≤ C0 * R / (P * T) * Cg ^ k :=
          mul_le_mul hK0 hGC hG1 (by positivity)
      _ = C0 * Cg ^ k * R / (P * T) := by ring
  have hnum : 0 ≤ CK * Cg ^ k * k * A + C0 * Cg ^ k * R := by positivity
  calc |K₀| * (G - 1) ≤ (|Ki| + |K₀ - Ki|) * (G - 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hG1
        calc |K₀| = |Ki + (K₀ - Ki)| := by ring_nf
          _ ≤ |Ki| + |K₀ - Ki| := abs_add_le _ _
    _ = |Ki| * (G - 1) + |K₀ - Ki| * (G - 1) := by ring
    _ ≤ CK * Cg ^ k * k * A / (P * T) + C0 * Cg ^ k * R / (P * T) := add_le_add h1 h2
    _ = (CK * Cg ^ k * k * A + C0 * Cg ^ k * R) / (P * T) := by ring
    _ ≤ B * (CK * Cg ^ k * k * A + C0 * Cg ^ k * R) / (Pz * T) :=
        div_le_div_of_le_mul hnum hP hPz hT hB
    _ = B * (CK * Cg ^ k * k * A + C0 * Cg ^ k * R) / (T * Pz) := by rw [mul_comm Pz T]

/-- The product of the external factors: if `1 ≤ g_S ≤ C_g` and `g_S - 1 ≤ η'` for `S ∈ X`,
`|X| ≤ k`, `η' ≥ 0`, then `1 ≤ ∏ g`, `∏ g - 1 ≤ C_g^k k η'` and `∏ g - 1 ≤ C_g^k`. -/
theorem prod_external_le {X : Finset (Finset ℕ)} {g : Finset ℕ → ℝ} {Cg η' : ℝ} {k : ℕ}
    (hCg : 1 ≤ Cg) (hk : X.card ≤ k) (hη' : 0 ≤ η') (hg1 : ∀ S ∈ X, 1 ≤ g S)
    (hgC : ∀ S ∈ X, g S ≤ Cg) (hgη : ∀ S ∈ X, g S - 1 ≤ η') :
    1 ≤ ∏ S ∈ X, g S ∧ ∏ S ∈ X, g S - 1 ≤ Cg ^ k * (k * η') ∧ ∏ S ∈ X, g S - 1 ≤ Cg ^ k := by
  have hone : 1 ≤ ∏ S ∈ X, g S := by
    have := Finset.prod_le_prod₀ (s := X) (f := fun _ => (1 : ℝ)) (g := g)
      (fun _ _ => zero_le_one) hg1
    simpa using this
  have hg0 : ∀ S ∈ X, 0 ≤ g S := fun S hS => zero_le_one.trans (hg1 S hS)
  refine ⟨hone, ?_, ?_⟩
  · have h := abs_prod_sub_one_le X hCg hg0 hgC fun S hS => by
      rw [abs_of_nonneg (sub_nonneg.2 (hg1 S hS))]
      exact hgη S hS
    refine (le_abs_self _).trans (h.trans ?_)
    have h1 : Cg ^ X.card ≤ Cg ^ k := pow_le_pow_right₀ hCg hk
    have h2 : (X.card : ℝ) * η' ≤ k * η' :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hη'
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  · have h := prod_le_pow_card_of_nonneg X hg0 hgC
    have h1 : Cg ^ X.card ≤ Cg ^ k := pow_le_pow_right₀ hCg hk
    linarith

open scoped Classical in
/-- **The hatted correction** (internal; proof of Proposition 5.19): for `β > 2`,
`p₀ ≥ 1`, `L` and `2 ≤ k ≤ p(β)` there is `M₀ > 20` such that for every `M ≥ M₀` with
`3^{p(β)} ≤ M` for which (A.50) of Lemma A.7 holds, there is `C > 0` (not depending
on `ε₀`) such that for every `ε₀ ∈ (0, 1)` there are `C_{ε₀} > 0` and `λ₀ > 0` such that for every
`λ ∈ (0, λ₀)` there is `N₀` with, for `N ≥ N₀`, every frozen configuration and every subpartition
`X` of `[N] ∖ V` with `|V_X| = k`: `1 ≤ ∏_{S ∈ X} g^Z_{ε₀}(S)` and
`|𝖪^0_{ε₀}(X)| (∏_{S ∈ X} g^Z_{ε₀}(S) - 1) ≤ (C_{ε₀} R̄^{-2} + C ε₀^{α(β)k} |V_bad|/N) /
(N^{k-1} 𝖬^0_{ε₀}(X))`. -/
theorem zeroActivity_mul_external_le (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (L : ℝ) {k : ℕ} (hk : 2 ≤ k) (hkp : k ≤ pBeta p₀ β) :
    ∃ M₀ : ℝ, 20 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M →
      LemmaA8BisStatement χ β M p₀ k →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
        ∀ X : Finset (Finset ℕ), IsSubpartition X → X.biUnion id ⊆ goodLabels V →
          (X.biUnion id).card = k →
          1 ≤ ∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S ∧
          |zeroActivity χ N p₀ β lam M ε₀ X| *
              (∏ S ∈ X, externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1) ≤
            (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) +
                C * ε₀ ^ (alphaExponent β * k) * (V.card / N)) /
              ((N : ℝ) ^ (k - 1) * zeroPartitionFunction χ N p₀ β lam M ε₀ X) := by
  have hkp' : (k : ℕ∞) ≤ pStar β := TheoremTwo.natCast_le_pStar_of_le_pBeta hp₀ hβ hkp
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨M₁, hM₁, hK38⟩ := BoundedLower.multipoleActivity_bound χ hχ β hβ k hkp'
  obtain ⟨M₂, hM₂, hK0⟩ := eq_K_diff0_of_lemma_A8 hχ hβ hk hkp' p₀
  refine ⟨max M₁ M₂, lt_max_of_lt_left hM₁, fun M hM hMp hA8b => ?_⟩
  have hM20 : 20 < M := lt_of_lt_of_le hM₁ ((le_max_left _ _).trans hM)
  have hM3 : 3 ≤ M := by linarith
  obtain ⟨CK, hCK, lK, hlK, -, hKb⟩ := hK38 M ((le_max_left _ _).trans hM)
  have hK0' := hK0 M ((le_max_right _ _).trans hM) hA8b
  obtain ⟨CB, hCB, hblocks⟩ := plus_blocks (χ := χ) hχ hβ L hM20 hMp hkp'
  obtain ⟨Cgx, hCgx, hext⟩ := external_uniform (χ := χ) hχ hβ hp₀ L hM20 hMp hkp
  obtain ⟨Ce, hCe, hgle⟩ := externalNormalization_le hχ p₀ β hβ0
  set Cg := Real.exp (β * (Ce * k))
  have hCg : 1 ≤ Cg := Real.one_le_exp (by positivity)
  set CB' := max CB 1
  have hCB' : 1 ≤ CB' := le_max_right _ _
  refine ⟨CB' ^ k * (CK * Cg ^ k * k * Cgx) + 1, by positivity, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cεb, hCεb, lb, hlb, hb⟩ := hblocks ε₀ hε₀ hε₁
  obtain ⟨Cεg, hCεg, lg, hlg, hg⟩ := hext ε₀ hε₀ hε₁
  obtain ⟨C0, hC0, l0, hl0, -, hK0''⟩ := hK0' ε₀ hε₀ hε₁
  set α := alphaExponent β
  refine ⟨CB' ^ k * (CK * Cg ^ k * k * Cεg + C0 * Cg ^ k) + 1, by positivity,
    min (min (min lb lg) (min l0 lK)) (min (min 1 (ε₀ ^ α)) ε₀),
    lt_min (lt_min (lt_min hlb hlg) (lt_min hl0 hlK))
      (lt_min (lt_min one_pos (Real.rpow_pos_of_pos hε₀ _)) hε₀), fun lam hlam hlt => ?_⟩
  have hltb : lam < lb := hlt.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hltg : lam < lg := hlt.trans_le ((min_le_left _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hlt0 : lam < l0 := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hltK : lam < lK := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))).le
  have hlamα : lam ≤ ε₀ ^ α := (hlt.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))).le
  have hlε : lam ≤ ε₀ := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨Nb, hNb⟩ := hb lam hlam hltb
  obtain ⟨Ng, hNg⟩ := hg lam hlam hltg
  obtain ⟨N0, hN0⟩ := hK0'' lam hlam hlt0
  obtain ⟨NK, hNK⟩ := hKb lam hlam hltK
  refine ⟨max (max Nb Ng) (max (max N0 NK) 1), fun N hN V Z hV X hX hXV hXk => ?_⟩
  have hNb' : Nb ≤ N := le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN
  have hNg' : Ng ≤ N := le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN
  have hN0' : N0 ≤ N := le_trans ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _))) hN
  have hNK' : NK ≤ N := le_trans ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _))) hN
  have hN1 : 1 ≤ N := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hT : (0 : ℝ) < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  set e := ε₀ ^ (α * k)
  have he : 0 ≤ e := by positivity
  set v : ℝ := V.card / N
  have hv : 0 ≤ v := by positivity
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have hlamh : lam ≤ ε₀ * truncationScale p₀ β lam :=
    hlε.trans (le_mul_of_one_le_right hε₀.le hR1)
  have hVZ : V ⊆ badPointsOn p₀ β lam M ε₀ V Z := hV.symm.subset
  have hXN : X.biUnion id ⊆ Finset.range N := hXV.trans (goodLabels_subset_range V)
  have hXk' : X.card ≤ k := hXk ▸ card_le_card_biUnion hX
  -- the blocks
  have hblk : ∀ S ∈ X, PlusBlockFacts χ N p₀ β lam M ε₀ L k S.card CB Cεb := fun S hS =>
    hNb N hNb' S.card (card_block_mem hX hS).1 (hXk ▸ (card_block_mem hX hS).2)
  set P₀ := ∏ S ∈ X, multipolePartitionFunction χ N β lam M S
  set Pz := zeroPartitionFunction χ N p₀ β lam M ε₀ X
  have hPz_eq : Pz = ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} :=
    zeroPartitionFunction_eq_prod' X
  have hP₀ : 0 < P₀ := prod_pos fun S hS => (hblk S hS V Z hV S rfl).2.2.1
  have hPz : 0 < Pz := by
    rw [hPz_eq]; exact prod_pos fun S hS => (hblk S hS V Z hV S rfl).2.2.2.1
  have hB₀ : Pz ≤ CB' ^ k * P₀ := by
    rw [hPz_eq]
    exact prod_le_pow_mul_prod hCB' hXk' (fun S hS => (hblk S hS V Z hV S rfl).2.2.2.1.le)
      (fun S hS => (hblk S hS V Z hV S rfl).2.2.1) fun S hS =>
        ((hblk S hS V Z hV S rfl).2.2.2.2.2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (hblk S hS V Z hV S rfl).2.2.1.le)
  -- the external factors
  set η' := (Cεg * R + Cgx * e * v) / lam ^ (2 * (k - 1))
  have hη' : 0 ≤ η' := by positivity
  have hgS : ∀ S ∈ X, 1 ≤ externalNormalization χ N p₀ β lam M ε₀ L V Z S ∧
      externalNormalization χ N p₀ β lam M ε₀ L V Z S ≤ Cg ∧
      externalNormalization χ N p₀ β lam M ε₀ L V Z S - 1 ≤ η' := by
    intro S hS
    obtain ⟨hs1, hsk⟩ := card_block_mem hX hS
    rw [hXk] at hsk
    have hpos := (hblk S hS V Z hV S rfl).2.1
    obtain ⟨h0, h1⟩ := hNg N hNg' S.card hs1 hsk V Z hV S rfl
    refine ⟨by linarith, (hgle lam M ε₀ L V Z hlam hε₀ hN1 hlamh hMp hM3 hVZ S hpos).trans ?_,
      h1.trans ?_⟩
    · refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hβ0)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsk) hCe.le
    · have := size_shift_le hlam hlam1 hlamα hε₀ (mul_nonneg hCεg.le hR0)
        (mul_nonneg hCgx.le hv) hs1 hsk (A := Cεg * R) (B := Cgx * v)
      have e1 : Cεg * R + Cgx * ε₀ ^ (α * S.card) * v = Cεg * R + Cgx * v * ε₀ ^ (α * S.card) := by
        ring
      have e2 : Cεg * R + Cgx * e * v = Cεg * R + Cgx * v * e := by ring
      simp only [η', e2]
      rw [e1]
      exact this
  obtain ⟨hG1, hGη, hGC⟩ := prod_external_le hCg hXk' hη' (fun S hS => (hgS S hS).1)
    (fun S hS => (hgS S hS).2.1) fun S hS => (hgS S hS).2.2
  refine ⟨hG1, ?_⟩
  -- the case `|X| ≤ 1`
  by_cases h2 : 2 ≤ X.card
  swap
  · have h1 : X.card ≤ 1 := by omega
    rw [zeroActivity, modelActivity_eq_zero_of_card_le_one _ _ _ _ _ _ h1, abs_zero, zero_mul]
    exact div_nonneg (by positivity) (mul_pos hT hPz).le
  -- (4.40) and (4.45)
  have hKi : |zeroActivityInf χ N β lam M X| ≤
      CK * lam ^ (2 * (k - 1)) / (P₀ * (N : ℝ) ^ (k - 1)) := by
    rw [zeroActivityInf_eq_multipoleActivity hχ hlam β hN1 (by linarith) hX]
    exact hNK N hNK' X hX hXN h2 hXk
  have hK0X := hN0 N hN0' X hX hXN h2 hXk
  have hA : lam ^ (2 * (k - 1)) * η' = Cεg * R + Cgx * e * v := by
    simp only [η']
    field_simp
  have h := hat_correction_arith hP₀ hPz hT hCK.le hC0.le hCg hR0 (pow_pos hlam _).le hη'
    (sub_nonneg.2 hG1) hGη hGC hA hKi hK0X hB₀
  refine h.trans (div_le_div_of_nonneg_right ?_ (mul_pos hT hPz).le)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hev : 0 ≤ e * v := mul_nonneg he hv
  have hCgk : 0 ≤ Cg ^ k := by positivity
  have e3 : CB' ^ k * (CK * Cg ^ k * k * (Cεg * R + Cgx * e * v) + C0 * Cg ^ k * R) =
      CB' ^ k * (CK * Cg ^ k * k * Cεg + C0 * Cg ^ k) * R +
        CB' ^ k * (CK * Cg ^ k * k * Cgx) * e * v := by ring
  rw [e3]
  have h5 : CB' ^ k * (CK * Cg ^ k * k * Cεg + C0 * Cg ^ k) * R ≤
      (CB' ^ k * (CK * Cg ^ k * k * Cεg + C0 * Cg ^ k) + 1) * R :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hR0
  have h6 : CB' ^ k * (CK * Cg ^ k * k * Cgx) * e * v ≤
      (CB' ^ k * (CK * Cg ^ k * k * Cgx) + 1) * e * v := by
    rw [mul_assoc, mul_assoc (CB' ^ k * (CK * Cg ^ k * k * Cgx) + 1)]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hev
  linarith

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
