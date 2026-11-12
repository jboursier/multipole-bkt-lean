/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.ExpansionPlus.MultipoleHat
public import MultipoleBKT.LowerBound.ExpansionErrors.Main
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole
public import MultipoleBKT.UpperBound.BoundedUpper.MultipoleBounds
public import MultipoleBKT.Appendix.MultipoleIntegral.Bounds

/-!
# The blocks of the model with frozen bad points, uniformly in `ε₀`

The paper: proof of Proposition 5.19: the block comparisons used in "Proceeding as in (4.81), and using
`λ^{2(k-|S|)} θ_{|S|} ≤ θ_k` for the normalizing factors" and in the change of
denominators `𝖬^0_∞ → 𝖬^0_{ε₀}`, with constants independent of `ε₀`.

Here `θ = C_{ε₀} R̄^{-2} + ε₀^{α(β)k} |V_bad|/N` for `|V_X| = k`, and `λ ≤ min(1, ε₀^{α(β)})` gives
`λ^{2(k-s)} ε₀^{α(β)s} ≤ ε₀^{α(β)k}` for `s ≤ k` (proof of Proposition 5.19).

* `exists_uniform_eps`: common constants for the block sizes `1 ≤ s ≤ k`, with a constant `C`
  independent of `ε₀` and a constant `C_{ε₀}`;
* `plus_blocks`: for `1 ≤ |S| ≤ k ≤ p*(β)`,
  `BlockComparison C λ^{2(k-1)} θ (I^{+,Z}_{mult,ε₀}(S)) (I^0_{mult,∞}(S))` (Lemma A.3 for
  `(v^Z, τ^Z)`, Lemma A.3 for `v` and Lemma A.6), and the denominators
  `𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)`, `𝖬^0_{ε₀}(S) ≤ C 𝖬_{β,λ}(S)` (equations (4.38)–(4.39) for `𝖬^0_{ε₀}`,
  `𝖬_{β,λ}` and (5.65)), with `C` independent of `ε₀`.
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBound

namespace ExpansionPlus

open MeasureTheory Set Finset
open Hierarchical GeneralExpansion BoundedUpper MultipoleIntegral ExpansionErrors

variable {χ : ℂ → ℝ} {β M : ℝ}

/-! ### Uniform constants over the block sizes -/

/-- **Common constants for the block sizes `1 ≤ s ≤ k`, with an `ε₀`-independent constant.** -/
theorem exists_uniform_eps (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℕ → Prop)
    (hmono : ∀ s C C' ε₀ Cε Cε' lam N, 0 < ε₀ → 0 < lam → C ≤ C' → Cε ≤ Cε' →
      P s C ε₀ Cε lam N → P s C' ε₀ Cε' lam N) :
    ∀ k : ℕ, (∀ s, 1 ≤ s → s ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
        ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → P s C ε₀ Cε lam N) →
      ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
        ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ s, 1 ≤ s → s ≤ k → P s C ε₀ Cε lam N := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, one_pos, fun _ _ _ => ⟨1, one_pos, 1, one_pos,
      fun _ _ _ => ⟨0, fun _ _ s hs hsk => by omega⟩⟩⟩
  | succ k ih =>
    intro h
    obtain ⟨C₁, hC₁, h₁⟩ := ih fun s hs hsk => h s hs (by omega)
    obtain ⟨C₂, hC₂, h₂⟩ := h (k + 1) (by omega) le_rfl
    refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, fun ε₀ hε₀ hε₁ => ?_⟩
    obtain ⟨D₁, hD₁, l₁, hl₁, h₁'⟩ := h₁ ε₀ hε₀ hε₁
    obtain ⟨D₂, hD₂, l₂, hl₂, h₂'⟩ := h₂ ε₀ hε₀ hε₁
    refine ⟨max D₁ D₂, lt_max_of_lt_left hD₁, min l₁ l₂, lt_min hl₁ hl₂, fun lam hlam hlt => ?_⟩
    obtain ⟨N₁, hN₁⟩ := h₁' lam hlam (hlt.trans_le (min_le_left _ _))
    obtain ⟨N₂, hN₂⟩ := h₂' lam hlam (hlt.trans_le (min_le_right _ _))
    refine ⟨max N₁ N₂, fun N hN s hs hsk => ?_⟩
    rcases Nat.lt_or_ge s (k + 1) with hlt' | hge
    · exact hmono s C₁ _ ε₀ D₁ _ lam N hε₀ hlam (le_max_left _ _) (le_max_left _ _)
        (hN₁ N (le_trans (le_max_left _ _) hN) s hs (by omega))
    · have hs' : s = k + 1 := by omega
      subst hs'
      exact hmono _ C₂ _ ε₀ D₂ _ lam N hε₀ hlam (le_max_right _ _) (le_max_right _ _)
        (hN₂ N (le_trans (le_max_right _ _) hN))

/-! ### Elementary facts -/

theorem blockComparison_mono_eta {C ℓ η η' I₁ I₀ : ℝ} (hηη' : η ≤ η') (hC : 0 ≤ C)
    (h : BlockComparison C ℓ η I₁ I₀) : BlockComparison C ℓ η' I₁ I₀ := by
  obtain ⟨hη, h1, h0, hle, hd⟩ := h
  exact ⟨hη.trans hηη', h1, h0, hle, hd.trans (mul_le_mul_of_nonneg_left hηη' (by positivity))⟩

/-- `λ^{2(k-s)} ε₀^{αs} ≤ ε₀^{αk}` for `0 < λ ≤ min(1, ε₀^α)`, `ε₀ > 0`, `α ≥ 0`, `s ≤ k`
(proof of Proposition 5.19). -/
theorem pow_mul_rpow_le {lam ε₀ α : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamε : lam ≤ ε₀ ^ α) (hε₀ : 0 < ε₀) {s k : ℕ} (hsk : s ≤ k) :
    lam ^ (2 * (k - s)) * ε₀ ^ (α * s) ≤ ε₀ ^ (α * k) := by
  have h1 : lam ^ (2 * (k - s)) ≤ lam ^ (k - s) :=
    pow_le_pow_of_le_one hlam.le hlam1 (by omega)
  have h2 : lam ^ (k - s) ≤ (ε₀ ^ α) ^ (k - s) := pow_le_pow_left₀ hlam.le hlamε _
  have h3 : (ε₀ ^ α) ^ (k - s) * ε₀ ^ (α * s) = ε₀ ^ (α * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε₀.le, ← Real.rpow_add hε₀, Nat.cast_sub hsk]
    ring_nf
  calc lam ^ (2 * (k - s)) * ε₀ ^ (α * s) ≤ (ε₀ ^ α) ^ (k - s) * ε₀ ^ (α * s) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (Real.rpow_nonneg hε₀.le _)
    _ = ε₀ ^ (α * k) := h3

theorem alphaExponent_nonneg (β : ℝ) : 0 ≤ alphaExponent β := by
  unfold alphaExponent
  split_ifs with h
  · linarith
  · norm_num

/-! ### The sizes of the block functions, uniformly in `ε₀` -/

/-- **(4.38) for `𝖬_{β,λ}`, every size `s ≥ 1`** (Lemma A.3 for `v`): for `M ≥ 9` there is
`C > 0` such that for `λ > 0` and `N` large, `λ^{2(s-1)} / (C N^{s-1}) ≤ 𝖬_{β,λ}(S)` for `|S| = s`. -/
theorem multipolePartitionFunction_lower (hχ : IsMollifier χ) (hβ : 2 < β) {s : ℕ} (hs : 1 ≤ s)
    (hM : 9 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S.card = s →
        lam ^ (2 * (s - 1)) / (C * (N : ℝ) ^ (s - 1)) ≤
          multipolePartitionFunction χ N β lam M S := by
  obtain ⟨Cl, hCl, hlow⟩ := le_multipoleIntegral hχ hβ hs hM
  set Z := dipoleConstant χ β
  have hZ : 0 < Z := dipoleConstant_pos hχ hβ
  refine ⟨Cl * Z ^ s, by positivity, fun lam hlam => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hlow lam hlam
  refine ⟨max N₁ 1, fun N hN S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hℓ : 0 < lam ^ (2 - β) := Real.rpow_pos_of_pos hlam _
  have hℓk : (lam ^ (2 - β)) ^ s = lam ^ ((2 - β) * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
  have hCN' := dipoleNormalization_le hχ hβ hlam N
  have hA0 := natCast_mul_dipoleNormalization_pos hχ hlam β hN1
  have hΛ : 0 ≤ lam ^ (2 * (s - 1)) := pow_nonneg hlam.le _
  rw [multipolePartitionFunction_eq_multipoleIntegral hχ hlam β M hN1 S, hS]
  have hI := hN₁ N (le_trans (le_max_left _ _) hN) S hS
  rw [← hℓk] at hI
  have hA : (N : ℝ) * dipoleNormalization χ N β lam ≤ N * Z * lam ^ (2 - β) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hCN') hNpos.le
  exact gate_lower_algebra hs hNpos hℓ hZ hCl hΛ hA0 hA hI

/-- **(4.39) for `𝖬^0_{ε₀}`, every size `1 ≤ s ≤ p*(β)`** ( for `s ≥ 2`, `𝖬^0_{ε₀}({i}) = 1`):
for `M > 20` there is `C > 0` (not depending on `ε₀`) such that for `ε₀ ∈ (0, 1)`, `λ` small and
`N` large, `𝖬^0_{ε₀}(S) ≤ C λ^{2(s-1)} / N^{s-1}` for `|S| = s`. -/
theorem zeroPartitionFunction_upper (hχ : IsMollifier χ) (hβ : 2 < β) {s : ℕ} (hs : 1 ≤ s)
    (hsp : (s : ℕ∞) ≤ pStar β) (hM : 20 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (p₀ : ℕ) (lam : ℝ), 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = s →
          0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
          zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
            C * lam ^ (2 * (s - 1)) / (N : ℝ) ^ (s - 1) := by
  rcases Nat.lt_or_ge 1 s with hs2 | hs1
  · obtain ⟨C, hC, h⟩ := BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ hs2 hsp hM
    refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
    obtain ⟨lam₀, hlam₀, -, h'⟩ := h ε₀ hε₀ hε₁
    refine ⟨lam₀, hlam₀, fun p₀ lam hlam hlt => ?_⟩
    obtain ⟨N₀, hN₀⟩ := h' p₀ lam hlam hlt
    refine ⟨max N₀ 1, fun N hN S hS => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
    obtain ⟨hlo, hup⟩ := hN₀ N (le_trans (le_max_left _ _) hN) S hS
    exact ⟨lt_of_lt_of_le (by positivity) hlo, hup⟩
  · have hs' : s = 1 := by omega
    subst hs'
    refine ⟨1, one_pos, fun ε₀ hε₀ _ => ⟨1, one_pos, fun p₀ lam hlam _ => ⟨1, fun N hN S hS => ?_⟩⟩⟩
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hS
    rw [BoundedUpper.zeroPartitionFunction_singleton hχ hlam hε₀ hN]
    norm_num

theorem blockComparison_nonneg {C ℓ η I₁ I₀ : ℝ} (h : BlockComparison C ℓ η I₁ I₀) : 0 ≤ C := by
  obtain ⟨-, h1, h0, hle, -⟩ := h
  by_contra hC
  push Not at hC
  nlinarith

/-! ### The blocks of one size -/

/-- The facts on one block `S` of size `s` used in the proof of (5.69), for a subpartition with
`|V_X| = k`: `BlockComparison C λ^{2(k-1)} θ (I^{+,Z}_{mult,ε₀}(S)) (I^0_{mult,∞}(S))` with
`θ = C_{ε₀} R̄^{-2} + ε₀^{α(β)k} |V_bad|/N`, the positivity of `𝖬^{+,Z}_{ε₀}(S)`, `𝖬_{β,λ}(S)`, and
`𝖬^0_{ε₀}(S) ≤ C 𝖬^{+,Z}_{ε₀}(S)`, `𝖬^0_{ε₀}(S) ≤ C 𝖬_{β,λ}(S)`. -/
def PlusBlockFacts (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam M ε₀ L : ℝ) (k s : ℕ) (C Cε : ℝ) : Prop :=
  ∀ (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), badPointsOn p₀ β lam M ε₀ V Z = V →
    ∀ S : Finset ℕ, S.card = s →
      BlockComparison C (lam ^ (2 * (k - 1)))
          (Cε * truncationScale p₀ β lam ^ (-2 : ℝ) + ε₀ ^ (alphaExponent β * k) * (V.card / N))
          (multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S) (multipoleIntegral χ N β lam M S) ∧
        0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
        0 < multipolePartitionFunction χ N β lam M S ∧
        0 < zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ∧
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤
          C * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S ∧
        zeroPartitionFunction χ N p₀ β lam M ε₀ {S} ≤ C * multipolePartitionFunction χ N β lam M S

theorem PlusBlockFacts.mono {N p₀ : ℕ} {lam ε₀ L : ℝ} {k s : ℕ} {C C' Cε Cε' : ℝ}
    (hlam : 0 < lam) (hC : C ≤ C') (hCε : Cε ≤ Cε')
    (h : PlusBlockFacts χ N p₀ β lam M ε₀ L k s C Cε) :
    PlusBlockFacts χ N p₀ β lam M ε₀ L k s C' Cε' := by
  intro V Z hV S hS
  obtain ⟨hB, h1, h2, h5, h3, h4⟩ := h V Z hV S hS
  have hC0 := blockComparison_nonneg hB
  have hR : 0 ≤ truncationScale p₀ β lam ^ (-2 : ℝ) :=
    (Real.rpow_pos_of_pos (Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam) _).le
  refine ⟨(blockComparison_mono_eta ?_ hC0 hB).mono hC, h1, h2, h5,
    h3.trans (mul_le_mul_of_nonneg_right hC h1.le),
    h4.trans (mul_le_mul_of_nonneg_right hC h2.le)⟩
  exact add_le_add_left (mul_le_mul_of_nonneg_right hCε hR) _

/-- **The blocks of one size `1 ≤ s ≤ k ≤ p*(β)`** (Lemmas A.3 and A.6 for `(v^Z, τ^Z)`, Lemma A.3
for `v`, (4.39) for `𝖬^0_{ε₀}`, (5.65)): for `M > 20` with `3^{p(β)} ≤ M` and `L`, there is
`C > 0` (not depending on `ε₀`) such that for `ε₀ ∈ (0, 1)` there are `C_{ε₀} > 0` and `λ₀ > 0` with
`PlusBlockFacts … k s C C_{ε₀}` for `λ ∈ (0, λ₀)` and `N` large. -/
theorem plus_block_size (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (L : ℝ) (hM : 20 < M)
    (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k s : ℕ} (hs : 1 ≤ s) (hsk : s ≤ k)
    (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        PlusBlockFacts χ N p₀ β lam M ε₀ L k s C Cε := by
  have hsp : (s : ℕ∞) ≤ pStar β := le_trans (by exact_mod_cast hsk) hkp
  have hM0 : 0 ≤ M := by linarith
  have hM9 : 9 ≤ M := by linarith
  obtain ⟨Cp, hCp, hIp⟩ := multipoleIntegralPlus_two_sided (χ := χ) hχ hβ hs hsp hM9 L
  obtain ⟨Cu, hCu, hIu⟩ := multipoleIntegral_le hχ hβ hs hsp (χ := χ) hM0
  obtain ⟨CA, hCA, hA7⟩ := multipoleIntegralPlus_sub_le (χ := χ) hχ hβ hs hsp hM0 L p₀
  obtain ⟨Cm, hCm, hMp'⟩ := plusPartitionFunction_two_sided (χ := χ) hχ hβ hs hsp hM9 L
  obtain ⟨Cz, hCz, hZ⟩ := zeroPartitionFunction_upper (χ := χ) hχ hβ hs hsp hM
  obtain ⟨Cl, hCl, hL⟩ := multipolePartitionFunction_lower (χ := χ) hχ hβ hs hM9
  set C := max (Cu * Cp) (max (max 1 CA * Cp) (max (Cz * Cm) (Cz * Cl)))
  have hC : 0 < C := lt_max_of_lt_left (by positivity)
  refine ⟨C, hC, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨Cε, hCε, h7⟩ := hA7 ε₀ hε₀ hε₁.le
  obtain ⟨lm, hlm, hm⟩ := hMp' ε₀ hε₀ hε₁
  obtain ⟨lz, hlz, hz⟩ := hZ ε₀ hε₀ hε₁
  set α := alphaExponent β
  have hα : 0 ≤ α := alphaExponent_nonneg β
  set lM : ℝ := (16 * (6 * s + 2 * M))⁻¹
  have hlM : 0 < lM := by positivity
  refine ⟨Cε, hCε, min (min lM (min lm lz)) (min (min 1 (ε₀ ^ α)) (ε₀ / 2)),
    lt_min (lt_min hlM (lt_min hlm hlz)) (lt_min (lt_min one_pos (Real.rpow_pos_of_pos hε₀ _))
      (by linarith)), fun lam hlam hlt => ?_⟩
  have hltM : lam ≤ lM := (hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hltm : lam < lm := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hltz : lam < lz := hlt.trans_le ((min_le_left _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))).le
  have hlamα : lam ≤ ε₀ ^ α := (hlt.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))).le
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hR1 : 1 ≤ truncationScale p₀ β lam := Appendix.one_le_truncationScale hβ hlam hlam1
  have h2 : 2 * lam ≤ ε₀ * truncationScale p₀ β lam := by
    have : ε₀ ≤ ε₀ * truncationScale p₀ β lam := le_mul_of_one_le_right hε₀.le hR1
    linarith
  obtain ⟨Np, hNp⟩ := hIp lam hlam hltM
  obtain ⟨Nm, hNm⟩ := hm p₀ lam hlam hltm
  obtain ⟨Nz, hNz⟩ := hz p₀ lam hlam hltz
  obtain ⟨Nl, hNl⟩ := hL lam hlam
  refine ⟨max (max Np Nm) (max (max Nz Nl) 1), fun N hN V Z hV S hS => ?_⟩
  have hN1 : 1 ≤ N := le_trans ((le_max_right _ _).trans (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNs : 0 < (N : ℝ) ^ (s - 1) := pow_pos hNpos _
  have hR := Appendix.truncationScale_pos (p₀ := p₀) (β := β) hlam
  set R := truncationScale p₀ β lam ^ (-2 : ℝ) with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hΛs : 0 < lam ^ (2 * (s - 1)) := pow_pos hlam _
  obtain ⟨hIlo, -⟩ := hNp N (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hN) p₀ ε₀ h2 hMp
    V Z hV S hS
  have hIup := hIu lam hlam N S hS
  have hdiff := h7 lam hlam (by linarith) hMp N V Z hV S hS
  obtain ⟨hMlo, -⟩ := hNm N (le_trans ((le_max_right _ _).trans (le_max_left _ _)) hN) hMp V Z
    hV S hS
  obtain ⟨hZpos, hZup⟩ := hNz N (le_trans ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _))) hN) S hS
  have hLlo := hNl N (le_trans ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
    hN) S hS
  set u : ℝ := N * lam ^ ((2 - β) * s) * lam ^ (2 * (s - 1)) with hu_def
  have hu : 0 < u := by positivity
  have hI₁ : u ≤ Cp * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
    have := hIlo
    rw [show Cp⁻¹ * N * lam ^ ((2 - β) * s) * lam ^ (2 * (s - 1)) = Cp⁻¹ * u by ring] at this
    rw [inv_mul_le_iff₀ hCp] at this
    exact this
  have hI₁pos : 0 < multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by
    have : 0 < Cp * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := hu.trans_le hI₁
    exact pos_of_mul_pos_right this hCp.le
  have hI₀ : 0 ≤ multipoleIntegral χ N β lam M S := by
    rw [multipoleIntegral_eq_toReal_lintegral hχ hlam N β M S]
    exact ENNReal.toReal_nonneg
  set η : ℝ := Cε * R + ε₀ ^ (α * k) * (V.card / N) with hη_def
  have hη : 0 ≤ η := by positivity
  have hPpos : 0 < plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
    lt_of_lt_of_le (by positivity) hMlo
  have hMpos : 0 < multipolePartitionFunction χ N β lam M S :=
    multipolePartitionFunction_pos hχ hlam β (by linarith) hN1 (Finset.card_pos.1 (hS ▸ hs))
  refine ⟨⟨hη, hI₁pos, hI₀, ?_, ?_⟩, hPpos, hMpos, hZpos, ?_, ?_⟩
  · -- `I^0_∞ ≤ C I^+`
    have hup : multipoleIntegral χ N β lam M S ≤ Cu * u := by
      have := hIup; rw [hu_def]; linarith
    calc multipoleIntegral χ N β lam M S ≤ Cu * u := hup
      _ ≤ Cu * (Cp * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S) :=
          mul_le_mul_of_nonneg_left hI₁ hCu.le
      _ = (Cu * Cp) * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S := by ring
      _ ≤ C * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hI₁pos.le
  · -- `|I^0_∞ - I^+| λ^{2(k-1)} ≤ C I^+ θ`
    have hsplit : lam ^ (2 * (k - 1)) = lam ^ (2 * (s - 1)) * lam ^ (2 * (k - s)) := by
      rw [← pow_add]; congr 1; omega
    have hgain : lam ^ (2 * (k - s)) * (Cε * R + CA * ε₀ ^ (α * s) * (V.card / N)) ≤
        max 1 CA * η := by
      have h1 : lam ^ (2 * (k - s)) ≤ 1 := pow_le_one₀ hlam.le hlam1
      have h2' := pow_mul_rpow_le hlam hlam1 hlamα hε₀ hsk
      have hv : 0 ≤ (V.card : ℝ) / N := by positivity
      calc lam ^ (2 * (k - s)) * (Cε * R + CA * ε₀ ^ (α * s) * (V.card / N))
          = lam ^ (2 * (k - s)) * (Cε * R) +
              CA * (lam ^ (2 * (k - s)) * ε₀ ^ (α * s)) * (V.card / N) := by ring
        _ ≤ 1 * (Cε * R) + CA * ε₀ ^ (α * k) * (V.card / N) := by
            gcongr
        _ ≤ max 1 CA * (Cε * R) + max 1 CA * ε₀ ^ (α * k) * (V.card / N) := by
            gcongr
            · exact le_max_left _ _
            · exact le_max_right _ _
        _ = max 1 CA * η := by rw [hη_def]; ring
    have hd : |multipoleIntegral χ N β lam M S - multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S| ≤
        N * lam ^ ((2 - β) * s) * (Cε * R + CA * ε₀ ^ (α * s) * (V.card / N)) := by
      rw [abs_sub_comm]
      refine hdiff.trans (le_of_eq ?_)
      field_simp
      rw [hRdef]
    calc |multipoleIntegral χ N β lam M S - multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S| *
          lam ^ (2 * (k - 1))
        ≤ N * lam ^ ((2 - β) * s) * (Cε * R + CA * ε₀ ^ (α * s) * (V.card / N)) *
            (lam ^ (2 * (s - 1)) * lam ^ (2 * (k - s))) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_right hd (by positivity)
      _ = u * (lam ^ (2 * (k - s)) * (Cε * R + CA * ε₀ ^ (α * s) * (V.card / N))) := by
          rw [hu_def]; ring
      _ ≤ (Cp * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S) * (max 1 CA * η) :=
          mul_le_mul hI₁ hgain (by positivity) (by positivity)
      _ = (max 1 CA * Cp) * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S * η := by ring
      _ ≤ C * multipoleIntegralPlus χ N p₀ β lam M ε₀ L V Z S * η := by
          gcongr
          exact (le_max_left _ _).trans (le_max_right _ _)
  · -- `𝖬^0_{ε₀} ≤ C 𝖬^{+,Z}`
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ {S}
        ≤ Cz * lam ^ (2 * (s - 1)) / (N : ℝ) ^ (s - 1) :=
          hZup
      _ = (Cz * Cm) * (lam ^ (2 * (s - 1)) / (Cm * (N : ℝ) ^ (s - 1))) := by field_simp
      _ ≤ (Cz * Cm) * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S :=
          mul_le_mul_of_nonneg_left hMlo (by positivity)
      _ ≤ C * plusPartitionFunction χ N p₀ β lam M ε₀ L V Z S := by
          gcongr
          exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  · -- `𝖬^0_{ε₀} ≤ C 𝖬_{β,λ}`
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ {S}
        ≤ Cz * lam ^ (2 * (s - 1)) / (N : ℝ) ^ (s - 1) :=
          hZup
      _ = (Cz * Cl) * (lam ^ (2 * (s - 1)) / (Cl * (N : ℝ) ^ (s - 1))) := by field_simp
      _ ≤ (Cz * Cl) * multipolePartitionFunction χ N β lam M S :=
          mul_le_mul_of_nonneg_left hLlo (by positivity)
      _ ≤ C * multipolePartitionFunction χ N β lam M S := by
          gcongr
          exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- **The blocks of all sizes `1 ≤ s ≤ k`**, uniformly (`exists_uniform_eps`). -/
theorem plus_blocks (hχ : IsMollifier χ) (hβ : 2 < β) {p₀ : ℕ} (L : ℝ) (hM : 20 < M)
    (hMp : (3 : ℝ) ^ pBeta p₀ β ≤ M) {k : ℕ} (hkp : (k : ℕ∞) ≤ pStar β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ Cε : ℝ, 0 < Cε ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ s, 1 ≤ s → s ≤ k → PlusBlockFacts χ N p₀ β lam M ε₀ L k s C Cε :=
  exists_uniform_eps (fun s C ε₀ Cε lam N => PlusBlockFacts χ N p₀ β lam M ε₀ L k s C Cε)
    (fun _ _ _ _ _ _ _ _ _ hlam hC hCε h => h.mono hlam hC hCε) k
    fun _ hs hsk => plus_block_size hχ hβ L hM hMp hs hsk hkp

end ExpansionPlus

end UpperBound

end MultipoleBKT

end
