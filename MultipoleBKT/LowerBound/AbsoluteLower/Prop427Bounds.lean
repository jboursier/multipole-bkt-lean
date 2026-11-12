/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Large
public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Series
public import MultipoleBKT.LowerBound.BoundedLowerEps.Multipole
public import MultipoleBKT.UpperBound.AbsoluteUpper.Bounded
public import MultipoleBKT.UpperBound.BadPointTypes.TypeTwoLow

/-!
# The per-cluster bounds of Lemma 4.59 and Proposition 4.27

The proof of Lemma 4.59: equations (4.127)–(4.128) and the vanishing anchored norm.

`gammaBeta_le_errorRate` compares the bounded-cluster remainder with
`errorRate`. `exists_errorRate_le_mul_pow` proves that the large-cluster
contribution to the anchored norm tends to zero. `exists_zero_lower`
collects the lower bounds for all bounded block sizes with a coefficient
independent of the cutoff. `abs_mul_le_of_zero_lower` inserts those lower
bounds into the activity denominator before the profile entropy sums.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open Finset Hierarchical
open TheoremTwo (errorRate_of_lt_four' errorRate_of_four_le tsum_transition_nonneg
  exists_rpow_mul_log_le one_le_pBeta' transitionBeta_pBeta_lt natCast_le_pStar_of_le_pBeta)

variable {β lam : ℝ} {p₀ : ℕ}

/-! ### `γ_{β,λ,k} ≤ δ_{β,λ}` for `k > p(β)` -/

theorem tsum_transition_eq {β lam : ℝ} {q₀ : ℕ} (hq₀ : 2 ≤ q₀) (hβ : β = transitionBeta q₀) :
    (∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0)) =
      |Real.log lam| := by
  rw [tsum_eq_single q₀]
  · rw [ite_eq_left ⟨hq₀, hβ⟩]
  · intro q hq
    rw [ite_eq_right]
    rintro ⟨hq2, hβq⟩
    apply hq
    have h1 : transitionBeta q = transitionBeta q₀ := hβq.symm.trans hβ
    unfold transitionBeta at h1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hq00 : (0 : ℝ) < q₀ := by exact_mod_cast (show 0 < q₀ by omega)
    have : (2 : ℝ) / q = 2 / q₀ := by linarith
    field_simp at this
    exact_mod_cast (by linarith : (q : ℝ) = q₀)

/-- **`γ_{β,λ,k} ≤ δ_{β,λ}` for `k > p(β)`** (Definitions 2.9 and 4.22). -/
theorem gammaBeta_le_errorRate (hp₀ : 1 ≤ p₀) (hβ : 2 < β) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    {k : ℕ} (hk : pBeta p₀ β < k) : Appendix.gammaBeta p₀ β lam k ≤ errorRate p₀ β lam := by
  by_cases hβ4 : β < 4
  · have hne := BadPointTypes.pStar_ne_top hβ4
    have hp : pBeta p₀ β = (pStar β).toNat := by unfold pBeta; rw [ite_eq_left hβ4]
    have hp1 := one_le_pBeta' hp₀ hβ
    have hkp : ¬ (k : ℕ∞) ≤ pStar β := by
      intro h
      have := ENat.toNat_le_toNat h hne
      simp only [ENat.toNat_natCast] at this
      omega
    have hR : truncationScale p₀ β lam ^ (-2 : ℤ) = lam ^ (2 * (β - 2) / (4 - β)) := by
      rw [Appendix.truncationScale_of_lt hβ4 hlam, ← Real.rpow_intCast, ← Real.rpow_mul hlam.le]
      congr 1
      push_cast
      ring
    have hT := tsum_transition_nonneg β lam
    rw [errorRate_of_lt_four' hβ hβ4 hlam]
    have hpos : 0 ≤ lam ^ (2 * (β - 2) / (4 - β)) := Real.rpow_nonneg hlam.le _
    unfold Appendix.gammaBeta
    rw [ite_eq_right hkp]
    split_ifs with h
    · rw [hR]
      have hq : 2 ≤ (pStar β).toNat + 1 := by omega
      rw [tsum_transition_eq hq h.2]
      nlinarith [abs_nonneg (Real.log lam)]
    · rw [hR]
      nlinarith
  · have hβ4' : 4 ≤ β := not_lt.1 hβ4
    have hp : pBeta p₀ β = p₀ := by unfold pBeta; rw [ite_eq_right hβ4]
    have hk1 : 1 ≤ k := by omega
    have hkp : (k : ℕ∞) ≤ pStar β := (Appendix.le_pStar_iff hk1).2 (by
      unfold transitionBeta
      have : (0 : ℝ) < 2 / (k : ℝ) := by
        have : (0 : ℝ) < k := by exact_mod_cast hk1
        positivity
      linarith)
    rw [UpperBound.AbsoluteUpper.gammaBeta_of_le_pStar hk1 hkp, errorRate_of_four_le hβ4']
    exact pow_le_pow_of_le_one hlam.le hlam1 (by omega)

/-! ### `δ_{β,λ} = o(λ^{2(p-1)})` -/

/-- **`δ_{β,λ} ≤ η λ^{2(p(β)-1)}` for `λ` small** (eq. (4.138)). -/
theorem exists_errorRate_le_mul_pow (hp₀ : 1 ≤ p₀) (hβ : 2 < β) {η : ℝ} (hη : 0 < η) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      errorRate p₀ β lam ≤ η * lam ^ (2 * (pBeta p₀ β - 1)) := by
  by_cases h4 : β < 4
  · set p := pBeta p₀ β
    have hp1 : 1 ≤ p := one_le_pBeta' hp₀ hβ
    have hlt := transitionBeta_pBeta_lt hp₀ hβ
    have h4' : 0 < 4 - β := by linarith
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    have hkey : (4 - β) * p < 2 := by
      unfold transitionBeta at hlt
      have : 4 - β < 2 / (p : ℝ) := by linarith
      rwa [lt_div_iff₀ hp0] at this
    set θ : ℝ := 2 * (β - 2) / (4 - β) - 2 * ((p : ℝ) - 1)
    have hθ : 0 < θ := by
      have : 2 * (β - 2) / (4 - β) - 2 * ((p : ℝ) - 1) = 2 * (2 - (4 - β) * p) / (4 - β) := by
        field_simp
        ring
      simp only [θ]
      rw [this]
      have : 0 < 2 - (4 - β) * p := by linarith
      positivity
    obtain ⟨x₀, hx₀, hx₀1, hx⟩ := exists_rpow_mul_log_le (half_pos hθ)
    -- `λ^{θ/2} ≤ η` for `λ < η^{2/θ}`
    set x₁ := η ^ (2 / θ) with hx₁
    have hx₁0 : 0 < x₁ := Real.rpow_pos_of_pos hη _
    refine ⟨min x₀ x₁, lt_min hx₀ hx₁0, (min_le_left _ _).trans hx₀1, fun lam hlam hlamx => ?_⟩
    rw [errorRate_of_lt_four' hβ h4 hlam]
    have hsplit : lam ^ (2 * (β - 2) / (4 - β)) =
        lam ^ (2 * (p - 1)) * (lam ^ (θ / 2) * lam ^ (θ / 2)) := by
      rw [← Real.rpow_add hlam, ← Real.rpow_natCast, ← Real.rpow_add hlam]
      congr 1
      simp only [θ]
      push_cast [Nat.cast_sub hp1]
      ring
    have h1 := hx lam hlam (hlamx.trans_le (min_le_left _ _))
    have h2 := TheoremTwo.tsum_transition_le β lam
    have h3 : lam ^ (θ / 2) ≤ η := by
      have hl : lam < x₁ := hlamx.trans_le (min_le_right _ _)
      calc lam ^ (θ / 2) ≤ x₁ ^ (θ / 2) :=
            Real.rpow_le_rpow hlam.le hl.le (by positivity)
        _ = η := by
            rw [hx₁, ← Real.rpow_mul hη.le]
            field_simp
            simp
    have hT := tsum_transition_nonneg β lam
    have h5 : lam ^ (θ / 2) * (1 + ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then
        |Real.log lam| else 0)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hlam.le _)) h1
    rw [hsplit]
    have hA : 0 ≤ lam ^ (2 * (p - 1)) := by positivity
    have hB : 0 ≤ lam ^ (θ / 2) := Real.rpow_nonneg hlam.le _
    calc lam ^ (2 * (p - 1)) * (lam ^ (θ / 2) * lam ^ (θ / 2)) *
          (1 + ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0))
        = lam ^ (2 * (p - 1)) * lam ^ (θ / 2) * (lam ^ (θ / 2) *
          (1 + ∑' q : ℕ, (if 2 ≤ q ∧ β = transitionBeta q then |Real.log lam| else 0))) := by
          ring
      _ ≤ lam ^ (2 * (p - 1)) * η * 1 := by gcongr
      _ = η * lam ^ (2 * (p - 1)) := by ring
  · refine ⟨min 1 η, lt_min one_pos hη, min_le_left _ _, fun lam hlam hlam1 => ?_⟩
    have hl1 : lam ≤ 1 := (hlam1.trans_le (min_le_left _ _)).le
    have hlη : lam ≤ η := (hlam1.trans_le (min_le_right _ _)).le
    rw [errorRate_of_four_le (not_lt.mp h4)]
    have hp : pBeta p₀ β = p₀ := by unfold pBeta; rw [ite_eq_right h4]
    rw [hp]
    have : 2 * p₀ = 2 * (p₀ - 1) + 2 := by omega
    rw [this, pow_add]
    have h2 : lam ^ 2 ≤ η := by nlinarith
    calc lam ^ (2 * (p₀ - 1)) * lam ^ 2 ≤ lam ^ (2 * (p₀ - 1)) * η :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = η * lam ^ (2 * (p₀ - 1)) := mul_comm _ _

/-! ### (4.38) for all block sizes -/

open UpperBound.AbsoluteUpper (zeroPartitionFunction_singleton sum_card_sub_one_add_card
  exists_lam_N_forall_le) in
/-- **Eq. (4.38) for `𝖬^0_{ε₀}` and all block sizes `1 ≤ |S| ≤ p(β)`** (Proposition 4.23, with `𝖬^0_{ε₀}({i}) = 1`): there is `C_m ≥ 1`, independent of `ε₀`, such
that for `λ` small and `N` large, `λ^{2(|S|-1)} / (C_m N^{|S|-1}) ≤ 𝖬^0_{ε₀}(S)`. -/
theorem exists_zero_lower {χ : ℂ → ℝ} (hχ : IsMollifier χ) (hβ : 2 < β) (hp₀ : 1 ≤ p₀) {M : ℝ}
    (hM : 20 < M) :
    ∃ Cm : ℝ, 1 ≤ Cm ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ S : Finset ℕ,
        1 ≤ S.card → S.card ≤ pBeta p₀ β →
          lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := by
  set p := pBeta p₀ β with hp
  have hC : ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ (2 ≤ s → s ≤ p → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 →
      ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ S : Finset ℕ, S.card = s →
          lam ^ (2 * (s - 1)) / (C * (N : ℝ) ^ (s - 1)) ≤
            zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) := by
    intro s
    by_cases hs : 2 ≤ s ∧ s ≤ p
    · obtain ⟨C, hC0, hCs⟩ := BoundedLowerEps.zeroPartitionFunction_two_sided hχ hβ hs.1
        (natCast_le_pStar_of_le_pBeta hp₀ hβ hs.2) hM
      refine ⟨C, hC0, fun _ _ ε₀ hε₀ hε₁ => ?_⟩
      obtain ⟨lam₀, hlam₀, -, hlam⟩ := hCs ε₀ hε₀ hε₁
      refine ⟨lam₀, hlam₀, fun lam hl hlt => ?_⟩
      obtain ⟨N₀, hN₀⟩ := hlam p₀ lam hl hlt
      exact ⟨N₀, fun N hN S hS => (hN₀ N hN S hS).1⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩
  choose C hC0 hCs using hC
  set Cm : ℝ := 1 + ∑ s ∈ range (p + 1), C s with hCm
  have hCm1 : 1 ≤ Cm := le_add_of_nonneg_right (sum_nonneg fun s _ => (hC0 s).le)
  have hCsm : ∀ s ≤ p, C s ≤ Cm := fun s hs => by
    have := single_le_sum (f := C) (fun s _ => (hC0 s).le) (mem_range.2 (Nat.lt_succ_of_le hs))
    linarith
  refine ⟨Cm, hCm1, fun ε₀ hε₀ hε₁ => ?_⟩
  obtain ⟨lam₀, hlam₀, hU⟩ := exists_lam_N_forall_le (P := fun s lam N => 2 ≤ s → s ≤ p →
    ∀ S : Finset ℕ, S.card = s → lam ^ (2 * (s - 1)) / (C s * (N : ℝ) ^ (s - 1)) ≤
      zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) p fun s _ => by
    by_cases hs : 2 ≤ s ∧ s ≤ p
    · obtain ⟨lam₀, hlam₀, h⟩ := hCs s hs.1 hs.2 ε₀ hε₀ hε₁
      exact ⟨lam₀, hlam₀, fun lam hl hlt => by
        obtain ⟨N₀, hN₀⟩ := h lam hl hlt
        exact ⟨N₀, fun N hN _ _ => hN₀ N hN⟩⟩
    · exact ⟨1, one_pos, fun lam _ _ => ⟨0, fun N _ h1 h2 => absurd ⟨h1, h2⟩ hs⟩⟩
  refine ⟨lam₀, hlam₀, fun lam hl hlt => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hU lam hl hlt
  refine ⟨max N₀ 1, fun N hN S hS1 hSp => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  rcases Nat.lt_or_ge S.card 2 with h1 | h2
  · have hS : S.card = 1 := by omega
    rw [zeroPartitionFunction_singleton hχ hl hε₀ hN1 hS, hS]
    simp only [Nat.sub_self, mul_zero, pow_zero, mul_one]
    exact (div_le_one (by linarith)).2 hCm1
  · have h := hN₀ N ((le_max_left _ _).trans hN) S.card hSp h2 hSp S rfl
    refine le_trans (div_le_div_of_nonneg_left (by positivity)
      (mul_pos (hC0 _) (by positivity)) ?_) h
    exact mul_le_mul_of_nonneg_right (hCsm _ hSp) (by positivity)

/-! ### From `|K(X)| ≤ A / (𝖬^0(X) N^{|V_X|-1})` to the multiplicative form -/

open UpperBound.AbsoluteUpper (sum_card_sub_one_add_card) in
/-- **The multiplicative form of a cluster bound** (eqs. (4.127)–(4.128)): if
`|K| ≤ A / (∏_{S ∈ X} m_S N^{|V_X|-1})`, `m_S ≥ λ^{2(|S|-1)} / (C_m N^{|S|-1})` and
`20^{|V_X|} A C_m^{|X|} ≤ C_l δ |X|^{|X|} (20θ)^{|V_X|}`, then
`|K| 20^{|V_X|} ≤ C_l N δ |X|^{|X|} ∏_{S ∈ X} (20θ)^{|S|} / (λ^{2(|S|-1)} N)`. -/
theorem abs_mul_le_of_zero_lower {X : Finset (Finset ℕ)} (hX : IsSubpartition X)
    (hX1 : 1 ≤ X.card) {K A Cm Cl δ θ lam : ℝ} {N : ℕ} (hN : 0 < (N : ℝ)) (hlam : 0 < lam)
    (hCm : 0 < Cm) (hA : 0 ≤ A) {m : Finset ℕ → ℝ}
    (hm : ∀ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤ m S)
    (hK : |K| ≤ A / ((∏ S ∈ X, m S) * (N : ℝ) ^ ((X.biUnion id).card - 1)))
    (hAC : 20 ^ (X.biUnion id).card * A * Cm ^ X.card ≤
      Cl * δ * ((X.card : ℝ) ^ X.card * (20 * θ) ^ (X.biUnion id).card)) :
    |K| * 20 ^ (X.biUnion id).card ≤ Cl * N * δ * ((X.card : ℝ) ^ X.card *
      ∏ S ∈ X, (20 * θ) ^ S.card / (lam ^ (2 * (S.card - 1)) * N)) := by
  set a := X.card
  set k := (X.biUnion id).card
  set s := ∑ S ∈ X, (S.card - 1) with hs
  have hsk : s + a = k := sum_card_sub_one_add_card hX
  have hQ : lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s) ≤ ∏ S ∈ X, m S := by
    calc lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s)
        = ∏ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) := by
          rw [prod_div_distrib, prod_mul_distrib, prod_const, prod_pow_eq_pow_sum,
            prod_pow_eq_pow_sum, hs, mul_sum]
      _ ≤ ∏ S ∈ X, m S := prod_le_prod₀ (fun S _ => by positivity) hm
  have hQ0 : 0 < lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s) := by positivity
  have hk1 : k - 1 = s + (a - 1) := by omega
  have hsumcard : ∑ S ∈ X, S.card = k := by
    show ∑ S ∈ X, S.card = (X.biUnion id).card
    rw [card_biUnion fun S hS T hT hST => hX.2 hS hT hST]
    rfl
  have hprod : ∏ S ∈ X, (20 * θ) ^ S.card / (lam ^ (2 * (S.card - 1)) * N) =
      (20 * θ) ^ k / (lam ^ (2 * s) * (N : ℝ) ^ a) := by
    rw [prod_div_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, prod_pow_eq_pow_sum,
      prod_const, hsumcard, hs, mul_sum]
  have hKb : |K| ≤ A * Cm ^ a / (lam ^ (2 * s) * (N : ℝ) ^ (a - 1)) := by
    calc |K| ≤ A / ((∏ S ∈ X, m S) * (N : ℝ) ^ (k - 1)) := hK
      _ ≤ A / (lam ^ (2 * s) / (Cm ^ a * (N : ℝ) ^ s) * (N : ℝ) ^ (k - 1)) := by
          refine div_le_div_of_nonneg_left hA (by positivity) ?_
          exact mul_le_mul_of_nonneg_right hQ (by positivity)
      _ = A * Cm ^ a / (lam ^ (2 * s) * (N : ℝ) ^ (a - 1)) := by
          rw [hk1, pow_add]
          field_simp
  have hNa : (N : ℝ) ^ a = N * (N : ℝ) ^ (a - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hprod]
  calc |K| * 20 ^ k ≤ A * Cm ^ a / (lam ^ (2 * s) * (N : ℝ) ^ (a - 1)) * 20 ^ k :=
        mul_le_mul_of_nonneg_right hKb (by positivity)
    _ = (20 ^ k * A * Cm ^ a) / (lam ^ (2 * s) * (N : ℝ) ^ (a - 1)) := by ring
    _ ≤ (Cl * δ * ((a : ℝ) ^ a * (20 * θ) ^ k)) / (lam ^ (2 * s) * (N : ℝ) ^ (a - 1)) :=
        div_le_div_of_nonneg_right hAC (by positivity)
    _ = Cl * N * δ * ((a : ℝ) ^ a * ((20 * θ) ^ k / (lam ^ (2 * s) * (N : ℝ) ^ a))) := by
        rw [hNa]
        field_simp

end AbsoluteLower

end MultipoleBKT

end
