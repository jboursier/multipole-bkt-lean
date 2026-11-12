/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.AbsoluteLower.Prop427Bounds
public import MultipoleBKT.LowerBound.AbsoluteLower.RouteProfiles.Weights
public import MultipoleBKT.UpperBound.AbsoluteUpper.Inputs

/-!
# Profile entropy and the three convergence regimes

Lemma 4.59,
(4.120), and proof of Proposition 4.27.

The bounded regime uses (4.40) and (4.38). The medium regime
uses (4.128), with its finitely many sizes absorbed into a constant
that may depend on the cutoff. The large regime uses the simplification of Lemma 4.57
and the integration and group summation, followed by (4.38) and
(4.127).

For each size profile, binomial counting, Stirling and convexity of
`x log x` are supplied by `RouteProfiles`. The ambient profile constraint
pays for half the cutoff power, leaving geometric decay in the total
label size. Erasing a prescribed block retains its exact weight. Only
at the end is its size bounded by `p(β)` to make the anchored norm small.
The transfer to other activities is in Section 4.18.
Both applications choose `q = max q₀ p(β)`, with `q₀` from (4.120), so that the bounded regime includes the size `q₀`.
-/

@[expose] public section

namespace MultipoleBKT

namespace AbsoluteLower

open MeasureTheory Finset Hierarchical
open UpperBound.AbsoluteUpper (jLarge simplifiedMajorant bigClusterTerm connectedTerm
  ProfileBound AbsoluteConvergenceTransfer)
open TheoremTwo (alphaExponent_pos)
open scoped ENNReal

variable {χ : ℂ → ℝ} {N p₀ : ℕ} {β lam M ε₀ C₀ C : ℝ}

/-- **Lemma 4.57's bound with Lemma 4.59 inserted**: from `|K| ≤ simplifiedMajorant` and
`treeSeries ≤ N λ^{(2-β)k} T'`, `|K| ≤ e^{Ck} T' / (𝖬^0_{ε₀}(X) N^{k-1})`, `k = |V_X| ≥ 1`. -/
theorem abs_le_of_simplifiedMajorant {X : Finset (Finset ℕ)} {K : ℝ} (hN : 0 < (N : ℝ))
    (hlam : 0 < lam) (hZ : 0 < zeroPartitionFunction χ N p₀ β lam M ε₀ X)
    (hk : 1 ≤ (X.biUnion id).card)
    (hK : ENNReal.ofReal |K| ≤ simplifiedMajorant χ N p₀ β lam M ε₀ C₀ C X) {T' : ℝ}
    (hT' : 0 ≤ T')
    (htree : treeSeries χ N p₀ β lam M ε₀ C₀ X ≤
      ENNReal.ofReal (N * (lam ^ ((2 - β) * (X.biUnion id).card) * T'))) :
    |K| ≤ Real.exp (C * (X.biUnion id).card) * T' /
      (zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ ((X.biUnion id).card - 1)) := by
  set k := (X.biUnion id).card with hkdef
  set Z := zeroPartitionFunction χ N p₀ β lam M ε₀ X with hZdef
  have hD : 0 < ((N : ℝ) * lam ^ (2 - β)) ^ k * Z := by positivity
  rw [simplifiedMajorant_eq, ← ENNReal.ofReal_div_of_pos hD] at hK
  have h1 := hK.trans (mul_le_mul_right htree _)
  rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
  refine h1.trans (le_of_eq ?_)
  have hpow : ((N : ℝ) * lam ^ (2 - β)) ^ k = (N : ℝ) * (N : ℝ) ^ (k - 1) *
      lam ^ ((2 - β) * k) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hlam.le, ← pow_succ']
    congr 2
    omega
  rw [hpow]
  have hl : 0 < lam ^ ((2 - β) * (k : ℝ)) := Real.rpow_pos_of_pos hlam _
  field_simp
  rw [hkdef]
  ring

/-- The arithmetic of the large clusters: with `θ = e^C B C_m ε₀^{2α}` and `C_l ≥ ε₀^{-2}`,
`20^k e^{Ck} B^k a! ε₀^{2αk-2} δ C_m^a ≤ C_l δ a^a (20θ)^k` for `a ≤ k`. -/
theorem large_arith {B Cm Cl δ α : ℝ} (hB : 0 ≤ B) (hCm : 1 ≤ Cm) (hε₀ : 0 < ε₀) (hδ : 0 ≤ δ)
    (hCl : 1 / ε₀ ^ 2 ≤ Cl) {a k : ℕ} (hak : a ≤ k) :
    20 ^ k * (Real.exp (C * k) * B ^ k * (a.factorial : ℝ) * ε₀ ^ (2 * α * k - 2) * δ) *
        Cm ^ a ≤
      Cl * δ * ((a : ℝ) ^ a * (20 * (Real.exp C * B * Cm * ε₀ ^ (2 * α))) ^ k) := by
  have hf : (a.factorial : ℝ) ≤ (a : ℝ) ^ a := by exact_mod_cast Nat.factorial_le_pow a
  have hCmk : Cm ^ a ≤ Cm ^ k := pow_le_pow_right₀ hCm hak
  have he : Real.exp (C * k) = Real.exp C ^ k := by rw [← Real.exp_nat_mul, mul_comm]
  have hε : ε₀ ^ (2 * α * k - 2) = (ε₀ ^ (2 * α)) ^ k / ε₀ ^ 2 := by
    rw [Real.rpow_sub hε₀, Real.rpow_mul_natCast hε₀.le, Real.rpow_two]
  rw [he, hε]
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hCl0 : 0 ≤ Cl := le_trans (by positivity) hCl
  have hE : 0 ≤ ε₀ ^ (2 * α) := Real.rpow_nonneg hε₀.le _
  calc 20 ^ k * (Real.exp C ^ k * B ^ k * (a.factorial : ℝ) * ((ε₀ ^ (2 * α)) ^ k / ε₀ ^ 2) * δ) *
        Cm ^ a
      ≤ 20 ^ k * (Real.exp C ^ k * B ^ k * (a : ℝ) ^ a * ((ε₀ ^ (2 * α)) ^ k / ε₀ ^ 2) * δ) *
        Cm ^ k := by gcongr
    _ = (1 / ε₀ ^ 2) * δ * ((a : ℝ) ^ a * (20 * (Real.exp C * B * Cm * ε₀ ^ (2 * α))) ^ k) := by
        simp only [mul_pow]
        field_simp
    _ ≤ Cl * δ * ((a : ℝ) ^ a * (20 * (Real.exp C * B * Cm * ε₀ ^ (2 * α))) ^ k) := by
        gcongr

open UpperBound.AbsoluteUpper (abs_le_of_gamma_bound gammaBeta_of_le_pStar bigClusterTerm_nonneg)
  in
open TheoremTwo (natCast_le_pStar_of_le_pBeta) in
/-- **Lemma 4.59 and Proposition 4.27 for an abstract activity, core form** (proofs of
Lemma 4.59 and Proposition 4.27, (4.120)): for `M > 20`, `B ≥ 1` and `q ≥ p(β)`,
if an activity `K` vanishes on families of at most one block, satisfies the large-cluster bound
`𝖬^0_{ε₀}(X) N^{|V_X|-1} |K(X)| ≤ B^{|V_X|} |X|! ε₀^{2α|V_X|-2} δ` for `|V_X| > q` (the output of
Lemmas 4.57 and 4.59) and the bounded-cluster estimate with constant `C_b` for `|V_X| ≤ q`, then
eqs. (4.55), (4.56) hold with `C' N δ`, the series of (4.56) converges and so does the full connected
series. The constants: `ε₁` depends on `χ, β, p₀, M, B`. The constant `C'` also depends on `ε₀`, `C_b`. -/
theorem absolute_core (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) {M : ℝ} (hM20 : 20 < M)
    {B : ℝ} (hB1 : 1 ≤ B) {q : ℕ} (hpq : pBeta p₀ β ≤ q) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ Cb : ℝ, 0 ≤ Cb →
      ∃ C' : ℝ, 0 < C' ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ π : Finset (Finset ℕ), IsSubpartition π → (∀ S ∈ π, S ⊆ Finset.range N) →
          (∀ S ∈ π, S.card ≤ pBeta p₀ β) → ProfileBound p₀ β lam ε₀ N π →
        ∀ K : Finset (Finset ℕ) → ℝ, (∀ X ⊆ π, X.card ≤ 1 → K X = 0) →
          (∀ X ⊆ π, 2 ≤ X.card → q < (X.biUnion id).card →
            zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ ((X.biUnion id).card - 1) *
                |K X| ≤
              B ^ (X.biUnion id).card * ((X.card.factorial : ℝ) *
                (ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) * errorRate p₀ β lam))) →
          (∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ q →
            |K X| ≤ Cb * Appendix.gammaBeta p₀ β lam (X.biUnion id).card /
              (zeroPartitionFunction χ N p₀ β lam M ε₀ X *
                (N : ℝ) ^ ((X.biUnion id).card - 1))) →
          (∑ X ∈ π.powerset.filter (fun X => pBeta p₀ β < (X.biUnion id).card), |K X| ≤
              C' * N * errorRate p₀ β lam) ∧
            Summable (connectedTerm K π) ∧ Summable (bigClusterTerm K π (pBeta p₀ β)) ∧
            ∑' n, bigClusterTerm K π (pBeta p₀ β) n ≤ C' * N * errorRate p₀ β lam := by
  obtain ⟨Cm, hCm1, hzero⟩ := exists_zero_lower hχ hβ hp₀ hM20
  have hCm0 : 0 < Cm := by linarith
  set p := pBeta p₀ β with hp
  set α := alphaExponent β with hαdef
  have hα : 0 < α := alphaExponent_pos β
  set B' := B * Cm with hB'
  have hB'1 : 1 ≤ B' := one_le_mul_of_one_le_of_one_le hB1 hCm1
  set H := RouteProfiles.entropyConstant p with hH
  have hH1 : 1 ≤ H := by
    have ht : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
    have hb := RouteProfiles.entropy_base_one_le p
    dsimp [H, RouteProfiles.entropyConstant]
    nlinarith
  set η := 1 / (2 * H * (20 * B')) with hη
  have hη0 : 0 < η := by positivity
  set ε₁ := min 1 (η ^ (1 / α)) with hε₁
  refine ⟨ε₁, lt_min one_pos (Real.rpow_pos_of_pos hη0 _), min_le_left _ _,
    fun ε₀ hε₀ hε₀₁ Cb hCb => ?_⟩
  have hε₀1 : ε₀ < 1 := hε₀₁.trans_le (min_le_left _ _)
  have hεα : ε₀ ^ α ≤ η := by
    have h1 : ε₀ ≤ η ^ (1 / α) := (hε₀₁.trans_le (min_le_right _ _)).le
    calc ε₀ ^ α ≤ (η ^ (1 / α)) ^ α := Real.rpow_le_rpow hε₀.le h1 hα.le
      _ = η := by rw [← Real.rpow_mul hη0.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  have hεη : ε₀ ^ (2 * α) ≤ ε₀ ^ α :=
    Real.rpow_le_rpow_of_exponent_ge hε₀ hε₀1.le (by linarith)
  set θ := B' * ε₀ ^ (2 * α) with hθ
  set z := 20 * B' * ε₀ ^ α with hz
  have hz0 : 0 ≤ z := by positivity
  have hθ0 : 0 < θ := by positivity
  have hzsmall : H * z ≤ 1 / 2 := by
    calc H * z ≤ H * (20 * B' * η) := by dsimp [z]; gcongr
      _ = 1 / 2 := by rw [hη]; field_simp
  have h20θ : 20 * θ ≤ 1 := by
    have htz : 20 * θ ≤ z := by
      calc 20 * θ = (20 * B') * ε₀ ^ (2 * α) := by rw [hθ]; ring
        _ ≤ (20 * B') * ε₀ ^ α := mul_le_mul_of_nonneg_left hεη (by positivity)
        _ = z := rfl
    have hh : z ≤ H * z := le_mul_of_one_le_left hz0 hH1
    linarith
  have hθ1 : θ ≤ 1 := by linarith
  -- the constants
  set Cl := max (1 / ε₀ ^ 2) (Cb * Cm ^ q / θ ^ q) with hCl
  have hCl0 : 0 < Cl := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set Cs := Cb * Cm ^ p with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  refine ⟨8 * Cl, by positivity, ?_⟩
  obtain ⟨lamZ, hlamZ, hZ⟩ := hzero ε₀ hε₀ hε₀1
  obtain ⟨lamδ, hlamδ, -, hδ⟩ := exists_errorRate_le_mul_pow hp₀ hβ
    (η := 1 / (4 * Real.exp 1 * Cl)) (by positivity)
  set lam₀ := min (min lamZ lamδ) (min 1 (1 / (2 * 20 ^ p * Cs + 1))) with hlam₀
  refine ⟨lam₀, lt_min (lt_min hlamZ hlamδ) (lt_min one_pos (by positivity)),
    (min_le_right _ _).trans (min_le_left _ _), fun lam hlam hlt => ?_⟩
  have hltZ : lam < lamZ := hlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hltδ : lam < lamδ := hlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hlam1 : lam ≤ 1 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlamC : lam ≤ 1 / (2 * 20 ^ p * Cs + 1) :=
    (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  obtain ⟨N₀, hN₀⟩ := hZ lam hlam hltZ
  refine ⟨max N₀ 1, fun N hN π hπ hπN hπp hprof K hK1 hbig hbdd => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  set δ := errorRate p₀ β lam with hδdef
  have hδ0 : 0 ≤ δ := (TheoremTwo.errorRate_pos hβ hlam).le
  set w : Finset ℕ → ℝ := fun S => (20 * θ) ^ S.card / (lam ^ (2 * (S.card - 1)) * N) with hw
  have hsubX : ∀ X ⊆ π, IsSubpartition X := fun X hX =>
    SmallIntegral.isSubpartition_of_subset hπ hX
  have hm : ∀ X ⊆ π, ∀ S ∈ X, lam ^ (2 * (S.card - 1)) / (Cm * (N : ℝ) ^ (S.card - 1)) ≤
      zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := fun X hX S hS =>
    hN₀ N ((le_max_left _ _).trans hN) S (hπ.1 S (hX hS)).card_pos (hπp S (hX hS))
  have hZX : ∀ X : Finset (Finset ℕ), zeroPartitionFunction χ N p₀ β lam M ε₀ X =
      ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} := fun X => by
    unfold zeroPartitionFunction
    exact prod_congr rfl fun S _ => (prod_singleton _ S).symm
  have hπcard : (π.card : ℝ) ≤ N := by
    have h1 : π.card ≤ (π.biUnion id).card :=
      card_le_card_biUnion (fun S hS T hT hST => hπ.2 hS hT hST) fun S hS => hπ.1 S hS
    have h2 : (π.biUnion id).card ≤ N := by
      have := card_le_card (biUnion_subset.2 hπN)
      rwa [card_range] at this
    exact_mod_cast h1.trans h2
  have hXk : ∀ X ⊆ π, X.card ≤ (X.biUnion id).card := fun X hX =>
    card_le_card_biUnion (fun S hS T hT hST => (hsubX X hX).2 hS hT hST)
      fun S hS => (hsubX X hX).1 S hS
  -- small clusters
  have hsmall : ∀ X ⊆ π, 2 ≤ X.card → (X.biUnion id).card ≤ p →
      |K X| ≤ Cs * (lam ^ 2 / N) ^ (X.card - 1) := by
    intro X hX h2 hkp
    have hk1 : 1 ≤ (X.biUnion id).card := by have := hXk X hX; omega
    have hb := hbdd X hX h2 (hkp.trans hpq)
    rw [gammaBeta_of_le_pStar hk1 (natCast_le_pStar_of_le_pBeta hp₀ hβ hkp), hZX X] at hb
    have h := abs_le_of_gamma_bound (hsubX X hX) (by omega) hNR hlam hCm0 hCb (hm X hX) hb
    refine h.trans ?_
    have hpow : Cm ^ X.card ≤ Cm ^ p := pow_le_pow_right₀ hCm1 ((hXk X hX).trans hkp)
    rw [hCs]
    gcongr
  -- large clusters
  have hlarge : ∀ X ⊆ π, 2 ≤ X.card → p < (X.biUnion id).card →
      |K X| * 20 ^ (X.biUnion id).card ≤ Cl * N * δ * ((X.card : ℝ) ^ X.card * ∏ S ∈ X, w S) := by
    intro X hX h2 hpk
    have hXs := hsubX X hX
    have hk1 : 1 ≤ (X.biUnion id).card := by omega
    have hXk' := hXk X hX
    have hZpos : 0 < ∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S} :=
      prod_pos fun S hS => lt_of_lt_of_le (by positivity) (hm X hX S hS)
    by_cases hkq : (X.biUnion id).card ≤ q
    · -- bounded clusters with `|V_X| > p(β)`
      have hb := hbdd X hX h2 hkq
      have hγ := gammaBeta_le_errorRate hp₀ hβ hlam hlam1 hpk
      rw [hZX X] at hb
      have hb' : |K X| ≤ Cb * δ / ((∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) *
          (N : ℝ) ^ ((X.biUnion id).card - 1)) :=
        hb.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hγ hCb) (by positivity))
      refine abs_mul_le_of_zero_lower hXs (by omega) hNR hlam hCm0 (by positivity) (hm X hX) hb'
        ?_
      -- `C_b C_m^{|X|} ≤ C_l θ^{|V_X|}`
      have hθk : θ ^ q ≤ θ ^ (X.biUnion id).card := pow_le_pow_of_le_one hθ0.le hθ1 hkq
      have hθq : 0 < θ ^ q := by positivity
      have hCmq : Cm ^ X.card ≤ Cm ^ q := pow_le_pow_right₀ hCm1 (hXk'.trans hkq)
      have hCl' : Cb * Cm ^ q ≤ Cl * θ ^ q := by
        rw [← div_le_iff₀ hθq]
        exact le_max_right _ _
      have hXX : (1 : ℝ) ≤ (X.card : ℝ) ^ X.card :=
        one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ X.card))
      have hkey : Cb * Cm ^ X.card ≤ Cl * θ ^ (X.biUnion id).card :=
        (mul_le_mul_of_nonneg_left hCmq hCb).trans (hCl'.trans
          (mul_le_mul_of_nonneg_left hθk hCl0.le))
      calc 20 ^ (X.biUnion id).card * (Cb * δ) * Cm ^ X.card
          = 20 ^ (X.biUnion id).card * δ * (Cb * Cm ^ X.card) := by ring
        _ ≤ 20 ^ (X.biUnion id).card * δ * (Cl * θ ^ (X.biUnion id).card) := by gcongr
        _ ≤ 20 ^ (X.biUnion id).card * δ * (Cl * θ ^ (X.biUnion id).card) *
            (X.card : ℝ) ^ X.card := le_mul_of_one_le_right (by positivity) hXX
        _ = Cl * δ * ((X.card : ℝ) ^ X.card * (20 * θ) ^ (X.biUnion id).card) := by ring
    · -- large clusters: the bound of Lemmas 4.57 and 4.59
      have hb := hbig X hX h2 (not_le.1 hkq)
      set T' := B ^ (X.biUnion id).card * ((X.card.factorial : ℝ) *
        (ε₀ ^ (2 * α * (X.biUnion id).card - 2) * δ)) with hT'
      have hK' : |K X| ≤ T' / ((∏ S ∈ X, zeroPartitionFunction χ N p₀ β lam M ε₀ {S}) *
          (N : ℝ) ^ ((X.biUnion id).card - 1)) := by
        rw [le_div_iff₀ (by positivity), ← hZX X, mul_comm]
        exact hb
      refine abs_mul_le_of_zero_lower hXs (by omega) hNR hlam hCm0 (by positivity) (hm X hX) hK'
        ?_
      have h := large_arith (C := 0) (ε₀ := ε₀) (B := B) (Cm := Cm) (Cl := Cl) (δ := δ) (α := α)
        (by linarith) hCm1 hε₀ hδ0 (le_max_left _ _) hXk'
      simp only [zero_mul, Real.exp_zero, one_mul] at h
      refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
      · rw [hT']
        ring
      · rw [hθ, hB']
  -- Fix each size profile before applying Stirling and entropy.
  let v : ℕ → ℝ := fun s => (20 * θ) ^ s / (lam ^ (2 * (s - 1)) * N)
  have hv : ∀ s, 0 ≤ v s := fun s => by dsimp [v]; positivity
  have hn : ∀ i : Fin p, (PropFiveFortyFive.blockCount p π i : ℝ) * v ((i : ℕ) + 1) ≤
      z ^ ((i : ℕ) + 1) := by
    intro i
    have hi : (i : ℕ) + 1 ≤ p := by omega
    have hcount : (PropFiveFortyFive.blockCount p π i : ℝ) ≤
        (N : ℝ) * ε₀ ^ (-α) * lam ^ (2 * (((i : ℕ) + 1) - 1)) := by
      by_cases hi0 : (i : ℕ) = 0
      · have hncard : (PropFiveFortyFive.blockCount p π i : ℝ) ≤ π.card := by
          exact_mod_cast PropFiveFortyFive.blockCount_le_card p π i
        have hnN := hncard.trans hπcard
        have he : 1 ≤ ε₀ ^ (-α) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε₀ hε₀1.le
          (by linarith)
        simpa only [hi0, Nat.add_sub_cancel, mul_zero, pow_zero, mul_one] using
          hnN.trans (le_mul_of_one_le_right hNR.le he)
      · have hn := hprof ((i : ℕ) + 1) (by omega) hi
        change ((π.filter fun S => S.card = (i : ℕ) + 1).card : ℝ) ≤ _
        dsimp [α]
        simpa only [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using hn
    have hh := RouteProfiles.cutoff_weight_le hε₀ hε₀1.le hα.le
      (show 0 ≤ 20 * B' by positivity) hlam hNR (show 1 ≤ (i : ℕ) + 1 by omega) hcount
    convert hh using 1; dsimp [v, θ, z]; congr 2; ring
  -- the anchored norm
  have hanch : ∀ S₀ ∈ π, 2 * 20 ^ p * Cs * lam ^ 2 + 4 * Real.exp 1 * (Cl * N * δ) * w S₀ ≤ 2 := by
    intro S₀ hS₀
    have hS1 : 1 ≤ S₀.card := (hπ.1 S₀ hS₀).card_pos
    have hSp := hπp S₀ hS₀
    have h1 : 2 * 20 ^ p * Cs * lam ^ 2 ≤ 1 := by
      have hl2 : lam ^ 2 ≤ lam := pow_le_of_le_one hlam.le hlam1 two_ne_zero
      have hpos : 0 < 2 * 20 ^ p * Cs + 1 := by positivity
      have h0 : (0 : ℝ) ≤ 2 * 20 ^ p * Cs := by positivity
      have h5 : (2 * 20 ^ p * Cs) * lam ≤ (2 * 20 ^ p * Cs) * (1 / (2 * 20 ^ p * Cs + 1)) :=
        mul_le_mul_of_nonneg_left hlamC h0
      have h3 : (2 * 20 ^ p * Cs) * (1 / (2 * 20 ^ p * Cs + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hpos]
        linarith
      exact (mul_le_mul_of_nonneg_left hl2 h0).trans (h5.trans h3)
    have hδl := hδ lam hlam hltδ
    have hlp : lam ^ (2 * (p - 1)) ≤ lam ^ (2 * (S₀.card - 1)) :=
      pow_le_pow_of_le_one hlam.le hlam1 (by omega)
    have hl0 : 0 < lam ^ (2 * (S₀.card - 1)) := by positivity
    have h20 : (20 * θ) ^ S₀.card ≤ 1 := pow_le_one₀ (by positivity) h20θ
    have h2 : Cl * N * δ * w S₀ ≤ 1 / (4 * Real.exp 1) := by
      simp only [hw]
      calc Cl * N * δ * ((20 * θ) ^ S₀.card / (lam ^ (2 * (S₀.card - 1)) * N))
          = Cl * δ * (20 * θ) ^ S₀.card / lam ^ (2 * (S₀.card - 1)) :=
            by simpa only [mul_assoc, mul_left_comm, mul_comm] using
              (RouteProfiles.prescribed_weight (D := Cl * δ) (t := 20 * θ)
                (lam := lam) (r := S₀.card) hNR.ne')
        _ ≤ Cl * δ * 1 / lam ^ (2 * (S₀.card - 1)) := by gcongr
        _ ≤ Cl * (1 / (4 * Real.exp 1 * Cl) * lam ^ (2 * (p - 1))) * 1 /
            lam ^ (2 * (S₀.card - 1)) := by gcongr
        _ ≤ Cl * (1 / (4 * Real.exp 1 * Cl) * lam ^ (2 * (S₀.card - 1))) * 1 /
            lam ^ (2 * (S₀.card - 1)) := by gcongr
        _ = 1 / (4 * Real.exp 1) := by
            field_simp
    have h4 : 4 * Real.exp 1 * (Cl * N * δ) * w S₀ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Real.exp 1)
      rw [mul_one_div, div_self (by positivity)] at this
      linarith
    linarith
  obtain ⟨hbb12, hroot⟩ := cvgentseries_of_bounds K p hπ hπp v hv hz0 hn hzsmall
    hNR hπcard hlam.le hlam1 hCs0 hCl0.le hδ0 hK1 hsmall hlarge
  obtain ⟨hbb1, hfull, hbb2⟩ := series_of_norm_bounds K p hπ hK1 hbb12
    (fun S hS => (hroot S hS).trans (hanch S hS))
  have hCNδ : 0 ≤ Cl * N * δ := by positivity
  refine ⟨hbb1.trans (by linarith), hfull, ?_, ?_⟩
  · classical
    refine Summable.of_nonneg_of_le (fun n => bigClusterTerm_nonneg K π p n) (fun n => ?_) hfull
    unfold bigClusterTerm
    refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ =>
      abs_nonneg _) (by positivity)
    intro X hX
    rw [mem_filter] at hX ⊢
    exact ⟨hX.1, hX.2.1⟩
  · classical
    refine le_trans (le_of_eq ?_) (hbb2.trans (le_of_eq (by ring)))
    rfl

/-- **Lemma 4.59 and Proposition 4.27 for an abstract activity** (the claim of the proof of
proof of Proposition 5.20, `MultipoleBKT.UpperBound.AbsoluteUpper.AbsoluteConvergenceTransfer`),
for every mollifier `χ`, `p₀ ≥ 1` and `β > 2`. -/
theorem absoluteConvergenceTransfer (hχ : IsMollifier χ) (hp₀ : 1 ≤ p₀) (hβ : 2 < β) :
    AbsoluteConvergenceTransfer χ p₀ β := by
  intro C₀ hC₀
  obtain ⟨M₀, hM₀, h459⟩ := lemma_4_59 hχ hβ hp₀ hC₀
  refine ⟨M₀, hM₀, fun M hM C hC => ?_⟩
  have hM20 : 20 < M := hM₀.trans_le hM
  obtain ⟨B, hB1, hB⟩ := h459 M hM
  set q := max (qZero p₀ β) (pBeta p₀ β) with hq
  obtain ⟨ε₁, hε₁, hε₁1, hcore⟩ := absolute_core hχ hp₀ hβ hM20 (B := Real.exp C * B)
    (one_le_mul_of_one_le_of_one_le (Real.one_le_exp hC) hB1) (q := q) (le_max_right _ _)
  refine ⟨ε₁, hε₁, hε₁1, q, fun ε₀ hε₀ hε₀₁ Cb hCb => ?_⟩
  have hε₀1 : ε₀ < 1 := hε₀₁.trans_le hε₁1
  obtain ⟨C', hC', lamc, hlamc, hlamc1, hcore'⟩ := hcore ε₀ hε₀ hε₀₁ Cb hCb
  refine ⟨C', hC', min lamc (min (ε₀ / 2) (ε₀ ^ 2)), lt_min hlamc (lt_min (by linarith)
    (by positivity)), (min_le_left _ _).trans hlamc1, fun lam hlam hlt => ?_⟩
  have hltc : lam < lamc := hlt.trans_le (min_le_left _ _)
  have hlam1 : lam ≤ 1 := (hltc.trans_le hlamc1).le
  have hlamε : lam ≤ ε₀ / 2 := (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlamε2 : lam ≤ ε₀ ^ 2 := (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hlh : lam ≤ ε₀ * truncationScale p₀ β lam := by
    have := BoundedLowerEps.two_mul_le_cutoff hβ hlam hlam1 hε₀ hlamε p₀
    linarith
  obtain ⟨N₀, hN₀⟩ := hcore' lam hlam hltc
  refine ⟨max N₀ 1, fun N hN π hπ hπN hπp hprof K hK1 hsimp hbdd => ?_⟩
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hbig : ∀ X ⊆ π, 2 ≤ X.card → q < (X.biUnion id).card →
      zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ ((X.biUnion id).card - 1) *
          |K X| ≤
        (Real.exp C * B) ^ (X.biUnion id).card * ((X.card.factorial : ℝ) *
          (ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) * errorRate p₀ β lam)) := by
    intro X hX h2 hqk
    -- the large clusters: Lemma 4.57's bound and Lemma 4.59
    have hXs := SmallIntegral.isSubpartition_of_subset hπ hX
    have hk1 : 1 ≤ (X.biUnion id).card := by
      have : X.card ≤ (X.biUnion id).card :=
        card_le_card_biUnion (fun S hS T hT hST => hXs.2 hS hT hST) fun S hS => hXs.1 S hS
      omega
    have hZ0 := UpperBound.AbsoluteUpper.zeroPartitionFunction_nonneg χ N p₀ β lam M ε₀ X
    have hR : 0 ≤ Real.exp C * B := by positivity
    rcases hZ0.eq_or_lt with hZ | hZpos
    · rw [← hZ, zero_mul, zero_mul]
      have : 0 ≤ ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) :=
        Real.rpow_nonneg hε₀.le _
      have := (TheoremTwo.errorRate_pos (p₀ := p₀) hβ hlam).le
      positivity
    have hq₀k : qZero p₀ β < (X.biUnion id).card :=
      lt_of_le_of_lt (le_max_left _ _) hqk
    have hthr : largeThreshold p₀ β < (X.biUnion id).card :=
      (largeThreshold_le_qZero p₀ β).trans_lt hq₀k
    have htree := hB ε₀ lam hε₀ hε₀1.le hlam hlh (fun _ => hlamε2) N X hXs
      (fun S hS => hπp S (hX hS)) hthr
    set T' := B ^ (X.biUnion id).card * (X.card.factorial : ℝ) *
      (ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) * errorRate p₀ β lam) with hT'
    have hT'0 : 0 ≤ T' := by
      have := (TheoremTwo.errorRate_pos (p₀ := p₀) hβ hlam).le
      have : 0 ≤ ε₀ ^ (2 * alphaExponent β * (X.biUnion id).card - 2) :=
        Real.rpow_nonneg hε₀.le _
      positivity
    have htree' : treeSeries χ N p₀ β lam M ε₀ C₀ X ≤
        ENNReal.ofReal (N * (lam ^ ((2 - β) * (X.biUnion id).card) * T')) :=
      htree.trans (le_of_eq (congrArg ENNReal.ofReal (by rw [hT']; ring)))
    have hK' := abs_le_of_simplifiedMajorant (C := C) hNR hlam hZpos hk1 (hsimp X hX h2) hT'0 htree'
    rw [le_div_iff₀ (by positivity)] at hK'
    calc zeroPartitionFunction χ N p₀ β lam M ε₀ X * (N : ℝ) ^ ((X.biUnion id).card - 1) * |K X|
        = |K X| * (zeroPartitionFunction χ N p₀ β lam M ε₀ X *
            (N : ℝ) ^ ((X.biUnion id).card - 1)) := by ring
      _ ≤ Real.exp (C * (X.biUnion id).card) * T' := hK'
      _ = _ := by
          rw [hT', mul_pow, ← Real.exp_nat_mul, mul_comm ((X.biUnion id).card : ℝ) C]
          ring

  obtain ⟨h1, -, h3, h4⟩ := hN₀ N ((le_max_left _ _).trans hN) π hπ hπN hπp hprof K hK1 hbig hbdd
  exact ⟨h1, h3, h4⟩

end AbsoluteLower

end MultipoleBKT

end
