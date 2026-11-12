/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.SimplifiedUpper.ExpIntegral
public import MultipoleBKT.UpperBound.SimplifiedUpper.GroupBound

/-!
# The pointwise bound of the reduced sum (Lemmas 5.35–5.36)

The paper: Lemma 5.35 and Lemma 5.36. On the support of `𝖯^{+,ε₀,Z}_X` (all dipoles of `V_X` good,
of length in `(0, ε₀ R̄]`, and every block linked), for disjoint groups `X₁, …, Xₙ ⊆ X` of at least
two blocks and `U ⊆ V_X`,
`parAbsSum ≤ (2 C₂² C_out)^{|V_X|} ∏_{i ∈ V_X} (ε₀ R̄ / r_i)^{C₀/M} Λ(X)
  ∑_{T^b ∈ 𝖳_0^{Coarse_X(X₁, …, Xₙ)}} ∏_{T^b} b^abs ∏ₗ 𝒰(Xₗ)`
(`parAbsSum_le`), where `𝒰(Xₗ) = innerSeries(Xₗ)` is the series of Lemma 5.36 and
`C₀ = 2 C₁ C_p + 1` depends only on `χ`, `β` and `p(β)`:

* the reversal parity of the marks splits along the groups (`mem_markEulerPairs_of_parity`).
* each group is bounded by `outerGroup_le` (Lemmas 5.35–5.36 with Lemma 4.56), with
  `a = |a^{v^Z} 𝟙_{𝓑^c}|`, `B = b^{v^Z} 𝟙_{𝓑^c}` (eq. (5.73)), `m = |sinh(β S)|`
  (eq. (5.72)) and `δ = d_{bad}` (eq. (5.9), Lemma 5.32).
* the tree term `∑_F ∏_F (-𝟙_𝓑)` is bounded by the `b^abs`-trees (`abs_sum_negLinked_le`), and the
  remaining external factors by `C₂`.

The group bound retains `Λ(Y)`. In `parAbsSum_le`, its factors are combined over
the disjoint outer groups together with the radial powers. The paper-range block
sizes, positive radii and separation are supplied before each use of the reattachment
count. No logarithm is dropped at this stage.
-/

@[expose] public section

open MeasureTheory Finset

namespace MultipoleBKT

namespace UpperBound

namespace SimplifiedUpper

open Hierarchical Multipole SetPartition AbsoluteLower Parity BoundedUpper

/-! ### Combinatorics of the parity condition -/

section Parity

open scoped Classical

/-- **The parity of the marks splits along the groups**: for disjoint groups `Xₗ ⊆ X` and odd edge
sets `E₁ₗ ⊆ ℰ^inter(Xₗ)`, if `∑ₗ deg_{E₁ₗ}(S) + |S ∩ U₁|` is even for every `S ∈ X`, then
`E₁ₗ ∈ Eul^{Xₗ}(U₁)` for every `l`. -/
theorem mem_markEulerPairs_of_parity {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) {E₁s : Fin n → Finset (ℕ × ℕ)}
    (hE₁s : ∀ l, E₁s l ⊆ interPairs (Xs l)) {U₁ : Finset ℕ}
    (hpar : ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card)) (l : Fin n) :
    E₁s l ∈ markEulerPairs (Xs l) U₁ := by
  refine mem_markEulerPairs.2 ⟨hE₁s l, fun S hS => ?_⟩
  have h0 : ∀ l' ∈ (univ : Finset (Fin n)), l' ≠ l → blockDeg (E₁s l') S = 0 := by
    intro l' _ hl'
    refine blockDeg_eq_zero fun p hp => ?_
    have hpV := interPairs_subset_pairsOn_biUnion _ (hE₁s l' hp)
    have hd := Hierarchical.disjoint_biUnion_of_disjoint hX (hXs l') (hXs l) (hdisj l' l hl')
    have hSV : S ⊆ (Xs l).biUnion id := subset_biUnion_of_mem id hS
    exact ⟨fun h => Finset.disjoint_left.1 hd hpV.1 (hSV h),
      fun h => Finset.disjoint_left.1 hd hpV.2 (hSV h)⟩
  have := hpar S (hXs l hS)
  rwa [sum_eq_single_of_mem l (mem_univ l) h0] at this

end Parity

/-! ### One group -/

section Group

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ}

theorem evenBondUnlinked_nonneg (hM : 1 ≤ M) (d e : ℂ × ℂ) :
    0 ≤ evenBondUnlinked β w M lam d e := by
  by_cases h : MultipoleLinked M lam d e
  · rw [evenBondUnlinked_of_linked h]
  · rw [evenBondUnlinked_of_not_linked hM h]
    have h1 := Real.add_one_le_exp (β * w d e)
    have h2 := Real.add_one_le_exp (-(β * w d e))
    rw [Real.cosh_eq]
    linarith

/-- `|𝒰-term| ≤ ∏_{E₁} |a| ∑_{E₂} ∏_{E₂} b`. -/
theorem abs_groupTerm_le (hM : 1 ≤ M) (Y : Finset (Finset ℕ)) (E₁ : Finset (ℕ × ℕ))
    (c : ℕ → ℂ × ℂ) :
    |groupTerm β w M lam Y E₁ c| ≤
      (∏ q ∈ E₁, |oddBondUnlinked β w M lam (c q.1) (c q.2)|) *
        ∑ E₂ ∈ (interPairs Y).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets Y),
          ∏ q ∈ E₂, evenBondUnlinked β w M lam (c q.1) (c q.2) := by
  unfold groupTerm evenSum
  have hS0 : 0 ≤ ∑ E₂ ∈ (interPairs Y).powerset.filter
      (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets Y),
      ∏ q ∈ E₂, evenBondUnlinked β w M lam (c q.1) (c q.2) :=
    sum_nonneg fun _ _ => prod_nonneg fun _ _ => evenBondUnlinked_nonneg hM _ _
  have hI : |∏ q ∈ interPairs Y, (if MultipoleLinked M lam (c q.1) (c q.2) then (0 : ℝ) else 1)|
      ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ => abs_nonneg _) fun q _ => by split_ifs <;> norm_num
  rw [abs_mul, abs_mul, abs_prod, abs_of_nonneg hS0]
  calc (∏ q ∈ E₁, |oddBondUnlinked β w M lam (c q.1) (c q.2)|) *
        ((∑ E₂ ∈ (interPairs Y).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets Y),
          ∏ q ∈ E₂, evenBondUnlinked β w M lam (c q.1) (c q.2)) *
        |∏ q ∈ interPairs Y, (if MultipoleLinked M lam (c q.1) (c q.2) then (0 : ℝ) else 1)|)
      ≤ (∏ q ∈ E₁, |oddBondUnlinked β w M lam (c q.1) (c q.2)|) *
        ((∑ E₂ ∈ (interPairs Y).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets Y),
          ∏ q ∈ E₂, evenBondUnlinked β w M lam (c q.1) (c q.2)) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI hS0)
          (prod_nonneg fun _ _ => abs_nonneg _)
    _ = _ := by rw [mul_one]

theorem groupTerm_eq_zero_of_linked {Y : Finset (Finset ℕ)} (E₁ : Finset (ℕ × ℕ))
    {c : ℕ → ℂ × ℂ} {q : ℕ × ℕ} (hq : q ∈ interPairs Y)
    (hL : MultipoleLinked M lam (c q.1) (c q.2)) : groupTerm β w M lam Y E₁ c = 0 := by
  have h0 : ∏ q' ∈ interPairs Y,
      (if MultipoleLinked M lam (c q'.1) (c q'.2) then (0 : ℝ) else 1) = 0 :=
    prod_eq_zero hq (ite_eq_left hL)
  unfold groupTerm evenSum
  rw [h0, mul_zero, mul_zero]

/-- Inter-block pairs are unlinked if the pairs of `ℰ^inter(Y)` are. -/
theorem not_linked_of_forall_interPairs {Y : Finset (Finset ℕ)} (hY : IsSubpartition Y)
    {c : ℕ → ℂ × ℂ} (hL : ∀ q ∈ interPairs Y, ¬ MultipoleLinked M lam (c q.1) (c q.2))
    {i j : ℕ} (hi : i ∈ Y.biUnion id) (hj : j ∈ Y.biUnion id) (hij : ¬ SameBlock Y i j) :
    ¬ MultipoleLinked M lam (c i) (c j) := by
  obtain ⟨B, hB, hiB⟩ := mem_biUnion_id.1 hi
  obtain ⟨B', hB', hjB'⟩ := mem_biUnion_id.1 hj
  have hBB' : B ≠ B' := fun h => hij ⟨B, hB, hiB, h ▸ hjB'⟩
  rcases lt_trichotomy i j with h | rfl | h
  · exact hL (i, j) (mem_interPairs_of hY hB hB' hBB' hiB hjB' h)
  · exact absurd ⟨B, hB, hiB, hiB⟩ hij
  · intro hl
    exact hL (j, i) (mem_interPairs_of hY hB' hB hBB'.symm hjB' hiB h)
      (Multipole.multipoleLinked_comm.1 hl)

end Group

/-! ### The bound on the support -/

section Bound

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}

/-- The comparison constant `K = max(6, (M + 2)^p)` of the bad distances. -/
noncomputable def compConst (M : ℝ) (p : ℕ) : ℝ := max 6 ((M + 2) ^ p)

theorem one_le_compConst (M : ℝ) (p : ℕ) : 1 ≤ compConst M p :=
  le_trans (by norm_num) (le_max_left _ _)

open scoped Classical in
/-- **One outer group on the support** (Lemmas 5.35–5.36): with `a = |a^{v^Z} 𝟙_{𝓑^c}|`,
`m = |sinh(β S)|`,
`∑_{E₁ ∈ Eul^Y(U₁)} |𝒰-term(E₁)| ∏_{i ∈ U₁ ∩ V_Y} m_i
≤ C_out^{|V_Y|} ∏_{V_Y} (ε₀R̄/r_i)^{C₀/M} Λ(Y) 𝒰(Y)`. -/
theorem groupSum_abs_le (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ Q : ℝ, 1 ≤ Q ∧ ∃ Cp : ℝ, 0 < Cp ∧ ∀ {M : ℝ}, 20 < M →
      (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ {N : ℕ} (lam ε₀ : ℝ) (V : Finset (Fin N))
      (Z : Fin N → ℂ × ℂ), 0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ {Y : Finset (Finset ℕ)}, IsSubpartition Y →
      (∀ S ∈ Y, S.card ≤ pBeta p₀ β) → ∀ (U₁ : Finset ℕ) (c : ℕ → ℂ × ℂ),
      (∀ i ∈ Y.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) ∧ 0 < ‖(c i).1 - (c i).2‖) →
      (∀ S ∈ Y, ConnOn S (linkedPairs M lam c S)) →
      ∑ E₁ ∈ markEulerPairs Y U₁,
          |groupTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Y E₁ c| *
            ∏ i ∈ U₁ ∩ Y.biUnion id, |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| ≤
        outerConst Cp Q M C₁ C₂ (compConst M (pBeta p₀ β)) ^ (Y.biUnion id).card *
          (∏ i ∈ Y.biUnion id, (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^
            ((2 * C₁ * Cp + 1) / M) *
              (1 + Real.logb M (17 * ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖)) ^ 2) *
          innerSeries M lam ε₀ (truncationScale p₀ β lam) c Y := by
  obtain ⟨C₁, hC₁, hab⟩ := bornesabZ_Z hχ β
  obtain ⟨C₂, hC₂, hinf⟩ := bornesabinfty_Z hχ p₀ β
  obtain ⟨Q, hQ, Cp, hCp, hout⟩ := outerGroup_le (pBeta p₀ β) hC₁
  refine ⟨C₁, hC₁, C₂, hC₂, Q, hQ, Cp, hCp, fun {M} hM hMp {N} lam ε₀ V Z hlam hlamh hVZ {Y} hY hYp U₁ c
    hc hconn => ?_⟩
  set R := truncationScale p₀ β lam with hR
  set K := compConst M (pBeta p₀ β) with hK
  have hM1 : 1 ≤ M := by linarith
  have hM3 : 3 ≤ M := by linarith
  have hRHS0 : 0 ≤ outerConst Cp Q M C₁ C₂ K ^ (Y.biUnion id).card *
      (∏ i ∈ Y.biUnion id, (ε₀ * R / ‖(c i).1 - (c i).2‖) ^ ((2 * C₁ * Cp + 1) / M) *
              (1 + Real.logb M (17 * ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖)) ^ 2) *
      innerSeries M lam ε₀ R c Y := by
    refine mul_nonneg (mul_nonneg (pow_nonneg ?_ _) (prod_nonneg fun i hi => ?_))
      (innerSeries_nonneg _ _ _ _ _ _)
    · unfold outerConst
      have := one_le_compConst M (pBeta p₀ β)
      positivity
    · have hr := (hc i hi).2
      have hle := (hc i hi).1.norm_le
      exact mul_nonneg (Real.rpow_nonneg (div_nonneg (hr.le.trans hle) hr.le) _) (sq_nonneg _)
  -- a linked inter-block pair kills every term
  by_cases hL : ∀ q ∈ interPairs Y, ¬ MultipoleLinked M lam (c q.1) (c q.2)
  swap
  · push Not at hL
    obtain ⟨q, hq, hql⟩ := hL
    rw [sum_eq_zero fun E₁ _ => by rw [groupTerm_eq_zero_of_linked E₁ hq hql, abs_zero, zero_mul]]
    exact hRHS0
  -- the hypotheses of `outerGroup_le`
  set a : ℕ → ℕ → ℝ := fun i j =>
    |oddBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c i) (c j)| with ha
  set B : ℕ × ℕ → ℝ := fun q =>
    evenBondUnlinked β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (c q.1) (c q.2) with hB
  set m : ℕ → ℝ := fun i => |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z (c i))| with hm
  set δ : ℕ → ℝ := fun i => badDistZ p₀ β lam ε₀ V Z (c i) with hδ
  have hsupp : ∀ i ∈ Y.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) := fun i hi => (hc i hi).1
  have hKS : ∀ S ∈ Y, ∀ i ∈ S, ∀ j ∈ S, δ j ≤ K * δ i := by
    intro S hS i hi j hj
    have hSV : S ⊆ Y.biUnion id := subset_biUnion_of_mem id hS
    have h1 := badDistZ_le_of_connOn hlam hlamh hMp hVZ (fun k hk => hsupp k (hSV hk))
      (hconn S hS) hi hj
    have hδ0 : 0 ≤ δ i := (hlam.trans_le (lam_le_badDistZ hlam hlamh hMp hVZ (hsupp i (hSV hi)).2
      (hsupp i (hSV hi)).norm_le)).le
    have h2 : (M + 2) ^ S.card ≤ K :=
      (pow_le_pow_right₀ (by linarith) (hYp S hS)).trans (le_max_right _ _)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hδ0)
  have hKE : ∀ i ∈ Y.biUnion id, ∀ j ∈ Y.biUnion id, a i j ≠ 0 → δ j ≤ K * δ i := by
    intro i hi j _ hne
    have hv : interactionGoodZ χ p₀ β lam ε₀ V Z (c i) (c j) ≠ 0 :=
      interactionGoodZ_ne_zero_of_oddBond (M := M) (c i) (c j) fun h0 => hne (by
        simp only [ha, h0, abs_zero])
    have h1 := badDistZ_le_six_mul hχ hlam hlamh hMp hVZ (hsupp i hi).2 (hsupp i hi).norm_le hv
    have hδ0 : 0 ≤ δ i := (hlam.trans_le (lam_le_badDistZ hlam hlamh hMp hVZ (hsupp i hi).2
      (hsupp i hi).norm_le)).le
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0)
  have hmain := hout hM hC₂ (one_le_compConst M (pBeta p₀ β)) lam ε₀ R hlam hY hYp U₁ c
    (fun i hi => ⟨(hc i hi).2, (hc i hi).1.norm_le⟩)
    (fun i hi j hj hij => not_linked_of_forall_interPairs hY hL hi hj hij)
    a (fun i j => abs_nonneg _) (fun i j => abs_oddBondUnlinked_comm hχ hM1 (c i) (c j))
    (fun i hi j hj => (hab p₀ lam M ε₀ V Z hlam hlamh hMp hVZ (c i) (c j) (hsupp i hi)
      (hsupp j hj)).1)
    B (fun q _ => evenBondUnlinked_nonneg hM1 _ _)
    (fun q hq => by
      have hq' := interPairs_subset_pairsOn_biUnion _ hq
      have h2 := (hab p₀ lam M ε₀ V Z hlam hlamh hMp hVZ (c q.1) (c q.2) (hsupp _ hq'.1)
        (hsupp _ hq'.2)).2
      unfold evenBondMult at h2
      rw [ite_eq_right (hL q hq), sub_zero] at h2
      exact (le_abs_self _).trans h2)
    m δ (fun i => abs_nonneg _)
    (fun i hi => (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ (c i)
      (hsupp i (mem_inter.1 hi).2)).1)
    (fun i hi => hlam.trans_le (lam_le_badDistZ hlam hlamh hMp hVZ (hsupp i hi).2
      (hsupp i hi).norm_le))
    (fun i hi => norm_le_badDistZ hlam hlamh hMp hVZ (hsupp i hi).2 (hsupp i hi).norm_le)
    hKE hKS
  refine le_trans (sum_le_sum fun E₁ _ => ?_) (hmain.trans_eq (by
    rw [prod_mul_distrib, logProduct]
    ring))
  have hm0 : 0 ≤ ∏ i ∈ U₁ ∩ Y.biUnion id, m i := prod_nonneg fun _ _ => abs_nonneg _
  calc |groupTerm β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam Y E₁ c| *
        ∏ i ∈ U₁ ∩ Y.biUnion id, m i
      ≤ ((∏ q ∈ E₁, a q.1 q.2) * ∑ E₂ ∈ (interPairs Y).powerset.filter
          (fun E₂ => Disjoint E₁ E₂ ∧ E₁ ∪ E₂ ∈ relEdgeSets Y), ∏ q ∈ E₂, B q) *
          ∏ i ∈ U₁ ∩ Y.biUnion id, m i :=
        mul_le_mul_of_nonneg_right (abs_groupTerm_le hM1 Y E₁ c) hm0
    _ = _ := by ring

/-- `max (outerConst …) 1`. -/
noncomputable def outerConst' (Cp Q M C₁ C₂ K : ℝ) : ℝ := max (outerConst Cp Q M C₁ C₂ K) 1

end Bound

/-! ### Splitting the reduced sum along the groups -/

section Split

open scoped Classical

variable {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}

theorem abs_expTerm_eq (X : Finset (Finset ℕ)) {n : ℕ} (Xs : Fin n → Finset (Finset ℕ))
    (U U₁ : Finset ℕ) (E₁s : Fin n → Finset (ℕ × ℕ)) (c : ℕ → ℂ × ℂ) :
    |expTerm β w M lam s X Xs U U₁ E₁s c| =
      (∏ l, |groupTerm β w M lam (Xs l) (E₁s l) c|) *
        (|treeF M lam (coarsen X (univ.image Xs)) c| * (∏ i ∈ U₁, |Real.sinh (β * s (c i))|) *
          ∏ i ∈ U \ U₁, |Real.cosh (β * s (c i)) - 1|) := by
  unfold expTerm
  simp only [abs_mul, abs_prod, abs_neg]
  ring

/-- The product over the marks splits along the groups. -/
theorem prod_marks_split {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (U₁ : Finset ℕ) (f : ℕ → ℝ) :
    ∏ i ∈ U₁, f i = (∏ l, ∏ i ∈ U₁ ∩ (Xs l).biUnion id, f i) *
      ∏ i ∈ U₁ \ univ.biUnion (fun l => (Xs l).biUnion id), f i := by
  rw [← prod_inter_mul_prod_sdiff U₁ (univ.biUnion fun l => (Xs l).biUnion id) f, inter_biUnion,
    prod_biUnion]
  intro i _ j _ hij
  exact Finset.disjoint_of_subset_left inter_subset_right
    (Finset.disjoint_of_subset_right inter_subset_right
      (Hierarchical.disjoint_biUnion_of_disjoint hX (hXs i) (hXs j) (hdisj i j hij)))

/-- **The reduced sum for fixed marks, split along the groups.** -/
theorem sum_parity_le {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ}
    {Xs : Fin n → Finset (Finset ℕ)} (hXs : ∀ l, Xs l ⊆ X)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) (U U₁ : Finset ℕ) (c : ℕ → ℂ × ℂ) :
    ∑ E₁s ∈ (Fintype.piFinset fun l => (interPairs (Xs l)).powerset).filter
        (fun E₁s => ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card)),
      |expTerm β w M lam s X Xs U U₁ E₁s c| ≤
    (∏ l, ((∑ E₁ ∈ markEulerPairs (Xs l) U₁, |groupTerm β w M lam (Xs l) E₁ c|) *
        ∏ i ∈ U₁ ∩ (Xs l).biUnion id, |Real.sinh (β * s (c i))|)) *
      |treeF M lam (coarsen X (univ.image Xs)) c| *
      (∏ i ∈ U₁ \ univ.biUnion (fun l => (Xs l).biUnion id), |Real.sinh (β * s (c i))|) *
      ∏ i ∈ U \ U₁, |Real.cosh (β * s (c i)) - 1| := by
  have hsub : (Fintype.piFinset fun l => (interPairs (Xs l)).powerset).filter
      (fun E₁s => ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card)) ⊆
      Fintype.piFinset fun l => markEulerPairs (Xs l) U₁ := by
    intro E₁s hE₁s
    obtain ⟨hE, hpar⟩ := mem_filter.1 hE₁s
    exact Fintype.mem_piFinset.2 fun l => mem_markEulerPairs_of_parity hX hXs hdisj
      (fun l => mem_powerset.1 (Fintype.mem_piFinset.1 hE l)) hpar l
  refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _).trans (le_of_eq ?_)
  simp_rw [abs_expTerm_eq]
  have hfac : ∑ E₁s ∈ Fintype.piFinset (fun l => markEulerPairs (Xs l) U₁),
      ∏ l, |groupTerm β w M lam (Xs l) (E₁s l) c| =
      ∏ l, ∑ E₁ ∈ markEulerPairs (Xs l) U₁, |groupTerm β w M lam (Xs l) E₁ c| :=
    (prod_univ_sum (fun l => markEulerPairs (Xs l) U₁)
      (fun l E₁ => |groupTerm β w M lam (Xs l) E₁ c|)).symm
  rw [← sum_mul, hfac, prod_marks_split hX hXs hdisj U₁, prod_mul_distrib]
  ring

theorem prod_le_pow_of_le' {ι : Type*} (s : Finset ι) {f : ι → ℝ} {C : ℝ} (hC : 1 ≤ C) {k : ℕ}
    (hk : s.card ≤ k) (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ C) : ∏ i ∈ s, f i ≤ C ^ k := by
  refine (prod_le_prod₀ h0 h).trans ?_
  rw [prod_const]
  exact pow_le_pow_right₀ hC hk

/-- An abstract product bound: `∏ₗ Aₗ ≤ m^k ∏_{W} rad ∏ₗ Iₗ` from
`Aₗ ≤ o^{|Vₗ|} ∏_{Vₗ} rad Iₗ`, for disjoint `Vₗ ⊆ W`, `rad ≥ 1` on `W`, `o ≤ m`, `1 ≤ m` and
`∑ₗ |Vₗ| ≤ k`. -/
theorem prod_group_bounds_le {n : ℕ} (Vl : Fin n → Finset ℕ) {W : Finset ℕ}
    (hVd : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint Vl) (hVlW : ∀ l, Vl l ⊆ W)
    {rad : ℕ → ℝ} (hrad1 : ∀ i ∈ W, 1 ≤ rad i) {o m : ℝ} (ho0 : 0 ≤ o) (hom : o ≤ m)
    (hm1 : 1 ≤ m) {k : ℕ} (hk : ∑ l, (Vl l).card ≤ k) (A I : Fin n → ℝ) (hA0 : ∀ l, 0 ≤ A l)
    (hI0 : ∀ l, 0 ≤ I l) (hA : ∀ l, A l ≤ o ^ (Vl l).card * (∏ i ∈ Vl l, rad i) * I l) :
    ∏ l, A l ≤ m ^ k * (∏ i ∈ W, rad i) * ∏ l, I l := by
  have hV'W : univ.biUnion Vl ⊆ W := biUnion_subset.2 fun l _ => hVlW l
  have hrad0 : ∀ l, 0 ≤ ∏ i ∈ Vl l, rad i := fun l =>
    prod_nonneg fun i hi => zero_le_one.trans (hrad1 i (hVlW l hi))
  refine (prod_le_prod₀ (fun l _ => hA0 l) fun l _ => hA l).trans ?_
  rw [prod_mul_distrib, prod_mul_distrib]
  have hO : ∏ l, o ^ (Vl l).card ≤ m ^ k := by
    calc ∏ l, o ^ (Vl l).card ≤ ∏ l, m ^ (Vl l).card :=
          prod_le_prod₀ (fun l _ => pow_nonneg ho0 _) fun l _ => pow_le_pow_left₀ ho0 hom _
      _ = m ^ ∑ l, (Vl l).card := by rw [prod_pow_eq_pow_sum]
      _ ≤ m ^ k := pow_le_pow_right₀ hm1 hk
  have hRad : ∏ l, ∏ i ∈ Vl l, rad i ≤ ∏ i ∈ W, rad i := by
    rw [← prod_biUnion hVd, ← prod_sdiff hV'W]
    have h1 : 1 ≤ ∏ i ∈ W \ univ.biUnion Vl, rad i := by
      calc (1 : ℝ) = ∏ _i ∈ W \ univ.biUnion Vl, (1 : ℝ) := prod_const_one.symm
        _ ≤ ∏ i ∈ W \ univ.biUnion Vl, rad i :=
          prod_le_prod₀ (fun _ _ => zero_le_one) fun i hi => hrad1 i (mem_sdiff.1 hi).1
    have h0 : 0 ≤ ∏ i ∈ univ.biUnion Vl, rad i :=
      prod_nonneg fun i hi => zero_le_one.trans (hrad1 i (hV'W hi))
    nlinarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul hO hRad (prod_nonneg fun l _ => hrad0 l)
    (pow_nonneg (by linarith) _)) (prod_nonneg fun l _ => hI0 l)

end Split

/-! ### The pointwise bound -/

section Main

variable {N : ℕ} {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}

/-- The external factors on the support: `|sinh(β S)| ≤ C₃` and `|cosh(β S) - 1| ≤ C₃`. -/
theorem abs_sinh_cosh_le_const (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) :
    ∃ C₃ : ℝ, 1 ≤ C₃ ∧ ∀ {M : ℝ}, 3 ≤ M → (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ {N : ℕ} (lam ε₀ : ℝ)
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ e : ℂ × ℂ, OnSupportZ p₀ β lam M ε₀ V Z e →
      |Real.sinh (β * extSumZ χ p₀ β lam ε₀ V Z e)| ≤ C₃ ∧
        |Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z e) - 1| ≤ C₃ := by
  obtain ⟨C₃, hC₃, hinf⟩ := bornesabinfty_Z hχ p₀ β
  refine ⟨C₃, hC₃, fun {M} hM3 hMp {N} lam ε₀ V Z hlam hlamh hVZ e he => ⟨?_, ?_⟩⟩
  · have h1 := (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ e he).1
    have hδ := lam_le_badDistZ hlam hlamh hMp hVZ he.2 he.norm_le
    have hrδ := norm_le_badDistZ hlam hlamh hMp hVZ he.2 he.norm_le
    have hq : ‖e.1 - e.2‖ / badDistZ p₀ β lam ε₀ V Z e ≤ 1 :=
      (div_le_one (hlam.trans_le hδ)).2 hrδ
    exact h1.trans (by nlinarith)
  · have h1 := (hinf lam M ε₀ V Z hlam hlamh hMp hM3 hVZ e he).2
    have h2 := Real.add_one_le_exp (β * extSumZ χ p₀ β lam ε₀ V Z e)
    have h3 := Real.add_one_le_exp (-(β * extSumZ χ p₀ β lam ε₀ V Z e))
    have h4 : 0 ≤ Real.cosh (β * extSumZ χ p₀ β lam ε₀ V Z e) - 1 := by
      rw [Real.cosh_eq]
      linarith
    rw [abs_of_nonneg h4]
    exact (sub_le_self _ zero_le_one).trans (by unfold extSumZ; exact h1)

theorem outerConst_nonneg {Cp Q M C₁ C₂ K : ℝ} (hQ : 1 ≤ Q) (hCp : 0 < Cp) (hM : 0 < M) (hC₁ : 1 ≤ C₁)
    (hC₂ : 1 ≤ C₂) (hK : 1 ≤ K) : 0 ≤ outerConst Cp Q M C₁ C₂ K := by
  unfold outerConst
  have : 0 ≤ C₁ := by linarith
  have : 0 ≤ C₂ := by linarith
  have : 0 ≤ K := by linarith
  positivity

/-- `2^k (a^k b d c C^k C^k) = (2 C² a)^k b c d`. -/
theorem two_pow_mul_eq (a b c d C : ℝ) (k : ℕ) :
    2 ^ k * (a ^ k * b * c * d * C ^ k * C ^ k) = (2 * C ^ 2 * a) ^ k * b * d * c := by
  rw [mul_pow, mul_pow, ← pow_mul]
  ring

open scoped Classical in
/-- The pointwise bound of the reduced sum from the bounds of its pieces (internal). -/
theorem parAbsSum_le_of {β : ℝ} {w : ℂ × ℂ → ℂ × ℂ → ℝ} {M lam : ℝ} {s : ℂ × ℂ → ℝ}
    {X : Finset (Finset ℕ)} (hX : IsSubpartition X) {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)}
    (hXs : ∀ l, Xs l ⊆ X) (hdisj : ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) {U : Finset ℕ}
    (hU : U ⊆ X.biUnion id) (c : ℕ → ℂ × ℂ) {rad : ℕ → ℝ}
    (hrad1 : ∀ i ∈ X.biUnion id, 1 ≤ rad i) {o m C₃ : ℝ} (ho0 : 0 ≤ o) (hom : o ≤ m)
    (hm1 : 1 ≤ m) (hC₃ : 1 ≤ C₃) (I : Fin n → ℝ) (hI0 : ∀ l, 0 ≤ I l) {TB : ℝ}
    (htree : |treeF M lam (coarsen X (univ.image Xs)) c| ≤ TB)
    (hgrp : ∀ U₁ ⊆ U, ∀ l, (∑ E₁ ∈ markEulerPairs (Xs l) U₁, |groupTerm β w M lam (Xs l) E₁ c|) *
        ∏ i ∈ U₁ ∩ (Xs l).biUnion id, |Real.sinh (β * s (c i))| ≤
      o ^ ((Xs l).biUnion id).card * (∏ i ∈ (Xs l).biUnion id, rad i) * I l)
    (hsh : ∀ i ∈ X.biUnion id, |Real.sinh (β * s (c i))| ≤ C₃)
    (hch : ∀ i ∈ X.biUnion id, |Real.cosh (β * s (c i)) - 1| ≤ C₃) :
    parAbsSum β w M lam s X Xs U c ≤
      (2 * C₃ ^ 2 * m) ^ (X.biUnion id).card * (∏ i ∈ X.biUnion id, rad i) * TB * ∏ l, I l := by
  have hTB0 : 0 ≤ TB := (abs_nonneg _).trans htree
  have hW0 : 0 ≤ ∏ i ∈ X.biUnion id, rad i := prod_nonneg fun i hi => zero_le_one.trans (hrad1 i hi)
  have hIp : 0 ≤ ∏ l, I l := prod_nonneg fun l _ => hI0 l
  have hC₃0 : 0 ≤ C₃ := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hfix : ∀ U₁ ∈ U.powerset,
      ∑ E₁s ∈ (Fintype.piFinset fun l => (interPairs (Xs l)).powerset).filter
          (fun E₁s => ∀ S ∈ X, Even (∑ l, blockDeg (E₁s l) S + (S ∩ U₁).card)),
        |expTerm β w M lam s X Xs U U₁ E₁s c| ≤
        m ^ (X.biUnion id).card * (∏ i ∈ X.biUnion id, rad i) * (∏ l, I l) * TB *
          C₃ ^ (X.biUnion id).card * C₃ ^ (X.biUnion id).card := by
    intro U₁ hU₁
    have hU₁U := mem_powerset.1 hU₁
    have hU₁W : U₁ ⊆ X.biUnion id := hU₁U.trans hU
    refine (sum_parity_le hX hXs hdisj U U₁ c).trans ?_
    have hP1 := prod_group_bounds_le (fun l => (Xs l).biUnion id)
      (fun i _ j _ hij => Hierarchical.disjoint_biUnion_of_disjoint hX (hXs i) (hXs j)
        (hdisj i j hij))
      (fun l => biUnion_subset_biUnion_of_subset_left id (hXs l)) hrad1 ho0 hom hm1
      (sum_card_biUnion_le hX hXs hdisj)
      (fun l => (∑ E₁ ∈ markEulerPairs (Xs l) U₁, |groupTerm β w M lam (Xs l) E₁ c|) *
        ∏ i ∈ U₁ ∩ (Xs l).biUnion id, |Real.sinh (β * s (c i))|) I
      (fun l => mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
        (prod_nonneg fun _ _ => abs_nonneg _)) hI0 (hgrp U₁ hU₁U)
    have hP2 := prod_le_pow_of_le' (U₁ \ univ.biUnion fun l => (Xs l).biUnion id) hC₃
      (k := (X.biUnion id).card) ((card_le_card sdiff_subset).trans (card_le_card hU₁W))
      (f := fun i => |Real.sinh (β * s (c i))|)
      (fun _ _ => abs_nonneg _) fun i hi => hsh i (hU₁W (mem_sdiff.1 hi).1)
    have hP3 := prod_le_pow_of_le' (U \ U₁) hC₃ (k := (X.biUnion id).card)
      ((card_le_card sdiff_subset).trans (card_le_card hU))
      (f := fun i => |Real.cosh (β * s (c i)) - 1|)
      (fun _ _ => abs_nonneg _) fun i hi => hch i (hU (mem_sdiff.1 hi).1)
    have hA0 : 0 ≤ m ^ (X.biUnion id).card * (∏ i ∈ X.biUnion id, rad i) * ∏ l, I l := by
      positivity
    exact mul_le_mul (mul_le_mul (mul_le_mul hP1 htree (abs_nonneg _) hA0)
      hP2 (prod_nonneg fun _ _ => abs_nonneg _) (by positivity)) hP3
      (prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
  unfold parAbsSum
  refine (sum_le_card_nsmul _ _ _ hfix).trans ?_
  rw [nsmul_eq_mul, card_powerset]
  have h2k : ((2 ^ U.card : ℕ) : ℝ) ≤ 2 ^ (X.biUnion id).card := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) (card_le_card hU)
  have hB0 : 0 ≤ m ^ (X.biUnion id).card * (∏ i ∈ X.biUnion id, rad i) * (∏ l, I l) * TB *
      C₃ ^ (X.biUnion id).card * C₃ ^ (X.biUnion id).card := by positivity
  refine (mul_le_mul_of_nonneg_right h2k hB0).trans (le_of_eq ?_)
  exact two_pow_mul_eq _ _ _ _ _ _

open scoped Classical in
/-- **The pointwise bound of the reduced sum** (Lemmas 5.35–5.36): see the module docstring. -/
theorem parAbsSum_le (hχ : IsMollifier χ) (p₀ : ℕ) (β : ℝ) :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ Q : ℝ, 1 ≤ Q ∧ ∃ Cp : ℝ, 0 < Cp ∧ ∃ C₃ : ℝ, 1 ≤ C₃ ∧
      ∀ {M : ℝ}, 20 < M → (3 : ℝ) ^ pBeta p₀ β ≤ M → ∀ {N : ℕ} (lam ε₀ : ℝ)
      (V : Finset (Fin N)) (Z : Fin N → ℂ × ℂ), 0 < lam → lam ≤ ε₀ * truncationScale p₀ β lam →
      V ⊆ badPointsOn p₀ β lam M ε₀ V Z → ∀ {X : Finset (Finset ℕ)}, IsSubpartition X →
      (∀ S ∈ X, S.card ≤ pBeta p₀ β) → ∀ {n : ℕ} {Xs : Fin n → Finset (Finset ℕ)},
      (∀ l, Xs l ⊆ X) → (∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) → (∀ l, 2 ≤ (Xs l).card) →
      ∀ {U : Finset ℕ}, U ⊆ X.biUnion id → ∀ c : ℕ → ℂ × ℂ,
      (∀ i ∈ X.biUnion id, OnSupportZ p₀ β lam M ε₀ V Z (c i) ∧ 0 < ‖(c i).1 - (c i).2‖) →
      (∀ S ∈ X, ConnOn S (linkedPairs M lam c S)) →
      parAbsSum β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam (extSumZ χ p₀ β lam ε₀ V Z) X Xs U
          c ≤
        (2 * C₃ ^ 2 * outerConst' Cp Q M C₁ C₂ (compConst M (pBeta p₀ β))) ^
            (X.biUnion id).card *
          (∏ i ∈ X.biUnion id, (ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖) ^
            ((2 * C₁ * Cp + 1) / M) *
              (1 + Real.logb M (17 * ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖)) ^ 2) *
          treeWeightB M lam ε₀ (truncationScale p₀ β lam) c X (univ.image Xs) *
          ∏ l, innerSeries M lam ε₀ (truncationScale p₀ β lam) c (Xs l) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, Q, hQ, Cp, hCp, hgrp⟩ := groupSum_abs_le hχ p₀ β
  obtain ⟨C₃, hC₃, hext⟩ := abs_sinh_cosh_le_const hχ p₀ β
  refine ⟨C₁, hC₁, C₂, hC₂, Q, hQ, Cp, hCp, C₃, hC₃, fun {M} hM hMp {N} lam ε₀ V Z hlam hlamh hVZ {X} hX
    hXp {n} {Xs} hXs hdisj h2 {U} hU c hc hconn => ?_⟩
  have hM3 : 3 ≤ M := by linarith
  have hK1 := one_le_compConst M (pBeta p₀ β)
  have hoc0 := outerConst_nonneg (M := M) (K := compConst M (pBeta p₀ β)) hQ hCp (by linarith) hC₁
    hC₂ hK1
  have hrad1 : ∀ i ∈ X.biUnion id, 1 ≤ (ε₀ * truncationScale p₀ β lam /
      ‖(c i).1 - (c i).2‖) ^ ((2 * C₁ * Cp + 1) / M) *
        (1 + Real.logb M (17 * ε₀ * truncationScale p₀ β lam / ‖(c i).1 - (c i).2‖)) ^ 2 := by
    intro i hi
    refine one_le_mul_of_one_le_of_one_le (Real.one_le_rpow
      ((one_le_div (hc i hi).2).2 (hc i hi).1.norm_le) ?_)
      (one_le_logFactor (by linarith) (hc i hi).2 (hc i hi).1.norm_le)
    have : 0 ≤ C₁ * Cp := mul_nonneg (by linarith) hCp.le
    have : 0 < M := by linarith
    positivity
  have hcoarse : IsSubpartition (coarsen X (univ.image Xs)) := by
    refine isSubpartition_coarsen hX (fun Y hY => ?_) (fun Y hY => ?_) ?_
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hY
      exact hXs l
    · obtain ⟨l, -, rfl⟩ := mem_image.1 hY
      exact card_pos.1 (by have := h2 l; omega)
    · intro Y hY Y' hY' hne
      obtain ⟨l, -, rfl⟩ := mem_image.1 (mem_coe.1 hY)
      obtain ⟨l', -, rfl⟩ := mem_image.1 (mem_coe.1 hY')
      exact hdisj l l' fun h => hne (by rw [h])
  exact parAbsSum_le_of hX hXs hdisj hU c hrad1 hoc0 (le_max_left _ _) (le_max_right _ _) hC₃
    (fun l => innerSeries M lam ε₀ (truncationScale p₀ β lam) c (Xs l))
    (fun l => innerSeries_nonneg _ _ _ _ _ _)
    (abs_sum_negLinked_le hcoarse M lam ε₀ (truncationScale p₀ β lam) c)
    (fun U₁ _ l => by
      rw [sum_mul]
      exact hgrp hM hMp lam ε₀ V Z hlam hlamh hVZ (isSubpartition_mono hX (hXs l))
        (fun S hS => hXp S (hXs l hS)) U₁ c
        (fun i hi => hc i (biUnion_subset_biUnion_of_subset_left id (hXs l) hi))
        (fun S hS => hconn S (hXs l hS)))
    (fun i hi => (hext hM3 hMp lam ε₀ V Z hlam hlamh hVZ (c i) (hc i hi).1).1)
    (fun i hi => (hext hM3 hMp lam ε₀ V Z hlam hlamh hVZ (c i) (hc i hi).1).2)

end Main

end SimplifiedUpper

end UpperBound

end MultipoleBKT

end
