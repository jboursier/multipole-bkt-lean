/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.LowerBound.LowerBoundLDP.Telescoping
public import MultipoleBKT.Main.PropFiveFortyFive.Polymer

/-!
# Proposition 4.62, Step 2: the logarithm of the cluster sum

Step 2 of the proof of Proposition 4.62, equation (4.146).

For activities `K₁` (the paper's `𝖪^-_{ε₀}`) and `K₂` (the paper's `𝖪^0_∞ = 𝖪^mult`) on the
subfamilies of a partition `π ∈ 𝚷_p([N])`, with

* `K₁(X) = 0` for `|X| ≤ 1`,
* `|K₁(X)|, |K₂(X)| ≤ C₀ (λ²/N)^{|X|-1}` on the retained clusters (`2 ≤ |X|`, `|V_X| ≤ p`),
* the full connected series of `K₁` absolutely convergent, with the part over the tuples having
  some `|V_{X_i}| > p` at most `B` (Proposition 4.27, eqs. (4.55)–(4.56)),

and `λ` small, the disjoint-cluster sum `Ξ(π) = ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint}
K₁(X₁) ⋯ K₁(Xₙ)` of Lemma 4.18 (`disjointSum`) is positive and

  `log Ξ(π) ≥ log polymerSum_p(K₂)(π) - 4 e² ∑_{X ⊂ π retained} |K₁(X) - K₂(X)| - B`

(`exists_log_disjointSum_ge`), where `polymerSum_p(K₂)(π)` is the polymer gas of retained clusters
of Proposition 5.45 (`MultipoleBKT.PropFiveFortyFive.polymerSum`). The steps are the paper's:
Lemma 4.7 turns `log Ξ` into the full connected series (`MultipoleBKT.lemma_4_7_subsets`); the
tuples with a cluster of more than `p` points are dropped at cost `B` (eq. (4.56)); the retained
series of `K₁` and `K₂` are compared by the telescoping estimate
(`MultipoleBKT.LowerBoundLDP.abs_tsum_connected_sub_le`); and the retained series of `K₂` is
`log polymerSum_p(K₂)(π)` (Lemmas 4.53 and 4.7, `MultipoleBKT.PropFiveFortyFive.exists_logSeries`).
-/

@[expose] public section

namespace MultipoleBKT

namespace LowerBoundLDP

open Finset PropFiveFortyFive

/-- The disjoint-cluster sum of Lemma 4.18 (eq. (4.142)):
`Ξ(π) = ∑_{n ≥ 0} (1/n!) ∑_{X₁, …, Xₙ ⊂ π disjoint} K(X₁) ⋯ K(Xₙ)`. -/
noncomputable def disjointSum (K : Finset (Finset ℕ) → ℝ) (π : Finset (Finset ℕ)) : ℝ :=
  ∑' k : ℕ, 1 / (k.factorial : ℝ) *
    ∑ Xs ∈ (Fintype.piFinset fun _ : Fin k => π.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)),
      ∏ i, K (Xs i)

/-- The retained clusters: at least two blocks and at most `p` points. -/
def Retained (p : ℕ) (X : Finset (Finset ℕ)) : Prop :=
  2 ≤ X.card ∧ (X.biUnion id).card ≤ p

instance (p : ℕ) : DecidablePred (Retained p) := fun X => by
  unfold Retained
  infer_instance

/-- An activity cut off to the retained clusters. -/
noncomputable def retainedPart (p : ℕ) (K : Finset (Finset ℕ) → ℝ) (X : Finset (Finset ℕ)) : ℝ :=
  if Retained p X then K X else 0

open scoped Classical in
/-- The retained connected sum `clusterSum p n K π` is the connected sum of the retained part
of `K`. -/
theorem clusterSum_eq_sum_connected (p n : ℕ) (K : Finset (Finset ℕ) → ℝ)
    (π : Finset (Finset ℕ)) :
    clusterSum p n K π =
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected),
        (∏ i, retainedPart p K (X i)) * (ursell (connectionGraph X) : ℝ) := by
  unfold clusterSum
  rw [sum_filter]
  refine sum_congr rfl fun X _ => ?_
  unfold clusterWeight
  by_cases hc : (connectionGraph X).Connected
  · rw [ite_eq_left hc]
    by_cases hr : ∀ i, 2 ≤ (X i).card ∧ ((X i).biUnion id).card ≤ p
    · rw [ite_eq_left ⟨hc, hr⟩]
      congr 1
      exact prod_congr rfl fun i _ => (ite_eq_left (hr i)).symm
    · rw [ite_eq_right fun h => hr h.2]
      push Not at hr
      obtain ⟨i, hi⟩ := hr
      rw [prod_eq_zero (mem_univ i) (ite_eq_right fun h => by
        have := hi h.1
        exact absurd h.2 (by omega)), zero_mul]
  · rw [ite_eq_right hc, ite_eq_right fun h => hc h.1]

open scoped Classical in
/-- The connected sum of `K` splits into its retained part and the part over the tuples with a
cluster of more than `p` points, when `K` vanishes on the subfamilies with at most one block. -/
theorem sum_connected_eq_add {p n : ℕ} {π : Finset (Finset ℕ)} {K : Finset (Finset ℕ) → ℝ}
    (hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0) :
    ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun X => (connectionGraph X).Connected),
      (∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ) =
      clusterSum p n K π +
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
          (∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ) := by
  rw [clusterSum_eq_sum_connected, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
  refine sum_congr rfl fun X hX => ?_
  have hsub : ∀ i, X i ⊆ π := fun i => mem_powerset.mp (Fintype.mem_piFinset.mp hX i)
  by_cases hc : (connectionGraph X).Connected
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hr : ∀ i, Retained p (X i)
    · have hnot : ¬ ((connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card) :=
        fun h => by obtain ⟨i, hi⟩ := h.2; have := (hr i).2; omega
      rw [ite_eq_right hnot, add_zero]
      congr 1
      exact prod_congr rfl fun i _ => (ite_eq_left (hr i)).symm
    · push Not at hr
      obtain ⟨i, hi⟩ := hr
      have hz : ∏ j, retainedPart p K (X j) = 0 := prod_eq_zero (mem_univ i) (ite_eq_right hi)
      rw [hz, zero_mul, zero_add]
      by_cases hbig : ∃ j, p < ((X j).biUnion id).card
      · rw [ite_eq_left ⟨hc, hbig⟩]
      · rw [ite_eq_right fun h => hbig h.2]
        push Not at hbig
        have h1 : (X i).card ≤ 1 := by
          by_contra h
          exact hi ⟨by omega, hbig i⟩
        rw [prod_eq_zero (mem_univ i) (hK1 _ (hsub i) h1), zero_mul]
  · rw [ite_eq_right hc, ite_eq_right hc, ite_eq_right fun h => hc h.1, add_zero]

/-- Basic facts on a partition in `𝚷_p([N])`. -/
theorem facts_of_mem_boundedBlockPartitions {N p : ℕ} (hN : 1 ≤ N) {π : Finset (Finset ℕ)}
    (hπ : π ∈ boundedBlockPartitions N p) :
    IsSubpartition π ∧ π.Nonempty ∧ π.card ≤ N ∧ ∀ S ∈ π, 1 ≤ S.card ∧ S.card ≤ p := by
  have hπP := isSubpartition_of_mem_boundedBlockPartitions hπ
  have hπ1 := card_mem_Icc_of_mem_boundedBlockPartitions hπ
  refine ⟨hπP, ?_, ?_, hπ1⟩
  · have h := biUnion_of_mem_boundedBlockPartitions hπ
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, biUnion_empty] at h
    have : 0 ∈ Finset.range N := mem_range.2 hN
    rw [← h] at this
    exact notMem_empty 0 this
  · have h := sum_mul_blockCount_of_mem_boundedBlockPartitions hπ
    rw [← sum_blockCount hπ1, ← h]
    exact sum_le_sum fun i _ => Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- The retained clusters of a subpartition have at most `p` blocks. -/
theorem card_le_of_retained {π X : Finset (Finset ℕ)} (hπ : IsSubpartition π) (hX : X ⊆ π)
    {p : ℕ} (h : Retained p X) : X.card ≤ p :=
  (PropFiveFortyFive.card_le_card_biUnion (SetPartition.isSubpartition_mono hπ hX)).trans h.2

/-- The leaf cost of the telescoping estimate: for weights `v` vanishing off the retained clusters
and `w` with anchored norm `q`, `v(Z) ∑_{Y ∩ Z ≠ ∅} w(Y) ≤ p q v(Z)`. -/
theorem leaf_cost_le {π : Finset (Finset ℕ)} (hπ : IsSubpartition π) {p : ℕ}
    {v w : Finset (Finset ℕ) → ℝ} {q : ℝ} (hq0 : 0 ≤ q) (hv : ∀ Y, 0 ≤ v Y)
    (hw : ∀ Y, 0 ≤ w Y) (hv0 : ∀ Z, ¬ Retained p Z → v Z = 0)
    (hq : ∀ a ∈ π, ∑ Y ∈ π.powerset, (if a ∈ Y then |w Y| else 0) ≤ q) :
    ∀ Z ⊆ π, v Z * ∑ Y ∈ π.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ (p * q) * v Z := by
  intro Z hZ
  by_cases hr : Retained p Z
  · have hsum : ∑ Y ∈ π.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) ≤ p * q := by
      have h := sum_powerset_ite_inter_nonempty_le hZ hq
      have he : ∑ Y ∈ π.powerset, (if (Y ∩ Z).Nonempty then |w Y| else 0) =
          ∑ Y ∈ π.powerset, (if (Y ∩ Z).Nonempty then w Y else 0) :=
        sum_congr rfl fun Y _ => by rw [abs_of_nonneg (hw Y)]
      rw [he] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ hq0)
      exact_mod_cast card_le_of_retained hπ hZ hr
    rw [mul_comm (p * q)]
    exact mul_le_mul_of_nonneg_left hsum (hv Z)
  · rw [hv0 Z hr, zero_mul, mul_zero]

/-- A series dominated by a convergent nonnegative series of sum at most `B` converges, with sum
of absolute value at most `B`. -/
theorem summable_and_abs_tsum_le {b : ℕ+ → ℝ} {g : ℕ → ℝ} {B : ℝ} (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g) (hgB : ∑' n, g n ≤ B) (hb : ∀ n : ℕ+, ‖b n‖ ≤ g n) :
    Summable b ∧ |∑' n, b n| ≤ B := by
  have hgp : Summable fun n : ℕ+ => g n := hg.comp_injective PNat.coe_injective
  have hbn : Summable fun n => ‖b n‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgp
  refine ⟨Summable.of_norm hbn, ?_⟩
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hbn).trans ((hbn.tsum_le_tsum hb hgp).trans
    ((tsum_comp_le_tsum_of_inj hg hg0 PNat.coe_injective).trans hgB))

open scoped Classical in
/-- **Lemma 4.7 for the disjoint-cluster sum** (proof of Proposition 4.62): if the full connected series of `K`
converges absolutely and `K(∅) = 0`, then `Ξ(π) > 0` and
`log Ξ(π) = ∑_{n ≥ 1} (1/n!) ∑_{X₁, …, Xₙ ⊂ π connected} K(X₁) ⋯ K(Xₙ) I(G(X))`. -/
theorem log_disjointSum_eq {π : Finset (Finset ℕ)} {K : Finset (Finset ℕ) → ℝ} (hK0 : K ∅ = 0)
    (habs : Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)|) :
    0 < disjointSum K π ∧ Real.log (disjointSum K π) =
      ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
          (∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ) := by
  have hfilt : ∀ n : ℕ, (Fintype.piFinset fun _ : Fin n => π.powerset).filter
      (fun V => (connectionGraph V).Connected ∧ ∀ i, (fun _ : Finset (Finset ℕ) => True) (V i)) =
      (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun X => (connectionGraph X).Connected) :=
    fun n => filter_congr fun V _ => by simp only [implies_true, and_true]
  have hfilt' : ∀ n : ℕ, (Fintype.piFinset fun _ : Fin n => π.powerset).filter
      (fun V => (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
        ∀ i, (fun _ : Finset (Finset ℕ) => True) (V i)) =
      (Fintype.piFinset fun _ : Fin n => π.powerset).filter
        (fun Xs => ∀ i j, i ≠ j → Disjoint (Xs i) (Xs j)) :=
    fun n => filter_congr fun V _ => by simp only [implies_true, and_true]
  have hsum : Summable fun n : ℕ+ => ‖1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun V => (connectionGraph V).Connected ∧ ∀ i, (fun _ : Finset (Finset ℕ) => True) (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)‖ := by
    refine Summable.of_norm_bounded (habs.comp_injective PNat.coe_injective) fun n => ?_
    rw [norm_norm, hfilt, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℕ).factorial : ℝ))]
    exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
  have h47 := lemma_4_7_subsets π (fun _ => True) K (fun _ => hK0) hsum
  have hZeq : (∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun V => (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
            ∀ i, (fun _ : Finset (Finset ℕ) => True) (V i)),
        ∏ i, K (V i)) = disjointSum K π := by
    unfold disjointSum
    exact tsum_congr fun n => by rw [hfilt']
  have hFeq : (∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
      ∑ V ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun V => (connectionGraph V).Connected ∧
            ∀ i, (fun _ : Finset (Finset ℕ) => True) (V i)),
        (∏ i, K (V i)) * (ursell (connectionGraph V) : ℝ)) =
      ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) *
        ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
            (fun X => (connectionGraph X).Connected),
          (∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ) :=
    tsum_congr fun n => by rw [hfilt]
  exact ⟨h47.1.trans_eq hZeq, hZeq ▸ h47.2.1.trans hFeq⟩

open scoped Classical in
/-- **Dropping the large clusters** (proof of Proposition 4.62, eq. (4.56)): if moreover `K` vanishes on the
subfamilies with at most one block and the part of the full connected series over the tuples with
some `|V_{X_i}| > p` is at most `B`, then
`log Ξ(π) = ∑_{n ≥ 1} (1/n!) clusterSum_n(K) + E` with `|E| ≤ B`, where `clusterSum_n(K)` is the
connected sum over the retained clusters. -/
theorem log_disjointSum_eq_add {p : ℕ} {π : Finset (Finset ℕ)} {K : Finset (Finset ℕ) → ℝ}
    {B : ℝ} (hK1 : ∀ X ⊆ π, X.card ≤ 1 → K X = 0)
    (habs : Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)|)
    (hbad : ∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| ≤ B)
    (hsr : Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K π) :
    0 < disjointSum K π ∧ ∃ E : ℝ, |E| ≤ B ∧
      Real.log (disjointSum K π) =
        (∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K π) + E := by
  obtain ⟨hZ, hlogZ⟩ := log_disjointSum_eq (hK1 ∅ (empty_subset _) (by simp)) habs
  refine ⟨hZ, ?_⟩
  have hg0 : ∀ n : ℕ, 0 ≤ 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| := fun n =>
    mul_nonneg (by positivity) (sum_nonneg fun _ _ => abs_nonneg _)
  have hgle : ∀ n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| ≤
      1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected),
        |(∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)| := by
    intro n
    refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_
      fun _ _ _ => abs_nonneg _) (by positivity)
    intro X hX
    rw [mem_filter] at hX ⊢
    exact ⟨hX.1, hX.2.1⟩
  obtain ⟨hsb, hbB⟩ := summable_and_abs_tsum_le hg0 (Summable.of_nonneg_of_le hg0 hgle habs) hbad
    (b := fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
        (∏ i, K (X i)) * (ursell (connectionGraph X) : ℝ)) fun n => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℕ).factorial : ℝ))]
      exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by positivity)
  refine ⟨_, hbB, ?_⟩
  rw [hlogZ, ← hsr.tsum_add hsb]
  refine tsum_congr fun n => ?_
  rw [sum_connected_eq_add (p := p) hK1, mul_add]

open scoped Classical in
/-- **Replacing `K₁` by `K₂` in the retained series** (proof of Proposition 4.62): if
`|K₁(X)|, |K₂(X)| ≤ C₀ (λ²/N)^{|X|-1}` on the retained clusters and `e² p² (2C₀) λ² ≤ 1/2`, then
`|∑_n (1/n!) clusterSum_n(K₁) - ∑_n (1/n!) clusterSum_n(K₂)|
≤ 4 e² ∑_{X ⊂ π retained} |K₁(X) - K₂(X)|`. -/
theorem abs_tsum_clusterSum_sub_le {N p : ℕ} {π : Finset (Finset ℕ)} (hπP : IsSubpartition π)
    (hπN : π.card ≤ N) {K₁ K₂ : Finset (Finset ℕ) → ℝ} {lam C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hb₁ : ∀ X ⊆ π, Retained p X → |K₁ X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1))
    (hb₂ : ∀ X ⊆ π, Retained p X → |K₂ X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1))
    (hsmall : Real.exp 2 * (p * (p * (2 * C₀) * lam ^ 2)) ≤ 1 / 2)
    (hs₁ : Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K₁ π)
    (hs₂ : Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K₂ π) :
    |(∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K₁ π) -
        ∑' n : ℕ+, 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K₂ π| ≤
      4 * Real.exp 2 * ∑ Y ∈ π.powerset, (if Retained p Y then |K₁ Y - K₂ Y| else 0) := by
  have hw0 : ∀ Y, 0 ≤ (fun Y => if Retained p Y then |K₁ Y| + |K₂ Y| else (0 : ℝ)) Y := fun Y => by
    simp only
    split_ifs
    · positivity
    · exact le_rfl
  have hd0 : ∀ Y, 0 ≤ (fun Y => if Retained p Y then |K₁ Y - K₂ Y| else (0 : ℝ)) Y := fun Y => by
    simp only
    split_ifs
    · positivity
    · exact le_rfl
  have hq : ∀ a ∈ π, ∑ Y ∈ π.powerset,
      (if a ∈ Y then |(fun Y => if Retained p Y then |K₁ Y| + |K₂ Y| else (0 : ℝ)) Y| else 0) ≤
        p * (2 * C₀) * lam ^ 2 := by
    intro a ha
    refine sum_powerset_ite_mem_le hπN (by positivity) hlam.le hlam1 (fun X hX hX2 => ?_)
      (fun X hX h2 hp' => ?_) ha
    · exact ite_eq_right fun hr => hX2 ⟨hr.1, card_le_of_retained hπP hX hr⟩
    · split_ifs with hr
      · rw [abs_of_nonneg (by positivity)]
        have h1 := hb₁ X hX hr
        have h2 := hb₂ X hX hr
        linarith
      · rw [abs_zero]
        positivity
  have hq0 : 0 ≤ p * (2 * C₀) * lam ^ 2 := by positivity
  have hcw := leaf_cost_le hπP hq0 hw0 hw0 (fun Z hZ => ite_eq_right hZ) hq
  have hcd := leaf_cost_le hπP hq0 hd0 hw0 (fun Z hZ => ite_eq_right hZ) hq
  simp only [clusterSum_eq_sum_connected] at hs₁ hs₂ ⊢
  refine abs_tsum_connected_sub_le (by positivity) hw0 hd0 (fun Y _ => ?_) (fun Y _ => ?_)
    (fun Y _ => ?_) hcw hcd hsmall hs₁ hs₂
  · simp only [retainedPart]
    split_ifs
    · linarith [abs_nonneg (K₂ Y)]
    · simp
  · simp only [retainedPart]
    split_ifs
    · linarith [abs_nonneg (K₁ Y)]
    · simp
  · simp only [retainedPart]
    split_ifs
    · exact le_rfl
    · simp

open scoped Classical in
/-- The conclusion of `exists_log_disjointSum_ge` for the constants `C₀` (the bound on the retained
activities) and `Ct` (the constant of Lemma 4.53): for `π ∈ 𝚷_p([N])`, `λ` small and activities
`K₁`, `K₂` as in the module docstring,
`log Ξ(π) ≥ log polymerSum_p(K₂)(π) - 4 e² ∑_{X ⊂ π retained} |K₁(X) - K₂(X)| - B`. -/
def DisjointSumLogBound (p : ℕ) (C₀ Ct : ℝ) : Prop :=
  ∀ (N : ℕ) (π : Finset (Finset ℕ)) (K₁ K₂ : Finset (Finset ℕ) → ℝ)
    (lam B : ℝ), π ∈ boundedBlockPartitions N p → 1 ≤ N → 0 < lam → lam ≤ 1 →
    Ct * lam ^ 2 ≤ 1 / 2 → Real.exp 2 * (p * (p * (2 * C₀) * lam ^ 2)) ≤ 1 / 2 →
    (∀ X ⊆ π, X.card ≤ 1 → K₁ X = 0) →
    (∀ X ⊆ π, Retained p X → |K₁ X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
    (∀ X ⊆ π, Retained p X → |K₂ X| ≤ C₀ * (lam ^ 2 / N) ^ (X.card - 1)) →
    (Summable fun n : ℕ => 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected),
        |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)|) →
    (∑' n : ℕ, 1 / (n.factorial : ℝ) *
      ∑ X ∈ (Fintype.piFinset fun _ : Fin n => π.powerset).filter
          (fun X => (connectionGraph X).Connected ∧ ∃ i, p < ((X i).biUnion id).card),
        |(∏ i, K₁ (X i)) * (ursell (connectionGraph X) : ℝ)| ≤ B) →
    0 < disjointSum K₁ π ∧ 0 < polymerSum p K₂ π ∧
      Real.log (polymerSum p K₂ π) - 4 * Real.exp 2 *
          (∑ Y ∈ π.powerset, if Retained p Y then |K₁ Y - K₂ Y| else 0) - B ≤
        Real.log (disjointSum K₁ π)

/-- **The logarithm of the cluster sum** (Step 2 of the proof of Proposition 4.62):
see the module docstring. With `Ct` from Lemma 4.53 for the bound `C₀` and `p`, for `λ` small,
`log Ξ(π) ≥ log polymerSum_p(K₂)(π) - 4 e² ∑_{X ⊂ π retained} |K₁(X) - K₂(X)| - B`. -/
theorem exists_log_disjointSum_ge (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (p : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧ DisjointSumLogBound p C₀ Ct := by
  obtain ⟨Ct, hCt, hlogS⟩ := exists_logSeries C₀ hC₀ p
  refine ⟨Ct, hCt, fun N π K₁ K₂ lam B hπ hN hlam hlam1 hCtl hsmall hK1 hb₁ hb₂ habs hbad => ?_⟩
  obtain ⟨hπP, hπne, hπN, -⟩ := facts_of_mem_boundedBlockPartitions hN hπ
  obtain ⟨hbd₁, -⟩ := hlogS N K₁ π lam hπne hπN hπP (fun X hX h2 hV => hb₁ X hX ⟨h2, hV⟩)
    hlam hlam1
  obtain ⟨hbd₂, hpos₂⟩ := hlogS N K₂ π lam hπne hπN hπP (fun X hX h2 hV => hb₂ X hX ⟨h2, hV⟩)
    hlam hlam1
  obtain ⟨hP₂, hlog₂⟩ := hpos₂ (by linarith)
  have hgeo : ∀ {K : Finset (Finset ℕ) → ℝ},
      (∀ n : ℕ, 1 ≤ n → |1 / (n.factorial : ℝ) * clusterSum p n K π| ≤ N * (Ct * lam ^ 2) ^ n) →
      Summable fun n : ℕ+ => 1 / ((n : ℕ).factorial : ℝ) * clusterSum p n K π := by
    intro K hK
    have hr0 : 0 ≤ Ct * lam ^ 2 := by positivity
    have hg : Summable fun n : ℕ+ => (N : ℝ) * (Ct * lam ^ 2) ^ (n : ℕ) :=
      ((summable_geometric_of_lt_one hr0 (by linarith)).mul_left (N : ℝ)).comp_injective
        PNat.coe_injective
    exact Summable.of_norm_bounded hg fun n => by rw [Real.norm_eq_abs]; exact hK n n.pos
  have hs₁ := hgeo hbd₁
  have hs₂ := hgeo hbd₂
  obtain ⟨hZ, E, hE, hlogZ⟩ := log_disjointSum_eq_add hK1 habs hbad hs₁
  have htel := abs_tsum_clusterSum_sub_le hπP hπN hC₀ hlam hlam1 hb₁ hb₂ hsmall hs₁ hs₂
  refine ⟨hZ, hP₂, ?_⟩
  rw [hlogZ, hlog₂]
  have h1 := (abs_le.mp htel).1
  have h2 := (abs_le.mp hE).1
  linarith

end LowerBoundLDP

end MultipoleBKT

end
