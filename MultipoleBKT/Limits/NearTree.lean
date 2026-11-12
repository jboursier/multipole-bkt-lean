/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Integrands

/-!
# Tree bounds for multipoles

The untruncated tree bound (A.13) used in the proof of
Lemma 4.26 and the near-edge part of the proof of Lemma A.5.

A configuration is described by its positions `xᵢ` and dipole vectors `uᵢ = yᵢ - xᵢ`
(`ofPosVec`). The near graph `nearGraph M λ c` joins `i ≠ j` when `i ↔ j`
(`MultipoleLinked`). For a spanning tree `T` of the near graph, integrating the positions along
`T` gives a factor `4π M² min(ρᵢ, ρⱼ)²` per edge (`lintegral_near_le`), the ordering of the
radii (Lemma A.1) and `prod_rpow_mul_rpow_neg_le` reduce the radial factors to
`∏ᵢ ρᵢ^{2 - 2/k}`, and the radial integral is finite for `k ≤ p*(β)`:

* `lintegral_tree_near_lt_top`: `∫ 𝟙_{[0,1]²}(x_{i₀}) ∏_{ij ∈ T} 𝟙_{i ↔ j} ∏ᵢ e^{β g_λ(xᵢ - yᵢ)} < ∞`;
this gives the integrability of the rooted integrand of `𝖬(S)` for `|S| ≤ p*(β)`
(`integrable_anchor_multipoleBox`, in `MultipoleBKT.Limits.MultipoleLimit`).
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Function
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ} {ι : Type*}

/-- The configuration with positions `x` and dipole vectors `u`: `cᵢ = (xᵢ, xᵢ + uᵢ)`. -/
def ofPosVec (x u : ι → ℂ) : ι → ℂ × ℂ := fun i => (x i, x i + u i)

theorem ofPosVec_apply (x u : ι → ℂ) (i : ι) : ofPosVec x u i = (x i, x i + u i) := rfl

theorem norm_ofPosVec_sub (x u : ι → ℂ) (i : ι) :
    ‖(ofPosVec x u i).1 - (ofPosVec x u i).2‖ = ‖u i‖ := by
  simp [ofPosVec]

theorem pairDensity_ofPosVec (hχ : IsMollifier χ) (x u : ι → ℂ) (i : ι) :
    pairDensity χ β lam (ofPosVec x u i) = Real.exp (β * smearedKernel χ lam (u i)) := by
  simp only [pairDensity, ofPosVec, sub_add_cancel_left, smearedKernel_neg hχ]

theorem multipoleLinked_iff_dipoleDist {d e : ℂ × ℂ} :
    MultipoleLinked M lam d e ↔
      dipoleDist d e ≤ M * min (max ‖d.1 - d.2‖ lam) (max ‖e.1 - e.2‖ lam) := Iff.rfl

theorem multipoleLinked_comm {d e : ℂ × ℂ} :
    MultipoleLinked M lam d e ↔ MultipoleLinked M lam e d := by
  rw [multipoleLinked_iff_dipoleDist, multipoleLinked_iff_dipoleDist, dipoleDist_comm,
    min_comm]

/-- The near graph of a configuration: `i ~ j` iff `i ≠ j` and `i ↔ j`. -/
abbrev nearGraph (M lam : ℝ) (c : ι → ℂ × ℂ) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j => MultipoleLinked M lam (c i) (c j)

theorem nearGraph_adj {c : ι → ℂ × ℂ} {i j : ι} :
    (nearGraph M lam c).Adj i j ↔ i ≠ j ∧ MultipoleLinked M lam (c i) (c j) := by
  rw [fromRel_adj]
  exact and_congr_right fun _ => or_iff_left_of_imp fun h => multipoleLinked_comm.1 h

theorem measurableSet_nearGraph_edge (M lam : ℝ) (e : Sym2 ι) :
    MeasurableSet {c : ι → ℂ × ℂ | e ∈ (nearGraph M lam c).edgeSet} := by
  induction e using Sym2.ind with
  | h i j =>
    simp only [mem_edgeSet, nearGraph_adj]
    exact (MeasurableSet.const _).inter (measurableSet_setOf_multipoleLinked M lam i j)

open scoped Classical in
/-- The indicator `𝟙_{e ∈ G}` of an edge. -/
noncomputable def edgeInd (G : SimpleGraph ι) (e : Sym2 ι) : ℝ≥0∞ :=
  if e ∈ G.edgeSet then 1 else 0

theorem edgeInd_mk (G : SimpleGraph ι) [DecidableRel G.Adj] (i j : ι) :
    edgeInd G s(i, j) = if G.Adj i j then 1 else 0 := by
  unfold edgeInd
  simp only [mem_edgeSet]

theorem edgeInd_le_one (G : SimpleGraph ι) (e : Sym2 ι) : edgeInd G e ≤ 1 := by
  unfold edgeInd
  split_ifs <;> simp

theorem measurable_edgeInd_nearGraph (M lam : ℝ) (e : Sym2 ι) :
    Measurable fun c : ι → ℂ × ℂ => edgeInd (nearGraph M lam c) e := by
  classical
  unfold edgeInd
  exact Measurable.ite (measurableSet_nearGraph_edge M lam e) measurable_const measurable_const

open scoped Classical in
/-- `∑_{T tree on ι} 𝟙_{T ≤ G}`, the number of spanning trees of `G`. -/
noncomputable def treeSum [Fintype ι] (G : SimpleGraph ι) : ℝ≥0∞ :=
  ∑ T ∈ (univ : Finset (SimpleGraph ι)).filter IsTree, ∏ e ∈ T.edgeFinset, edgeInd G e

open scoped Classical in
/-- `𝟙_{G connected} ≤ ∑_{T tree} 𝟙_{T ≤ G}`. -/
theorem indicator_connected_le [Fintype ι] (G : SimpleGraph ι) :
    (if G.Connected then 1 else 0 : ℝ≥0∞) ≤ treeSum G := by
  unfold treeSum
  split_ifs with h
  · obtain ⟨T, hTG, hT⟩ := h.exists_isTree_le
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => bot_le)
      (mem_filter.2 ⟨mem_univ T, hT⟩))
    refine (Finset.prod_eq_one fun e he => ?_).symm
    unfold edgeInd
    rw [ite_eq_left (edgeSet_mono hTG (mem_edgeFinset.1 he))]
  · exact bot_le

open scoped Classical in
/-- **Near edges.** `∫ 𝟙_{(t, t + uᵢ) ↔ (y, y + uⱼ)} dt ≤ 4π M² min(ρ(uᵢ), ρ(uⱼ))²`. -/
theorem lintegral_near_le (hM : 0 ≤ M) (ui uj y : ℂ) :
    ∫⁻ t : ℂ, (if MultipoleLinked M lam (t, t + ui) (y, y + uj) then 1 else 0 : ℝ≥0∞) ≤
      ENNReal.ofReal (4 * Real.pi * (M * min (rho lam ui) (rho lam uj)) ^ 2) := by
  set A := M * min (rho lam ui) (rho lam uj)
  have hA : 0 ≤ A := mul_nonneg hM (le_min (le_max_of_le_left (norm_nonneg _))
    (le_max_of_le_left (norm_nonneg _)))
  have hpt : ∀ t : ℂ, (if MultipoleLinked M lam (t, t + ui) (y, y + uj) then 1 else 0 : ℝ≥0∞) =
      (Iic A).indicator 1 (dipoleDist (t, t + ui) (y, y + uj)) := by
    intro t
    have : MultipoleLinked M lam (t, t + ui) (y, y + uj) ↔ dipoleDist (t, t + ui) (y, y + uj) ≤ A := by
      unfold MultipoleLinked dipoleDist
      simp only [sub_add_cancel_left, norm_neg]
      rfl
    by_cases h : dipoleDist (t, t + ui) (y, y + uj) ≤ A
    · rw [ite_eq_left (this.2 h), indicator_of_mem (show _ ∈ Iic A from h), Pi.one_apply]
    · rw [ite_eq_right (mt this.1 h), indicator_of_notMem (show _ ∉ Iic A from h)]
  simp_rw [hpt]
  have hanti : Antitone ((Iic A).indicator (1 : ℝ → ℝ≥0∞)) := by
    intro a b hab
    by_cases hb : b ≤ A
    · rw [indicator_of_mem (show b ∈ Iic A from hb), indicator_of_mem (show a ∈ Iic A from
        hab.trans hb)]
      exact le_rfl
    · rw [indicator_of_notMem (show b ∉ Iic A from hb)]
      exact bot_le
  have hy : (y, y + uj) = (y, y + uj) := rfl
  calc ∫⁻ t : ℂ, (Iic A).indicator 1 (dipoleDist (t, t + ui) (y, y + uj))
      ≤ 4 * ∫⁻ z : ℂ, (Iic A).indicator (1 : ℝ → ℝ≥0∞) ‖z‖ :=
        lintegral_antitone_dipoleDist_le hanti (measurable_one.indicator measurableSet_Iic) ui _
    _ = ENNReal.ofReal (4 * Real.pi * A ^ 2) := by
        rw [lintegral_indicator_norm_le]
        clear_value A
        rw [← ENNReal.ofReal_pow hA, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-- `x ↦ (max x 0)²`, a nonnegative nondecreasing function equal to `x²` for `x ≥ 0`. -/
noncomputable def sqPos (x : ℝ) : ℝ := max x 0 ^ 2

theorem sqPos_mono : Monotone sqPos := fun _ _ h =>
  pow_le_pow_left₀ (le_max_right _ _) (max_le_max h le_rfl) 2

theorem sqPos_nonneg (x : ℝ) : 0 ≤ sqPos x := sq_nonneg _

theorem sqPos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : sqPos x = x ^ 2 := by
  rw [sqPos, max_eq_left hx]

section Tree

variable [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- **The tree bound for near edges.** For a tree `T` on `ι` with `|ι| = k` and
`2 - 2/k < β - 2` (i.e. `k ≤ p*(β)`),
`∫ 𝟙_{[0,1]²}(x_{i₀}) ∏_{ij ∈ T} 𝟙_{i ↔ j} ∏ᵢ e^{β g_λ(xᵢ - yᵢ)} dc < ∞`. -/
theorem lintegral_tree_near_lt_top (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 0 ≤ M) [Nonempty ι] (hk : 2 - 2 / (Fintype.card ι : ℝ) < β - 2)
    {T : SimpleGraph ι} [DecidableRel T.Adj] (hT : T.IsTree) (i₀ : ι) :
    ∫⁻ c : ι → ℂ × ℂ, anchor i₀ c * (∏ e ∈ T.edgeFinset, edgeInd (nearGraph M lam c) e) *
        ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i)) < ∞ := by
  classical
  set k := Fintype.card ι
  set s : ℝ := 2 - 2 / (k : ℝ)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Fintype.card_pos
  -- measurability
  have hmeasF : Measurable fun c : ι → ℂ × ℂ => anchor i₀ c *
      (∏ e ∈ T.edgeFinset, edgeInd (nearGraph M lam c) e) *
      ∏ i, ENNReal.ofReal (pairDensity χ β lam (c i)) :=
    ((measurable_anchor i₀).mul (Finset.measurable_prod _ fun e _ =>
      measurable_edgeInd_nearGraph M lam e)).mul
      (Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp
        ((measurable_pairDensity hχ hlam β).comp (measurable_pi_apply i)))
  rw [lintegral_eq_lintegral_pos_vec _ hmeasF]
  -- integrate the positions for fixed dipole vectors
  have hpos : ∀ u : ι → ℂ, ∫⁻ x : ι → ℂ, anchor i₀ (ofPosVec x u) *
      (∏ e ∈ T.edgeFinset, edgeInd (nearGraph M lam (ofPosVec x u)) e) *
      ∏ i, ENNReal.ofReal (pairDensity χ β lam (ofPosVec x u i)) ≤
      (∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (u i)))) *
        ∏ e ∈ T.edgeFinset, ENNReal.ofReal (4 * Real.pi * M ^ 2 *
          edgeMin sqPos (fun i => rho lam (u i)) e) := by
    intro u
    simp_rw [pairDensity_ofPosVec hχ]
    have hw : ∀ e : Sym2 ι, Measurable fun x : ι → ℂ =>
        edgeInd (nearGraph M lam (ofPosVec x u)) e := by
      intro e
      have hmp : Measurable fun x : ι → ℂ => ofPosVec x u :=
        measurable_pi_iff.2 fun i => (measurable_pi_apply i).prodMk
          ((measurable_pi_apply i).add_const _)
      exact (measurable_edgeInd_nearGraph M lam e).comp hmp
    have htree := lintegral_tree_le hT i₀
      (fun e x => edgeInd (nearGraph M lam (ofPosVec x u)) e) hw
      (fun i j _ x y hi hj => by
        simp only [edgeInd_mk, nearGraph_adj, ofPosVec_apply, hi, hj])
      (fun e => ENNReal.ofReal (4 * Real.pi * M ^ 2 * edgeMin sqPos (fun i => rho lam (u i)) e))
      (fun i j hij x => by
        have hne : i ≠ j := T.ne_of_adj hij
        simp only [edgeInd_mk, nearGraph_adj, ofPosVec_apply, update_self,
          update_of_ne hne.symm, ne_eq, hne, not_false_eq_true, true_and, edgeMin_mk]
        refine (lintegral_near_le hM (u i) (u j) (x j)).trans (le_of_eq ?_)
        rw [sqPos_of_nonneg (le_min (lam_le_rho lam _ |>.trans' hlam.le)
          (lam_le_rho lam _ |>.trans' hlam.le))]
        ring_nf)
      ((box 1).indicator 1) (measurable_one.indicator (TwoComponentCoulomb.measurableSet_box 1))
    have hbox : ∫⁻ t : ℂ, (box 1).indicator (1 : ℂ → ℝ≥0∞) t = 1 := by
      rw [lintegral_indicator_one (TwoComponentCoulomb.measurableSet_box 1),
        TwoComponentCoulomb.volume_box]
      simp
    rw [hbox, one_mul] at htree
    have hre : ∀ x : ι → ℂ, anchor i₀ (ofPosVec x u) *
        (∏ e ∈ T.edgeFinset, edgeInd (nearGraph M lam (ofPosVec x u)) e) *
        ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (u i))) =
        (∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (u i)))) *
          ((box 1).indicator 1 (x i₀) * ∏ e ∈ T.edgeFinset,
            edgeInd (nearGraph M lam (ofPosVec x u)) e) := by
      intro x
      simp only [anchor, ofPosVec_apply]
      ring
    simp_rw [hre]
    rw [lintegral_const_mul' _ _ (ENNReal.prod_ne_top fun i _ => ENNReal.ofReal_ne_top)]
    gcongr
  refine lt_of_le_of_lt (lintegral_mono hpos) ?_
  -- the radial bound
  set C : ℝ := (4 * Real.pi * M ^ 2) ^ T.edgeFinset.card
  have hrad : ∀ u : ι → ℂ,
      (∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (u i)))) *
        ∏ e ∈ T.edgeFinset, ENNReal.ofReal (4 * Real.pi * M ^ 2 *
          edgeMin sqPos (fun i => rho lam (u i)) e) ≤
      ENNReal.ofReal C *
        ∏ i, ENNReal.ofReal (Real.exp (β * smearedKernel χ lam (u i)) * rho lam (u i) ^ s) := by
    intro u
    have hρ : ∀ i, 0 < rho lam (u i) := fun i => rho_pos hlam _
    obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image univ (fun i => rho lam (u i)) univ_nonempty
    have hord := prod_edgeMin_le_prod_erase hT sqPos_mono sqPos_nonneg
      (fun i => rho lam (u i)) i₁
    have hord' : ∏ i ∈ univ.erase i₁, sqPos (rho lam (u i)) ≤ ∏ i, rho lam (u i) ^ s := by
      have h1 : ∏ i ∈ univ.erase i₁, sqPos (rho lam (u i)) =
          rho lam (u i₁) ^ (-(2 : ℝ)) * ∏ i, rho lam (u i) ^ (2 : ℝ) := by
        rw [← Finset.prod_erase_mul _ _ (mem_univ i₁), ← mul_assoc, mul_comm _ (∏ i ∈ _, _),
          mul_assoc, ← Real.rpow_add (hρ i₁)]
        simp only [neg_add_cancel, Real.rpow_zero, mul_one]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [sqPos_of_nonneg (hρ i).le, Real.rpow_two]
      rw [h1]
      exact prod_rpow_mul_rpow_neg_le (fun i => rho lam (u i)) hρ
        (fun i => hi₁ i (mem_univ i)) (by norm_num)
    have hEmin : ∀ e ∈ T.edgeFinset, 0 ≤ edgeMin sqPos (fun i => rho lam (u i)) e := by
      intro e _
      induction e using Sym2.ind with
      | h i j => exact sqPos_nonneg _
    rw [← ENNReal.ofReal_prod_of_nonneg (fun e he => mul_nonneg (by positivity) (hEmin e he)),
      Finset.prod_mul_distrib, Finset.prod_const,
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (Real.exp_pos _).le
        (Real.rpow_nonneg (hρ i).le _)), ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ =>
        (Real.exp_pos _).le), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.prod_mul_distrib]
    have hE : 0 ≤ ∏ i, Real.exp (β * smearedKernel χ lam (u i)) :=
      Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
    calc (∏ i, Real.exp (β * smearedKernel χ lam (u i))) *
          ((4 * Real.pi * M ^ 2) ^ T.edgeFinset.card *
            ∏ e ∈ T.edgeFinset, edgeMin sqPos (fun i => rho lam (u i)) e)
        ≤ (∏ i, Real.exp (β * smearedKernel χ lam (u i))) *
          ((4 * Real.pi * M ^ 2) ^ T.edgeFinset.card * ∏ i, rho lam (u i) ^ s) := by
          gcongr
          exact hord.trans hord'
      _ = C * ((∏ i, Real.exp (β * smearedKernel χ lam (u i))) *
            ∏ i, rho lam (u i) ^ s) := by ring
  refine lt_of_le_of_lt (lintegral_mono hrad) ?_
  have hmr : ∀ i : ι, Measurable fun t : ℂ =>
      ENNReal.ofReal (Real.exp (β * smearedKernel χ lam t) * rho lam t ^ s) := fun i =>
    ENNReal.measurable_ofReal.comp ((measurable_exp_smearedKernel hχ hlam β).mul
      ((measurable_rho lam).pow_const s))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, volume_pi,
    lintegral_pi_prod (fun _ : ι => (volume : Measure ℂ))
      (fun _ t => ENNReal.ofReal (Real.exp (β * smearedKernel χ lam t) * rho lam t ^ s)) hmr]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.prod_lt_top fun i _ =>
    lintegral_exp_mul_rpow_lt_top hχ hβ hlam hk)

end Tree

end Limits

end MultipoleBKT

end
