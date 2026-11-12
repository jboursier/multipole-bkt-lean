/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.Majorant
public import MultipoleBKT.Limits.RouteOdd.Assembly

/-!
# Paper-shaped majorants for singleton and multipole block systems

See (A.30),
and the averaged-integrand argument in Lemma 4.26.
Odd components are treated before selecting the even quotient tree. The one tail
is retained, with no power absorption into the individual odd kernels.
-/

@[expose] public section

namespace MultipoleBKT.Limits

open Finset SimpleGraph

variable {χ : ℂ → ℝ} {β lam M : ℝ}
variable {ι κ : Type*} [Fintype ι] [LinearOrder ι] [Fintype κ] [DecidableEq κ]

/-- The unmodified distance of the two dipoles at a label edge. -/
noncomputable def paperDistE (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => dipoleDist (c i) (c j)) fun i j => dipoleDist_comm (c i) (c j)

open scoped Classical in
/-- The paper's even majorant `b̂ = â² + 𝟙_B`, where `â` includes `𝟙_{Bᶜ}`. -/
noncomputable def paperEvenE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 1 else ahat (c i) (c j) ^ 2)
    fun i j => by
      simp only [multipoleLinked_comm]
      congr 1
      unfold ahat
      rw [dipoleDist_comm, mul_comm ‖(c i).1 - (c i).2‖, max_comm ‖(c i).1 - (c i).2‖]

open scoped Classical in
/-- The odd tree kernel `𝟙_{Bᶜ}/d²`, with no individual tail. -/
noncomputable def paperOddE (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 0 else
    (dipoleDist (c i) (c j) ^ 2)⁻¹) fun i j => by
      rw [multipoleLinked_comm, dipoleDist_comm]

omit [Fintype ι] [LinearOrder ι] in
theorem paperEvenE_nonneg (M lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    0 ≤ paperEvenE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j => show 0 ≤ ite _ _ _; split_ifs <;> positivity

omit [Fintype ι] [LinearOrder ι] in
theorem paperOddE_nonneg (M lam : ℝ) (c : ι → ℂ × ℂ) (e : Sym2 ι) :
    0 ≤ paperOddE M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j => show 0 ≤ ite _ _ _; split_ifs <;> positivity

open scoped Classical in
/-- A pointwise majorant for a connected, cut-even term on any block system.
The radii `s` are block radii, and each odd component has a maximal-radius root.
For singleton blocks take `blk = id` and `s i = rhoD lam (c i)`.
For merged multipole blocks take the maximum radius in each block.
The returned trees have actual label edges, so two-edge quotient cycles are retained.
The coefficient is uniform in `lam`, `M`, the block map and both edge families,
as required by Lemma A.5. -/
theorem exists_paper_term_le (hχ : IsMollifier χ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ M : ℝ, 1 ≤ M →
      ∀ (blk : ι → κ) (E : SimpleGraph ι),
      (∀ i j, E.Adj i j → blk i ≠ blk j) →
      (nodeGraph (Sym2.map blk) E.edgeFinset).Connected →
      ∀ F : Finset (Sym2 ι), F ⊆ E.edgeFinset → CutEven (Sym2.map blk) F →
      ∀ (c : ι → ℂ × ℂ) (s : κ → ℝ),
      (∀ S, 0 < s S) → (∀ i, rhoD lam (c i) ≤ s (blk i)) →
      ∀ R : ℝ, (∀ S, s S ≤ R) →
      ∃ (root : (nodeGraph (Sym2.map blk) F).ConnectedComponent → κ)
        (A B : Finset (Sym2 ι)),
        (∀ D, (nodeGraph (Sym2.map blk) F).connectedComponentMk (root D) = D) ∧
        (∀ D v, (nodeGraph (Sym2.map blk) F).connectedComponentMk v = D → s v ≤ s (root D)) ∧
        A ⊆ F ∧ B ⊆ E.edgeFinset \ F ∧
        (nodeGraph (Sym2.map blk) (A ∪ B)).IsTree ∧
        (∀ D : (nodeGraph (Sym2.map blk) F).ConnectedComponent,
          ((nodeGraph (Sym2.map blk) A).induce D.supp).IsTree) ∧
        (nodeGraph (Sym2.map (nodeGraph (Sym2.map blk) F).connectedComponentMk ∘ Sym2.map blk) B).IsTree ∧
        A.card + Nat.card (nodeGraph (Sym2.map blk) F).ConnectedComponent = Fintype.card κ ∧
        B.card + 1 = Nat.card (nodeGraph (Sym2.map blk) F).ConnectedComponent ∧
        (∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e| ≤
          C ^ E.edgeFinset.card *
            (∏ S ∈ univ.filter (fun S => S ∉ Set.range root), s S ^ 2) *
            globalTail R (paperDistE c) A * (∏ e ∈ A, paperOddE M lam c e) *
              ∏ e ∈ B, paperEvenE M lam c e := by
  classical
  obtain ⟨Cb, -, hCb⟩ := exists_bond_bounds hχ hβ
  let C := max Cb 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  refine ⟨C, hC1, fun lam hlam M hM blk E hEinter hconn F hFE hcut c s hs hρ R hR => ?_⟩
  let ends := Sym2.map blk
  let q := (nodeGraph ends F).connectedComponentMk
  let : Fintype (nodeGraph ends F).ConnectedComponent := Fintype.ofFinite _
  have hroots : ∀ D : (nodeGraph ends F).ConnectedComponent,
      ∃ r : κ, q r = D ∧ ∀ v, q v = D → s v ≤ s r := by
    intro D
    obtain ⟨v, hv⟩ := D.exists_rep
    obtain ⟨r, hr, hm⟩ := exists_max_image (univ.filter (fun v => q v = D)) s
      ⟨v, mem_filter.2 ⟨mem_univ _, hv⟩⟩
    exact ⟨r, (mem_filter.1 hr).2, fun v hv => hm v (mem_filter.2 ⟨mem_univ _, hv⟩)⟩
  choose root hroot hrootmax using hroots
  let a := fun e => |gammaE hχ β lam M c e| / C
  let b := fun e => |alphaE hχ β lam M c e| / C
  have ha0 : ∀ e ∈ F, 0 ≤ a e := fun e _ => div_nonneg (abs_nonneg _) hC.le
  have hb0 : ∀ e ∈ E.edgeFinset \ F, 0 ≤ b e := fun e _ => div_nonneg (abs_nonneg _) hC.le
  have hbhat : ∀ e, b e ≤ paperEvenE M lam c e ∧ paperEvenE M lam c e ≤ 1 := by
    intro e
    induction e using Sym2.ind with
    | h i j =>
      show |edgeAlpha χ β lam M (c i) (c j)| / C ≤ ite _ _ _ ∧ ite _ _ _ ≤ 1
      by_cases hn : MultipoleLinked M lam (c i) (c j)
      · simp only [ite_eq_left hn, edgeAlpha, abs_neg, abs_one]
        exact ⟨(div_le_one hC).2 hC1, le_rfl⟩
      · obtain ⟨-, ha1, -, hα⟩ := hCb lam hlam M hM (c i) (c j) hn
        simp only [ite_eq_right hn]
        refine ⟨(div_le_iff₀ hC).2 ?_, ?_⟩
        · calc |edgeAlpha χ β lam M (c i) (c j)| ≤ Cb * ahat (c i) (c j) ^ 2 := hα
            _ ≤ ahat (c i) (c j) ^ 2 * C := by
              simpa only [mul_comm] using
                mul_le_mul_of_nonneg_right (show Cb ≤ C from le_max_left _ _) (sq_nonneg (ahat (c i) (c j)))
        · nlinarith [ahat_nonneg (c i) (c j)]
  have hageom : ∀ e, a e ≤ 1 ∧ ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (lenE lam c e * max (lenE lam c e) (max (s v) (s w))) := by
    intro e
    induction e using Sym2.ind with
    | h i j =>
      have hD : 0 < lenE lam c s(i, j) := hlam.trans_le (le_max_right _ _)
      have hgeom0 : 0 ≤ s (blk i) * s (blk j) /
          (lenE lam c s(i, j) * max (lenE lam c s(i, j)) (max (s (blk i)) (s (blk j)))) := by
        have := hs (blk i); have := hs (blk j)
        positivity
      have hh : a s(i, j) ≤ 1 ∧ a s(i, j) ≤ s (blk i) * s (blk j) /
          (lenE lam c s(i, j) * max (lenE lam c s(i, j)) (max (s (blk i)) (s (blk j)))) := by
        by_cases hn : MultipoleLinked M lam (c i) (c j)
        · have hz : a s(i, j) = 0 := by simp [a, gammaE, symmLift, edgeGamma, hn]
          rw [hz]; exact ⟨zero_le_one, hgeom0⟩
        · obtain ⟨hld, ha1, hγ, -⟩ := hCb lam hlam M hM (c i) (c j) hn
          have hγ' : a s(i, j) ≤ ahat (c i) (c j) := by
            apply (div_le_iff₀ hC).2
            exact hγ.trans (by
              simpa only [mul_comm] using
                mul_le_mul_of_nonneg_right (show Cb ≤ C from le_max_left _ _) (ahat_nonneg (c i) (c j)))
          refine ⟨hγ'.trans ha1, hγ'.trans ?_⟩
          change ahat (c i) (c j) ≤ s (blk i) * s (blk j) /
            (max (dipoleDist (c i) (c j)) lam * max (max (dipoleDist (c i) (c j)) lam)
              (max (s (blk i)) (s (blk j))))
          rw [max_eq_left hld.le]
          exact div_mul_max_le (norm_nonneg _) (norm_nonneg _)
            ((le_max_left _ _).trans (hρ i)) ((le_max_left _ _).trans (hρ j)) (hlam.trans hld)
      refine ⟨hh.1, fun v w hvw => ?_⟩
      simp only [ends, Sym2.map_mk] at hvw
      rcases Sym2.eq_iff.1 hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hh.2
      · simpa only [mul_comm (s (blk i)), max_comm (s (blk i))] using hh.2
  have hloop : ∀ e ∈ F, ¬ (ends e).IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | h i j => exact Sym2.mk_isDiag_iff.not.2 (hEinter i j (mem_edgeFinset.1 (hFE he)))
  obtain ⟨A, hAF, B, hBE, hT, hAT, hBT, -, hAc, hBc, hbound⟩ :=
    separate_trees_singleTail ends hFE hloop hcut hconn root hroot s hs hR (lenE lam c) a b
      (fun e _ => by induction e using Sym2.ind with | h i j => exact hlam.trans_le (le_max_right _ _))
      ha0 (fun e _ => (hageom e).1) (fun e _ => (hageom e).2) hb0 (fun e _ => (hbhat e).1.trans (hbhat e).2)
  refine ⟨root, A, B, hroot, hrootmax, hAF, hBE, hT, hAT, hBT, hAc, hBc, ?_⟩
  have hscale : (∏ e ∈ E.edgeFinset \ F, |alphaE hχ β lam M c e|) * ∏ e ∈ F, |gammaE hχ β lam M c e| =
      C ^ E.edgeFinset.card * ((∏ e ∈ F, a e) * ∏ e ∈ E.edgeFinset \ F, b e) := by
    have hcard := card_sdiff_add_card_eq_card hFE
    rw [← hcard, pow_add, ← prod_const, ← prod_const]
    dsimp [a, b]
    rw [prod_div_distrib, prod_div_distrib]
    field_simp
  rw [hscale]
  by_cases hpos : 0 < ∏ e ∈ F, a e
  · have hodd : ∀ e ∈ A, paperOddE M lam c e = (lenE lam c e ^ 2)⁻¹ := by
      intro e he
      induction e using Sym2.ind with
      | h i j =>
        have hn : ¬ MultipoleLinked M lam (c i) (c j) := by
          intro hn
          have hz : a s(i, j) = 0 := by simp [a, gammaE, symmLift, edgeGamma, hn]
          have := prod_eq_zero (hAF he) hz
          linarith
        obtain ⟨hld, -⟩ := hCb lam hlam M hM (c i) (c j) hn
        change ite _ _ _ = (max (dipoleDist (c i) (c j)) lam ^ 2)⁻¹
        rw [ite_eq_right hn, max_eq_left hld.le]
    have hlength : ∀ e ∈ A, lenE lam c e = paperDistE c e := by
      intro e he
      induction e using Sym2.ind with
      | h i j =>
        have hn : ¬ MultipoleLinked M lam (c i) (c j) := by
          intro hn
          have hz : a s(i, j) = 0 := by simp [a, gammaE, symmLift, edgeGamma, hn]
          have := prod_eq_zero (hAF he) hz
          linarith
        have hd := (hCb lam hlam M hM (c i) (c j) hn).1
        exact max_eq_left hd.le
    have htail : globalTail R (lenE lam c) A = globalTail R (paperDistE c) A := by
      apply fold_congr
      intro e he
      rw [hlength e he]
    rw [htail] at hbound
    have heven : ∏ e ∈ B, b e ≤ ∏ e ∈ B, paperEvenE M lam c e :=
      prod_le_prod₀ (fun e he => hb0 e (hBE he)) fun e _ => (hbhat e).1
    have hoddprod := prod_congr rfl hodd
    rw [← hoddprod] at hbound
    have hbound' : (∏ e ∈ F, a e) * ∏ e ∈ E.edgeFinset \ F, b e ≤
        ((∏ S ∈ univ.filter (fun S => S ∉ Set.range root), s S ^ 2) *
          globalTail R (paperDistE c) A * ∏ e ∈ A, paperOddE M lam c e) * ∏ e ∈ B, b e := by
      convert hbound using 1
      simp [sdiff_eq_filter]
    have hnon : 0 ≤ (∏ S ∈ univ.filter (fun S => S ∉ Set.range root), s S ^ 2) *
        globalTail R (paperDistE c) A * ∏ e ∈ A, paperOddE M lam c e :=
      mul_nonneg (mul_nonneg (prod_nonneg fun S _ => sq_nonneg _) (globalTail_nonneg _ _ _))
        (prod_nonneg fun e _ => paperOddE_nonneg _ _ _ _)
    calc C ^ E.edgeFinset.card * ((∏ e ∈ F, a e) * ∏ e ∈ E.edgeFinset \ F, b e)
        ≤ C ^ E.edgeFinset.card *
          (((∏ S ∈ univ.filter (fun S => S ∉ Set.range root), s S ^ 2) *
            globalTail R (paperDistE c) A * ∏ e ∈ A, paperOddE M lam c e) * ∏ e ∈ B, b e) := by
              exact mul_le_mul_of_nonneg_left hbound' (pow_nonneg hC.le _)
      _ ≤ C ^ E.edgeFinset.card *
          (((∏ S ∈ univ.filter (fun S => S ∉ Set.range root), s S ^ 2) *
            globalTail R (paperDistE c) A * ∏ e ∈ A, paperOddE M lam c e) *
              ∏ e ∈ B, paperEvenE M lam c e) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left heven hnon) (pow_nonneg hC.le _)
      _ = _ := by
        simp only [mul_assoc]
        congr 3
        simp [ends]

  · have hz : ∏ e ∈ F, a e = 0 := le_antisymm (le_of_not_gt hpos) (prod_nonneg ha0)
    rw [hz, zero_mul, mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hC.le _)
      (prod_nonneg fun S _ => sq_nonneg _)) (globalTail_nonneg _ _ _))
      (prod_nonneg fun e _ => paperOddE_nonneg _ _ _ _))
      (prod_nonneg fun e _ => paperEvenE_nonneg _ _ _ _)

end MultipoleBKT.Limits

end
