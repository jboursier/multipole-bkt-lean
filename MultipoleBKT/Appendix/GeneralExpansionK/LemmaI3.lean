/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.TailIntegral
public import MultipoleBKT.Appendix.SmallIntegral.IntDipole
import MultipoleBKT.Appendix.GeneralExpansionK.RouteAssembly.DipoleTail

/-!
# Lemma A.8 by the direct dipole tail argument

See Lemma A.8. The cutoff difference is the integral of the unchanged
connected dipole product against its radial cutoff complement. This factor
is reversal invariant. Split near and far bonds, average the merged parts,
and use the separate odd and even trees. Spatial integration retains the
joint odd tail and the logarithms. The three radial regimes then give
(A.64). Finally sum over the finitely many connected graphs.

The statement includes every positive epsilon. Monotonicity of
the cutoff complement reduces that stronger range to `min epsilon 1`.
The empty and singleton cases have no connected graph with a nonempty edge.
-/

@[expose] public section

namespace MultipoleBKT

namespace ExpansionK

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open Limits SmallIntegral BoundedLower Appendix

variable {χ : ℂ → ℝ} {β lam M : ℝ}

/-! ### The cutoff factor -/

section Cut

variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The radial cutoff `∏_i 𝟙_{|x_i - y_i| ≤ h}`. -/
noncomputable def cutInd (h : ℝ) (c : ι → ℂ × ℂ) : ℝ :=
  ∏ i, if ‖(c i).1 - (c i).2‖ ≤ h then 1 else 0

theorem cutInd_nonneg (h : ℝ) (c : ι → ℂ × ℂ) : 0 ≤ cutInd h c := by
  classical
  exact prod_nonneg fun i _ => by split_ifs <;> norm_num

theorem cutInd_le_one (h : ℝ) (c : ι → ℂ × ℂ) : cutInd h c ≤ 1 := by
  classical
  exact prod_le_one₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by split_ifs <;> norm_num

theorem measurable_cutInd (h : ℝ) : Measurable (cutInd (ι := ι) h) := by
  classical
  unfold cutInd
  refine Finset.measurable_prod _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le ((continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable.comp
    (measurable_pi_apply i)) measurable_const

theorem cutInd_flip [DecidableEq ι] (h : ℝ) (B : Finset ι) (c : ι → ℂ × ℂ) :
    cutInd h (flipCfg B c) = cutInd h c := by
  classical
  unfold cutInd
  refine prod_congr rfl fun i _ => ?_
  rw [flipCfg_apply]
  split_ifs <;> simp_all [norm_sub_rev]

end Cut

/-! ### The dipole integrals with a radial cutoff -/

open scoped Classical in
/-- **The dipole integral with a radial cutoff** `I_{dip,ε₀}(V; E)` ((A.28), `ε₀ ∈ (0, 1)`):
`∫_{(Λ²)^{|V|}} ∏_{ij ∈ E} f_ij^v ∏_{i ∈ V} e^{β g_λ(x_i - y_i)} 𝟙_{r_i ≤ ε₀ R̄} dx_i dy_i`. -/
noncomputable def dipoleIntegralCut (χ : ℂ → ℝ) (N p₀ : ℕ) (β lam ε₀ : ℝ) (V : Finset ℕ)
    (E : SimpleGraph V) : ℝ :=
  ∫ c in boxConfig V N, dipoleActivityIntegrand χ β lam E c * (∏ i, pairDensity χ β lam (c i)) *
    cutInd (ε₀ * truncationScale p₀ β lam) c

/-! ### The crude bond bound for finite-box integrability -/

section Parity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The bond constant `e^{β C}` of `MultipoleBKT.abs_dipoleBond_sub_one_le`. -/
noncomputable def dipBondExp (hχ : IsMollifier χ) (_hβ0 : 0 ≤ β) : ℝ :=
  Real.exp (β * Classical.choose (abs_dipoleBond_sub_one_le hχ))

end Parity

/-! ### Lemma A.8 -/

section Direct

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [Nonempty ι]

omit [LinearOrder ι] [Nonempty ι] in
/-- The strict radial support used in the written proof of Lemma A.8. -/
theorem one_sub_cutInd_strict {h : ℝ} (c : ι → ℂ × ℂ) :
    1 - cutInd h c ≤ {c : ι → ℂ × ℂ | h < maxRad lam c}.indicator 1 c := by
  classical
  by_cases hall : ∀ i, ‖(c i).1 - (c i).2‖ ≤ h
  · have he : cutInd h c = 1 := prod_eq_one fun i _ => by rw [ite_eq_left (hall i)]
    rw [he,sub_self]
    exact indicator_nonneg (fun _ _ => zero_le_one) _
  · push Not at hall
    obtain ⟨i,hi⟩ := hall
    have hm : h < maxRad lam c := hi.trans_le
      ((le_max_left _ _).trans (rhoD_le_maxRad lam c i))
    rw [indicator_of_mem (show c ∈ {c : ι → ℂ × ℂ | h < maxRad lam c} from hm),Pi.one_apply]
    linarith [cutInd_nonneg h c]

/-- The near/far expansion and merged reversals give the direct case-F bound
for one connected dipole graph. The cutoff complement keeps strict support. -/
theorem abs_integral_dipBox_cut_log_le (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ)
    (hι : 2 ≤ Fintype.card ι) (hk : (Fintype.card ι : ℕ∞) ≤ pStar β)
    (E : SimpleGraph ι) (hE : E.Connected) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ min eps 1 → ∀ N : ℕ,
      |∫ c in boxConfig ι N, dipBox χ β lam E c *
        (1 - cutInd (eps * truncationScale p₀ β lam) c)| ≤
      C*N*lam^((2-β)*Fintype.card ι)*truncationScale p₀ β lam^(-2 : ℝ) := by
  classical
  let e := min eps 1
  have he : 0 < e := lt_min heps one_pos
  have hterm := fun E' hE' => RouteAssembly.dipSym_tail_bound hχ hβ p₀ hι hk E hE
    (E' := E') hE' he (min_le_right eps 1)
  choose! A hA ha using hterm
  refine ⟨∑ E' ∈ E.edgeFinset.powerset, A E',sum_nonneg (fun E' hE' => hA E' hE'),?_⟩
  intro lam hlam hle N
  let h := eps * truncationScale p₀ β lam
  let h' := e * truncationScale p₀ β lam
  have hcut1 : ∀ c : ι → ℂ × ℂ, |1-cutInd h c| ≤ 1 := fun c => by
    rw [abs_le]
    constructor <;> linarith [cutInd_nonneg h c,cutInd_le_one h c]
  obtain ⟨B,hB⟩ := exists_abs_dipTerm_le (M := 30) hχ (by linarith : 0 ≤ β) hlam E
  have hint (E') (hE' : E' ∈ E.edgeFinset.powerset) : IntegrableOn
      (fun c => dipTerm χ β lam 30 E E' c * (1-cutInd h c)) (boxConfig ι N) :=
    integrableOn_boxConfig_of_bounded (F := fun c => dipTerm χ β lam 30 E E' c * (1-cutInd h c))
      ((measurable_dipTerm hχ hlam β 30 E E').mul (measurable_const.sub (measurable_cutInd h)))
      (fun c => by
        rw [abs_mul]
        exact (mul_le_mul (hB E' hE' c) (hcut1 c) (abs_nonneg _)
          ((abs_nonneg _).trans (hB E' hE' c))).trans_eq (mul_one B)) N
  have hF (E') (hE' : E' ∈ E.edgeFinset.powerset) :
      |∫ c in boxConfig ι N, dipTerm χ β lam 30 E E' c * (1-cutInd h c)| ≤
        A E'*N*lam^((2-β)*Fintype.card ι)*truncationScale p₀ β lam^(-2 : ℝ) := by
    have hm : Measurable (fun c => dipTerm χ β lam 30 E E' c * (1-cutInd h c)) :=
      (measurable_dipTerm hχ hlam β 30 E E').mul
      (measurable_const.sub (measurable_cutInd h))
    have hb : ∀ c : ι → ℂ × ℂ, |dipTerm χ β lam 30 E E' c * (1-cutInd h c)| ≤ B := fun c => by
      rw [abs_mul]
      exact (mul_le_mul (hB E' hE' c) (hcut1 c) (abs_nonneg _)
        ((abs_nonneg _).trans (hB E' hE' c))).trans_eq (mul_one B)
    have havg := integral_boxConfig_avg_flip (blkOf E E') hm hb N
    have hs (c : ι → ℂ × ℂ) :
        (∑ U : Finset (nearPart E E').ConnectedComponent,
          dipTerm χ β lam 30 E E' (flipCfg (blockLabels (blkOf E E') U) c) *
            (1-cutInd h (flipCfg (blockLabels (blkOf E E') U) c))) /
          2^Fintype.card (nearPart E E').ConnectedComponent =
          dipSym χ β lam 30 E E' c * (1-cutInd h c) := by
      simp_rw [cutInd_flip]
      unfold dipSym
      rw [← sum_mul,div_mul_eq_mul_div]
    simp_rw [hs] at havg
    rw [← havg,← Real.norm_eq_abs]
    refine (norm_integral_le_lintegral_norm _).trans ?_
    apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg
      (mul_nonneg (mul_nonneg (hA E' hE') (Nat.cast_nonneg _)) (Real.rpow_nonneg hlam.le _))
      (Real.rpow_nonneg (truncationScale_pos hlam).le _))
    have htail : MeasurableSet {c : ι → ℂ × ℂ | h' < maxRad lam c} :=
      measurableSet_lt measurable_const (measurable_maxRad lam)
    have hp (c : ι → ℂ × ℂ) : ENNReal.ofReal ‖dipSym χ β lam 30 E E' c * (1-cutInd h c)‖ ≤
        {c : ι → ℂ × ℂ | h' < maxRad lam c}.indicator
          (fun c => ENNReal.ofReal |dipSym χ β lam 30 E E' c|) c := by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by linarith [cutInd_le_one h c] : 0 ≤ 1-cutInd h c)]
      by_cases hc : h' < maxRad lam c
      · rw [indicator_of_mem (show c ∈ {c : ι → ℂ × ℂ | h' < maxRad lam c} from hc)]
        exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (abs_nonneg _) (by linarith [cutInd_nonneg h c]))
      · rw [indicator_of_notMem (show c ∉ {c : ι → ℂ × ℂ | h' < maxRad lam c} from hc)]
        have hhh : h' ≤ h := mul_le_mul_of_nonneg_right (min_le_left eps 1)
          (truncationScale_pos hlam).le
        have hsup := one_sub_cutInd_strict (lam := lam) (h := h) c
        rw [indicator_of_notMem (show c ∉ {c : ι → ℂ × ℂ | h < maxRad lam c} from
          fun hh => hc (hhh.trans_lt hh))] at hsup
        have hz : 1-cutInd h c = 0 := le_antisymm hsup (by linarith [cutInd_le_one h c])
        rw [hz,mul_zero,ENNReal.ofReal_zero]
    calc
      _ ≤ ∫⁻ c in boxConfig ι N, {c : ι → ℂ × ℂ | h' < maxRad lam c}.indicator
          (fun c => ENNReal.ofReal |dipSym χ β lam 30 E E' c|) c := lintegral_mono hp
      _ = ∫⁻ c in boxConfig ι N ∩ {c : ι → ℂ × ℂ | h' < maxRad lam c},
          ENNReal.ofReal |dipSym χ β lam 30 E E' c| := by
        rw [lintegral_indicator htail,Measure.restrict_restrict htail,Set.inter_comm]
      _ ≤ _ := ha E' hE' lam hlam hle N
  have hsum : (∫ c in boxConfig ι N, dipBox χ β lam E c * (1-cutInd h c)) =
      ∑ E' ∈ E.edgeFinset.powerset, ∫ c in boxConfig ι N,
        dipTerm χ β lam 30 E E' c * (1-cutInd h c) := by
    simp_rw [dipBox_eq_sum (M := 30),sum_mul]
    exact integral_finsetSum _ hint
  rw [hsum,sum_mul,sum_mul,sum_mul]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum hF)

end Direct

open scoped Classical in
/-- `I_{dip,ε₀}(V; E) - I_{dip,∞}(V; E) = -∫ dipBox (1 - ∏ 𝟙_{r_i ≤ ε₀ R̄})`. -/
theorem dipoleIntegralCut_sub (hχ : IsMollifier χ) (hβ0 : 0 ≤ β) (hlam : 0 < lam) (N p₀ : ℕ)
    (ε₀ : ℝ) (V : Finset ℕ) (E : SimpleGraph V) :
    dipoleIntegralCut χ N p₀ β lam ε₀ V E - dipoleIntegral χ N β lam V E =
      -∫ c in boxConfig V N, dipBox χ β lam E c * (1 - cutInd (ε₀ * truncationScale p₀ β lam) c) := by
  set h := ε₀ * truncationScale p₀ β lam
  obtain ⟨B, hB⟩ := exists_abs_dipTerm_le (M := 1) hχ hβ0 hlam E
  have hint : ∀ E' ∈ E.edgeFinset.powerset, ∀ g : (V → ℂ × ℂ) → ℝ, Measurable g →
      (∀ c, |g c| ≤ 1) → IntegrableOn (fun c => dipTerm χ β lam 1 E E' c * g c)
        (boxConfig V N) := fun E' hE' g hg hg1 =>
    integrableOn_boxConfig_of_bounded (F := fun c => dipTerm χ β lam 1 E E' c * g c)
      ((measurable_dipTerm hχ hlam β 1 E E').mul hg) (fun c => by
        rw [abs_mul]
        exact (mul_le_mul (hB E' hE' c) (hg1 c) (abs_nonneg _)
          ((abs_nonneg _).trans (hB E' hE' c))).trans_eq (mul_one B)) N
  have hboxint : ∀ g : (V → ℂ × ℂ) → ℝ, Measurable g → (∀ c, |g c| ≤ 1) →
      IntegrableOn (fun c => dipBox χ β lam E c * g c) (boxConfig V N) := by
    intro g hg hg1
    have : (fun c => dipBox χ β lam E c * g c) =
        fun c => ∑ E' ∈ E.edgeFinset.powerset, dipTerm χ β lam 1 E E' c * g c := by
      funext c
      rw [dipBox_eq_sum (M := 1), Finset.sum_mul]
    rw [this]
    exact integrable_finsetSum _ fun E' hE' => hint E' hE' g hg hg1
  have hcutm := measurable_cutInd (ι := V) h
  have hcut1 : ∀ c : V → ℂ × ℂ, |cutInd h c| ≤ 1 := fun c => by
    rw [abs_of_nonneg (cutInd_nonneg h c)]; exact cutInd_le_one h c
  have h1 := hboxint (cutInd h) hcutm hcut1
  have h2 := hboxint (fun _ => 1) measurable_const (fun _ => by norm_num)
  simp only [mul_one] at h2
  have hcut : dipoleIntegralCut χ N p₀ β lam ε₀ V E =
      ∫ c in boxConfig V N, dipBox χ β lam E c * cutInd h c := rfl
  rw [hcut, dipoleIntegral_eq_dipBox, ← integral_sub h1 h2, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
  simp only
  ring

open scoped Classical in
/-- The cutoff dipole integral is preserved by an order isomorphism of labels. -/
theorem dipoleIntegralCut_congr_orderIso {V W : Finset ℕ} (e : V ≃o W) (E : SimpleGraph V)
    (N p₀ : ℕ) (eps : ℝ) :
    dipoleIntegralCut χ N p₀ β lam eps V E =
      dipoleIntegralCut χ N p₀ β lam eps W (Equiv.simpleGraph e.toEquiv E) := by
  unfold dipoleIntegralCut
  rw [← integral_boxConfig_comp_equiv e.toEquiv]
  refine setIntegral_congr_fun (measurableSet_boxConfig N) fun c _ => ?_
  unfold dipoleActivityIntegrand
  apply congrArg₂ (· * ·)
  · apply congrArg₂ (· * ·)
    · refine Fintype.prod_equiv e.toEquiv _ _ fun i => ?_
      refine Fintype.prod_equiv e.toEquiv _ _ fun j => ?_
      simp only [Equiv.simpleGraph_apply,SimpleGraph.comap_adj,RelIso.coe_fn_toEquiv,
        e.lt_iff_lt,OrderIso.coe_symm_toEquiv,OrderIso.symm_apply_apply]
    · exact Fintype.prod_equiv e.toEquiv _ _ fun i => by
        simp only [RelIso.coe_fn_toEquiv,OrderIso.coe_symm_toEquiv,OrderIso.symm_apply_apply]
  · unfold cutInd
    exact Fintype.prod_equiv e.toEquiv _ _ fun i => by
      simp only [RelIso.coe_fn_toEquiv,OrderIso.coe_symm_toEquiv,OrderIso.symm_apply_apply]

open scoped Classical in
/-- **Lemma A.8**: for `β > 2`, `|V| = k ≤ p*(β)` and
`ε₀ ∈ (0, 1)`, there are `C > 0` and `λ₀ > 0` (depending on `χ, β, k, ε₀, p₀`) such that for
`0 < λ ≤ λ₀` and every `N`,
`|∑_{E ∈ 𝒢_c(V)} (I_{dip,ε₀}(V; E) - I_{dip,∞}(V; E))| ≤ C N λ^{(2-β)k} R̄_{β,λ}^{-2}`. -/
theorem lemma_I3 (hχ : IsMollifier χ) (hβ : 2 < β) (p₀ : ℕ) {k : ℕ} (hk : (k : ℕ∞) ≤ pStar β)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam₀ →
      ∀ (N : ℕ) (V : Finset ℕ), V.card = k →
        |∑ E ∈ (univ : Finset (SimpleGraph V)).filter (fun E => E.Connected ∧ E.edgeSet.Nonempty),
            (dipoleIntegralCut χ N p₀ β lam ε₀ V E - dipoleIntegral χ N β lam V E)| ≤
          C * N * lam ^ ((2 - β) * k) * truncationScale p₀ β lam ^ (-(2 : ℝ)) := by
  let W := range k
  have hW : W.card = k := card_range k
  have hterm : ∀ E₀ ∈ (univ : Finset (SimpleGraph W)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty),
      ∃ A : ℝ, 0 ≤ A ∧ ∀ lam : ℝ, 0 < lam → lam ≤ min ε₀ 1 → ∀ N : ℕ,
      |dipoleIntegralCut χ N p₀ β lam ε₀ W E₀ - dipoleIntegral χ N β lam W E₀| ≤
        A*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ) := by
    intro E₀ hE₀
    obtain ⟨hconn,hedge⟩ := (mem_filter.mp hE₀).2
    have : Nonempty W := hconn.nonempty
    obtain ⟨i,j,hij⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp (SimpleGraph.edgeSet_nonempty.mp hedge)
    have hW2 : 2 ≤ Fintype.card W := Fintype.one_lt_card_iff.mpr ⟨i,j,hij.ne⟩
    obtain ⟨A,hA,ha⟩ := abs_integral_dipBox_cut_log_le hχ hβ p₀ hW2
      (by rwa [Fintype.card_coe,hW]) E₀ hconn hε₀
    refine ⟨A,hA,fun lam hlam hle N => ?_⟩
    rw [dipoleIntegralCut_sub hχ (by linarith : 0 ≤ β) hlam,abs_neg]
    simpa only [Fintype.card_coe,hW] using ha lam hlam hle N
  choose! A hA ha using hterm
  let Atot := ∑ E₀ ∈ (univ : Finset (SimpleGraph W)).filter
    (fun E => E.Connected ∧ E.edgeSet.Nonempty), A E₀
  have hAtot : 0 ≤ Atot := sum_nonneg fun E₀ hE₀ => hA E₀ hE₀
  refine ⟨(2 : ℝ)^(k*k)*(Atot+1),mul_pos (pow_pos (by norm_num) _) (by linarith),
    min ε₀ 1,lt_min hε₀ one_pos,?_⟩
  intro lam hlam hle N V hV
  have hp : 0 ≤ (N : ℝ)*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hlam.le _))
      (Real.rpow_nonneg (truncationScale_pos hlam).le _)
  have hE : ∀ E ∈ (univ : Finset (SimpleGraph V)).filter
      (fun E => E.Connected ∧ E.edgeSet.Nonempty),
      |dipoleIntegralCut χ N p₀ β lam ε₀ V E - dipoleIntegral χ N β lam V E| ≤
        (Atot+1)*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ) := by
    intro E hEmem
    have hconn := (mem_filter.mp hEmem).2.1
    let e : V ≃o W := (V.orderIsoOfFin hV).symm.trans (W.orderIsoOfFin hW)
    let E₀ := Equiv.simpleGraph e.toEquiv E
    have hiso : E ≃g E₀ := { toEquiv := e.toEquiv, map_rel_iff' := by intro a b; simp [E₀] }
    have hE₀ : E₀ ∈ (univ : Finset (SimpleGraph W)).filter
        (fun E => E.Connected ∧ E.edgeSet.Nonempty) := by
      refine mem_filter.mpr ⟨mem_univ _,hiso.connected_iff.mp hconn,?_⟩
      obtain ⟨i,j,hij⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp
        (SimpleGraph.edgeSet_nonempty.mp (mem_filter.mp hEmem).2.2)
      exact SimpleGraph.edgeSet_nonempty.mpr (SimpleGraph.ne_bot_iff_exists_adj.mpr
        ⟨e i,e j,by
          change E.Adj (e.symm (e i)) (e.symm (e j))
          simpa only [OrderIso.symm_apply_apply] using hij⟩)
    rw [dipoleIntegralCut_congr_orderIso e E,dipoleIntegral_congr_orderIso e E]
    refine (ha E₀ hE₀ lam hlam hle N).trans ?_
    have hAle : A E₀ ≤ Atot+1 := (single_le_sum (f := A) (fun F hF => hA F hF) hE₀).trans (by linarith)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hAle hp
  calc
    _ ≤ ∑ E ∈ (univ : Finset (SimpleGraph V)).filter
        (fun E => E.Connected ∧ E.edgeSet.Nonempty),
        |dipoleIntegralCut χ N p₀ β lam ε₀ V E - dipoleIntegral χ N β lam V E| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _E ∈ (univ : Finset (SimpleGraph V)).filter
        (fun E => E.Connected ∧ E.edgeSet.Nonempty),
        (Atot+1)*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ) := sum_le_sum hE
    _ ≤ (2 : ℝ)^(k*k)*((Atot+1)*N*lam^((2-β)*k)*truncationScale p₀ β lam^(-2 : ℝ)) := by
      rw [sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by
        simpa only [mul_assoc] using mul_nonneg (by linarith : 0 ≤ Atot+1) hp)
      have hc : ((univ : Finset (SimpleGraph V)).filter
          (fun E => E.Connected ∧ E.edgeSet.Nonempty)).card ≤ 2^(k*k) := by
        refine (card_filter_le _ _).trans ?_
        rw [card_univ,← hV,← Fintype.card_coe]
        exact card_simpleGraph_le
      exact_mod_cast hc
    _ = _ := by ring

end ExpansionK

end MultipoleBKT

end
