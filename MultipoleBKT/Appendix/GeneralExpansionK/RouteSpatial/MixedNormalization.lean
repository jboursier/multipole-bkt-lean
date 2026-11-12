/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.CommonNormalization
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceRoot

/-!
# Complete normalization of the actual mixed alternatives

See Step 3 of
the proof of Lemma A.7. The common support is used to
choose near trees. Ordinary and marked products are identified with their
activity trees before the root comparison.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases
open scoped Classical ENNReal

/-- Internal scalar cancellation of the extracted maximum-radius square. -/
theorem internal_gain_combine {R : ℝ} (hR : 0 < R) (τ v : ℝ) :
    R ^ 2 / τ ^ 2 ≤ R ^ 2 * ((τ ^ 2)⁻¹ + |v| / R ^ 2) ∧
    |v| ≤ R ^ 2 * ((τ ^ 2)⁻¹ + |v| / R ^ 2) := by
  have he : R ^ 2 * ((τ ^ 2)⁻¹ + |v| / R ^ 2) = R ^ 2 / τ ^ 2 + |v| := by
    rw [mul_add,mul_div_cancel₀ _ (pow_ne_zero 2 hR.ne')]
    rfl
  rw [he]
  exact ⟨le_add_of_nonneg_right (abs_nonneg _),le_add_of_nonneg_left (by positivity)⟩

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Internal normalization of a nonzero-support original alternative. The
root factor still contains the actual screening radius and bad correction. -/
theorem internal_paper_normalized (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {χ : ℂ → ℝ} {β lam M h A t : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (hA : 0 ≤ A)
    (τ v : ℂ × ℂ → ℝ) (Near Far : Finset (ℕ × ℕ)) (hOF : O ⊆ Far)
    (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ)
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (P : FiveSubsets (Sym2 (X.biUnion id)) (X.biUnion id))
    (hP : P ∈ fiveSubsets (symOf (X.biUnion id) O)
      (symOf (X.biUnion id) Far \ symOf (X.biUnion id) O) (RouteCases.intraEdges (Limits.blockOf X)) univ)
    (hS : clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
      (fun i : X.biUnion id => c i) ≠ 0)
    (hD : mixedDensity χ β lam h (symOf (X.biUnion id) Far) (fun i : X.biUnion id => c i) ≠ 0)
    (H : PaperPointwise hX hOX hpar (fun i => rhoD lam (c i)) (paperDistE c) (farInd M lam c)
      (fun i : X.biUnion id => τ (c i)) (fun i : X.biUnion id => v (c i))
      (paperEvenE M lam (fun i : X.biUnion id => c i)) (markedEvenE lam (fun i : X.biUnion id => c i))
      (symOf (X.biUnion id) (graphPairs Tb)) P (maxRad lam (fun i : X.biUnion id => c i))
      (A * clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
        (fun i : X.biUnion id => c i) * mixedDensity χ β lam h (symOf (X.biUnion id) Far)
        (fun i : X.biUnion id => c i)) t) :
    ∃ (T : SimpleGraph (X.biUnion id)) (_hT : T.IsTree)
      (Ao Eo : Finset (Sym2 (X.biUnion id))) (mark : Option (Sym2 (X.biUnion id))) (i : X.biUnion id),
      ENNReal.ofReal |t| ≤ ENNReal.ofReal A *
        (ENNReal.ofReal ((τ (c i) ^ 2)⁻¹ + |v (c i)| / maxRad lam (fun i : X.biUnion id => c i) ^ 2) *
          activityTree M lam h T Ao Eo mark (fun i : X.biUnion id => c i) *
            activityDensity χ β lam h (fun i : X.biUnion id => c i)) := by
  let cfg := fun i : X.biUnion id => c i
  let S := clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz cfg
  let D := mixedDensity χ β lam h (symOf (X.biUnion id) Far) cfg
  let R := maxRad lam cfg
  have hR : 0 < R := hlam.trans_le (lam_le_maxRad lam cfg)
  have hconn := connected_of_clusterSupport_ne_zero M lam (Limits.blockOf X) _ _ cfg hS
  obtain ⟨Q,hnear⟩ := exists_linked_nearTreeFamily (Limits.blockOf X) M lam cfg hconn
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  have hE : E = symOf (X.biUnion id) (graphPairs Tb) := by
    dsimp only [E]
    rw [← graphPairs_eq_edgesOf]
    apply evenEdges_eq_symOf
    exact (graphPairs_subset_pairsOn Tb).trans (pairsOn_mono (by
      rw [biUnion_coarsen (fun Y hY => subset_of_mem_relComponents (oddComponents_subset O hY))]))
  have hshort := (mixedDensity_support χ β lam h (symOf (X.biUnion id) Far) cfg hD).2
  have hodd (F : OddFamily hX hOX hpar (fun i => rhoD lam (c i))) :
      ∀ e ∈ oddEdges F, dipoleDistOn cfg e ≤ 17 * h := by
    intro e he
    exact hshort e (symOf_mono hOF (oddEdges_subset hX hOX hpar F he))
  have hroot (i : X.biUnion id) : 0 ≤ (τ (c i) ^ 2)⁻¹ + |v (c i)| / R ^ 2 := by positivity
  rcases H with ⟨F,i,hh⟩ | ⟨F,i,j,hm,hh⟩
  · let Ao := oddEdges F
    let T : SimpleGraph (X.biUnion id) := fromEdgeSet ((N ∪ (Ao ∪ E) : Finset _) : Set _)
    obtain ⟨hT,hTE,-,-,-⟩ := source_family_structure hX hOX hpar _ F Tb hTb Q
    have hn := ordinary_family_normalized hX hOX hpar hlam hM c F Tb hTb Q hnear (hodd F)
    rw [← activityTree_none_eq M lam h Ao E N T (by
      ext e
      simpa only [mem_edgeFinset] using Finset.ext_iff.mp hTE e) cfg] at hn
    refine ⟨T,hT,Ao,E,none,i,?_⟩
    have hb0 : 0 ≤ A * S * D * F.weight (paperDistE c) (farInd M lam c) *
        ∏ e ∈ E, paperEvenE M lam cfg e :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA (clusterSupport_nonneg _ _ _ _ _ _))
        (mixedDensity_nonneg _ _ _ _ _ _)) (F.weight_nonneg _ _ (farInd_nonneg c)))
        (prod_nonneg fun _ _ => paperEvenE_nonneg _ _ _ _)
    have hbound : |t| ≤ A * (S * D * (R ^ 2 * F.weight (paperDistE c) (farInd M lam c) *
        ∏ e ∈ E, paperEvenE M lam cfg e) * ((τ (c i) ^ 2)⁻¹ + |v (c i)| / R ^ 2)) := by
      rcases hh with hh | ⟨-,hh⟩
      · rw [← hE] at hh
        calc
          _ ≤ A * S * D * (R ^ 2 / τ (c i) ^ 2) * F.weight (paperDistE c) (farInd M lam c) *
              ∏ e ∈ E, paperEvenE M lam cfg e := hh
          _ = (A * S * D * F.weight (paperDistE c) (farInd M lam c) *
              ∏ e ∈ E, paperEvenE M lam cfg e) * (R ^ 2 / τ (c i) ^ 2) := by ring
          _ ≤ (A * S * D * F.weight (paperDistE c) (farInd M lam c) *
              ∏ e ∈ E, paperEvenE M lam cfg e) *
              (R ^ 2 * ((τ (c i) ^ 2)⁻¹ + |v (c i)| / R ^ 2)) :=
            mul_le_mul_of_nonneg_left (internal_gain_combine hR _ _).1 hb0
          _ = _ := by ring
      · rw [← hE] at hh
        calc
          _ ≤ A * S * D * |v (c i)| * F.weight (paperDistE c) (farInd M lam c) *
              ∏ e ∈ E, paperEvenE M lam cfg e := hh
          _ = (A * S * D * F.weight (paperDistE c) (farInd M lam c) *
              ∏ e ∈ E, paperEvenE M lam cfg e) * |v (c i)| := by ring
          _ ≤ (A * S * D * F.weight (paperDistE c) (farInd M lam c) *
              ∏ e ∈ E, paperEvenE M lam cfg e) *
              (R ^ 2 * ((τ (c i) ^ 2)⁻¹ + |v (c i)| / R ^ 2)) :=
            mul_le_mul_of_nonneg_left (internal_gain_combine hR _ _).2 hb0
          _ = _ := by ring
    have hc := internal_common_normalization χ β M lam h (Limits.blockOf X)
      (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) cfg (hroot i) hn
    exact (ENNReal.ofReal_le_ofReal hbound).trans (by
      rw [ENNReal.ofReal_mul hA]
      exact mul_le_mul' le_rfl hc)
  · have hme : s(i,j) ∈ E := hE ▸ (mem_inter.1 hm).1
    have hmf : s(i,j) ∈ symOf (X.biUnion id) Far :=
      (Finset.mem_sdiff.1 ((show P.2.1 ⊆ symOf (X.biUnion id) Far \ symOf (X.biUnion id) O from by
        exact Finset.mem_powerset.1 (Finset.mem_product.1 (Finset.mem_product.1 hP).2).1) (mem_inter.1 hm).2)).1
    let Ao := oddEdges F
    let T : SimpleGraph (X.biUnion id) := fromEdgeSet ((N ∪ (Ao ∪ E) : Finset _) : Set _)
    obtain ⟨hT,hTE,hNA,hAE,-⟩ := source_family_structure hX hOX hpar _ F Tb hTb Q
    have hn := marked_family_normalized hX hOX hpar hlam hM c F Tb hTb Q hnear (hodd F) hme (hshort _ hmf)
    rw [← activityTree_some_eq hlam M h Ao E N hNA hAE T (by
      ext e
      simpa only [mem_edgeFinset] using Finset.ext_iff.mp hTE e) hme cfg] at hn
    refine ⟨T,hT,Ao,E,some s(i,j),i,?_⟩
    rw [← hE] at hh
    have he : A * S * D * (τ (c i) ^ 2)⁻¹ * markedEvenE lam cfg s(i,j) *
        F.weight (paperDistE c) (farInd M lam c) * (∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e) =
        A * (S * D * (markedEvenE lam cfg s(i,j) * F.weight (paperDistE c) (farInd M lam c) *
          ∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e) * (τ (c i) ^ 2)⁻¹) := by ring
    have hc := internal_common_normalization χ β M lam h (Limits.blockOf X)
      (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) cfg (inv_nonneg.2 (sq_nonneg (τ (c i)))) hn
    refine (ENNReal.ofReal_le_ofReal (hh.trans_eq he)).trans ?_
    rw [ENNReal.ofReal_mul hA]
    exact mul_le_mul' le_rfl (hc.trans (mul_le_mul' (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (div_nonneg (abs_nonneg (v (c i))) (sq_nonneg R)))) le_rfl) le_rfl))

end MultipoleBKT.ExpansionK.RouteSpatial

end
