/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Transport

/-!
# Both original omitted alternatives with common factors

See Lemma A.7. Nonzero block support supplies
the near trees. Each original alternative enters the fixed finite envelope.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

variable {X : Finset (Finset ℕ)} {O : Finset (ℕ × ℕ)}

/-- Internal assembly of the two pointwise alternatives. All common-factor zero
branches are removed before selecting and normalizing the near trees. -/
theorem internal_boundary_envelope (hX : IsSubpartition X) (hOX : O ⊆ interPairs X)
    (hpar : IsParityPair X O ∅) [Nonempty (X.biUnion id)] {χ : ℂ → ℝ} {β lam M h A t : ℝ}
    (hlam : 0 < lam) (hM : 1 ≤ M) (hlh : lam ≤ h) (hA : 0 ≤ A)
    (Near Far : Finset (ℕ × ℕ)) (Dz : Finset (Sym2 (X.biUnion id))) (c : ℕ → ℂ × ℂ)
    (Tb : SimpleGraph ((coarsen X (oddComponents X O)).biUnion id))
    (hTb : IsRelTree₀ (coarsen X (oddComponents X O)) Tb)
    (H : OmittedPointwise hX hOX hpar lam M (17*h) c (graphPairs Tb)
      (A * clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz
        (fun i : X.biUnion id => c i) * omittedDensity χ β lam h (symOf (X.biUnion id) Far)
        (fun i : X.biUnion id => c i)) t) :
    ENNReal.ofReal |t| ≤ ENNReal.ofReal A * omittedEnvelope χ β M lam h (fun i : X.biUnion id => c i) := by
  let cfg := fun i : X.biUnion id => c i
  let S := clusterSupport M lam (Limits.blockOf X) (symOf (X.biUnion id) Near) Dz cfg
  let D := omittedDensity χ β lam h (symOf (X.biUnion id) Far) cfg
  have hzero (ht : t = 0) : ENNReal.ofReal |t| ≤ ENNReal.ofReal A * omittedEnvelope χ β M lam h cfg := by
    rw [ht,abs_zero,ENNReal.ofReal_zero]
    exact bot_le
  by_cases hS : S = 0
  · apply hzero
    have hz : A*S*D = 0 := by rw [hS,mul_zero,zero_mul]
    change OmittedPointwise hX hOX hpar lam M (17*h) c (graphPairs Tb) (A*S*D) t at H
    rw [hz] at H
    exact internal_zero H
  by_cases hD : D = 0
  · apply hzero
    have hz : A*S*D = 0 := by rw [hD,mul_zero]
    change OmittedPointwise hX hOX hpar lam M (17*h) c (graphPairs Tb) (A*S*D) t at H
    rw [hz] at H
    exact internal_zero H
  have hcut : ∀ i, ‖(cfg i).1-(cfg i).2‖ ≤ h := by
    rcases cutInd_eq_one_or h cfg with hc | hc
    · exact hc.2
    · exact False.elim (hD (by dsimp only [D,omittedDensity]; rw [hc,mul_zero,zero_mul]))
  have hRh := maxRad_le_of_cut hlh cfg hcut
  have hh : 0 < h := hlam.trans_le hlh
  have hRH : maxRad lam cfg ≤ 17*h := hRh.trans (by linarith)
  obtain ⟨Q,hnear⟩ := exists_linked_nearTreeFamily (Limits.blockOf X) M lam cfg
    (connected_of_clusterSupport_ne_zero M lam (Limits.blockOf X) _ _ cfg hS)
  let E := (graphOf (X.biUnion id) (edgesOf Tb)).edgeFinset
  let N := nearForest (Limits.blockOf X) (fun S => (Q S).val)
  have hTP : graphPairs Tb ⊆ pairsOn (X.biUnion id) :=
    (graphPairs_subset_pairsOn Tb).trans (pairsOn_mono (by
      rw [biUnion_coarsen (fun Y hY => subset_of_mem_relComponents (oddComponents_subset O hY))]))
  have hE : E = symOf (X.biUnion id) (graphPairs Tb) := by
    dsimp only [E]
    rw [← graphPairs_eq_edgesOf]
    exact evenEdges_eq_symOf _ hTP
  have hprod : (∏ p ∈ graphPairs Tb, paperEvenE M lam c s(p.1,p.2)) =
      ∏ e ∈ E, paperEvenE M lam cfg e := by
    rw [hE]
    exact prod_symOf hTP _ _ (fun _ _ _ => rfl)
  have hshape (F : OddFamily hX hOX hpar (fun i => rhoD lam (c i))) :
      ∃ s : JointShape (X.biUnion id), s.odd = oddEdges F ∧ s.even = E ∧ s.near = N := by
    let Ao := oddEdges F
    let T : SimpleGraph (X.biUnion id) := fromEdgeSet ((N ∪ (Ao ∪ E) : Finset _) : Set _)
    obtain ⟨hT,hTE,hNA,hAE,-⟩ := source_family_structure hX hOX hpar _ F Tb hTb Q
    have hTE' : T.edgeFinset = N ∪ (Ao ∪ E) := hTE
    have hpart : Ao ∪ (E ∪ N) = T.edgeFinset := by
      rw [hTE']
      ac_rfl
    have hpart' : Ao ∪ (E ∪ N) = @SimpleGraph.edgeFinset _ T
        (@SimpleGraph.fintypeEdgeSet _ T _ (fun a b => Classical.propDecidable (T.Adj a b))) := by
      ext e
      simpa only [mem_edgeFinset] using Finset.ext_iff.mp hpart e
    exact ⟨⟨T,Ao,E,N,hT,hpart',
      Finset.disjoint_union_right.2 ⟨hAE,(Finset.disjoint_union_right.1 hNA).1.symm⟩,
      (Finset.disjoint_union_right.1 hNA).2.symm⟩,rfl,rfl,rfl⟩
  have hfinish (z : ℝ) (s : OmittedChoice (X.biUnion id))
      (hb : |t| ≤ A*(S*D*z))
      (hn : ENNReal.ofReal z ≤ ENNReal.ofReal (∏ i : X.biUnion id, rhoD lam (c i)^2) *
        omittedTree M lam (17*h) s.shape.odd s.shape.even s.shape.near s.mark cfg) :
      ENNReal.ofReal |t| ≤ ENNReal.ofReal A * omittedEnvelope χ β M lam h cfg := by
    have hc := RouteOmitted.internal_common_normalization χ β M lam h (Limits.blockOf X)
      (symOf (X.biUnion id) Near) Dz (symOf (X.biUnion id) Far) cfg hn
    refine (ENNReal.ofReal_le_ofReal hb).trans ?_
    rw [ENNReal.ofReal_mul hA]
    exact mul_le_mul' le_rfl (hc.trans (le_omittedEnvelope χ β M lam h s cfg))
  rcases H with ⟨F,hb⟩ | ⟨F,p,hp,hlong,hb⟩
  · obtain ⟨s,hsA,hsE,hsN⟩ := hshape F
    let q : OmittedChoice (X.biUnion id) := ⟨s,none,by intro m hm; cases hm⟩
    have hn := odd_family_normalized hX hOX hpar hlam hM (by positivity : 0 < 17*h) c F Tb hTb hRH Q hnear
    rw [hprod] at hb
    refine hfinish (F.weight (paperDistE c) (farInd M lam c) *
      min (maxRad lam cfg^2/(17*h)^2) (globalTail (maxRad lam cfg) (paperDistE c) F.edges) *
        ∏ e ∈ E, paperEvenE M lam cfg e) q ?_ ?_
    · exact hb.trans_eq (by dsimp only [S,D,cfg]; ring)
    · simpa only [q,hsA,hsE,hsN] using hn
  · have hpV := mem_pairsOn.1 (hTP hp)
    let i : X.biUnion id := ⟨p.1,hpV.1⟩
    let j : X.biUnion id := ⟨p.2,hpV.2.1⟩
    have hij : i < j := hpV.2.2
    have hm : s(i,j) ∈ E := by rw [hE]; exact mem_symOf.2 ⟨i,j,hij,hp,rfl⟩
    have hprod' : (∏ q ∈ (graphPairs Tb).erase p, paperEvenE M lam c s(q.1,q.2)) =
        ∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e := by
      rw [prod_symOf ((erase_subset p _).trans hTP) _ (paperEvenE M lam cfg) (fun _ _ _ => rfl)]
      rw [show p = ((i:ℕ),(j:ℕ)) from Prod.ext rfl rfl,symOf_erase _ hij,← hE]
    obtain ⟨s,hsA,hsE,hsN⟩ := hshape F
    let q : OmittedChoice (X.biUnion id) := ⟨s,some s(i,j),by
      intro m he
      have he' : s(i,j) = m := Option.some.inj he
      rw [← he',hsE]
      exact hm⟩
    have hn := even_family_normalized hX hOX hpar hlam hM c F Tb hTb Q hnear hm hlong
    rw [hprod'] at hb
    refine hfinish ((rhoD lam (c i)^2*rhoD lam (c j)^2/dipoleDist (c i) (c j)^4) *
      F.weight (paperDistE c) (farInd M lam c) * globalTail (maxRad lam cfg) (paperDistE c) F.edges *
        ∏ e ∈ E.erase s(i,j), paperEvenE M lam cfg e) q ?_ ?_
    · exact hb.trans_eq (by dsimp only [S,D,cfg,i,j,paperDistE]; simp only [symmLift_mk]; ring)
    · simpa only [q,hsA,hsE,hsN] using hn

end MultipoleBKT.ExpansionK.RouteOmitted

end
