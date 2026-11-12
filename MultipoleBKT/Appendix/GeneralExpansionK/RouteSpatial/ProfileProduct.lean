/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.Support

/-!
# Identifying the separated marked product with the activity tree

See (A.62)
and Step 3 of the proof of Lemma A.7. Delete the even mark before splitting the
remaining product into near, odd and even edges.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteSpatial

open MeasureTheory Set Finset SimpleGraph Limits Peeling SmallIntegral
open SmallIntegral.RouteJ SmallIntegral.RouteJext
open scoped Classical ENNReal

variable {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]

/-- Normalizing the marked kernel removes its endpoint squares. -/
theorem markedProfile_eq {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (h d : ℝ) :
    markedProfile s t h d =
      (Iic (17 * h)).indicator (fun d => (d * max d (max s t))⁻¹) d := by
  unfold markedProfile RouteCases.markedEvenKernel
  by_cases hd : d ∈ Iic (17 * h)
  · rw [indicator_of_mem hd,indicator_of_mem hd]
    field_simp
  · rw [indicator_of_notMem hd,indicator_of_notMem hd]

/-- Ordinary activityTree is exactly the retained three-family cutTree. -/
theorem activityTree_none_eq (M lam h : ℝ) (A E N : Finset (Sym2 W))
    (T : SimpleGraph W) (hT : T.edgeFinset = N ∪ (A ∪ E))
    (c : W → ℂ × ℂ) : activityTree M lam h T A E none c = cutTree M lam h A E N c := by
  unfold activityTree cutTree activityProfile
  rw [hT]

/-- The separated marked product is the selected activityTree, including
both endpoint radii and every remaining near, odd and even profile. -/
theorem activityTree_some_eq {lam : ℝ} (hlam : 0 < lam) (M h : ℝ)
    (A E N : Finset (Sym2 W)) (hNA : Disjoint N (A ∪ E)) (hAE : Disjoint A E)
    (T : SimpleGraph W) (hT : T.edgeFinset = N ∪ (A ∪ E))
    {i j : W} (hm : s(i,j) ∈ E) (c : W → ℂ × ℂ) :
    activityTree M lam h T A E (some s(i,j)) c =
      ENNReal.ofReal (markedProfile (rhoD lam (c i)) (rhoD lam (c j)) h (dipoleDist (c i) (c j))) *
        ((∏ e ∈ A, ENNReal.ofReal (oddProfile (minRad lam c) h (dipoleDistOn c e))) *
          ((∏ e ∈ E.erase s(i,j), ENNReal.ofReal (edgeProfile true M lam c e)) *
            ∏ e ∈ N, ENNReal.ofReal (nearE M lam c e))) := by
  have hmA : s(i,j) ∉ A := fun ha => Finset.disjoint_left.1 hAE ha hm
  have hmN : s(i,j) ∉ N := fun hn => Finset.disjoint_left.1 hNA hn (mem_union_right _ hm)
  have hmT : s(i,j) ∈ T.edgeFinset := by rw [hT]; exact mem_union_right _ (mem_union_right _ hm)
  unfold activityTree
  rw [← mul_prod_erase T.edgeFinset _ hmT]
  have hmark : activityProfile A E (some s(i,j)) M lam h (vectors c) s(i,j) (dipoleDistOn c s(i,j)) =
      markedProfile (rhoD lam (c i)) (rhoD lam (c j)) h (dipoleDist (c i) (c j)) := by
    simp only [activityProfile,markedCutProfile,ite_true,edgeMin_mk,radMax_mk,id_eq,dipoleDistOn_mk]
    have hi : rho lam (vectors c i) = rhoD lam (c i) := by unfold rho rhoD vectors; rw [norm_sub_rev]
    have hj : rho lam (vectors c j) = rhoD lam (c j) := by unfold rho rhoD vectors; rw [norm_sub_rev]
    rw [hi,hj,markedProfile_eq (lt_min (rhoD_pos hlam _) (rhoD_pos hlam _))
      (lt_max_of_lt_left (rhoD_pos hlam _)),markedProfile_eq (rhoD_pos hlam _) (rhoD_pos hlam _),max_eq_right (min_le_max)]
  rw [hmark]
  congr 1
  have herase : T.edgeFinset.erase s(i,j) = N ∪ (A ∪ E.erase s(i,j)) := by
    rw [hT]
    ext e
    simp only [mem_erase]
    aesop
  have hprod : (∏ e ∈ T.edgeFinset.erase s(i,j), ENNReal.ofReal
      (activityProfile A E (some s(i,j)) M lam h (vectors c) e (dipoleDistOn c e))) =
      cutTree M lam h A (E.erase s(i,j)) N c := by
    unfold cutTree
    rw [herase]
    apply prod_congr rfl
    intro e he
    have hem : e ≠ s(i,j) := by
      intro heq
      subst e
      simp only [Finset.mem_union,mem_erase,ne_eq,not_true_eq_false,false_and,or_false] at he
      exact he.elim hmN hmA
    simp only [activityProfile,markedCutProfile,ite_eq_right hem]
    rw [cutProfile_of_config,cutProfile_of_config]
    by_cases hea : e ∈ A
    · rw [ite_eq_left hea,ite_eq_left hea]
    · rw [ite_eq_right hea,ite_eq_right hea]
      simp only [mem_erase,hem,ne_eq,not_false_eq_true,true_and]
  rw [hprod,cutTree_split M lam h A (E.erase s(i,j)) N
    (hNA.mono_right (Finset.union_subset_union (Finset.Subset.refl _) (erase_subset _ _))) (hAE.mono_right (erase_subset _ _)) c]

end MultipoleBKT.ExpansionK.RouteSpatial

end
