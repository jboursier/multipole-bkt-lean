/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.Profiles

/-!
# Exterior even-edge integration with the unbounded odd family

See Lemma A.7. Deleting the long mark leaves
a coupled odd family. The endpoint-sector estimate integrates all coordinates.
-/

@[expose] public section

namespace MultipoleBKT.ExpansionK.RouteOmitted

open MeasureTheory Set Finset SimpleGraph Multipole Hierarchical Parity Peeling Limits
open SmallIntegral SmallIntegral.RouteJ SmallIntegral.RouteJext UpperBound.BoundedUpper RouteCases RouteSpatial
open scoped Classical ENNReal

/-- The exterior even alternative has the same inverse-square cutoff and
radial logarithm as the omitted odd alternative. -/
theorem lintegral_even_tree {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W],
      Fintype.card W ≤ k+1 → ∀ (T : SimpleGraph W), T.IsTree →
      ∀ (A E N : Finset (Sym2 W)), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ m ∈ E,
      ∀ (root : W) (u : W → ℂ) (lam H : ℝ),
      0 < lam → (∀ i, rho lam (u i) ≤ H) → ∀ n : ℕ,
      (∫⁻ x : W → ℂ, (TwoComponentCoulomb.box n).indicator 1 (x root) *
        omittedTree M lam H A E N (some m) (ofPosVec x u)) ≤
        ENNReal.ofReal (C * n / H ^ 2 * (1 + Real.log (H / minRho lam u)) ^ k) := by
  obtain ⟨C,hC,hb⟩ := lintegral_long_endpoint_tree hM k
  refine ⟨C,hC,?_⟩
  intro W _ _ _ hW T hT A E N hpart hA hEN m hm root u lam H hlam hu n
  have hmT : m ∈ T.edgeFinset := by rw [← hpart]; exact mem_union_right _ (mem_union_left _ hm)
  let mark : T.edgeFinset := ⟨m,hmT⟩
  let I := {e : T.edgeFinset // e ≠ mark}
  let f : I → T.edgeFinset.erase m := fun e => ⟨e.val.val,mem_erase.2
    ⟨fun he => e.property (Subtype.ext he),e.val.property⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      have hv : i.val.val = j.val.val := congrArg (fun e : T.edgeFinset.erase m => e.val) he
      exact Subtype.ext (Subtype.ext hv)
    · intro e
      refine ⟨⟨⟨e.val,(mem_erase.1 e.property).2⟩,?_⟩,rfl⟩
      intro he
      exact (mem_erase.1 e.property).1 (congrArg Subtype.val he)
  let eqv := Equiv.ofBijective f hf
  let s := edgeMin id (fun i => rho lam (u i))
  let t := radMax (fun i => rho lam (u i))
  let odd (e : I) := e.val.val ∈ A
  let ev (e : {e : I // ¬odd e}) : Bool := if e.val.val.val ∈ E.erase m then true else false
  have hmA : m ∉ A := fun ha => Finset.disjoint_left.1 hA ha (mem_union_left _ hm)
  have hmN : m ∉ N := fun hn => Finset.disjoint_left.1 hEN hm hn
  have hpart' : A ∪ (E.erase m ∪ N) = T.edgeFinset.erase m := by
    rw [← hpart]
    ext e
    simp only [Finset.mem_union,mem_erase]
    constructor
    · rintro (ha | ⟨hne,he⟩ | hn)
      · exact ⟨fun heq => hmA (heq ▸ ha),Or.inl ha⟩
      · exact ⟨hne,Or.inr (Or.inl he)⟩
      · exact ⟨fun heq => hmN (heq ▸ hn),Or.inr (Or.inr hn)⟩
    · rintro ⟨hne,ha | he | hn⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ⟨hne,he⟩)
      · exact Or.inr (Or.inr hn)
  have hA' := hA.mono_right (union_subset_union (erase_subset m E) (Subset.refl N))
  have hEN' := hEN.mono_left (erase_subset m E)
  have heq (x : W → ℂ) : omittedTree M lam H A E N (some m) (ofPosVec x u) =
      mixedDistanceProfile odd ev (fun e => s e.val.val) (fun e => t e.val.val)
        M (minRho lam u) (maxRho lam u) (fun e => dipoleDistOn (ofPosVec x u) e.val) *
          longEvenProfile 1 1 H (dipoleDistOn (ofPosVec x u) m) := by
    dsimp only [omittedTree]
    rw [minRad_ofPosVec_eq,maxRad_ofPosVec_eq]
    have hr : (fun i => rhoD lam (ofPosVec x u i)) = fun i => rho lam (u i) := by
      funext i
      simp only [ofPosVec_apply,rhoD_mk]
    rw [hr,distanceFamily_reindex (T.edgeFinset.erase m) A (E.erase m) N hpart' hA' hEN' eqv]
    exact mul_comm _ _
  simp_rw [heq]
  have ha := minRho_pos hlam u
  have haR : minRho lam u ≤ maxRho lam u :=
    (minRho_le_rho lam u root).trans (rho_le_maxRho lam u root)
  have hH : 0 < H := (rho_pos hlam (u root)).trans_le (hu root)
  have hst (e : {e : I // ¬odd e}) :
      minRho lam u ≤ s e.val.val ∧ s e.val.val ≤ t e.val.val ∧ t e.val.val ≤ maxRho lam u := by
    induction e.val.val.val using Sym2.ind with
    | h i j => exact ⟨le_min (minRho_le_rho lam u i) (minRho_le_rho lam u j),min_le_max,
        max_le (rho_le_maxRho lam u i) (rho_le_maxRho lam u j)⟩
  have hs := hb W hW T hT root u mark odd ev _ _ _ _ H ha haR hH hst n
  refine hs.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ C*n/H^2)
  apply pow_le_pow_left₀
  · have := Real.log_nonneg ((one_le_div ha).2 haR)
    linarith
  · have hRH : maxRho lam u ≤ H := (fold_max_le _).2 ⟨(le_max_right _ _).trans (hu root),fun i _ => hu i⟩
    exact add_le_add_right (Real.log_le_log (div_pos (maxRho_pos hlam u) ha)
      (div_le_div_of_nonneg_right hRH ha.le)) 1

/-- Both original alternatives share one spatial estimate before radial absorption. -/
theorem lintegral_omittedTree {M : ℝ} (hM : 1 ≤ M) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W],
      Fintype.card W ≤ k+1 → ∀ (T : SimpleGraph W), T.IsTree →
      ∀ (A E N : Finset (Sym2 W)), A ∪ (E ∪ N) = T.edgeFinset →
      Disjoint A (E ∪ N) → Disjoint E N → ∀ mark : Option (Sym2 W),
      (∀ m, mark = some m → m ∈ E) → ∀ (root : W) (u : W → ℂ) (lam H : ℝ),
      0 < lam → (∀ i, rho lam (u i) ≤ H) → ∀ n : ℕ,
      (∫⁻ x : W → ℂ, (TwoComponentCoulomb.box n).indicator 1 (x root) *
        omittedTree M lam H A E N mark (ofPosVec x u)) ≤
        ENNReal.ofReal (C * n / H ^ 2 * (1 + Real.log (H / minRho lam u)) ^ k) := by
  obtain ⟨A,hA,ha⟩ := lintegral_odd_tree hM k
  obtain ⟨B,hB,hb⟩ := lintegral_even_tree hM k
  refine ⟨A+B,add_pos hA hB,?_⟩
  intro W _ _ _ hW T hT Ao E N hpart hAo hEN mark hm root u lam H hlam hu n
  have ha0 := minRho_pos hlam u
  have hH : 0 < H := (rho_pos hlam (u root)).trans_le (hu root)
  have hL : 0 ≤ 1 + Real.log (H/minRho lam u) := by
    have := Real.log_nonneg ((one_le_div ha0).2 ((minRho_le_rho lam u root).trans (hu root)))
    linarith
  cases mark with
  | none =>
    exact (ha W hW T hT Ao E N hpart hAo hEN root u lam H hlam hu n).trans
      (ENNReal.ofReal_le_ofReal (by gcongr; exact le_add_of_nonneg_right hB.le))
  | some m =>
    exact (hb W hW T hT Ao E N hpart hAo hEN m (hm m rfl) root u lam H hlam hu n).trans
      (ENNReal.ofReal_le_ofReal (by gcongr; exact le_add_of_nonneg_left hA.le))

end MultipoleBKT.ExpansionK.RouteOmitted

end
