/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.RouteExchange.Choices

/-!
# Measurable events for the two exchangeability identities

The paper: (5.60) and (5.61). We retain the profile while fixing the bad labels, then fix
the good partition. The latter event implies the profile by its block counts.
-/

@[expose] public section

open MeasureTheory Finset
open TwoComponentCoulomb (box)

namespace MultipoleBKT.UpperBound.RouteExchange

open Hierarchical Multipole SetPartition TheoremTwo PropFiveFortyFive

variable {N p₀ : ℕ} {β lam M ε₀ : ℝ}

private noncomputable def blocksOf (G : SimpleGraph (Fin N)) (good : Finset (Fin N)) :
    Finset (Finset ℕ) := by
  classical
  exact (univ.filter fun C : G.ConnectedComponent => C.supp ⊆ ↑good).image
    (fun C => (univ.filter fun i => G.connectedComponentMk i = C).map Fin.valEmbedding)

private theorem fiberMeasurable_goodBlocks :
    FiberMeasurable (goodBlocks p₀ β lam M ε₀ : (Fin N → ℂ × ℂ) → _) := by
  classical
  let F := fun (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) => blocksOf
    (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (matchedBy σ c i) (matchedBy σ c j))
    (goodPoints p₀ β lam M ε₀ (matchedBy σ c))
  refine FiberMeasurable.of_cover (fun σ : Equiv.Perm (Fin N) => {c | stableMatching c = σ}) F
    measurableSet_stableMatching_eq (fun c => ⟨stableMatching c, rfl⟩) ?_ ?_
  · intro σ c hc
    change stableMatching c = σ at hc
    have hm : matched c = matchedBy σ c := by
      unfold matched
      rw [hc]
    change blocksOf (SimpleGraph.fromRel fun i j =>
      MultipoleLinked M lam (matched c i) (matched c j))
      (goodPoints p₀ β lam M ε₀ (matched c)) = _
    rw [hm]

  · intro σ
    have hL : FiberMeasurable fun c (i j : Fin N) =>
        decide (MultipoleLinked M lam (matchedBy σ c i) (matchedBy σ c j)) :=
      FiberMeasurable.pi fun i => FiberMeasurable.pi fun j => fiberMeasurable_decide
        (measurable_matchedBy σ (measurableSet_setOf_multipoleLinked M lam i j))
    have hB := fiberMeasurable_badPoints (measurable_matchedBy σ) p₀ β lam M ε₀
    refine (hL.prodMk hB).of_factor fun c d h => ?_
    have hG : (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (matchedBy σ c i) (matchedBy σ c j)) =
        (SimpleGraph.fromRel fun i j => MultipoleLinked M lam (matchedBy σ d i) (matchedBy σ d j)) := by
      have hL' : ∀ i j, MultipoleLinked M lam (matchedBy σ c i) (matchedBy σ c j) ↔
          MultipoleLinked M lam (matchedBy σ d i) (matchedBy σ d j) := by
        intro i j
        have hij := congrFun (congrFun (congrArg Prod.fst h) i) j
        simpa only [decide_eq_decide] using hij
      ext i j
      simp only [SimpleGraph.fromRel_adj, hL']
    change blocksOf _ (univ \ badPoints p₀ β lam M ε₀ (matchedBy σ c)) =
      blocksOf _ (univ \ badPoints p₀ β lam M ε₀ (matchedBy σ d))
    have hBd := congrArg Prod.snd h
    dsimp only at hBd
    rw [hG, hBd]

/-- The identity-matching event with the prescribed good profile. -/
def profileEvent (p₀ : ℕ) (β lam M ε₀ : ℝ) (n : Fin (pBeta p₀ β) → ℕ) :
    Set (Fin N → ℂ × ℂ) :=
  {c | stableMatching c = Equiv.refl _ ∧
    ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i}

/-- Fix the bad labels within the profile event. -/
def badEvent (p₀ : ℕ) (β lam M ε₀ : ℝ) (n : Fin (pBeta p₀ β) → ℕ)
    (V : Finset (Fin N)) : Set (Fin N → ℂ × ℂ) :=
  profileEvent p₀ β lam M ε₀ n ∩ {c | badPoints p₀ β lam M ε₀ c = V}

/-- Fix both the bad labels and the exact good-multipole partition. -/
def choiceEvent (p₀ : ℕ) (β lam M ε₀ : ℝ) (V : Finset (Fin N)) (π : Finset (Finset ℕ)) :
    Set (Fin N → ℂ × ℂ) :=
  {c | stableMatching c = Equiv.refl _ ∧ badPoints p₀ β lam M ε₀ c = V ∧
    goodBlocks p₀ β lam M ε₀ c = π}

theorem measurableSet_profileEvent (n : Fin (pBeta p₀ β) → ℕ) :
    MeasurableSet (profileEvent p₀ β lam M ε₀ n : Set (Fin N → ℂ × ℂ)) := by
  have h := (measurableSet_stableMatching_eq (N := N) (Equiv.refl _)).inter
    ((fiberMeasurable_goodBlocks (p₀ := p₀) (β := β) (lam := lam) (M := M) (ε₀ := ε₀)).comp
      (blockCount (pBeta p₀ β)) n)
  convert h using 1
  ext c
  simp only [profileEvent, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [funext_iff]
  simp only [blockCount_goodBlocks]

theorem measurableSet_badEvent (n : Fin (pBeta p₀ β) → ℕ) (V : Finset (Fin N)) :
    MeasurableSet (badEvent p₀ β lam M ε₀ n V) :=
  (measurableSet_profileEvent n).inter (fiberMeasurable_badPoints measurable_id p₀ β lam M ε₀ V)

theorem measurableSet_choiceEvent (V : Finset (Fin N)) (π : Finset (Finset ℕ)) :
    MeasurableSet (choiceEvent p₀ β lam M ε₀ V π) :=
  (measurableSet_stableMatching_eq (Equiv.refl _)).inter
    ((fiberMeasurable_badPoints measurable_id p₀ β lam M ε₀ V).inter
      (fiberMeasurable_goodBlocks π))

/-- The fixed partition implies its profile and lies in the frozen event used
for the energy bound and Tonelli integration. -/
theorem choiceEvent_subset {V : Finset (Fin N)} {π : Finset (Finset ℕ)}
    {n : Fin (pBeta p₀ β) → ℕ} (hπ : π ∈ choices V (pBeta p₀ β) n) :
    choiceEvent p₀ β lam M ε₀ V π ⊆
      badEvent p₀ β lam M ε₀ n V ∩ frozenEvent p₀ β lam M ε₀ V π := by
  classical
  intro c hc
  obtain ⟨hσ, hV, hπc⟩ := hc
  have hn : ∀ i : Fin (pBeta p₀ β), goodMultipoleCount p₀ β lam M ε₀ c ((i : ℕ) + 1) = n i := by
    intro i
    rw [← blockCount_goodBlocks, hπc]
    exact congrFun (mem_filter.1 hπ).2.2 i
  refine ⟨⟨⟨hσ, hn⟩, hV⟩, hσ, hV, ?_, ?_⟩
  · intro S hS
    exact connOn_goodBlocks hσ (hπc ▸ hS)
  · intro q hq
    exact not_linked_of_mem_interPairs_goodBlocks hσ (hπc ▸ hq)

/-- The bad-label fibers partition the profile event. -/
theorem profileEvent_eq_union (hM : 0 ≤ M) (n : Fin (pBeta p₀ β) → ℕ) :
    (profileEvent p₀ β lam M ε₀ n : Set (Fin N → ℂ × ℂ)) =
      ⋃ V ∈ (univ : Finset (Fin N)).powersetCard
        (N - ∑ i : Fin (pBeta p₀ β), ((i : ℕ) + 1) * n i), badEvent p₀ β lam M ε₀ n V := by
  classical
  ext c
  constructor
  · intro hc
    exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨(mem_frozenEvent hM hc.1 hc.2).1, hc, rfl⟩⟩
  · intro hc
    obtain ⟨V, hc⟩ := Set.mem_iUnion.1 hc
    obtain ⟨-, hc⟩ := Set.mem_iUnion.1 hc
    exact hc.1

/-- With bad labels fixed, the good-partition fibers partition the profile event. -/
theorem badEvent_eq_union (hM : 0 ≤ M) (n : Fin (pBeta p₀ β) → ℕ) (V : Finset (Fin N)) :
    badEvent p₀ β lam M ε₀ n V =
      ⋃ π ∈ choices V (pBeta p₀ β) n, choiceEvent p₀ β lam M ε₀ V π := by
  classical
  ext c
  constructor
  · rintro ⟨hc, hV⟩
    have hπ := (mem_frozenEvent hM hc.1 hc.2).2.1
    rw [hV] at hπ
    exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨hπ, hc.1, hV, rfl⟩⟩
  · intro hc
    obtain ⟨π, hc⟩ := Set.mem_iUnion.1 hc
    obtain ⟨hπ, hc⟩ := Set.mem_iUnion.1 hc
    exact (choiceEvent_subset hπ hc).1

end MultipoleBKT.UpperBound.RouteExchange

end
