/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremTwo.MeasurableClustering
public import MultipoleBKT.Main.TheoremTwo.GoodPoints
public import MultipoleBKT.Matching.Measurable
public import MultipoleBKT.Gibbs.Activities

/-!
# Measurability of the number of bad points

`c ↦ |I_bad(c)|` is measurable on configurations `c : Fin N → ℂ × ℂ`, with the bad points of
Definitions 5.2–5.5 computed on the
matched dipoles `(x_i, y_{σ_N(i)})` (`MultipoleBKT.TheoremTwo.measurable_card_badPoints`).

* `I^1_bad` is a function of the long dipoles and of the two clusterings, which are measurable
  (`MultipoleBKT.TheoremTwo.fiberMeasurable_clustering`).
* `I^2_bad` depends on the configuration only through `I^1_bad` and the relation `↔`
  (`badPointsTypeTwo_congr`); `I^3_bad` only through `I^1_bad`, `I^2_bad`, `↔` and the relation
  `d_ij ≤ M max(r_i, λ)` (`badPointsTypeThree_congr`). These finitely many relations are
  measurable.
* The stable matching `σ_N` is constant on the measurable sets `{σ_N = σ}`
  (`MultipoleBKT.measurableSet_stableMatching_eq`), on which the matched dipoles are a
  continuous function of the configuration.

This is the measurability needed to use Proposition 5.43 (`MultipoleBKT.TheoremTwo.master_upper`).
-/

@[expose] public section

open MeasureTheory Set

namespace MultipoleBKT

namespace TheoremTwo

variable {N : ℕ}

/-! ### Type 1 -/

theorem biUnion_filter_fst {q : ℕ} (S : Finset (Finset (Fin N) × ℝ)) :
    (S.filter fun Sτ => Sτ.1.card = q + 1).biUnion Prod.fst =
      ((S.image Prod.fst).filter fun T => T.card = q + 1).biUnion id := by
  classical
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image, id]
  constructor
  · rintro ⟨Sτ, ⟨hS, hc⟩, hi⟩
    exact ⟨Sτ.1, ⟨⟨Sτ, hS, rfl⟩, hc⟩, hi⟩
  · rintro ⟨T, ⟨⟨Sτ, hS, rfl⟩, hc⟩, hi⟩
    exact ⟨Sτ, ⟨hS, hc⟩, hi⟩

section General

variable {α : Type*} [MeasurableSpace α] {d : α → Fin N → ℂ × ℂ}

theorem measurable_dipole_fst (hd : Measurable d) (i : Fin N) : Measurable fun a => (d a i).1 :=
  ((measurable_pi_apply i).comp hd).fst

theorem measurable_dipole_snd (hd : Measurable d) (i : Fin N) : Measurable fun a => (d a i).2 :=
  ((measurable_pi_apply i).comp hd).snd

theorem measurable_dipole_length (hd : Measurable d) (i : Fin N) :
    Measurable fun a => ‖(d a i).1 - (d a i).2‖ :=
  ((measurable_dipole_fst hd i).sub (measurable_dipole_snd hd i)).norm

/-- `I^1_bad` from the long dipoles `L` and the two sets of clusters `X`, `Y`. -/
def typeOneOf (q : ℕ) (x : Finset (Fin N) × Finset (Finset (Fin N)) × Finset (Finset (Fin N))) :
    Finset (Fin N) :=
  (x.1 ∪ (x.2.1.filter fun T => T.card = q + 1).biUnion id) ∪
    (x.1 ∪ (x.2.2.filter fun T => T.card = q + 1).biUnion id)

open scoped Classical in
theorem badPointsTypeOne_eq (p₀ : ℕ) (β lam ε₀ : ℝ) (d : Fin N → ℂ × ℂ) :
    badPointsTypeOne p₀ β lam ε₀ d = typeOneOf (clusterThreshold p₀ β)
      ((Finset.univ.filter fun i => ε₀ * truncationScale p₀ β lam < ‖(d i).1 - (d i).2‖),
        (sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
          (fun i => (d i).1) (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).image Prod.fst,
        (sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
          (fun i => (d i).2) (fun i => ‖(d i).1 - (d i).2‖) Finset.univ).image Prod.fst) := by
  unfold badPointsTypeOne typeOneOf
  simp only []
  rw [biUnion_filter_fst, biUnion_filter_fst]

open scoped Classical in
theorem fiberMeasurable_badPointsTypeOne (hd : Measurable d) (p₀ : ℕ) (β lam ε₀ : ℝ) :
    FiberMeasurable fun a => badPointsTypeOne p₀ β lam ε₀ (d a) := by
  have hr := measurable_dipole_length hd
  have hL : FiberMeasurable fun a =>
      Finset.univ.filter fun i => ε₀ * truncationScale p₀ β lam < ‖(d a i).1 - (d a i).2‖ :=
    fiberMeasurable_filter _ fun i => measurableSet_lt measurable_const (hr i)
  have hX := fiberMeasurable_clustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
    (z := fun a i => (d a i).1) (r := fun a i => ‖(d a i).1 - (d a i).2‖)
    (measurable_dipole_fst hd) hr Finset.univ
  have hY := fiberMeasurable_clustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
    (z := fun a i => (d a i).2) (r := fun a i => ‖(d a i).1 - (d a i).2‖)
    (measurable_dipole_snd hd) hr Finset.univ
  have h := (hL.prodMk (hX.prodMk hY)).comp (typeOneOf (clusterThreshold p₀ β))
  intro B
  have hset : {a | badPointsTypeOne p₀ β lam ε₀ (d a) = B} =
      {a | typeOneOf (clusterThreshold p₀ β)
        ((Finset.univ.filter fun i => ε₀ * truncationScale p₀ β lam < ‖(d a i).1 - (d a i).2‖),
          (sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
            (fun i => (d a i).1) (fun i => ‖(d a i).1 - (d a i).2‖) Finset.univ).image Prod.fst,
          (sameSignClustering (clusterThreshold p₀ β) (ε₀ * truncationScale p₀ β lam)
            (fun i => (d a i).2) (fun i => ‖(d a i).1 - (d a i).2‖) Finset.univ).image
              Prod.fst) = B} := by
    ext a
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, badPointsTypeOne_eq]
  rw [hset]
  exact h B

end General

/-! ### Types 2 and 3 -/

theorem multipoleClassOn_congr {M lam : ℝ} {d e : Fin N → ℂ × ℂ}
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j))
    (U : Finset (Fin N)) (i : Fin N) :
    multipoleClassOn M lam d U i = multipoleClassOn M lam e U i := by
  have hG : (SimpleGraph.fromRel fun a b : Fin N =>
      a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (d a) (d b)) =
      SimpleGraph.fromRel fun a b : Fin N =>
        a ∈ U ∧ b ∈ U ∧ MultipoleLinked M lam (e a) (e b) := by
    ext a b
    simp only [SimpleGraph.fromRel_adj, hL]
  unfold multipoleClassOn
  rw [hG]

theorem badPointsTypeTwo_congr {p₀ : ℕ} {β lam M ε₀ : ℝ} {d e : Fin N → ℂ × ℂ}
    (h1 : badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e)
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j)) :
    badPointsTypeTwo p₀ β lam M ε₀ d = badPointsTypeTwo p₀ β lam M ε₀ e := by
  have hcls : multipoleClassOn M lam d = multipoleClassOn M lam e :=
    funext fun U => funext fun i => multipoleClassOn_congr hL U i
  unfold badPointsTypeTwo
  rw [h1, hcls]

theorem badPointsTypeThree_congr {p₀ : ℕ} {β lam M ε₀ : ℝ} {d e : Fin N → ℂ × ℂ}
    (h1 : badPointsTypeOne p₀ β lam ε₀ d = badPointsTypeOne p₀ β lam ε₀ e)
    (hL : ∀ i j, MultipoleLinked M lam (d i) (d j) ↔ MultipoleLinked M lam (e i) (e j))
    (hnear : ∀ j l, min (min ‖(d j).1 - (d l).1‖ ‖(d j).1 - (d l).2‖)
        (min ‖(d j).2 - (d l).1‖ ‖(d j).2 - (d l).2‖) ≤ M * max ‖(d j).1 - (d j).2‖ lam ↔
      min (min ‖(e j).1 - (e l).1‖ ‖(e j).1 - (e l).2‖)
        (min ‖(e j).2 - (e l).1‖ ‖(e j).2 - (e l).2‖) ≤ M * max ‖(e j).1 - (e j).2‖ lam) :
    badPointsTypeThree p₀ β lam M ε₀ d = badPointsTypeThree p₀ β lam M ε₀ e := by
  have h2 := badPointsTypeTwo_congr (M := M) h1 hL
  have hcls : multipoleClassOn M lam d = multipoleClassOn M lam e :=
    funext fun U => funext fun i => multipoleClassOn_congr hL U i
  unfold badPointsTypeThree
  simp only [h1, h2, hcls, hnear]

section General

variable {α : Type*} [MeasurableSpace α] {d : α → Fin N → ℂ × ℂ}

open scoped Classical in
/-- **The bad points have measurable fibres** (for a measurable family of dipole
configurations). -/
theorem fiberMeasurable_badPoints (hd : Measurable d) (p₀ : ℕ) (β lam M ε₀ : ℝ) :
    FiberMeasurable fun a => badPoints p₀ β lam M ε₀ (d a) := by
  have h1 := fiberMeasurable_badPointsTypeOne hd p₀ β lam ε₀
  have hL : FiberMeasurable fun a (i j : Fin N) =>
      decide (MultipoleLinked M lam (d a i) (d a j)) :=
    FiberMeasurable.pi fun i => FiberMeasurable.pi fun j => fiberMeasurable_decide
      (hd (measurableSet_setOf_multipoleLinked M lam i j))
  have hnear : FiberMeasurable fun a (j l : Fin N) =>
      decide (min (min ‖(d a j).1 - (d a l).1‖ ‖(d a j).1 - (d a l).2‖)
        (min ‖(d a j).2 - (d a l).1‖ ‖(d a j).2 - (d a l).2‖) ≤
          M * max ‖(d a j).1 - (d a j).2‖ lam) := by
    refine FiberMeasurable.pi fun j => FiberMeasurable.pi fun l => fiberMeasurable_decide ?_
    have hx := measurable_dipole_fst hd
    have hy := measurable_dipole_snd hd
    refine measurableSet_le ?_ (measurable_const.mul ((measurable_dipole_length hd j).max
      measurable_const))
    exact ((((hx j).sub (hx l)).norm.min ((hx j).sub (hy l)).norm).min
      (((hy j).sub (hx l)).norm.min ((hy j).sub (hy l)).norm))
  refine (h1.prodMk (hL.prodMk hnear)).of_factor fun a b hab => ?_
  simp only [Prod.mk.injEq] at hab
  obtain ⟨hI1, hLab, hNab⟩ := hab
  have hLiff : ∀ i j, MultipoleLinked M lam (d a i) (d a j) ↔
      MultipoleLinked M lam (d b i) (d b j) := fun i j => by
    have := congrFun (congrFun hLab i) j
    simpa only [decide_eq_decide] using this
  have hNiff : ∀ j l, min (min ‖(d a j).1 - (d a l).1‖ ‖(d a j).1 - (d a l).2‖)
        (min ‖(d a j).2 - (d a l).1‖ ‖(d a j).2 - (d a l).2‖) ≤
          M * max ‖(d a j).1 - (d a j).2‖ lam ↔
      min (min ‖(d b j).1 - (d b l).1‖ ‖(d b j).1 - (d b l).2‖)
        (min ‖(d b j).2 - (d b l).1‖ ‖(d b j).2 - (d b l).2‖) ≤
          M * max ‖(d b j).1 - (d b j).2‖ lam := fun j l => by
    have := congrFun (congrFun hNab j) l
    simpa only [decide_eq_decide] using this
  unfold badPoints
  rw [hI1, badPointsTypeTwo_congr (M := M) hI1 hLiff,
    badPointsTypeThree_congr hI1 hLiff hNiff]

end General

/-! ### The matched dipoles -/

/-- The dipoles `(x_i, y_{σ(i)})` for a fixed permutation `σ`. -/
abbrev matchedBy (σ : Equiv.Perm (Fin N)) (c : Fin N → ℂ × ℂ) : Fin N → ℂ × ℂ :=
  fun i => ((c i).1, (c (σ i)).2)

theorem measurable_matchedBy (σ : Equiv.Perm (Fin N)) :
    Measurable fun c : Fin N → ℂ × ℂ => matchedBy σ c :=
  measurable_pi_iff.mpr fun i =>
    ((measurable_pi_apply i).fst).prodMk ((measurable_pi_apply (σ i)).snd)

/-- **Measurability of the number of bad points**: `c ↦ |I_bad(c)|`, computed on the matched
dipoles `(x_i, y_{σ_N(i)})`, is measurable. -/
theorem measurable_card_badPoints (p₀ : ℕ) (β M lam ε₀ : ℝ) (N : ℕ) :
    Measurable fun c : Fin N → ℂ × ℂ => (badPoints p₀ β lam M ε₀ (matched c)).card := by
  have hB : FiberMeasurable fun c : Fin N → ℂ × ℂ => badPoints p₀ β lam M ε₀ (matched c) := by
    refine FiberMeasurable.of_cover (fun σ : Equiv.Perm (Fin N) => {c | stableMatching c = σ})
      (fun σ c => badPoints p₀ β lam M ε₀ (matchedBy σ c))
      (fun σ => measurableSet_stableMatching_eq σ) (fun c => ⟨stableMatching c, rfl⟩)
      (fun σ c hc => ?_)
      (fun σ => fiberMeasurable_badPoints (measurable_matchedBy σ) p₀ β lam M ε₀)
    have hc' : stableMatching c = σ := hc
    show badPoints p₀ β lam M ε₀ (matched c) = badPoints p₀ β lam M ε₀ (matchedBy σ c)
    subst hc'
    rfl
  exact measurable_to_countable' fun k => (hB.comp Finset.card) k

end TheoremTwo

end MultipoleBKT

end
