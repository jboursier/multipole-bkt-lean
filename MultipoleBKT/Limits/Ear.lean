/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.EarBound
public import MultipoleBKT.Limits.RouteOdd.DeletionAverage
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Data.Fintype.Pi

/-!
# Ear decompositions of cut-even edge sets

See the proof of Lemma A.5,
(A.30).

We retain distinct edges in an abstract multigraph with nodes `β` and endpoint
pairs `ends : ε → Sym2 β`. Cut parity supplies two distinct boundary edges of
every uncovered component. `exists_ear` joins them by a path outside the covered
nodes. This includes closed ears and two-edge cycles.

`odd_forest_singleTail_average` first constructs all ears. It retains the two
endpoint deletions on ordinary ears and makes one exceptional deletion when the
global longest edge exceeds the radius. Each choice adds one edge for every new
interior node and keeps the single maximal-distance tail. The component tree and sum-over-trees forms are in
`RouteOdd/Forest.lean`.

-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open Finset SimpleGraph

variable {β ε : Type*}

/-- An unordered pair of nodes crosses `A` if exactly one of the two nodes lies in `A`. -/
def Crosses (A : Finset β) (z : Sym2 β) : Prop :=
  Sym2.lift ⟨fun v w => (v ∈ A ↔ w ∉ A), fun v w => by
    by_cases hv : v ∈ A <;> by_cases hw : w ∈ A <;> simp [hv, hw]⟩ z

theorem crosses_mk {A : Finset β} {v w : β} : Crosses A s(v, w) ↔ (v ∈ A ↔ w ∉ A) := Iff.rfl

open scoped Classical in
/-- `F` is cut-even: every set of nodes is crossed by an even number of edges of `F`. -/
def CutEven (ends : ε → Sym2 β) (F : Finset ε) : Prop :=
  ∀ A : Finset β, Even (F.filter fun e => Crosses A (ends e)).card

/-- The graph on the nodes joined by the edges of `D`. -/
def nodeGraph (ends : ε → Sym2 β) (D : Finset ε) : SimpleGraph β :=
  SimpleGraph.fromRel fun v w => ∃ e ∈ D, ends e = s(v, w)

theorem nodeGraph_adj {ends : ε → Sym2 β} {D : Finset ε} {v w : β} :
    (nodeGraph ends D).Adj v w ↔ v ≠ w ∧ ∃ e ∈ D, ends e = s(v, w) := by
  unfold nodeGraph
  rw [fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (h | ⟨e, he, hew⟩)
  · exact h
  · exact ⟨e, he, by rw [hew, Sym2.eq_swap]⟩

theorem nodeGraph_mono {ends : ε → Sym2 β} {D D' : Finset ε} (h : D ⊆ D') :
    nodeGraph ends D ≤ nodeGraph ends D' := fun v w hvw => by
  rw [nodeGraph_adj] at hvw ⊢
  obtain ⟨hne, e, he, hew⟩ := hvw
  exact ⟨hne, e, h he, hew⟩

theorem nodeGraph_adj_of_mem {ends : ε → Sym2 β} {D : Finset ε} {e : ε} (he : e ∈ D)
    {v w : β} (hvw : ends e = s(v, w)) (hne : v ≠ w) : (nodeGraph ends D).Adj v w :=
  nodeGraph_adj.2 ⟨hne, e, he, hvw⟩

section Ear

variable [Fintype β] [DecidableEq β] [DecidableEq ε]

/-- **Existence of an ear.** -/
theorem exists_ear (ends : ε → Sym2 β) {F : Finset ε} (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag)
    (hcut : CutEven ends F) {U : Finset β} {v₀ z₀ : β} (hv₀ : v₀ ∉ U) (hz₀ : z₀ ∈ U)
    (hr : (nodeGraph ends F).Reachable z₀ v₀) :
    ∃ (h : ℕ) (w : ℕ → β) (e : ℕ → ε), 2 ≤ h ∧ w 0 ∈ U ∧ w h ∈ U ∧
      (∀ j ∈ Ioo 0 h, w j ∉ U) ∧ Set.InjOn w (Ioo 0 h) ∧
      (∀ j ∈ Icc 1 h, e j ∈ F ∧ ends (e j) = s(w (j - 1), w j)) ∧ Set.InjOn e (Icc 1 h) := by
  classical
  obtain ⟨p⟩ := hr
  obtain ⟨dt, -, hd1, hd2⟩ := p.exists_boundary_dart (U : Set β) hz₀ hv₀
  set a := dt.toProd.1 with ha
  set w₁ := dt.toProd.2 with hw₁
  have haU : a ∈ U := hd1
  have hw₁U : w₁ ∉ U := hd2
  obtain ⟨-, e₁, he₁F, he₁⟩ := nodeGraph_adj.1 dt.adj
  -- the component of `w₁` outside `U`
  set G' := (nodeGraph ends F).induce {v | v ∉ U} with hG'
  set K : Finset β := univ.filter fun v =>
    ∃ hv : v ∉ U, G'.Reachable ⟨w₁, hw₁U⟩ ⟨v, hv⟩ with hK
  have hw₁K : w₁ ∈ K := mem_filter.2 ⟨mem_univ _, hw₁U, Reachable.refl _⟩
  have haK : a ∉ K := fun h => (mem_filter.1 h).2.1 haU
  have he₁c : Crosses K (ends e₁) := by
    rw [he₁, crosses_mk]
    exact ⟨fun h => absurd h haK, fun h => absurd hw₁K h⟩
  -- a second crossing edge
  obtain ⟨e', he'F, he'ne, he'c⟩ : ∃ e' ∈ F, e' ≠ e₁ ∧ Crosses K (ends e') := by
    by_contra hcon
    push Not at hcon
    have hset : F.filter (fun e => Crosses K (ends e)) = {e₁} := by
      ext e
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨heF, hec⟩
        by_contra hne
        exact hcon e heF hne hec
      · rintro rfl
        exact ⟨he₁F, he₁c⟩
    have := hcut K
    rw [hset, card_singleton] at this
    exact Nat.not_even_one this
  -- orient `e'`: from `w' ∈ K` to `b ∉ K`
  obtain ⟨w', b, hends', hw'K, hbK⟩ : ∃ w' b, ends e' = s(w', b) ∧ w' ∈ K ∧ b ∉ K := by
    obtain ⟨⟨x, y⟩, hxy⟩ := Quot.exists_rep (ends e')
    have hxy' : ends e' = s(x, y) := hxy.symm
    rw [hxy', crosses_mk] at he'c
    by_cases hx : x ∈ K
    · exact ⟨x, y, hxy', hx, he'c.1 hx⟩
    · have hy : y ∈ K := by
        by_contra hy
        exact hx (he'c.2 hy)
      exact ⟨y, x, by rw [hxy', Sym2.eq_swap], hy, hx⟩
  obtain ⟨hw'U, hreach'⟩ := (mem_filter.1 hw'K).2
  have hw'b : w' ≠ b := by
    intro h
    apply hloop e' he'F
    rw [hends', h]
    exact Sym2.mk_isDiag_iff.2 rfl
  have hbU : b ∈ U := by
    by_contra hbU
    apply hbK
    refine mem_filter.2 ⟨mem_univ _, hbU, hreach'.trans ?_⟩
    refine Adj.reachable ?_
    show (nodeGraph ends F).Adj w' b
    exact nodeGraph_adj_of_mem he'F hends' hw'b
  -- a path from `w₁` to `w'` outside `U`
  obtain ⟨P, hP⟩ := hreach'.exists_isPath
  set n := P.length with hn
  set x : ℕ → β := fun i => (P.getVert i).val with hx
  have hxU : ∀ i, x i ∉ U := fun i => (P.getVert i).property
  have hx0 : x 0 = w₁ := by simp [hx, Walk.getVert_zero]
  have hxn : x n = w' := by simp [hx, hn, Walk.getVert_length]
  have hxinj : ∀ i l, i ≤ n → l ≤ n → x i = x l → i = l := fun i l hi hl hil =>
    hP.getVert_injOn hi hl (Subtype.ext hil)
  have hxadj : ∀ i, i < n → (nodeGraph ends F).Adj (x i) (x (i + 1)) := fun i hi =>
    P.adj_getVert_succ hi
  have hpick : ∀ v w, (nodeGraph ends F).Adj v w → ∃ e ∈ F, ends e = s(v, w) := fun v w hvw =>
    (nodeGraph_adj.1 hvw).2
  have : Nonempty ε := ⟨e₁⟩
  choose! pick hpickF hpickE using hpick
  -- the ear
  set w : ℕ → β := fun j => if j = 0 then a else if j ≤ n + 1 then x (j - 1) else b with hw
  set e : ℕ → ε := fun j => if j = 1 then e₁ else if j ≤ n + 1 then pick (x (j - 2)) (x (j - 1))
    else e' with he
  have hw0 : w 0 = a := by simp [hw]
  have hwh : w (n + 2) = b := by simp [hw]
  have hwint : ∀ j, 1 ≤ j → j ≤ n + 1 → w j = x (j - 1) := fun j h1 h2 => by
    simp only [hw]
    rw [ite_eq_right (by omega), ite_eq_left h2]
  -- middle edges have both ends outside `U`
  have hmid : ∀ j, 2 ≤ j → j ≤ n + 1 → e j ∈ F ∧ ends (e j) = s(x (j - 2), x (j - 1)) := by
    intro j h2 h3
    have hej : e j = pick (x (j - 2)) (x (j - 1)) := by
      simp only [he]
      rw [ite_eq_right (by omega), ite_eq_left h3]
    have hadj := hxadj (j - 2) (by omega)
    rw [show j - 2 + 1 = j - 1 by omega] at hadj
    rw [hej]
    exact ⟨hpickF _ _ hadj, hpickE _ _ hadj⟩
  refine ⟨n + 2, w, e, by omega, by rw [hw0]; exact haU, by rw [hwh]; exact hbU, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [mem_Ioo] at hj
    rw [hwint j (by omega) (by omega)]
    exact hxU _
  · intro j₁ hj₁ j₂ hj₂ h12
    rw [coe_Ioo, Set.mem_Ioo] at hj₁ hj₂
    rw [hwint j₁ (by omega) (by omega), hwint j₂ (by omega) (by omega)] at h12
    have := hxinj _ _ (by omega) (by omega) h12
    omega
  · intro j hj
    rw [mem_Icc] at hj
    rcases Nat.lt_or_ge j 2 with hj1 | hj2
    · have hj1' : j = 1 := by omega
      subst hj1'
      have he1 : e 1 = e₁ := by simp [he]
      rw [he1, hw0, hwint 1 le_rfl (by omega), Nat.sub_self, hx0]
      exact ⟨he₁F, he₁⟩
    · rcases Nat.lt_or_ge j (n + 2) with hjn | hjn
      · obtain ⟨h1, h2⟩ := hmid j hj2 (by omega)
        refine ⟨h1, ?_⟩
        rw [h2, hwint (j - 1) (by omega) (by omega), hwint j (by omega) (by omega),
          show j - 1 - 1 = j - 2 by omega]
      · have hjeq : j = n + 2 := by omega
        subst hjeq
        have hen : e (n + 2) = e' := by
          simp only [he]
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rw [hen, hwh, show n + 2 - 1 = n + 1 by omega, hwint (n + 1) (by omega) le_rfl,
          Nat.add_sub_cancel, hxn]
        exact ⟨he'F, hends'⟩
  · -- injectivity of the edges
    have he1 : e 1 = e₁ := by simp [he]
    have hen : e (n + 2) = e' := by
      simp only [he]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have hnotU : ∀ j, 2 ≤ j → j ≤ n + 1 → ∀ v ∈ ends (e j), v ∉ U := by
      intro j h2 h3 v hv
      rw [(hmid j h2 h3).2, Sym2.mem_iff] at hv
      rcases hv with rfl | rfl <;> exact hxU _
    have haE : a ∈ ends e₁ := by rw [he₁]; exact Sym2.mem_mk_left _ _
    have hbE : b ∈ ends e' := by rw [hends']; exact Sym2.mem_mk_right _ _
    intro j₁ hj₁ j₂ hj₂ h12
    rw [coe_Icc, Set.mem_Icc] at hj₁ hj₂
    -- classify the indices
    have key : ∀ j, 1 ≤ j → j ≤ n + 2 →
        (j = 1 ∧ e j = e₁) ∨ (j = n + 2 ∧ e j = e') ∨ (2 ≤ j ∧ j ≤ n + 1) := by
      intro j h1 h2
      rcases Nat.lt_or_ge j 2 with h | h
      · left; have : j = 1 := by omega
        subst this; exact ⟨rfl, he1⟩
      · rcases Nat.lt_or_ge j (n + 2) with h' | h'
        · right; right; exact ⟨h, by omega⟩
        · right; left; have : j = n + 2 := by omega
          subst this; exact ⟨rfl, hen⟩
    rcases key j₁ hj₁.1 hj₁.2 with ⟨r1, k1⟩ | ⟨r1, k1⟩ | ⟨m1, m1'⟩ <;>
      rcases key j₂ hj₂.1 hj₂.2 with ⟨r2, k2⟩ | ⟨r2, k2⟩ | ⟨m2, m2'⟩
    · omega
    · exact absurd (k1.symm.trans (h12.trans k2)) he'ne.symm
    · exfalso
      rw [k1] at h12
      exact hnotU j₂ m2 m2' a (h12 ▸ haE) haU
    · exact absurd (k2.symm.trans (h12.symm.trans k1)) he'ne.symm
    · omega
    · exfalso
      rw [k1] at h12
      exact hnotU j₂ m2 m2' b (h12 ▸ hbE) hbU
    · exfalso
      rw [k2] at h12
      exact hnotU j₁ m1 m1' a (h12.symm ▸ haE) haU
    · exfalso
      rw [k2] at h12
      exact hnotU j₁ m1 m1' b (h12.symm ▸ hbE) hbU
    · have hends := congrArg ends h12
      rw [(hmid j₁ m1 m1').2, (hmid j₂ m2 m2').2, Sym2.eq_iff] at hends
      rcases hends with ⟨h1, -⟩ | ⟨h1, h2⟩
      · have := hxinj _ _ (by omega) (by omega) h1
        omega
      · have := hxinj _ _ (by omega) (by omega) h1
        have := hxinj _ _ (by omega) (by omega) h2
        omega

omit [Fintype β] [DecidableEq β] [DecidableEq ε] in
/-- Reachability along consecutive edges of an ear. -/
theorem reachable_ear (ends : ε → Sym2 β) {T : Finset ε} (w : ℕ → β) (e : ℕ → ε) {i j : ℕ}
    (hij : i ≤ j) (hT : ∀ l, i < l → l ≤ j → e l ∈ T ∧ ends (e l) = s(w (l - 1), w l)) :
    (nodeGraph ends T).Reachable (w i) (w j) := by
  induction j, hij using Nat.le_induction with
  | base => exact Reachable.refl _
  | succ m him ih =>
    refine (ih fun l h1 h2 => hT l h1 (by omega)).trans ?_
    obtain ⟨hm, he⟩ := hT (m + 1) (by omega) le_rfl
    rw [Nat.add_sub_cancel] at he
    by_cases hw : w m = w (m + 1)
    · rw [hw]
    · exact (nodeGraph_adj_of_mem hm he hw).reachable

/-- A finite sequence of ears covering `U`, with original edge labels `Used`.
Each extension has new interior vertices and disjoint edges. -/
private inductive EarCover (ends : ε → Sym2 β) (Z : Finset β) :
    Finset β → Finset ε → Type _
  | root : EarCover ends Z Z ∅
  | extend {U : Finset β} {Used : Finset ε} (prev : EarCover ends Z U Used)
      (h : ℕ) (w : ℕ → β) (e : ℕ → ε) (hh : 2 ≤ h)
      (hw0 : w 0 ∈ U) (hwh : w h ∈ U)
      (hwint : ∀ j ∈ Ioo 0 h, w j ∉ U) (hwinj : Set.InjOn w (Ioo 0 h))
      (hedge : ∀ j ∈ Icc 1 h, ends (e j) = s(w (j - 1), w j))
      (heinj : Set.InjOn e (Icc 1 h))
      (hdisj : Disjoint Used ((Icc 1 h).image e)) :
      EarCover ends Z (U ∪ (Ioo 0 h).image w) (Used ∪ (Icc 1 h).image e)

/-- Construct the ears before choosing any edge to delete. -/
private theorem exists_earCover (ends : ε → Sym2 β) {F : Finset ε}
    (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag) (hcut : CutEven ends F) (Z : Finset β)
    (hZ : ∀ v, ∃ z ∈ Z, (nodeGraph ends F).Reachable z v) :
    ∃ Used ⊆ F, Nonempty (EarCover ends Z univ Used) := by
  let Data : Finset β → Prop := fun U => ∃ Used : Finset ε, Used ⊆ F ∧
    (∀ e ∈ Used, ∀ v ∈ ends e, v ∈ U) ∧ Nonempty (EarCover ends Z U Used)
  have hstep : ∀ n, ∀ U : Finset β, Z ⊆ U → (univ \ U).card = n → Data U → Data univ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro U hZU hn hU
    by_cases hUu : U = univ
    · rw [← hUu]; exact hU
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ U := by
      by_contra h
      push Not at h
      exact hUu (eq_univ_of_forall h)
    obtain ⟨z₀, hz₀Z, hz₀⟩ := hZ v₀
    obtain ⟨h, w, e, hh, hw0, hwh, hwint, hwinj, hedge, heinj⟩ :=
      exists_ear ends hloop hcut hv₀ (hZU hz₀Z) hz₀
    obtain ⟨Used, hUsedF, hUsedU, ⟨cover⟩⟩ := hU
    have heF : ∀ j ∈ Icc 1 h, e j ∈ F := fun j hj => (hedge j hj).1
    set Int := (Ioo 0 h).image w
    set P := (Icc 1 h).image e
    have hPUsed : Disjoint Used P := by
      rw [Finset.disjoint_left]
      intro f hfU hfP
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hfP
      rw [mem_Icc] at hj
      rcases Nat.lt_or_ge j h with hjh | hjh
      · refine hwint j (by simp; omega) (hUsedU _ hfU _ ?_)
        rw [(hedge j (by simp; omega)).2]
        exact Sym2.mem_mk_right _ _
      · refine hwint (j - 1) (by simp; omega) (hUsedU _ hfU _ ?_)
        rw [(hedge j (by simp; omega)).2]
        exact Sym2.mem_mk_left _ _
    have hData : Data (U ∪ Int) := by
      refine ⟨Used ∪ P, union_subset hUsedF ?_, ?_,
        ⟨cover.extend h w e hh hw0 hwh hwint hwinj (fun j hj => (hedge j hj).2) heinj hPUsed⟩⟩
      · intro f hf
        obtain ⟨j, hj, rfl⟩ := mem_image.1 hf
        exact heF j hj
      · intro f hf v hv
        rcases mem_union.1 hf with hf | hf
        · exact mem_union_left _ (hUsedU f hf v hv)
        · obtain ⟨j, hj, rfl⟩ := mem_image.1 hf
          rw [(hedge j hj).2, Sym2.mem_iff] at hv
          have hmem : ∀ i, i ≤ h → w i ∈ U ∪ Int := by
            intro i hi
            rcases Nat.eq_zero_or_pos i with rfl | hi0
            · exact mem_union_left _ hw0
            · rcases Nat.lt_or_ge i h with hih | hih
              · exact mem_union_right _ (mem_image_of_mem _ (by simp; omega))
              · have : i = h := by omega
                subst this
                exact mem_union_left _ hwh
          rw [mem_Icc] at hj
          rcases hv with rfl | rfl
          · exact hmem _ (by omega)
          · exact hmem _ hj.2
    have hlt : (univ \ (U ∪ Int)).card < n := by
      rw [← hn]
      refine card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨sdiff_subset_sdiff subset_rfl subset_union_left, ?_⟩)
      intro heq
      have h1 : w 1 ∈ univ \ U := mem_sdiff.2 ⟨mem_univ _, hwint 1 (by simp; omega)⟩
      rw [← heq] at h1
      exact (mem_sdiff.1 h1).2 (mem_union_right _ (mem_image_of_mem _ (by simp; omega)))
    exact ih _ hlt (U ∪ Int) (hZU.trans subset_union_left) rfl hData
  have hinit : Data Z := ⟨∅, empty_subset _, fun e he => absurd he (notMem_empty e), ⟨.root⟩⟩
  obtain ⟨Used, hUsedF, -, hcover⟩ := hstep _ Z subset_rfl rfl hinit
  exact ⟨Used, hUsedF, hcover⟩

omit [Fintype β] in
/-- Removing any one ear edge adds one edge per new interior node and connects
all of those nodes to the previous roots. -/
private theorem ear_extension_valid (ends : ε → Sym2 β) (Z U : Finset β)
    (hZU : Z ⊆ U) {Used T : Finset ε} (hTU : T ⊆ Used)
    (hcardT : T.card = (U \ Z).card)
    (hreachU : ∀ v ∈ U, ∃ z ∈ Z, (nodeGraph ends T).Reachable z v)
    {h : ℕ} (w : ℕ → β) (e : ℕ → ε) (hw0 : w 0 ∈ U) (hwh : w h ∈ U)
    (hwint : ∀ j ∈ Ioo 0 h, w j ∉ U) (hwinj : Set.InjOn w (Ioo 0 h))
    (hedge : ∀ j ∈ Icc 1 h, ends (e j) = s(w (j - 1), w j))
    (heinj : Set.InjOn e (Icc 1 h)) (hPUsed : Disjoint Used ((Icc 1 h).image e))
    {jx : ℕ} (hjx : jx ∈ Icc 1 h) :
    let Q := ((Icc 1 h).erase jx).image e
    T ∪ Q ⊆ Used ∪ (Icc 1 h).image e ∧
    (T ∪ Q).card = ((U ∪ (Ioo 0 h).image w) \ Z).card ∧
    (∀ v ∈ U ∪ (Ioo 0 h).image w, ∃ z ∈ Z, (nodeGraph ends (T ∪ Q)).Reachable z v) := by
  set Int := (Ioo 0 h).image w
  set Q := ((Icc 1 h).erase jx).image e with hQ
  have hIntU : Disjoint U Int := by
    refine disjoint_left.2 fun v hvU hvI => ?_
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hvI
    exact hwint j hj hvU
  have hQP : Q ⊆ (Icc 1 h).image e := image_subset_image (erase_subset _ _)
  have hTQ : Disjoint T Q := disjoint_of_subset_left hTU (disjoint_of_subset_right hQP hPUsed)
  have hZInt : Disjoint (U \ Z) Int := disjoint_of_subset_left sdiff_subset hIntU
  have hU'Z : (U ∪ Int) \ Z = (U \ Z) ∪ Int := by
    ext v
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, fun hz => disjoint_left.1 hIntU (hZU hz) h1⟩
  refine ⟨union_subset_union hTU hQP, ?_, ?_⟩
  · rw [card_union_of_disjoint hTQ, hcardT, hU'Z, card_union_of_disjoint hZInt]
    congr 1
    rw [hQ, card_image_of_injOn (heinj.mono (by intro j hj; exact mem_of_mem_erase hj)),
      card_erase_of_mem hjx, card_image_of_injOn hwinj]
    simp
  · intro v hv
    have hmono : nodeGraph ends T ≤ nodeGraph ends (T ∪ Q) := nodeGraph_mono subset_union_left
    have hinQ : ∀ l, l ∈ Icc 1 h → l ≠ jx →
        e l ∈ T ∪ Q ∧ ends (e l) = s(w (l - 1), w l) := fun l hl hlx =>
      ⟨mem_union_right _ (mem_image_of_mem _ (mem_erase.2 ⟨hlx, hl⟩)), hedge l hl⟩
    rcases mem_union.1 hv with hv | hv
    · obtain ⟨z, hz, hr⟩ := hreachU v hv
      exact ⟨z, hz, hr.mono hmono⟩
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 hv
      rw [mem_Ioo] at hj
      rw [mem_Icc] at hjx
      rcases Nat.lt_or_ge j jx with hjj | hjj
      · obtain ⟨z, hz, hr⟩ := hreachU _ hw0
        exact ⟨z, hz, (hr.mono hmono).trans
          (reachable_ear ends w e (Nat.zero_le j) fun l hl1 hl2 =>
            hinQ l (by simp; omega) (by omega))⟩
      · obtain ⟨z, hz, hr⟩ := hreachU _ hwh
        exact ⟨z, hz, (hr.mono hmono).trans
          (reachable_ear ends w e hj.2.le fun l hl1 hl2 =>
            hinQ l (by simp; omega) (by omega)).symm⟩

omit [Fintype β] in
private theorem EarCover.roots_subset {ends : ε → Sym2 β} {Z U : Finset β}
    {Used : Finset ε} (cover : EarCover ends Z U Used) : Z ⊆ U := by
  induction cover with
  | root => exact subset_rfl
  | extend prev h w e hh hw0 hwh hwint hwinj hedge heinj hdisj ih =>
    exact ih.trans subset_union_left

/-- Evaluate the fixed ear sequence. `none` keeps both endpoint choices on every
 ear. `some x` replaces those two choices by deletion of `x` in its unique ear.
All other ears still contribute their literal half-sums. -/
private theorem earCover_average (ends : ε → Sym2 β) (Z : Finset β)
    (s : β → ℝ) (hs : ∀ v, 0 < s v) {R : ℝ}
    (d a : ε → ℝ) {U : Finset β} {Used : Finset ε} (cover : EarCover ends Z U Used) :
    ∀ (_hR : ∀ f ∈ Used, ∀ v ∈ ends f, s v ≤ R) (_hd : ∀ e ∈ Used, 0 < d e) (_ha0 : ∀ e ∈ Used, 0 ≤ a e)
      (_ha : ∀ e ∈ Used, ∀ v w, ends e = s(v, w) →
        a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w))))
      (mark : Option ε), (∀ x, mark = some x → x ∈ Used) →
    ∃ L : List (Finset ε), L ≠ [] ∧
      (∀ T ∈ L, T ⊆ Used ∧ T.card = (U \ Z).card ∧
        ∀ v ∈ U, ∃ z ∈ Z, (nodeGraph ends T).Reachable z v) ∧
      ∏ e ∈ Used, a e ≤ (∏ v ∈ U \ Z, s v ^ 2) *
        mark.elim 1 (fun x => R ^ 2 / d x ^ 2) *
        deletionAverage L (fun T => ∏ e ∈ T, (d e ^ 2)⁻¹) := by
  induction cover with
  | root =>
    intro hR hd ha0 ha mark hm
    have hmnone : mark = none := by
      cases mark with
      | none => rfl
      | some x => exact False.elim (notMem_empty x (hm x rfl))
    subst mark
    refine ⟨[∅], by simp, ?_, ?_⟩
    · intro T hT
      have : T = ∅ := by simpa using hT
      subst T
      exact ⟨subset_rfl, by simp, fun v hv => ⟨v, hv, Reachable.refl _⟩⟩
    · simp [deletionAverage]
  | @extend U Used prev h w e hh hw0 hwh hwint hwinj hedge heinj hPUsed ih =>
    intro hR hd ha0 ha mark hm
    let P := (Icc 1 h).image e
    let Int := (Ioo 0 h).image w
    let Q := fun j => ((Icc 1 h).erase j).image e
    let K := fun T : Finset ε => ∏ f ∈ T, (d f ^ 2)⁻¹
    have hZU : Z ⊆ U := prev.roots_subset
    have hU'Z : (U ∪ Int) \ Z = (U \ Z) ∪ Int := by
      ext v
      simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr h1
      · rintro (⟨h1, h2⟩ | h1)
        · exact ⟨Or.inl h1, h2⟩
        · refine ⟨Or.inr h1, fun hz => ?_⟩
          obtain ⟨j, hj, rfl⟩ := mem_image.1 h1
          exact hwint j hj (hZU hz)
    have hZInt : Disjoint (U \ Z) Int := by
      refine disjoint_left.2 fun v hv hvI => ?_
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hvI
      exact hwint j hj (mem_sdiff.1 hv).1
    have hrad : ∏ v ∈ (U ∪ Int) \ Z, s v ^ 2 =
        (∏ v ∈ U \ Z, s v ^ 2) * ∏ j ∈ Ioo 0 h, s (w j) ^ 2 := by
      rw [hU'Z, prod_union hZInt, prod_image hwinj]
    have hprod : ∏ f ∈ Used ∪ P, a f = (∏ f ∈ Used, a f) * ∏ j ∈ Icc 1 h, a (e j) := by
      rw [prod_union hPUsed, prod_image heinj]
    have heP : ∀ j ∈ Icc 1 h, e j ∈ Used ∪ P := fun j hj =>
      mem_union_right _ (mem_image_of_mem _ hj)
    have hear : ∏ j ∈ Icc 1 h, a (e j) ≤
        (∏ j ∈ Ioo 0 h, s (w j) ^ 2) * deletionAverage [1, h] (fun j => K (Q j)) := by
      have hb := ear_bound_endpoints hh (fun j => s (w j)) (fun j => d (e j))
        (fun j => a (e j)) (fun j => hs _) (fun j hj => hd _ (heP j hj))
        (fun j hj => ha0 _ (heP j hj)) (fun j hj => ha _ (heP j hj) _ _ (hedge j hj))
      have hK : ∀ j, K (Q j) = ∏ l ∈ (Icc 1 h).erase j, (d (e l) ^ 2)⁻¹ := by
        intro j
        exact prod_image (heinj.mono (by intro l hl; exact mem_of_mem_erase hl))
      simp only [deletionAverage, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.length_cons, List.length_nil, add_zero, hK]
      convert hb using 1; ring
    -- A Cartesian product retains every previous choice and every new deletion.
    have extendFamily (m : Option ε) (hm : ∀ x, m = some x → x ∈ Used)
        (J : List ℕ) (hJ : J ≠ []) (hJI : ∀ j ∈ J, j ∈ Icc 1 h)
        (c : ℝ)
        (hb : ∏ j ∈ Icc 1 h, a (e j) ≤
          (∏ j ∈ Ioo 0 h, s (w j) ^ 2) * c * deletionAverage J (fun j => K (Q j)))
        (heq : m.elim 1 (fun x => R ^ 2 / d x ^ 2) * c =
          mark.elim 1 (fun x => R ^ 2 / d x ^ 2)) :
        ∃ L : List (Finset ε), L ≠ [] ∧
          (∀ T ∈ L, T ⊆ Used ∪ P ∧ T.card = ((U ∪ Int) \ Z).card ∧
            ∀ v ∈ U ∪ Int, ∃ z ∈ Z, (nodeGraph ends T).Reachable z v) ∧
          ∏ f ∈ Used ∪ P, a f ≤ (∏ v ∈ (U ∪ Int) \ Z, s v ^ 2) *
            mark.elim 1 (fun x => R ^ 2 / d x ^ 2) * deletionAverage L K := by
      obtain ⟨L, hL, hvalid, hbound⟩ := ih
        (fun f hf => hR f (mem_union_left _ hf))
        (fun f hf => hd f (mem_union_left _ hf)) (fun f hf => ha0 f (mem_union_left _ hf))
        (fun f hf => ha f (mem_union_left _ hf)) m hm
      let L' := L.flatMap fun T => J.map fun j => T ∪ Q j
      have hL' : L' ≠ [] := by
        obtain ⟨T, hT⟩ := List.exists_mem_of_ne_nil L hL
        obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil J hJ
        have hin : T ∪ Q j ∈ L' := List.mem_flatMap.2 ⟨T, hT, List.mem_map.2 ⟨j, hj, rfl⟩⟩
        intro hz
        rw [hz] at hin
        exact List.not_mem_nil hin
      have hmul : ∀ T ∈ L, ∀ j ∈ J, K (T ∪ Q j) = K T * K (Q j) := by
        intro T hT j hj
        exact prod_union (disjoint_of_subset_left (hvalid T hT).1
          (disjoint_of_subset_right (image_subset_image (erase_subset _ _)) hPUsed))
      have havg : deletionAverage L' K = deletionAverage L K *
          deletionAverage J (fun j => K (Q j)) :=
        deletionAverage_product L J (fun T j => T ∪ Q j) K K (fun j => K (Q j)) hmul
      refine ⟨L', hL', ?_, ?_⟩
      · intro T hT
        obtain ⟨T₀, hT₀, hTJ⟩ := List.mem_flatMap.1 hT
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hTJ
        obtain ⟨hsub, hcard, hreach⟩ := hvalid T₀ hT₀
        exact ear_extension_valid ends Z U hZU hsub hcard hreach w e hw0 hwh hwint hwinj
          hedge heinj hPUsed (hJI j hj)
      · rw [hprod, hrad, havg]
        have hright : 0 ≤ (∏ v ∈ U \ Z, s v ^ 2) *
            m.elim 1 (fun x => R ^ 2 / d x ^ 2) * deletionAverage L K :=
          (prod_nonneg fun f hf => ha0 f (mem_union_left _ hf)).trans hbound
        calc (∏ f ∈ Used, a f) * ∏ j ∈ Icc 1 h, a (e j)
            ≤ ((∏ v ∈ U \ Z, s v ^ 2) * m.elim 1 (fun x => R ^ 2 / d x ^ 2) *
                deletionAverage L K) *
              ((∏ j ∈ Ioo 0 h, s (w j) ^ 2) * c * deletionAverage J (fun j => K (Q j))) :=
                mul_le_mul hbound hb (prod_nonneg fun j hj => ha0 _ (heP j hj)) hright
          _ = ((∏ v ∈ U \ Z, s v ^ 2) * ∏ j ∈ Ioo 0 h, s (w j) ^ 2) *
              (m.elim 1 (fun x => R ^ 2 / d x ^ 2) * c) *
                (deletionAverage L K * deletionAverage J (fun j => K (Q j))) := by ring
          _ = _ := by rw [heq]
    have hJI : ∀ j ∈ [1, h], j ∈ Icc 1 h := by
      intro j hj
      simp at hj
      rcases hj with rfl | rfl <;> simp <;> omega
    cases mark with
    | none =>
      exact extendFamily none (by simp) [1, h] (by simp) hJI 1
        (by simpa only [mul_one] using hear) (by simp)
    | some x =>
      by_cases hx : x ∈ Used
      · exact extendFamily (some x) (by simpa using hx) [1, h] (by simp) hJI 1
          (by simpa only [mul_one] using hear) (by simp)
      · have hxP : x ∈ P := (mem_union.1 (hm x rfl)).resolve_left hx
        obtain ⟨jx, hjx, hex⟩ := mem_image.1 hxP
        have hRfirst : s (w 0) ≤ R := hR (e 1) (heP 1 (by simp; omega)) _ (by
          rw [hedge 1 (by simp; omega)]
          exact Sym2.mem_mk_left _ _)
        have hRlast : s (w h) ≤ R := hR (e h) (heP h (by simp; omega)) _ (by
          rw [hedge h (by simp; omega)]
          exact Sym2.mem_mk_right _ _)
        have hb := ear_bound_exceptional hh (fun j => s (w j)) (fun j => d (e j))
          (fun j => a (e j)) (fun j => hs _) hRfirst hRlast
          (fun j hj => hd _ (heP j hj)) (fun j hj => ha0 _ (heP j hj))
          (fun j hj => ha _ (heP j hj) _ _ (hedge j hj)) hjx
        have hK : K (Q jx) = ∏ j ∈ (Icc 1 h).erase jx, (d (e j) ^ 2)⁻¹ :=
          prod_image (heinj.mono (by intro j hj; exact mem_of_mem_erase hj))
        apply extendFamily none (by simp) [jx] (by simp) (by simpa using hjx)
          (R ^ 2 / d x ^ 2)
        · simpa [deletionAverage, hK, hex] using hb
        · simp

/-- The finite family of endpoint deletions with the single exceptional deletion
of (A.30). Every member connects the roots and has one edge per new node.
The average retains the paper's half-sums. It is bounded by the corresponding
unweighted finite sum of tree terms.
-/
theorem odd_forest_singleTail_average (ends : ε → Sym2 β) {F : Finset ε}
    (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag) (hcut : CutEven ends F) (Z : Finset β)
    (hZ : ∀ v, ∃ z ∈ Z, (nodeGraph ends F).Reachable z v)
    (s : β → ℝ) (hs : ∀ v, 0 < s v) {R : ℝ} (hR : ∀ f ∈ F, ∀ v ∈ ends f, s v ≤ R)
    (d a : ε → ℝ) (hd : ∀ e ∈ F, 0 < d e)
    (ha0 : ∀ e ∈ F, 0 ≤ a e) (ha1 : ∀ e ∈ F, a e ≤ 1)
    (ha : ∀ e ∈ F, ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w)))) :
    ∃ L : List (Finset ε), L ≠ [] ∧
      (∀ T ∈ L, T ⊆ F ∧ T.card = (univ \ Z).card ∧
        ∀ v, ∃ z ∈ Z, (nodeGraph ends T).Reachable z v) ∧
      ∏ e ∈ F, a e ≤ (∏ v ∈ univ \ Z, s v ^ 2) *
        deletionAverage L (fun T => globalTail R d T * ∏ e ∈ T, (d e ^ 2)⁻¹) := by
  obtain ⟨Used, hUsedF, ⟨cover⟩⟩ := exists_earCover ends hloop hcut Z hZ
  -- Choose the exceptional edge after constructing all ears, not in each ear.
  have hmark : ∃ mark : Option ε, (∀ x, mark = some x → x ∈ Used) ∧
      ∀ T ⊆ Used, mark.elim 1 (fun x => R ^ 2 / d x ^ 2) ≤ globalTail R d T := by
    by_cases hUsed : Used.Nonempty
    · obtain ⟨e₀, he₀, hmax⟩ := exists_max_image Used d hUsed
      have hd₀ := hd e₀ (hUsedF he₀)
      have htail : ∀ T ⊆ Used, min 1 (R ^ 2 / d e₀ ^ 2) ≤ globalTail R d T := fun T hT =>
        tail_le_globalTail_image d T (fun f hf => hd f (hUsedF (hT hf)))
          (fun f hf => hmax f (hT hf))
      by_cases hlarge : R ≤ d e₀
      · -- Delete `e₀` in its ear. Use the endpoint-radius bound there only.
        obtain ⟨⟨v, w⟩, hrep⟩ := Quot.exists_rep (ends e₀)
        have hR0 : 0 ≤ R := (hs v).le.trans
          (hR e₀ (hUsedF he₀) v (hrep ▸ Sym2.mem_mk_left v w))
        have hq : R ^ 2 / d e₀ ^ 2 ≤ 1 :=
          (div_le_one (sq_pos_of_pos hd₀)).2 (pow_le_pow_left₀ hR0 hlarge 2)
        refine ⟨some e₀, by simpa using he₀, fun T hT => ?_⟩
        exact (le_min hq le_rfl).trans (htail T hT)
      · -- All used distances are below `R`. Every tree tail is one.
        have hsmall : d e₀ ≤ R := (lt_of_not_ge hlarge).le
        have hq : 1 ≤ R ^ 2 / d e₀ ^ 2 :=
          (one_le_div (sq_pos_of_pos hd₀)).2 (pow_le_pow_left₀ hd₀.le hsmall 2)
        refine ⟨none, by simp, fun T hT => ?_⟩
        simpa only [Option.elim_none, min_eq_left hq] using htail T hT
    · have hUsed : Used = ∅ := not_nonempty_iff_eq_empty.1 hUsed
      refine ⟨none, by simp, fun T hT => ?_⟩
      have hT : T = ∅ := subset_empty.1 (hUsed ▸ hT)
      simp [hT, globalTail]
  obtain ⟨mark, hm, htail⟩ := hmark
  obtain ⟨L, hL, hvalid, hb⟩ := earCover_average ends Z s hs d a cover
    (fun f hf => hR f (hUsedF hf))
    (fun f hf => hd f (hUsedF hf)) (fun f hf => ha0 f (hUsedF hf))
    (fun f hf => ha f (hUsedF hf)) mark hm
  refine ⟨L, hL, fun T hT => ⟨(hvalid T hT).1.trans hUsedF,
    (hvalid T hT).2.1, fun v => (hvalid T hT).2.2 v (mem_univ _)⟩, ?_⟩
  have hdiscard : ∏ e ∈ F, a e ≤ ∏ e ∈ Used, a e := by
    rw [← prod_sdiff hUsedF]
    have hrest : ∏ e ∈ F \ Used, a e ≤ 1 :=
      prod_le_one₀ (fun e he => ha0 e (mem_sdiff.1 he).1)
        (fun e he => ha1 e (mem_sdiff.1 he).1)
    exact (mul_le_mul_of_nonneg_right hrest (prod_nonneg fun e he => ha0 e (hUsedF he))).trans_eq
      (one_mul _)
  calc ∏ e ∈ F, a e ≤ ∏ e ∈ Used, a e := hdiscard
    _ ≤ _ := hb
    _ = (∏ v ∈ univ \ Z, s v ^ 2) * deletionAverage L
        (fun T => mark.elim 1 (fun x => R ^ 2 / d x ^ 2) * ∏ e ∈ T, (d e ^ 2)⁻¹) := by
          rw [deletionAverage_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (deletionAverage_mono L _ _ fun T hT =>
        mul_le_mul_of_nonneg_right (htail T (hvalid T hT).1)
          (prod_nonneg fun e _ => inv_nonneg.2 (sq_nonneg _)))
      (prod_nonneg fun v _ => sq_nonneg _)

/-- A tree witness extracted from the written finite deletion average.
The cardinal identity records that each ear adds one edge per new interior block.
See (A.30). -/
theorem odd_forest_singleTail (ends : ε → Sym2 β) {F : Finset ε} (hloop : ∀ e ∈ F, ¬ (ends e).IsDiag)
    (hcut : CutEven ends F) (Z : Finset β)
    (hZ : ∀ v, ∃ z ∈ Z, (nodeGraph ends F).Reachable z v) (s : β → ℝ) (hs : ∀ v, 0 < s v)
    {R : ℝ} (hR : ∀ f ∈ F, ∀ v ∈ ends f, s v ≤ R)
    (d a : ε → ℝ) (hd : ∀ e ∈ F, 0 < d e) (ha0 : ∀ e ∈ F, 0 ≤ a e) (ha1 : ∀ e ∈ F, a e ≤ 1)
    (ha : ∀ e ∈ F, ∀ v w, ends e = s(v, w) →
      a e ≤ s v * s w / (d e * max (d e) (max (s v) (s w)))) :
    ∃ T ⊆ F, T.card = (univ \ Z).card ∧ (∀ v, ∃ z ∈ Z, (nodeGraph ends T).Reachable z v) ∧
      ∏ e ∈ F, a e ≤ (∏ v ∈ univ \ Z, s v ^ 2) * globalTail R d T * ∏ e ∈ T, (d e ^ 2)⁻¹ := by
  obtain ⟨L, hL, hvalid, hb⟩ := odd_forest_singleTail_average ends hloop hcut Z hZ s hs hR
    d a hd ha0 ha1 ha
  obtain ⟨T, hT, hmax⟩ := deletionAverage_le_member L hL
    (fun T => globalTail R d T * ∏ e ∈ T, (d e ^ 2)⁻¹)
  obtain ⟨hTF, hcard, hreach⟩ := hvalid T hT
  refine ⟨T, hTF, hcard, hreach, hb.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmax
    (prod_nonneg fun v _ => sq_nonneg (s v))

end Ear

end Limits

end MultipoleBKT

end
