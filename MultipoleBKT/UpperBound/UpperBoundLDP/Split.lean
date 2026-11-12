/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Finset.Sort

/-!
# Splitting the coordinates along a labelling

The decompositions (5.115) and (5.132) in the proof of Proposition 5.38
label each dipole by its type and integrate the dipoles of each type separately, after
dropping the matching constraints between different types. For a labelling
`f : Fin n → Fin K`, with `eⱼ : Fin |f⁻¹(j)| ↪o Fin n` the increasing enumeration of the fibre
`f⁻¹(j)` (`fiberEmb`), Tonelli's inequality gives

  `∫ ∏ⱼ Gⱼ(d ∘ eⱼ) dd ≤ ∏ⱼ ∫ Gⱼ` (`lintegral_prod_fiber_le`),

for every family of functions `Gⱼ` (no measurability is needed), by induction on `K`, splitting
off the fibre `f⁻¹(0)` (`lintegral_split2`, the two-part version of
`MultipoleBKT.BadPointTypes.lintegral_split3`).
-/

@[expose] public section

namespace MultipoleBKT

namespace UpperBoundLDP

open MeasureTheory Finset
open scoped ENNReal

variable {n : ℕ}

/-! ### Two parts -/

/-- The labels `Fin |V| ⊕ Fin |Vᶜ|` of `Fin n`. -/
noncomputable def splitEquiv (V : Finset (Fin n)) : Fin V.card ⊕ Fin Vᶜ.card ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (V.orderEmbOfFin rfl) (Vᶜ.orderEmbOfFin rfl)) (by
    have hm1 := fun a => V.orderEmbOfFin_mem rfl a
    have hm2 := fun a => Vᶜ.orderEmbOfFin_mem rfl a
    constructor
    · rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
      · rw [(V.orderEmbOfFin rfl).injective hab]
      · exact absurd (hab ▸ hm1 a) (Finset.mem_compl.1 (hm2 b))
      · exact absurd (hab ▸ hm1 b) (Finset.mem_compl.1 (hm2 a))
      · rw [(Vᶜ.orderEmbOfFin rfl).injective hab]
    · intro i
      by_cases hi : i ∈ V
      · have : i ∈ Set.range (V.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hi
        obtain ⟨a, rfl⟩ := this
        exact ⟨Sum.inl a, rfl⟩
      · have : i ∈ Set.range (Vᶜ.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact Finset.mem_compl.2 hi
        obtain ⟨a, rfl⟩ := this
        exact ⟨Sum.inr a, rfl⟩)

/-- **Splitting the coordinates in two.** For `V ⊆ Fin n` and any `F`,
`∫ F(d ∘ e_V, d ∘ e_{Vᶜ}) dd = ∫ F`. -/
theorem lintegral_split2 {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (V : Finset (Fin n)) (F : (Fin V.card → α) × (Fin Vᶜ.card → α) → ℝ≥0∞) :
    ∫⁻ d : Fin n → α, F (d ∘ V.orderEmbOfFin rfl, d ∘ Vᶜ.orderEmbOfFin rfl) = ∫⁻ p, F p := by
  set σ := splitEquiv V
  let Φ : (Fin n → α) ≃ᵐ (Fin V.card → α) × (Fin Vᶜ.card → α) :=
    (MeasurableEquiv.piCongrLeft (fun _ => α) σ).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi fun _ => α)
  have hΦ : MeasurePreserving Φ volume volume :=
    ((volume_measurePreserving_piCongrLeft (fun _ => α) σ).symm _).trans
      (volume_measurePreserving_sumPiEquivProdPi fun _ => α)
  have hΦd : ∀ d : Fin n → α, Φ d = (d ∘ V.orderEmbOfFin rfl, d ∘ Vᶜ.orderEmbOfFin rfl) := by
    intro d
    rfl
  calc ∫⁻ d : Fin n → α, F (d ∘ V.orderEmbOfFin rfl, d ∘ Vᶜ.orderEmbOfFin rfl)
      = ∫⁻ d : Fin n → α, F (Φ d) := by simp_rw [hΦd]
    _ = ∫⁻ p, F p := hΦ.lintegral_comp_emb Φ.measurableEmbedding F

/-! ### Fibres of a labelling -/

/-- The fibre `f⁻¹(j)` of a labelling. -/
def fiber {ι : Type*} [DecidableEq ι] (f : Fin n → ι) (j : ι) : Finset (Fin n) :=
  univ.filter fun a => f a = j

theorem mem_fiber {ι : Type*} [DecidableEq ι] {f : Fin n → ι} {j : ι} {a : Fin n} :
    a ∈ fiber f j ↔ f a = j := by
  simp [fiber]

/-- The increasing enumeration of the fibre `f⁻¹(j)`. -/
noncomputable def fiberEmb {ι : Type*} [DecidableEq ι] (f : Fin n → ι) (j : ι) :
    Fin (fiber f j).card ↪o Fin n :=
  (fiber f j).orderEmbOfFin rfl

/-- A function of the configurations of every size, evaluated along two enumerations of the
same set. -/
theorem apply_orderEmbOfFin_congr {α : Type*} (s : Finset (Fin n)) {k : ℕ} (h : s.card = k)
    (G : ∀ m, (Fin m → α) → ℝ≥0∞) (d : Fin n → α) :
    G k (d ∘ s.orderEmbOfFin h) = G s.card (d ∘ s.orderEmbOfFin rfl) := by
  subst h
  rfl

theorem card_fiber_eq_zero_of_fin_zero (f : Fin n → Fin 0) : n = 0 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact h
  · exact (f ⟨0, h⟩).elim0

/-- The sizes of the fibres of a labelling add up to `n`. -/
theorem sum_card_fiber {K : ℕ} (f : Fin n → Fin K) : ∑ j, (fiber f j).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ)
    (fun a _ => Finset.mem_univ (f a))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- `∏_a w(f(a)) = ∏_j w(j)^{|f⁻¹(j)|}`. -/
theorem prod_pow_card_fiber {K : ℕ} {M : Type*} [CommMonoid M] (f : Fin n → Fin K)
    (w : Fin K → M) : ∏ j, w j ^ (fiber f j).card = ∏ a, w (f a) := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := univ) (t := univ) (g := f)
    (fun a _ => Finset.mem_univ (f a)) (fun a => w (f a))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2], Finset.prod_const]
  rfl

/-! ### The induction -/

section Induction

variable {α : Type*} [MeasureSpace α] [SigmaFinite (volume : Measure α)]

/-- The labelling of the complement of `f⁻¹(0)`, shifted down by one. -/
noncomputable def restLabel {K : ℕ} (f : Fin n → Fin (K + 1)) :
    Fin (fiber f 0)ᶜ.card → Fin K := fun b =>
  (f ((fiber f 0)ᶜ.orderEmbOfFin rfl b)).pred (by
    have := (fiber f 0)ᶜ.orderEmbOfFin_mem rfl b
    rw [Finset.mem_compl, mem_fiber] at this
    exact this)

/-- The enumeration of the complement of `f⁻¹(0)`, followed by the enumeration of a fibre of
the shifted labelling, enumerates a fibre of `f`. -/
theorem comp_fiberEmb_restLabel {K : ℕ} (f : Fin n → Fin (K + 1)) (j : Fin K) :
    ∃ h : (fiber f j.succ).card = (fiber (restLabel f) j).card,
      (fun b => (fiber f 0)ᶜ.orderEmbOfFin rfl (fiberEmb (restLabel f) j b)) =
        (fiber f j.succ).orderEmbOfFin h := by
  set W := (fiber f 0)ᶜ
  set e := W.orderEmbOfFin rfl
  set g : Fin (fiber (restLabel f) j).card → Fin n := fun b => e (fiberEmb (restLabel f) j b)
  have hmem : ∀ b, g b ∈ fiber f j.succ := by
    intro b
    have h1 : restLabel f (fiberEmb (restLabel f) j b) = j :=
      mem_fiber.1 ((fiber (restLabel f) j).orderEmbOfFin_mem rfl b)
    rw [mem_fiber]
    unfold restLabel at h1
    rw [← h1, Fin.succ_pred]
    rfl
  have hmono : StrictMono g := e.strictMono.comp (fiberEmb (restLabel f) j).strictMono
  -- the cardinalities agree
  have hcard : (fiber f j.succ).card = (fiber (restLabel f) j).card := by
    have himg : (fiber (restLabel f) j).map e.toEmbedding = fiber f j.succ := by
      ext i
      simp only [Finset.mem_map, mem_fiber]
      constructor
      · rintro ⟨b, hb, rfl⟩
        unfold restLabel at hb
        show f (e b) = j.succ
        rw [← hb, Fin.succ_pred]
      · intro hi
        have hiW : i ∈ W := by
          rw [Finset.mem_compl, mem_fiber, hi]
          exact Fin.succ_ne_zero j
        have : i ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hiW
        obtain ⟨b, rfl⟩ := this
        refine ⟨b, ?_, rfl⟩
        unfold restLabel
        show (f (e b)).pred _ = j
        simp only [hi, Fin.pred_succ]
    rw [← himg, Finset.card_map]
  exact ⟨hcard, Finset.orderEmbOfFin_unique hcard hmem hmono⟩

/-- **Tonelli along a labelling.** For a labelling `f : Fin n → Fin K` and functions `Gⱼ` of
the configurations of every size, finite, with finite integrals,
`∫ ∏ⱼ Gⱼ(d ∘ eⱼ) dd ≤ ∏ⱼ ∫ Gⱼ`, `eⱼ` the increasing enumeration of `f⁻¹(j)`. -/
theorem lintegral_prod_fiber_le : ∀ (K : ℕ) {n : ℕ} (f : Fin n → Fin K)
    (G : Fin K → ∀ m, (Fin m → α) → ℝ≥0∞), (∀ j m y, G j m y ≠ ⊤) →
    (∀ j m, ∫⁻ y, G j m y ≠ ⊤) →
    ∫⁻ d : Fin n → α, ∏ j, G j (fiber f j).card (d ∘ fiberEmb f j) ≤
      ∏ j, ∫⁻ y, G j (fiber f j).card y
  | 0, n, f, G, _, _ => by
    obtain rfl := card_fiber_eq_zero_of_fin_zero f
    simp only [Finset.univ_eq_empty, Finset.prod_empty, lintegral_const, one_mul]
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    simp
  | K + 1, n, f, G, hGpt, hG => by
    set V := fiber f 0
    set f' := restLabel f
    -- the integrand as a function of the two parts
    set H : (Fin V.card → α) × (Fin Vᶜ.card → α) → ℝ≥0∞ := fun q =>
      G 0 V.card q.1 * ∏ j : Fin K, G j.succ (fiber f' j).card (q.2 ∘ fiberEmb f' j) with hH
    have hpt : ∀ d : Fin n → α, ∏ j, G j (fiber f j).card (d ∘ fiberEmb f j) =
        H (d ∘ V.orderEmbOfFin rfl, d ∘ Vᶜ.orderEmbOfFin rfl) := by
      intro d
      rw [Fin.prod_univ_succ]
      simp only [hH]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      obtain ⟨h, hcomp⟩ := comp_fiberEmb_restLabel f j
      have heq : (d ∘ Vᶜ.orderEmbOfFin rfl) ∘ fiberEmb f' j =
          d ∘ (fiber f j.succ).orderEmbOfFin h := by
        rw [← hcomp]
        rfl
      rw [heq, apply_orderEmbOfFin_congr (fiber f j.succ) h (G j.succ) d]
      rfl
    have hIH := lintegral_prod_fiber_le K f' (fun j => G j.succ) (fun j m y => hGpt j.succ m y)
      fun j m => hG j.succ m
    have hfin : ∏ j : Fin K, ∫⁻ y, G j.succ (fiber f' j).card y ≠ ⊤ :=
      ENNReal.prod_ne_top fun j _ => hG j.succ _
    calc ∫⁻ d : Fin n → α, ∏ j, G j (fiber f j).card (d ∘ fiberEmb f j)
        = ∫⁻ d : Fin n → α, H (d ∘ V.orderEmbOfFin rfl, d ∘ Vᶜ.orderEmbOfFin rfl) := by
          simp_rw [hpt]
      _ = ∫⁻ q, H q := lintegral_split2 V H
      _ ≤ ∫⁻ u, ∫⁻ v, H (u, v) := lintegral_prod_le H
      _ = ∫⁻ u, G 0 V.card u *
            ∫⁻ v, ∏ j : Fin K, G j.succ (fiber f' j).card (v ∘ fiberEmb f' j) := by
          refine lintegral_congr fun u => ?_
          simp only [hH]
          rw [lintegral_const_mul' _ _ (hGpt 0 V.card u)]
      _ ≤ ∫⁻ u, G 0 V.card u * ∏ j : Fin K, ∫⁻ y, G j.succ (fiber f' j).card y :=
          lintegral_mono fun u => mul_le_mul_right hIH _
      _ = (∫⁻ u, G 0 V.card u) * ∏ j : Fin K, ∫⁻ y, G j.succ (fiber f' j).card y :=
          lintegral_mul_const' _ _ hfin
      _ = ∏ j, ∫⁻ y, G j (fiber f j).card y := by
          rw [Fin.prod_univ_succ]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          obtain ⟨h, -⟩ := comp_fiberEmb_restLabel f j
          rw [h]

end Induction

end UpperBoundLDP

end MultipoleBKT

end
