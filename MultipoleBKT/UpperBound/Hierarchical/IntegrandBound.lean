/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.UpperBound.Hierarchical.Locality
public import MultipoleBKT.UpperBound.Hierarchical.PlusModel
public import MultipoleBKT.UpperBound.BadPoints.EnergyBound

/-!
# Isolating the good points: the bound on the Gibbs weight (Step 4 of Lemma 5.16)

The paper: Steps 3–4 of the proof of Lemma 5.16: on the event `{σ_N = Id, I_bad = V_bad, Π_mult^{V_good} = π}`, eq. (5.50) bounds
`e^{-β F_λ}` by a product of a factor of the bad dipoles alone (`badWeightZ`), of the dipole
densities `e^{β g_λ(x_i - y_i)} 𝟙_{|x_i - y_i| ≤ ε₀ R̄}` of the good dipoles, and of the cluster
weight of the good dipoles in the model with frozen bad points `Z = (x_j, y_j)_{j ∈ V_bad}`
(`exp_neg_energy_le`):

`e^{-β F_λ} ≤ e^{L |V_bad|} badWeightZ(Z) ∏_{i ∈ V_good} e^{β g_λ(r_i)} 𝟙_{r_i ≤ ε₀ R̄}
  (∏_{S ∈ π} bŵ_S) ∏_{ij ∈ ℰ^inter(π)} e^{-β v^Z_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c}`,

with `L = β L₀` and `bŵ_S = 𝟙_{𝓑_S} ∏_{i<j ∈ S} e^{-β v^Z_ij} 𝟙_{𝒜_ij} ∏_{i ∈ S} e^{L r_i²/(τ_i^Z)²}
𝟙_{i ∈ I_good^Z} ∏_{j ∈ V_bad} e^{-β v^Z_ij}`. The good dipoles are relabelled by `ℕ`
(`natConfig`). The ingredients: eq. (5.50) (`MultipoleBKT.UpperBound.eq_b1`, here as the predicate
`EnergyLowerBound χ L₀` on the constant, `exists_energyLowerBound`), the locality of the bad points (Remark 5.17,
`MultipoleBKT.UpperBound.Hierarchical.Locality`), `I_good ⊆ I_good^Z`, `σ_N = Id ⟺ ⋂ 𝒜_ij`
(eq. (5.64)) and `r_i ≤ ε₀ R̄` for good dipoles (Remark 5.6). The paper drops the
indicators `𝟙_{𝓑_ij^c} 𝟙_{𝒜_ij}` of the good–bad pairs; here they are bounded by `1`.
-/

@[expose] public section

open MeasureTheory Finset Metric
open TwoComponentCoulomb (logKernel box)

namespace MultipoleBKT

namespace UpperBound

open Hierarchical Multipole SetPartition Parity

variable {N : ℕ}

/-! ### Relabelling by `ℕ` -/

section Relabel

/-- The configuration of all labels `ℕ` extending a configuration of `Fin N` by `0`. -/
def natConfig (c : Fin N → ℂ × ℂ) : ℕ → ℂ × ℂ :=
  fun n => if h : n < N then c ⟨n, h⟩ else 0

theorem natConfig_apply (c : Fin N → ℂ × ℂ) (i : Fin N) : natConfig c i = c i := by
  simp [natConfig, i.isLt]

/-- The pairs `i < j` of a set of labels of `Fin N`, read in `ℕ`. -/
theorem pairsOn_map_val (G : Finset (Fin N)) :
    pairsOn (G.map Fin.valEmbedding) =
      ((G ×ˢ G).filter fun x => x.1 < x.2).map
        ⟨fun x => ((x.1 : ℕ), (x.2 : ℕ)), fun x y h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)⟩ := by
  ext ⟨q1, q2⟩
  simp only [mem_pairsOn, Finset.mem_map, Finset.mem_filter, Finset.mem_product,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hlt⟩
    exact ⟨(i, j), ⟨⟨hi, hj⟩, hlt⟩, rfl⟩
  · rintro ⟨⟨i, j⟩, ⟨⟨hi, hj⟩, hlt⟩, h⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    subst h1 h2
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hlt⟩

theorem prod_pairsOn_map_val {M : Type*} [CommMonoid M] (G : Finset (Fin N)) (F : ℕ → ℕ → M) :
    ∏ q ∈ pairsOn (G.map Fin.valEmbedding), F q.1 q.2 =
      ∏ i ∈ G, ∏ j ∈ G with i < j, F i j := by
  rw [pairsOn_map_val, Finset.prod_map, Finset.prod_filter, Finset.prod_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter]
  rfl

end Relabel

/-! ### Splitting the pair sum -/

section Split

/-- `∑_{i<j} f_ij = ∑_{i<j ∈ V} f_ij + ∑_{i<j ∈ G} f_ij + ∑_{i ∈ G} ∑_{j ∈ V} f_ij` for a
symmetric `f` and `G = [N] ∖ V`. -/
theorem sum_lt_split (V : Finset (Fin N)) (f : Fin N → Fin N → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j with i < j, f i j =
      ∑ i ∈ V, ∑ j ∈ V with i < j, f i j + ∑ i ∈ univ \ V, ∑ j ∈ univ \ V with i < j, f i j +
        ∑ i ∈ univ \ V, ∑ j ∈ V, f i j := by
  classical
  set G := univ \ V
  have hVG : Disjoint V G := Finset.disjoint_sdiff
  have hU : (univ : Finset (Fin N)) = V ∪ G := (Finset.union_sdiff_of_subset (subset_univ V)).symm
  have hsplit : ∀ i : Fin N, ∑ j with i < j, f i j =
      ∑ j ∈ V with i < j, f i j + ∑ j ∈ G with i < j, f i j := by
    intro i
    rw [hU, Finset.filter_union, Finset.sum_union (Finset.disjoint_filter_filter hVG)]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, hU, Finset.sum_union hVG, Finset.sum_union hVG]
  -- the mixed terms
  have hmix : ∑ i ∈ V, ∑ j ∈ G with i < j, f i j + ∑ i ∈ G, ∑ j ∈ V with i < j, f i j =
      ∑ i ∈ G, ∑ j ∈ V, f i j := by
    have h1 : ∑ i ∈ V, ∑ j ∈ G with i < j, f i j = ∑ i ∈ G, ∑ j ∈ V with j < i, f i j := by
      rw [Finset.sum_comm' (t' := G) (s' := fun j => V.filter fun i => i < j)]
      · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hf i j
      · intro i j
        simp only [Finset.mem_filter]
        tauto
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_filter_add_sum_filter_not V (fun j => j < i) (f i)]
    refine congrArg₂ (· + ·) rfl (Finset.sum_congr ?_ fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, not_lt]
    constructor
    · rintro ⟨hj, hlt⟩
      exact ⟨hj, hlt.le⟩
    · rintro ⟨hj, hle⟩
      refine ⟨hj, lt_of_le_of_ne hle fun h => ?_⟩
      subst h
      exact Finset.disjoint_left.1 hVG hj hi
  linarith [hmix]

end Split

/-! ### The cluster threshold -/

theorem one_le_clusterThreshold {p₀ : ℕ} {β : ℝ} (hβ : 2 < β) : 1 ≤ clusterThreshold p₀ β := by
  unfold clusterThreshold
  split_ifs with h
  · rw [Nat.one_le_floor_iff]
    have h1 : 0 < 2 - β / 2 := by linarith
    rw [le_div_iff₀ h1]
    linarith
  · omega

/-! ### Eq. (5.50) -/

/-- **Eq. (5.50)** with the constant `L₀` (the paper's `L/β`): the statement
of `MultipoleBKT.UpperBound.eq_b1` for a given `L₀`. -/
def EnergyLowerBound (χ : ℂ → ℝ) (L₀ : ℝ) : Prop :=
  ∀ {N : ℕ} (p₀ : ℕ) (β lam M ε₀ : ℝ) (d : Fin N → ℂ × ℂ), 0 < lam →
    -(∑ i ∈ goodPoints p₀ β lam M ε₀ d, smearedKernel χ lam ((d i).1 - (d i).2)) -
        (1 / 2) * ∑ i ∈ badPoints p₀ β lam M ε₀ d,
          (logKernel (radiusPlusZ p₀ β lam M ε₀ d i) + logKernel (radiusMinusZ p₀ β lam M ε₀ d i)) +
        ∑ i, ∑ j with i < j, interactionZ χ p₀ β lam M ε₀ d i j -
        L₀ * ∑ i ∈ goodPoints p₀ β lam M ε₀ d,
          (‖(d i).1 - (d i).2‖ / radiusPlusZ p₀ β lam M ε₀ d i) ^ 2 -
        L₀ * (badPoints p₀ β lam M ε₀ d).card ≤
      energy χ lam d

/-- **Eq. (5.50)**: there is `L₀ > 0`, depending only on `χ`, with `EnergyLowerBound χ L₀`
(`MultipoleBKT.UpperBound.eq_b1`). -/
theorem exists_energyLowerBound {χ : ℂ → ℝ} (hχ : IsMollifier χ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ EnergyLowerBound χ L₀ := by
  obtain ⟨L₀, hL₀, h⟩ := eq_b1 hχ
  exact ⟨L₀, hL₀, fun p₀ β lam M ε₀ d hlam => h p₀ β lam M ε₀ d hlam⟩

/-! ### The bound -/

section Bound

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β lam M ε₀ : ℝ}

/-- The density `e^{β g_λ(x - y)} 𝟙_{|x - y| ≤ ε₀ R̄}` of the dipole measure `μ_{β,λ,ε₀}`, up to the
normalization. -/
noncomputable def cutoffDensity (χ : ℂ → ℝ) (p₀ : ℕ) (β lam ε₀ : ℝ) (q : ℂ × ℂ) : ℝ :=
  (closedBall (0 : ℂ) (ε₀ * truncationScale p₀ β lam)).indicator
    (fun w => Real.exp (β * smearedKernel χ lam w)) (q.1 - q.2)

/-- The cluster weight of the good dipoles: `(∏_{S ∈ π} bŵ_S) ∏_{ij ∈ ℰ^inter(π)} (1 + u_ij)` in
the model `(v^Z, ψ̂)` with frozen bad points `Z`. -/
noncomputable def goodClusterWeight (χ : ℂ → ℝ) (p₀ : ℕ) (β lam M ε₀ L : ℝ) (V : Finset (Fin N))
    (Z : Fin N → ℂ × ℂ) (π : Finset (Finset ℕ)) (c : ℕ → ℂ × ℂ) : ℝ :=
  clusterWeight (blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V Z)
      (hatDipoleWeightZ χ p₀ β lam M ε₀ L V Z) M lam)
    (unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V Z) M lam) π c

open scoped Classical in
/-- **The bound on the Gibbs weight** (Steps 3–4 of Lemma 5.16): on
`{σ_N = Id, I_bad = V, ⋂_{S ∈ π} 𝓑_S, ⋂_{ij ∈ ℰ^inter(π)} 𝓑_ij^c}` (for a configuration with
distinct same-sign distances), with `L = β L₀`,
`e^{-β F_λ} ≤ e^{L |V|} badWeightZ ∏_{i ∉ V} e^{β g_λ(r_i)} 𝟙_{r_i ≤ ε₀ R̄}
  (∏_{S ∈ π} bŵ_S) ∏_{ij ∈ ℰ^inter(π)} e^{-β v^Z_ij} 𝟙_{𝒜_ij} 𝟙_{𝓑_ij^c}`. -/
theorem exp_neg_energy_le {L₀ : ℝ} (hχ : IsMollifier χ) (hb1 : EnergyLowerBound χ L₀)
    (hβ : 2 < β) (hlam : 0 < lam) (hM : 0 ≤ M) {V : Finset (Fin N)} {π : Finset (Finset ℕ)}
    (hπ : π ∈ partitions ((univ \ V).map Fin.valEmbedding)) {c : Fin N → ℂ × ℂ}
    (hσ : stableMatching c = Equiv.refl _) (hV : badPoints p₀ β lam M ε₀ c = V)
    (hconn : ∀ S ∈ π, ConnOn S (linkedPairs M lam (natConfig c) S))
    (hinter : ∀ q ∈ interPairs π, ¬ MultipoleLinked M lam (natConfig c q.1) (natConfig c q.2))
    (hgen : ClusterGeneric c) :
    Real.exp (-β * energy χ lam c) ≤
      Real.exp (β * L₀ * V.card) * badWeightZ χ p₀ β lam M ε₀ V c *
        (∏ i ∈ univ \ V, cutoffDensity χ p₀ β lam ε₀ (c i)) *
        goodClusterWeight χ p₀ β lam M ε₀ (β * L₀) V c π (natConfig c) := by
  have hq := one_le_clusterThreshold (p₀ := p₀) hβ
  have hβ0 : 0 ≤ β := by linarith
  subst hV
  set V := badPoints p₀ β lam M ε₀ c with hVdef
  set G := univ \ V with hGdef
  have hG : G = goodPoints p₀ β lam M ε₀ c := rfl
  have hstab : ∀ i j : Fin N, i < j → IsStableDipolePair (c i) (c j) :=
    (stableMatching_eq_refl_iff c).1 hσ
  -- the radii
  have hτG : ∀ i ∈ G, (radiusPlusZ p₀ β lam M ε₀ c i, radiusMinusZ p₀ β lam M ε₀ c i) =
      (goodRadiusZ p₀ β lam ε₀ V c (c i), goodRadiusZ p₀ β lam ε₀ V c (c i)) :=
    fun i hi => radii_eq_of_good hi
  have hτV : ∀ i ∈ V, (radiusPlusZ p₀ β lam M ε₀ c i, radiusMinusZ p₀ β lam M ε₀ c i) =
      badRadiiZ p₀ β lam ε₀ V c i :=
    fun i hi => radii_eq_of_bad hq hgen hi
  have hτpos : ∀ i ∈ V, 0 < badRadiusPlusOn p₀ β lam ε₀ V c i ∧
      0 < badRadiusMinusOn p₀ β lam ε₀ V c i := fun i _ =>
    ⟨hlam.trans_le (lam_le_badRadiusPlusOn i), hlam.trans_le (lam_le_badRadiusMinusOn i)⟩
  -- the energy bound, with the pair sum split
  have hE := hb1 p₀ β lam M ε₀ c hlam
  set f : Fin N → Fin N → ℝ := fun i j => interactionZ χ p₀ β lam M ε₀ c i j with hfdef
  have hfs : ∀ i j, f i j = f j i := fun i j => interactionZ_comm hχ p₀ β M ε₀ c i j
  rw [sum_lt_split V f hfs] at hE
  have hVV : ∑ i ∈ V, ∑ j ∈ V with i < j, f i j =
      ∑ i ∈ V, ∑ j ∈ V with i < j, interactionBadZ χ p₀ β lam ε₀ V c i j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [hfdef, interactionZ_eq_pairInteraction, interactionBadZ, hτV i hi,
      hτV j (Finset.mem_filter.1 hj).1]
  have hGG : ∑ i ∈ G, ∑ j ∈ G with i < j, f i j =
      ∑ i ∈ G, ∑ j ∈ G with i < j, interactionGoodZ χ p₀ β lam ε₀ V c (c i) (c j) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [hfdef, interactionZ_eq_pairInteraction, interactionGoodZ, hτG i hi,
      hτG j (Finset.mem_filter.1 hj).1]
  have hGV : ∑ i ∈ G, ∑ j ∈ V, f i j =
      ∑ i ∈ G, ∑ j ∈ V, interactionExtZ χ p₀ β lam ε₀ V c (c i) j := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    simp only [hfdef, interactionZ_eq_pairInteraction, interactionExtZ, hτG i hi, hτV j hj]
  have hlogV : ∑ i ∈ V, (logKernel (radiusPlusZ p₀ β lam M ε₀ c i) +
        logKernel (radiusMinusZ p₀ β lam M ε₀ c i)) =
      ∑ i ∈ V, (logKernel (badRadiusPlusOn p₀ β lam ε₀ V c i) +
        logKernel (badRadiusMinusOn p₀ β lam ε₀ V c i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hτV i hi
    simp only [badRadiiZ, Prod.mk.injEq] at this
    rw [this.1, this.2]
  have hrG : ∑ i ∈ goodPoints p₀ β lam M ε₀ c,
        (‖(c i).1 - (c i).2‖ / radiusPlusZ p₀ β lam M ε₀ c i) ^ 2 =
      ∑ i ∈ G, (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V c (c i)) ^ 2 := by
    refine Finset.sum_congr hG.symm fun i hi => ?_
    rw [goodRadiusZ_badPoints hi]
  rw [hVV, hGG, hGV, hlogV, hrG, ← hG] at hE
  -- the right-hand side as an exponential
  -- (a) the bad factor
  have hbad : badWeightZ χ p₀ β lam M ε₀ V c =
      Real.exp (∑ i ∈ V, ∑ j ∈ V with i < j, -β * interactionBadZ χ p₀ β lam ε₀ V c i j +
        (β / 2) * ∑ i ∈ V, (logKernel (badRadiusPlusOn p₀ β lam ε₀ V c i) +
          logKernel (badRadiusMinusOn p₀ β lam ε₀ V c i))) := by
    unfold badWeightZ
    rw [ite_eq_left (badPointsOn_badPoints hq hgen), one_mul, Real.exp_add, Finset.mul_sum,
      Real.exp_sum, Real.exp_sum]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [ite_eq_left (hstab i j (Finset.mem_filter.1 hj).2)]
    · refine Finset.prod_congr rfl fun i hi => ?_
      obtain ⟨hp, hm⟩ := hτpos i hi
      unfold logKernel
      rw [Complex.norm_real, Real.norm_of_nonneg hp.le, Complex.norm_real,
        Real.norm_of_nonneg hm.le, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hm,
        ← Real.exp_add, one_div, ← Real.exp_neg]
      congr 1
      ring
  -- (b) the good densities
  have hdens : ∏ i ∈ G, cutoffDensity χ p₀ β lam ε₀ (c i) =
      Real.exp (∑ i ∈ G, β * smearedKernel χ lam ((c i).1 - (c i).2)) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i hi => ?_
    unfold cutoffDensity
    rw [Set.indicator_of_mem]
    rw [mem_closedBall, dist_zero_right]
    exact norm_le_of_good (hG ▸ hi)
  -- (c) the cluster weight of the good dipoles
  have hcw : goodClusterWeight χ p₀ β lam M ε₀ (β * L₀) V c π (natConfig c) =
      Real.exp (∑ i ∈ G, ∑ j ∈ G with i < j, -β * interactionGoodZ χ p₀ β lam ε₀ V c (c i) (c j) +
        ∑ i ∈ G, (β * L₀ * (‖(c i).1 - (c i).2‖ / goodRadiusZ p₀ β lam ε₀ V c (c i)) ^ 2 +
          ∑ j ∈ V, -β * interactionExtZ χ p₀ β lam ε₀ V c (c i) j)) := by
    have hπs := (mem_partitions.1 hπ).1
    have hπV : π.biUnion id = G.map Fin.valEmbedding := (mem_partitions.1 hπ).2
    have hgood : ∀ n ∈ π.biUnion id, ∃ i ∈ G, (i : ℕ) = n := fun n hn => by
      rw [hπV, Finset.mem_map] at hn
      obtain ⟨i, hi, rfl⟩ := hn
      exact ⟨i, hi, rfl⟩
    -- the pair weights
    have hsw : ∀ q ∈ pairsOn (π.biUnion id),
        stableWeight β (interactionGoodZ χ p₀ β lam ε₀ V c) (natConfig c q.1) (natConfig c q.2) =
          Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c (natConfig c q.1)
            (natConfig c q.2)) := by
      rintro ⟨q1, q2⟩ hq'
      obtain ⟨h1, h2, h12⟩ := mem_pairsOn.1 hq'
      obtain ⟨i, -, rfl⟩ := hgood _ h1
      obtain ⟨j, -, rfl⟩ := hgood _ h2
      unfold stableWeight
      rw [natConfig_apply, natConfig_apply, ite_eq_left (hstab i j h12)]
    -- the one-body weights
    have hψ : ∀ n ∈ π.biUnion id,
        hatDipoleWeightZ χ p₀ β lam M ε₀ (β * L₀) V c (natConfig c n) =
          Real.exp (β * L₀ * (‖(natConfig c n).1 - (natConfig c n).2‖ /
            goodRadiusZ p₀ β lam ε₀ V c (natConfig c n)) ^ 2 +
            ∑ j ∈ V, -β * interactionExtZ χ p₀ β lam ε₀ V c (natConfig c n) j) := by
      intro n hn
      obtain ⟨i, hi, rfl⟩ := hgood n hn
      rw [natConfig_apply]
      unfold hatDipoleWeightZ dipoleWeightZ
      rw [ite_eq_left (isGoodZ_of_good hq hM hgen (hG ▸ hi)), mul_one, Real.exp_add, Real.exp_sum]
    unfold goodClusterWeight clusterWeight
    -- rewrite the blocks
    have hblock : ∀ S ∈ π, blockWeightOf β (interactionGoodZ χ p₀ β lam ε₀ V c)
        (hatDipoleWeightZ χ p₀ β lam M ε₀ (β * L₀) V c) M lam S (natConfig c) =
        (∏ q ∈ pairsOn S, Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c (natConfig c q.1)
          (natConfig c q.2))) *
        ∏ n ∈ S, hatDipoleWeightZ χ p₀ β lam M ε₀ (β * L₀) V c (natConfig c n) := by
      intro S hS
      unfold blockWeightOf
      rw [ite_eq_left (hconn S hS), one_mul]
      congr 1
      exact Finset.prod_congr rfl fun q hq' => hsw q (pairsOn_mono
        (subset_biUnion_of_mem hS) hq')
    have hinter' : ∀ q ∈ interPairs π, 1 + unlinkedBondOf β (interactionGoodZ χ p₀ β lam ε₀ V c)
        M lam (natConfig c q.1) (natConfig c q.2) =
        Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c (natConfig c q.1) (natConfig c q.2)) := by
      intro q hq'
      unfold unlinkedBondOf
      rw [ite_eq_right (hinter q hq'), add_sub_cancel, hsw q (interPairs_subset_pairsOn hq')]
    rw [Finset.prod_congr rfl hblock, Finset.prod_congr rfl hinter', Finset.prod_mul_distrib]
    -- the pairs
    have hpairs : (∏ S ∈ π, ∏ q ∈ pairsOn S, Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c
          (natConfig c q.1) (natConfig c q.2))) *
        ∏ q ∈ interPairs π, Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c (natConfig c q.1)
          (natConfig c q.2)) =
        ∏ q ∈ pairsOn (π.biUnion id), Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c
          (natConfig c q.1) (natConfig c q.2)) := by
      have hintra : ∏ S ∈ π, ∏ q ∈ pairsOn S, Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c
          (natConfig c q.1) (natConfig c q.2)) =
          ∏ q ∈ intraPairs π, Real.exp (-β * interactionGoodZ χ p₀ β lam ε₀ V c
            (natConfig c q.1) (natConfig c q.2)) := by
        rw [intraPairs, Finset.prod_biUnion]
        intro S hS T hT hST
        rw [Function.onFun, Finset.disjoint_left]
        intro q hqS hqT
        have := Finset.disjoint_left.1 (disjoint_of_isSubpartition hπs hS hT hST)
          (mem_pairsOn.1 hqS).1
        exact this (mem_pairsOn.1 hqT).1
      rw [hintra, ← Finset.prod_union (disjoint_interPairs_intraPairs (X := π)).symm]
      congr 1
      rw [interPairs, Finset.union_sdiff_of_subset intraPairs_subset_pairsOn]
    rw [mul_right_comm, hpairs, hπV, prod_pairsOn_map_val G (fun a b => Real.exp
      (-β * interactionGoodZ χ p₀ β lam ε₀ V c (natConfig c a) (natConfig c b)))]
    have hprodπ : ∏ S ∈ π, ∏ n ∈ S, hatDipoleWeightZ χ p₀ β lam M ε₀ (β * L₀) V c (natConfig c n) =
        ∏ n ∈ π.biUnion id, hatDipoleWeightZ χ p₀ β lam M ε₀ (β * L₀) V c (natConfig c n) :=
      (Finset.prod_biUnion hπs.2).symm
    rw [hprodπ, Finset.prod_congr rfl hψ, hπV, Finset.prod_map]
    simp only [Fin.valEmbedding_apply, natConfig_apply]
    rw [Real.exp_add, Real.exp_sum, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
  -- combining
  rw [hbad, hdens, hcw, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hβE := mul_le_mul_of_nonneg_left hE hβ0
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hβE ⊢
  rw [← hVdef] at hβE
  nlinarith [hβE]

end Bound

end UpperBound

end MultipoleBKT

end
