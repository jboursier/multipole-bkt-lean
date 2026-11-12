/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Main.TheoremOne.Mayer
public import MultipoleBKT.Main.TheoremOne.Coefficients
public import MultipoleBKT.Main.TheoremTwo.Parameters
public import MultipoleBKT.Cluster.Tail
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Theorem 1 from the gates: item (3)

Item (3) of Theorem 1, eq. (2.40):

  `∑_{n ≥ 1} (1/n!) ∑_{V connected, |Vᵢ| ≤ p} ∏ᵢ 𝖪^dip(Vᵢ) I(G(V)) = -N Mayer_{β,p,λ} + O(N δ)`.

For fixed `λ`, the `n`-th cluster term divided by `N` tends to `-∑_k mayerTerm n k` (only
hypertrees survive: `MultipoleBKT.TheoremOne.tendsto_clusterSum` and
`MultipoleBKT.TheoremOne.clusterLimit_eq_neg_tsum_mayerTerm`), and is bounded by `(C λ²)ⁿ`
uniformly in `N` (Lemma 4.53, `MultipoleBKT.abs_cluster_le'`). By dominated convergence
(`tendsto_tsum_of_dominated_convergence`) the cluster sum is `-N Mayer + o(N)`, and the `o(N)`
is absorbed in `N δ_{β,λ}` for `N ≥ N₀(λ)`. The absolute convergence of the Mayer
double series is `MultipoleBKT.TheoremOne.summable_mayerTerm`.
-/

@[expose] public section

open MeasureTheory Filter Topology Finset

namespace MultipoleBKT

namespace TheoremOne

variable {χ : ℂ → ℝ} {p₀ : ℕ} {β : ℝ}

/-- `λ` small: `c λ < 1` for `0 < λ < 1/(c + 1)` and `c ≥ 0`. -/
theorem mul_lt_one_of_lt_inv_add_one {c lam : ℝ} (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (hlaml : lam < 1 / (c + 1)) : c * lam < 1 := by
  have h1 : 0 < c + 1 := by linarith
  rw [lt_div_iff₀ h1] at hlaml
  nlinarith

open scoped Classical in
/-- **Item (3)** of Theorem 1, eq. (2.40), from a uniform (4.41), the limits (2.34) and a uniform
(2.39) for the sizes `2 ≤ k ≤ p(β)`. -/
theorem item_three (hχ : IsMollifier χ) (hβ : 2 < β)
    {kdip : ℝ → ℕ → ℝ}
    (hlim : ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ j : ℕ, 2 ≤ j → j ≤ pBeta p₀ β →
      Tendsto (fun N : ℕ => (N : ℝ) ^ (j - 1) * dipoleActivity χ N β lam (range j)) atTop
        (𝓝 (kdip lam j)))
    {C₀ lam₁ : ℝ} (hC₀ : 0 < C₀) (hlam₁ : 0 < lam₁) (hlam₁1 : lam₁ ≤ 1)
    (hb : ∀ lam : ℝ, 0 < lam → lam < lam₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ V : Finset ℕ, V ⊆ Finset.range N → 2 ≤ V.card → V.card ≤ pBeta p₀ β →
          |dipoleActivity χ N β lam V| ≤ C₀ * (lam ^ 2 / N) ^ (V.card - 1))
    (hkb : ∀ lam : ℝ, 0 < lam → lam < lam₁ →
      ∀ j : ℕ, 2 ≤ j → j ≤ pBeta p₀ β → |kdip lam j| ≤ C₀ * lam ^ (2 * (j - 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ 1 ∧
      ∀ lam : ℝ, 0 < lam → lam < lam₀ →
        Summable (fun nk : ℕ+ × ℕ+ => ‖mayerTerm (pBeta p₀ β) (kdip lam) nk.1 nk.2‖) ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          let cluster : ℕ+ → ℝ := fun n =>
            1 / (n : ℕ).factorial *
              ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
                  (fun V => (connectionGraph V).Connected ∧
                    ∀ i, (V i).card ≤ pBeta p₀ β),
                (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ)
          Summable (fun n => ‖cluster n‖) ∧
          |∑' n, cluster n - (-N * mayer (pBeta p₀ β) (kdip lam))|
            ≤ C * N * errorRate p₀ β lam := by
  set p := pBeta p₀ β with hp
  obtain ⟨Ct, hCt, htail⟩ := abs_cluster_le' C₀ p
  set E : ℝ := Real.exp 1 with hE
  have hE0 : 0 < E := Real.exp_pos 1
  set lam₀ : ℝ := min lam₁ (min (1 / (Ct + 1)) (min (1 / (E ^ 2 * C₀ + 1)) (1 / (E + 1))))
    with hlam₀
  have hlam₀pos : 0 < lam₀ := lt_min hlam₁ (lt_min (by positivity) (lt_min (by positivity)
    (by positivity)))
  refine ⟨1, one_pos, lam₀, hlam₀pos, (min_le_left _ _).trans hlam₁1, fun lam hlam hlaml => ?_⟩
  have hlam1' : lam < lam₁ := hlaml.trans_le (min_le_left _ _)
  have hlamt : lam < 1 / (Ct + 1) :=
    hlaml.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlamm : lam < 1 / (E ^ 2 * C₀ + 1) :=
    hlaml.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hlame : lam < 1 / (E + 1) :=
    hlaml.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlam_lt1 : lam < 1 := hlam1'.trans_le hlam₁1
  have hq0 : 0 ≤ Ct * lam ^ 2 := by positivity
  have hq : Ct * lam ^ 2 < 1 := by
    have h1 : Ct * lam < 1 := mul_lt_one_of_lt_inv_add_one hCt.le hlam.le hlamt
    have h2 : lam ^ 2 ≤ lam := by nlinarith
    calc Ct * lam ^ 2 ≤ Ct * lam := mul_le_mul_of_nonneg_left h2 hCt.le
      _ < 1 := h1
  -- the Mayer double series converges absolutely
  have hmayer : Summable (fun nk : ℕ+ × ℕ+ => ‖mayerTerm p (kdip lam) nk.1 nk.2‖) := by
    refine summable_mayerTerm hC₀.le hlam.le hlam_lt1.le (hkb lam hlam hlam1') ?_ ?_
    · exact mul_lt_one_of_lt_inv_add_one (by positivity : 0 ≤ E ^ 2 * C₀) hlam.le hlamm
    · exact mul_lt_one_of_lt_inv_add_one hE0.le hlam.le hlame
  refine ⟨hmayer, ?_⟩
  obtain ⟨N₁, hN₁⟩ := hb lam hlam hlam1'
  -- the cluster terms
  obtain ⟨cl, hcl⟩ : ∃ cl : ℕ → ℕ+ → ℝ, ∀ N n, cl N n =
      1 / ((n : ℕ).factorial : ℝ) *
        ∑ V ∈ (Fintype.piFinset fun _ : Fin n => (Finset.range N).powerset).filter
            (fun V => (connectionGraph V).Connected ∧ ∀ i, (V i).card ≤ p),
          (∏ i, dipoleActivity χ N β lam (V i)) * (ursell (connectionGraph V) : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  have hK1 : ∀ N, ∀ X ⊆ Finset.range N, X.card < 2 → dipoleActivity χ N β lam X = 0 :=
    fun N X _ hX => dipoleActivity_eq_zero_of_card_le_one χ N β lam (by omega)
  have hbound : ∀ N, max N₁ 1 ≤ N → ∀ n : ℕ+, |cl N n| ≤ N * (Ct * lam ^ 2) ^ (n : ℕ) :=
    fun N hN n => by
      rw [hcl]
      exact htail N (dipoleActivity χ N β lam) lam n ((le_max_right _ _).trans hN)
        (hK1 N) (hN₁ N ((le_max_left _ _).trans hN)) hlam hlam_lt1.le n.pos
  -- each cluster term, divided by `N`, tends to `-∑_k mayerTerm n k`
  have hterm : ∀ n : ℕ+, Tendsto (fun N : ℕ => 1 / (N : ℝ) * cl N n) atTop
      (𝓝 (-∑' k : ℕ+, mayerTerm p (kdip lam) n k)) := by
    intro n
    have hκ : ∀ N j, j ≤ 1 → dipoleActivity χ N β lam (range j) = 0 := fun N j hj =>
      dipoleActivity_eq_zero_of_card_le_one χ N β lam (by rw [card_range]; exact hj)
    have h := (tendsto_clusterSum (n := (n : ℕ)) p (κ := fun N j => dipoleActivity χ N β lam
      (range j)) (a := kdip lam) hκ (hlim lam hlam hlam_lt1)
      isRelabelInvariant_ursell).const_mul (1 / ((n : ℕ).factorial : ℝ))
    rw [clusterLimit_eq_neg_tsum_mayerTerm] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [hcl]
    have hprod : ∀ V : Fin n → Finset ℕ, ∏ i, dipoleActivity χ N β lam (V i) =
        ∏ i, dipoleActivity χ N β lam (range (V i).card) := fun V =>
      prod_congr rfl fun i _ => dipoleActivity_eq_range_card hχ hlam hN (V i)
    simp only [← hprod]
    ring
  -- dominated convergence
  have hdom : Tendsto (fun N : ℕ => ∑' n : ℕ+, 1 / (N : ℝ) * cl N n) atTop
      (𝓝 (∑' n : ℕ+, -∑' k : ℕ+, mayerTerm p (kdip lam) n k)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n : ℕ+ => (Ct * lam ^ 2) ^ (n : ℕ))
      ((summable_geometric_of_lt_one hq0 hq).comp_injective PNat.coe_injective) hterm ?_
    filter_upwards [eventually_ge_atTop (max N₁ 1)] with N hN n
    have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    calc 1 / (N : ℝ) * |cl N n| ≤ 1 / (N : ℝ) * (N * (Ct * lam ^ 2) ^ (n : ℕ)) :=
          mul_le_mul_of_nonneg_left (hbound N hN n) (by positivity)
      _ = (Ct * lam ^ 2) ^ (n : ℕ) := by field_simp
  have hmay : ∑' n : ℕ+, -∑' k : ℕ+, mayerTerm p (kdip lam) n k = -mayer p (kdip lam) := by
    rw [tsum_neg]
    rfl
  rw [hmay] at hdom
  have hδ : 0 < errorRate p₀ β lam := TheoremTwo.errorRate_pos hβ hlam
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hdom) _ hδ)
  refine ⟨max (max N₁ 1) N₂, fun N hN => ?_⟩
  intro cluster
  have hNb : max N₁ 1 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hNb
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hclus : ∀ n, cluster n = cl N n := fun n => (hcl N n).symm
  have hsum : Summable (fun n => ‖cluster n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by rw [hclus, Real.norm_eq_abs]; exact hbound N hNb n)
      (((summable_geometric_of_lt_one hq0 hq).comp_injective PNat.coe_injective).mul_left
        (N : ℝ))
  refine ⟨hsum, ?_⟩
  have hdist := hN₂ N ((le_max_right _ _).trans hN)
  rw [Real.dist_eq, tsum_mul_left] at hdist
  have heq : ∑' n, cluster n - (-N * mayer p (kdip lam)) =
      N * (1 / (N : ℝ) * ∑' n : ℕ+, cl N n - -mayer p (kdip lam)) := by
    rw [tsum_congr hclus]
    field_simp
  rw [heq, abs_mul, abs_of_pos hNpos, one_mul]
  exact mul_le_mul_of_nonneg_left hdist.le hNpos.le

end TheoremOne

end MultipoleBKT

end
