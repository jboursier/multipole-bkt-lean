/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.SmallIntegral.TreeTerm
public import MultipoleBKT.Appendix.SmallIntegral.Forest
public import MultipoleBKT.Cluster.Relative
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Hatted odd weights and edge distances

See Proposition 4.23 and (A.17). These elementary
interfaces are shared by the separate-tree reductions and the J integrands.
-/

@[expose] public section

namespace MultipoleBKT

namespace SmallIntegral

open Finset SimpleGraph
open Limits

variable {M lam : ℝ}

/-! ### The weights -/

section Weights

variable {ι : Type*}

theorem ahat_comm (d e : ℂ × ℂ) : ahat d e = ahat e d := by
  unfold ahat
  rw [dipoleDist_comm, mul_comm ‖d.1 - d.2‖, max_comm ‖d.1 - d.2‖]

open scoped Classical in
/-- The odd majorant `min(1, â_ij) 𝟙_{𝓑_ij^c}`. -/
noncomputable def oddMaj (M lam : ℝ) (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => if MultipoleLinked M lam (c i) (c j) then 0 else min 1 (ahat (c i) (c j)))
    fun i j => by rw [ahat_comm]; exact if_congr multipoleLinked_comm rfl rfl

open scoped Classical in
/-- The dipole distance as a function of unordered pairs of labels. -/
noncomputable def distE (c : ι → ℂ × ℂ) : Sym2 ι → ℝ :=
  symmLift (fun i j => dipoleDist (c i) (c j)) fun _ _ => dipoleDist_comm _ _

theorem oddMaj_nonneg (c : ι → ℂ × ℂ) (e : Sym2 ι) : 0 ≤ oddMaj M lam c e := by
  classical
  induction e using Sym2.ind with
  | h i j =>
    show 0 ≤ (if MultipoleLinked M lam (c i) (c j) then 0 else min 1 (ahat (c i) (c j)))
    split_ifs
    · exact le_rfl
    · exact le_min zero_le_one (ahat_nonneg _ _)

end Weights
end SmallIntegral

end MultipoleBKT

end
