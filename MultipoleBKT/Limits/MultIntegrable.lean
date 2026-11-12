/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Limits.RouteBase.Integrand
import MultipoleBKT.Limits.RouteDirect.BlockIntegrable

/-!
# Integrability of the original symmetrized multipole integrand

See Lemma 4.26 of the paper. The public interface follows the merged near/far expansion,
parity on merged blocks, separate odd and even trees, joint logarithmic spatial
integration and final logarithmic absorption of `RouteDirect.BlockIntegrable`.
The integrands and elementary regularity live below it in `RouteBase.Integrand`.
-/

@[expose] public section

namespace MultipoleBKT

namespace Limits

open MeasureTheory Set Finset SimpleGraph Filter
open scoped ENNReal
open TwoComponentCoulomb (box)

variable {χ : ℂ → ℝ} {β lam M : ℝ}

section Integrable

variable {ι β' : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [Fintype β'] [DecidableEq β']

open scoped Classical in
/-- **Integrability of the symmetrized multipole integrand** (Lemma 4.26): for
`|ι| ≤ p*(β)`, `𝟙_{[0,1]²}(x_{i₀}) symBox` is integrable. -/
theorem integrable_anchor_symBox (hχ : IsMollifier χ) (hβ : 2 < β) (hlam : 0 < lam)
    (hM : 1 ≤ M) [Nonempty ι] (hk : (Fintype.card ι : ℕ∞) ≤ pStar β)
    (blk : ι → β') (hblk : Function.Surjective blk) (E : SimpleGraph ι)
    (hEinter : ∀ i j, E.Adj i j → blk i ≠ blk j)
    (hEconn : ∀ S S' : β', (nodeGraph (Sym2.map blk) E.edgeFinset).Reachable S S') (i₀ : ι) :
    Integrable fun c => anchorR i₀ c * symBox χ β lam M blk E c := by
  exact RouteDirect.integrable_anchor_symBox_log hχ hβ hlam hM hk blk hblk E hEinter hEconn i₀

end Integrable

end Limits

end MultipoleBKT

end
