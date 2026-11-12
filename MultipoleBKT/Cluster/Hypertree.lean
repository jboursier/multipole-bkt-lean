/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Cluster.RouteChromatic.Polynomial

/-!
# The Ursell function of a hypertree

The proof follows the argument for (4.150) in the paper. The incidence graph is a tree. Rooting it gives a bijection
between proper colorings and a root color together with distinct child colors
at every element. These coloring counts determine the whole chromatic polynomial
`T ∏_a ∏_{j=1}^{d_a-1} (T-j)`. Inclusion-exclusion identifies its linear
coefficient with the Ursell function, and the incidence count gives the sign.
-/

@[expose] public section

namespace MultipoleBKT

open Finset SimpleGraph

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- The hypertree identity `I(G(X)) = (-1)^(n-1) ω(X)`, obtained from the
linear coefficient of the whole connection-graph chromatic polynomial.
See (4.150). -/
theorem ursell_connectionGraph_of_mem_hypertrees {A : Finset α} {X : Fin n → Finset α}
    (hX : X ∈ hypertrees n A) :
    ursell (connectionGraph X) = (-1) ^ (n - 1) * (hypertreeWeight X : ℤ) := by
  rw [← coeff_one_chromaticPoly,
    chromaticPoly_connectionGraph_of_mem_hypertrees hX]
  exact coeff_one_hypertreeChromaticPoly hX

end MultipoleBKT

end
