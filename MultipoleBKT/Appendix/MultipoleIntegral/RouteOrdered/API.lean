/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.Configuration
public import MultipoleBKT.Appendix.MultipoleIntegral.RouteOrdered.LegacyConstant

/-!
# Ordered multipole integration API

See (A.6) through
(A.14).

The API exposes the measurable endpoint-cell cover, the bijective and
measure-preserving tree coordinate map, the integral on a fixed realization
cell, the spanning-tree union bound, the ordering estimate of Lemma A.1, the exact polar
reduction of a single tree, and the separate radial temperature estimates.

`orderedRadial` is the literal nested integral in (A.13). Its comparison to
the separated-core majorant is `orderedRadial_le_logMajorant`. Finite
cutoffs have low, critical, and high estimates. Infinite cutoffs require
the negative-exponent condition below four and allow every size at or above
four. `Configuration` assembles the tree and endpoint sums for connected
weights, including finite-cutoff gamma normalization. `UpperBound` provides
the explicit-constant bounds through a numerical comparison.
-/

public section

end
