/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.RouteLog.Absorption
public import MultipoleBKT.Appendix.RouteLog.EvenEdge
public import MultipoleBKT.Appendix.RouteLog.JointTail
public import MultipoleBKT.Appendix.RouteLog.OrderedBounds
public import MultipoleBKT.Appendix.RouteLog.Root

/-!
# Appendix A logarithmic spatial and radial API

See the proof of Lemma A.4 and (A.41) through (A.44).

The namespace `MultipoleBKT.RouteLog` exports:

* `joint_maximum_tail_integral`, with one tail for the maximum of all odd edges.
* `lintegral_evenEdgeProfile_le`, with the even-edge factor `s² (1 + log(t/s))`.
* `lintegral_planar_truncated_inverse_square` and `lintegral_cappedInverseSquare_le`,
  for a single endpoint and a finite family of translated bad endpoints.
* `ordered_radial_lt_four` and `ordered_radial_ge_four_bound`, for the ordered
  logarithmic radial moments. The latter includes the critical temperature.
* `radial_cutoff_gain_lt_four`, `radial_cutoff_gain_four`, and
  `radial_cutoff_gain_gt_four`, which retain the logarithms in the three regimes.
* `radial_cutoff_gain`, where the paper finally absorbs those logarithms.

The moment parameters are natural numbers, as they count logarithmic factors.
Families with `k+1` or `k+2` indices express nonempty families without an extra
proof parameter. Integrals over `Ioc` or `Ioi` use Lebesgue measure, so their
endpoint conventions do not change the paper's integrals.
-/

public section

end
