/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.CutoffGain
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.OmittedMixed
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.LongEvenTree
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailAbsorption
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.SourceRoot
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.MarkedNormalization
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.TailSectors
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.CaseF
public import MultipoleBKT.Appendix.GeneralExpansionK.RouteSpatial.LongEndpoint

/-!
# Logarithmic activity-tree integration

See Lemma A.7. The ordinary and marked normalized trees have weighted
configuration bounds for both models. Omitted odd coordinates retain
their quadratic cutoff gain and one maximum tail. The retained even mark
uses its quartic exterior integral. The ordered case-F radial bounds
keep all three physical temperature regimes before final absorption.

The complete actual-model entry points are `screened_mixed_integral`,
`frozen_mixed_integral` and `caseF_baseline_integral`. Their constants
precede lambda and the frozen data. They use the separate odd-tree families,
finite shape envelopes, actual roots and logarithmic vector integrals.

The omitted domain additionally has exact tail transport and a full
endpoint-sector theorem with an exterior even mark. The omitted integral is assembled separately after the size split.
-/

public section
