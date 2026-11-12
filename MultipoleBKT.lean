/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Frozen.Theorem1
public import MultipoleBKT.Frozen.Theorem2
public import MultipoleBKT.Frozen.Proposition423
public import MultipoleBKT.Frozen.Proposition462
public import MultipoleBKT.Frozen.Proposition543
public import MultipoleBKT.Frozen.Proposition545
public import MultipoleBKT.Frozen.Lemma546

/-!
# Multipole and BKT transitions in the two-component plasma

Lean formalization of J. Boursier and S. Serfaty, *Multipole and Berezinskii–Kosterlitz–Thouless
Transitions in the Two-component Plasma* (arXiv:2509.09449), following the revised version of
the paper (2026) and its numbering.

This root module imports the seven formalized results: Theorem 1 (free energy expansion),
Theorem 2 (multipole distribution), Propositions 4.23, 4.62, 5.43 and 5.45, and Lemma 5.46.
Their statements are in `MultipoleBKT/Frozen/`, together with the definitions they use.
-/

public section
