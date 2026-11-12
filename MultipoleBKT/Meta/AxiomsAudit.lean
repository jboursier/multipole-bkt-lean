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
# Axiom report of the main results

Prints the axioms on which each of the seven main results depends. `scripts/check_axioms.py`
checks that each report lists exactly `propext`, `Classical.choice` and `Quot.sound`:

```bash
lake env lean MultipoleBKT/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

The root module `MultipoleBKT` does not import this file, because its `#print axioms` commands
run again whenever the module is rebuilt.
-/

#print axioms MultipoleBKT.theorem_1
#print axioms MultipoleBKT.theorem_2
#print axioms MultipoleBKT.proposition_4_23
#print axioms MultipoleBKT.proposition_4_62
#print axioms MultipoleBKT.proposition_5_43
#print axioms MultipoleBKT.proposition_5_45
#print axioms MultipoleBKT.lemma_5_46
