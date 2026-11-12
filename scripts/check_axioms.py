#!/usr/bin/env python3
"""Check the axiom report of the seven main results.

usage: check_axioms.py LOG

LOG is the output of `lake env lean MultipoleBKT/Meta/AxiomsAudit.lean`. The check fails on a warning,
on `sorryAx`, on any axiom other than `propext`, `Classical.choice` and `Quot.sound`, and on a
missing, unexpected or repeated report."""
import pathlib
import re
import sys

EXPECTED = {
    'MultipoleBKT.theorem_1',
    'MultipoleBKT.theorem_2',
    'MultipoleBKT.proposition_4_23',
    'MultipoleBKT.proposition_4_62',
    'MultipoleBKT.proposition_5_43',
    'MultipoleBKT.proposition_5_45',
    'MultipoleBKT.lemma_5_46',
}
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

log = pathlib.Path(sys.argv[1]).read_text()
if re.search(r'warning:|error:|sorryAx|declaration uses .sorry', log, re.IGNORECASE):
    raise SystemExit('The axiom report emitted a warning or an error, or mentions sorryAx')
seen = set()
for theorem, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
    if theorem not in EXPECTED or theorem in seen:
        raise SystemExit('Unexpected or repeated axiom report: ' + theorem)
    actual = [a.strip() for a in axioms.split(',')]
    if len(actual) != 3 or set(actual) != STANDARD:
        raise SystemExit('Unexpected axioms for ' + theorem + ': ' + axioms)
    seen.add(theorem)
if seen != EXPECTED:
    raise SystemExit('Missing axiom reports: ' + ', '.join(sorted(EXPECTED - seen)))
print('The seven main results depend exactly on propext, Classical.choice and Quot.sound.')
