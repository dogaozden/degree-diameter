#!/usr/bin/env python3
"""splice_rs.py: put SECTION_RS.md into BEYOND_TABLE.md (before "## What failed") and the one-line "Extended" note
after the beyond-d13 note; rerunnable (replaces an earlier copy). Run from the repo root after rows_rs.py."""
FILE = 'research/frontier/beyond/BEYOND_TABLE.md'
SEC = open('research/frontier/raise_small/SECTION_RS.md').read().rstrip('\n') + '\n'
HEAD = '### Δ = 3, 4 at D = 9..14 (job raise-small-d'
NOTE = ('Extended 2026-11-02 by job raise-small-d (branch claude/raise-d-delta-3-4-5wyh9b): (3,12), (3,13), (3,14), (4,12),\n'
        '(4,13), (4,14) raised by joint base+voltage annealing of small cubic lifts and fresh-seed Haar searches; see the\n'
        'section "Δ = 3, 4 at D = 9..14" below.\n')
t = open(FILE).read()
if HEAD in t:  # remove the old copy
    i = t.index(HEAD); j = t.index('\n## ', i)
    t = t[:i] + t[j + 1:]
if NOTE not in t:
    k = t.index('## Summary')
    t = t[:k] + NOTE + '\n' + t[k:]
k = t.index('## What failed, and why it matters')
t = t[:k] + SEC + '\n' + t[k:]
open(FILE, 'w').write(t)
print('spliced', len(SEC), 'chars')
