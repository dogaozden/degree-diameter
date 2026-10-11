"""Check that each found graph is the four-hat rule up to (1) the small gadget and (2) filler.

Coordinates as in al.py: ell = L_0 (the line x=0), A = P_0 (the horizontal direction).
Gadget points: A, the points of ell (P and (0,y)), Q0, all hat points (including NEW0).
Gadget lines: ell, the lines through A (L_inf and [0,b]), M0, all hat lines (including NEW1).
Bulk = every point-line pair with at least one end outside the gadget.

Claim checked: on the bulk, the found graph equals "PG(2,q) + hats for S = {0,1,a,c}" except
for filler edges (old point, old line, not a PG incidence), and no bulk PG incidence or bulk hat
incidence is missing.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from al import al_named  # noqa: E402
from diff_al import FILES, ROOT, norm  # noqa: E402
from found_core import pg_incident  # noqa: E402

for q, f in FILES.items():
    n0, e0, names, F = al_named(q)
    names = dict(names)
    n1, e1 = json.load(open(ROOT + f))['output']
    pts = {u for u, v in e0}
    edges = norm(e1)
    adj = {}
    for u, v in edges:
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)
    # identify the new pair: NEW0 = n0 (point side?), NEW1 = n0+1
    new_pt = n0 if any(names.get(w, ('',))[0] == 'ln' for w in adj[n0]) else n0 + 1
    new_ln = n0 + 1 if new_pt == n0 else n0
    rows = {names[w][2] for w in adj[new_pt] if names.get(w, ('',))[0] == 'ln'}
    c = max(rows, key=lambda r: sum(1 for w in adj[new_pt] if names.get(w, ('',))[0] == 'ln' and names[w][2] == r))
    names[new_pt] = ('hp', c)
    names[new_ln] = ('hl', c)
    pts.add(new_pt)
    S = {s for nm in names.values() if nm[0] == 'hp' for s in [nm[1]]}

    def gadget(nm):
        if nm[0] in ('Q0', 'M0', 'hp', 'hl'):
            return True
        if nm == ('P', 0) or nm == ('P',) or nm == ('L',) or nm == ('L', 0):
            return True
        return (nm[0] == 'pt' and nm[1] == 0) or (nm[0] == 'ln' and nm[1] == 0)

    def bulk_rule(p, L):
        """Incidence in the four-hat bulk for a pair outside gadget x gadget."""
        if p[0] in ('pt', 'P') and L[0] in ('ln', 'L'):
            return pg_incident(p, L, F)
        if p[0] == 'hp' and L[0] == 'ln':
            return L[2] == p[1]                       # [m, s] for all m
        if p[0] == 'pt' and L[0] == 'hl':
            return p[2] == L[1]                       # (t, s) for all t
        return False

    point_names = [names[u] for u in range(n1) if u in pts]
    line_names = [names[u] for u in range(n1) if u not in pts]
    ids = {nm: i for i, nm in names.items()}
    extra, missing, filler = [], [], 0
    for p in point_names:
        for L in line_names:
            if gadget(p) and gadget(L):
                continue
            present = (min(ids[p], ids[L]), max(ids[p], ids[L])) in edges
            want = bulk_rule(p, L)
            if present and not want:
                if p[0] in ('pt', 'P') and L[0] in ('ln', 'L'):
                    filler += 1
                else:
                    extra.append((p, L))
            elif want and not present:
                missing.append((p, L))
    g_edges = sum(1 for u, v in edges if gadget(names[u]) and gadget(names[v]))
    print(f'q={q}: hats S={sorted(S)} (new row c={c}); bulk: missing {len(missing)} {missing[:5]}, '
          f'non-filler extras {len(extra)} {extra[:5]}, filler {filler}; gadget edges {g_edges}')
