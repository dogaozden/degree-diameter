"""Write research/projects/table-audit/cells.csv and the per-cell table of AUDIT.md (table-audit).
Inputs: lit/wiki_table_2026-10-25.json (live wiki values, colours, upper bounds), results.json (per-cell audit
results, keyed "d,D"), README.md (the repo's current records, column "Ours")."""
import csv, json, os, re

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.join(HERE, '../../..')
HOLDER = {
    'Moore': 'bipartite Moore graph (incidence graph of PG(2,q) / GQ W(q) / hexagon H(q)); optimal',
    'DF': 'Delorme-Farhi duplication (Delorme 1985)',
    'DGQ': 'Delorme, Gomez, Quisquater',
    'BE-BD': 'Bar-Yehuda-Etzion; Bond-Delorme (optimal)',
    'CN-DGQ-Loz': 'Conder-Nedela; Delorme-Gomez-Quisquater; Loz (independently)',
    'Hafner-Loz': 'Hafner; Loz (independently)',
    'Loz': 'Loz (project of Loz, Perez-Roses, Pineda-Villavicencio)',
    'FMP-AL': 'Feria-Puron-Miller-Pineda-Villavicencio; Araujo-Pardo-Lopez',
    'AL': 'Araujo-Pardo-Lopez (2022)',
}


def main():
    cells = json.load(open(os.path.join(HERE, 'lit/wiki_table_2026-10-25.json')))
    res = json.load(open(os.path.join(HERE, 'results.json')))
    readme = open(os.path.join(ROOT, 'README.md')).read()
    ours = {(int(a), int(b)): int(o.replace(',', '')) for a, b, t, o in
            re.findall(r'^\| \((\d+), (\d+)\)[^|]*\| ([\d,]+) \| \*\*([\d,]+)\*\* \|', readme, flags=re.M)}
    rows = []
    for c in cells:
        d, D = c['d'], c['D']
        r = res.get(f'{d},{D}', {})
        rows.append(dict(
            d=d, D=D, value=c['wiki'], survey_2013=c['survey'] if c['survey'] is not None else '',
            holder=HOLDER[c['holder']], source=r.get('source', ''),
            construction=r.get('construction', ''),
            rebuilt=r.get('rebuilt', 'no'), check=r.get('check', ''),
            upper_bound=c['ub'], moore=c['moore'], our_record=ours.get((d, D), ''),
            flag=r.get('flag', ''), notes=r.get('notes', '')))
    with open(os.path.join(HERE, 'cells.csv'), 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    print('wrote cells.csv', len(rows))


if __name__ == '__main__':
    main()
