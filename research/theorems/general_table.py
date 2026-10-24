"""Parse the general (non-bipartite) degree-diameter table from Wikipedia's raw wikitext
(data/wiki_general_table_raw.txt, fetched 2026-10-24 via action=raw; the page says 'as of 14 October 2026')."""
import re, os
HERE = os.path.dirname(os.path.abspath(__file__))

def general_table():
    s = open(os.path.join(HERE, 'data', 'wiki_general_table_raw.txt')).read()
    s = re.sub(r'<ref[^>]*/>', '', s)
    s = re.sub(r'<ref[^>]*>.*?</ref>', '', s, flags=re.S)
    tab = {}
    start = s.index('{| class="wikitable"')
    end = s.index('|}', start)
    body = s[start:end]
    for row in body.split('|-')[1:]:
        m = re.search(r"!\s*(\d+)\s*\n(.*)", row, flags=re.S)
        if not m: continue
        d = int(m.group(1))
        cells = [c.strip() for c in m.group(2).replace('\n', ' ').split('||')]
        vals = []
        for c in cells:
            c = c.lstrip('|').replace("'''", '').replace('&nbsp;', '').replace(' ', '').replace(' ','')
            c = re.sub(r'[^0-9]', '', c)
            vals.append(int(c) if c else None)
        tab[d] = vals[:9]
    return tab   # tab[d][k-2] for k = 2..10

if __name__ == '__main__':
    for d, v in general_table().items(): print(d, v)
