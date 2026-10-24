# Stdlib-only HTML table dumper. Usage: python3 -I parse_tables.py FILE MIN_ROWS
import sys
from html.parser import HTMLParser

class T(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack = []          # stack of open tables: each is dict(rows=[], row=None, cell=None, style=...)
        self.done = []           # finished top-level tables
        self.depth_style = []
    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == 'table':
            self.stack.append({'rows': [], 'row': None, 'cell': None, 'style': a.get('style', ''), 'border': a.get('border', '')})
        elif tag == 'tr' and self.stack:
            self.stack[-1]['row'] = []
        elif tag in ('td', 'th') and self.stack:
            t = self.stack[-1]
            if t['row'] is None:
                t['row'] = []
            t['cell'] = {'text': [], 'style': a.get('style', ''), 'colspan': a.get('colspan', ''), 'bgcolor': a.get('bgcolor', ''), 'links': []}
        elif tag == 'a' and self.stack and self.stack[-1]['cell'] is not None:
            self.stack[-1]['cell']['links'].append(a.get('href', ''))
        elif tag == 'br' and self.stack and self.stack[-1]['cell'] is not None:
            self.stack[-1]['cell']['text'].append(' | ')
    def handle_endtag(self, tag):
        if not self.stack:
            return
        t = self.stack[-1]
        if tag in ('td', 'th') and t['cell'] is not None:
            c = t['cell']
            c['text'] = ' '.join(''.join(c['text']).split())
            if t['row'] is None:
                t['row'] = []
            t['row'].append(c)
            t['cell'] = None
        elif tag == 'tr' and t['row'] is not None:
            t['rows'].append(t['row'])
            t['row'] = None
        elif tag == 'table':
            fin = self.stack.pop()
            if fin['row']:
                fin['rows'].append(fin['row'])
            if self.stack:
                # nested table: keep its text inside parent cell
                parent = self.stack[-1]
                if parent['cell'] is not None:
                    parent['cell']['text'].append(' [nested:' + ' ; '.join(' , '.join(x['text'] for x in r) for r in fin['rows'])[:200] + '] ')
            else:
                self.done.append(fin)
    def handle_data(self, data):
        if self.stack and self.stack[-1]['cell'] is not None:
            self.stack[-1]['cell']['text'].append(data)

if __name__ == '__main__':
    path = sys.argv[1]
    minrows = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    p = T()
    with open(path, encoding='utf-8', errors='replace') as f:
        p.feed(f.read())
    idx = 0
    for tb in p.done:
        idx += 1
        rows = tb['rows']
        if len(rows) < minrows:
            continue
        print(f'=== TABLE #{idx} rows={len(rows)} style={tb["style"]!r}')
        for r in rows:
            print(' || '.join(f"{c['text']}" + (f" {{bg:{c['style']}}}" if c['style'] else '') + (f" {{links:{c['links']}}}" if c['links'] else '') for c in r))
