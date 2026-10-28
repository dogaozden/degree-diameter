"""Rewrap prose paragraphs and list items of a Markdown file whose lines exceed WIDTH characters (tables, code, display
math and headings untouched).  Usage: reflow.py FILE [WIDTH]"""
import re, sys, textwrap
path = sys.argv[1]; W = int(sys.argv[2]) if len(sys.argv) > 2 else 120
lines = open(path).read().split('\n')
out = []; i = 0; incode = False
def is_special(l):
    s = l.lstrip()
    return (not s) or s.startswith('|') or s.startswith('#') or s.startswith('$$') or s.startswith('<!--') or s.startswith('---')
item_re = re.compile(r'^(\s*)([-*]|\d+\.)\s+')
while i < len(lines):
    l = lines[i]
    if l.startswith('```'):
        incode = not incode; out.append(l); i += 1; continue
    if incode or is_special(l):
        out.append(l); i += 1; continue
    # collect a block: a list item with its continuation lines, or a plain paragraph
    m = item_re.match(l)
    block = [l]; j = i + 1
    if m:
        cont_indent = ' ' * len(m.group(0))
        while j < len(lines) and lines[j].startswith(cont_indent) and lines[j].strip() and not item_re.match(lines[j]) and not is_special(lines[j]):
            block.append(lines[j]); j += 1
        first_prefix, rest_prefix = m.group(0), cont_indent
        text = ' '.join([block[0][len(first_prefix):]] + [b.strip() for b in block[1:]])
    else:
        while j < len(lines) and lines[j].strip() and not item_re.match(lines[j]) and not is_special(lines[j]) and not lines[j].startswith('```'):
            block.append(lines[j]); j += 1
        ind = re.match(r'^\s*', l).group(0)
        first_prefix = rest_prefix = ind
        text = ' '.join(b.strip() for b in block)
    if max(len(b) for b in block) <= W:
        out.extend(block)
    else:
        wrapped = textwrap.wrap(text, width=W, initial_indent=first_prefix, subsequent_indent=rest_prefix,
                                break_long_words=False, break_on_hyphens=False)
        out.extend(wrapped)
    i = j
open(path, 'w').write('\n'.join(out))
