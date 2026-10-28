"""Pre-pass for the PDF build: turn plain-text sub/superscripts of the Markdown (S_p, Γ_{p,q}, p^{L/2}, M^b) into
inline TeX math, outside code spans, code blocks and existing $...$ math.  Usage: md2tex_filter.py IN.md OUT.md"""
import re, sys
src = open(sys.argv[1]).read()
out = []; incode = False
SUB_B = re.compile(r'(?<![\\$\w])([A-Za-zΓΔΛΩψαβγζσκρμεηΣ0-9]+)_\{([^{}$`]+)\}')
SUB_W = re.compile(r'(?<![\\$\w/.-])([A-Za-zΓΔΛψαβγζσκρμ][A-Za-z0-9′]?)_([A-Za-z0-9]{1,4})(?![A-Za-z0-9_/]|\.\w)')
SUP_B = re.compile(r'\^\{([^{}$`]+)\}')
SUP_W = re.compile(r'(?<=[\w)\]])\^([A-Za-zΔ+−0-9])(?![\w{])')
def conv(t):
    t = SUB_B.sub(lambda m: f'${m.group(1)}_{{{m.group(2)}}}$', t)
    t = SUB_W.sub(lambda m: f'${m.group(1)}_{{{m.group(2)}}}$', t)
    t = SUP_B.sub(lambda m: f'$^{{{m.group(1)}}}$', t)
    t = SUP_W.sub(lambda m: f'$^{{{m.group(1)}}}$', t)
    return t
for line in src.split('\n'):
    if line.startswith('```'): incode = not incode; out.append(line); continue
    if incode or line.startswith('$$'): out.append(line); continue
    parts = re.split(r'(`[^`]*`|\$\$[^$]*\$\$|\$[^$]+\$)', line)
    out.append(''.join(p if (p.startswith('`') or p.startswith('$')) else conv(p) for p in parts))
open(sys.argv[2], 'w').write('\n'.join(out))
