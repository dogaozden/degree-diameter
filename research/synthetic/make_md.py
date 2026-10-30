"""Make SYNTHETIC.md from SYNTHETIC.tex (pandoc, with light pre- and post-processing).

TikZ figures are replaced by a pointer to the PDF (their captions are kept); \\path{..} becomes code;
theorem-like environments become bold labels with their numbers as in the PDF.
Run: python3 make_md.py   (needs pandoc >= 3)
"""
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
tex = (HERE / 'SYNTHETIC.tex').read_text()

# 1. label values from the .aux file (tectonic --keep-intermediates)
subprocess.run(['/root/bin/tectonic', '--keep-intermediates', str(HERE / 'SYNTHETIC.tex')], cwd=HERE, check=True,
               capture_output=True)
aux = (HERE / 'SYNTHETIC.aux').read_text()
labels = {}
for m in re.finditer(r'\\newlabel\{([^}]*)\}\{\{(.*?)\}\{', aux):
    labels[m.group(1)] = re.sub(r'\\textup \{(.*)\}', r'\1', m.group(2)).replace('\\relax ', '')
for ext in ('aux', 'log', 'out'):
    f = HERE / f'SYNTHETIC.{ext}'
    if f.exists():
        f.unlink()
envs = ['theorem', 'lemma', 'proposition', 'corollary', 'definition', 'remark']
names = {'theorem': 'Theorem', 'lemma': 'Lemma', 'proposition': 'Proposition', 'corollary': 'Corollary',
         'definition': 'Definition', 'remark': 'Remark'}

# 2. pre-process
def braced(s, i):
    """s[i] == '{'; return (content, index after the closing brace)."""
    assert s[i] == '{'
    depth = 0
    for j in range(i, len(s)):
        if s[j] == '{':
            depth += 1
        elif s[j] == '}':
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
    raise ValueError('unbalanced')


def replace_cmd(s, cmd, fn):
    """Replace every backslash-cmd{arg} by fn(arg) (balanced braces)."""
    out, i = [], 0
    key = '\\' + cmd + '{'
    while True:
        k = s.find(key, i)
        if k < 0:
            out.append(s[i:])
            return ''.join(out)
        out.append(s[i:k])
        arg, j = braced(s, k + len(key) - 1)
        out.append(fn(arg))
        i = j


def roman(n):
    return ['i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x'][n - 1]


t = tex
t = re.sub(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}', r'\\emph{[Figure: see SYNTHETIC.pdf.]}', t, flags=re.S)
t = t.replace('\\emergencystretch=3em', '')
t = re.sub(r'\\path\{([^}]*)\}', lambda m: r'\texttt{' + m.group(1).replace('_', r'\_') + '}', t)
t = re.sub(r'~?\\ref\{([^}]*)\}', lambda m: ' ' + labels.get(m.group(1), '??'), t)
t = re.sub(r'~?\\cite(\[[^\]]*\])?\{([^}]*)\}',
           lambda m: ' [' + ', '.join(k.strip() for k in m.group(2).split(',')) + (', ' + m.group(1)[1:-1] if m.group(1) else '') + ']', t)
t = t.replace(r'\setcounter{section}{-1}', '')
t = t.replace(r'\begin{abstract}', r'\par\noindent\emph{Abstract.} ').replace(r'\end{abstract}', r'\par')
# figures and tables: drop the float, number the caption
counter = {'figure': 0, 'table': 0}


def unfloat(m):
    env, body = m.group(1), m.group(2)
    counter[env] += 1
    name = 'Figure' if env == 'figure' else 'Table'
    body = body.replace(r'\centering', '')
    body = replace_cmd(body, 'caption', lambda a: '\n\n\\par\\noindent\\emph{' + name + ' ' + str(counter[env]) + '.} ' + a + '\n\n')
    return body
t = re.sub(r'\\begin\{(figure|table)\}(?:\[[^\]]*\])?(.*?)\\end\{\1\}', unfloat, t, flags=re.S)
t = replace_cmd(t, 'multicolumn{2}{l}', lambda a: a + ' & (same)')
t = re.sub(r'\\multicolumn\{(\d+)\}\{c\}\{([^{}]*)\}\\\\\[2pt\]', r'\\multicolumn{\1}{c}{\2}\\\\', t)
# enumerate with labels -> labelled paragraphs


def enum(m):
    opts, body = m.group(1) or '', m.group(2)
    lab = re.search(r'label=\\textup\{(.*?)\}(,|\]|$)', opts)
    fmt = lab.group(1) if lab else '(\\arabic*)'
    st = re.search(r'start=(\d+)', opts)
    n0 = int(st.group(1)) if st else 1
    items = body.split('\\item')[1:]
    out = []
    for k, it in enumerate(items):
        n = n0 + k
        lb = fmt.replace('\\arabic*', str(n)).replace('\\alph*', 'abcdefghij'[n - 1]).replace('\\roman*', roman(n) if n >= 1 else str(n))
        out.append('\\par\\noindent ' + lb + '\\ ' + it.strip() + '\\par')
    return '\n'.join(out)
t = re.sub(r'\\begin\{enumerate\}(\[[^\n]*?\])?(.*?)\\end\{enumerate\}', enum, t, flags=re.S)
t = re.sub(r'\\label\{[^}]*\}', '', t)
for env in envs:
    def repl(m, env=env):
        opt = m.group(1)
        return r'\par\noindent\textbf{' + names[env] + ' ' + '@@NUM@@' + (' (' + opt[1:-1] + ')' if opt else '') + r'.} '
    t = re.sub(r'\\begin\{' + env + r'\}(\[[^\]]*\])?', repl, t)
    t = t.replace(r'\end{' + env + '}', r'\par')
# number the environments in order (section 0 is Conventions)
nums = []
cur_sec = -1
k = 0
for m in re.finditer(r'\\section\{|@@NUM@@', t):
    if m.group(0) == '@@NUM@@':
        k += 1
        nums.append(f'{cur_sec}.{k}')
    else:
        cur_sec += 1
        k = 0
for n in nums:
    t = t.replace('@@NUM@@', n, 1)
t = t.replace(r'\begin{proof}', r'\par\noindent\emph{Proof.} ').replace(r'\end{proof}', r' $\square$\par')
(HERE / '_md_tmp.tex').write_text(t)

# 3. pandoc
md = subprocess.run(['pandoc', str(HERE / '_md_tmp.tex'), '-f', 'latex', '-t', 'gfm+tex_math_dollars',
                     '--wrap=none'], capture_output=True, text=True, check=True).stdout
(HERE / '_md_tmp.tex').unlink()

# 4. post-process: section numbers, figure/table captions
lines = md.split('\n')
secno = -1
app = False
res = []
for ln in lines:
    if ln.startswith('# '):
        secno += 1
        title = ln[2:]
        if title.startswith('Coordinates and checks'):
            res.append('# Appendix A. ' + title)
        else:
            res.append(f'# {secno}. {title}')
        continue
    res.append(ln)
md = '\n'.join(res)
md = re.sub(r'<span id="[^"]*" label="[^"]*"></span>\s*', '', md)
md = re.sub(r'<span class="upright">(.*?)</span>', r'\1', md)
# number subsections
out, sec, sub = [], -1, 0
for ln in md.split('\n'):
    if ln.startswith('# ') and not ln.startswith('# Appendix'):
        sec = int(ln[2:].split('.')[0])
        sub = 0
    elif ln.startswith('## ') and sec >= 1:
        sub += 1
        ln = f'## {sec}.{sub} ' + ln[3:]
    out.append(ln)
md = '\n'.join(out)
header = ('<!-- Generated from SYNTHETIC.tex by make_md.py; the figures are in SYNTHETIC.pdf. -->\n\n'
          '# Adding points and lines to generalized polygons: the constructions without coordinates\n\n'
          '*Degree–diameter lab, 30 October 2026. Markdown copy of `SYNTHETIC.tex`; the PDF has the figures.*\n\n')
(HERE / 'SYNTHETIC.md').write_text(header + md)
print('wrote SYNTHETIC.md,', len(md.split()), 'words')
