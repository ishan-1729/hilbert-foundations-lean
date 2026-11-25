#!/usr/bin/env python3
"""Extract Hilbert's *The Foundations of Geometry* (Townsend's translation, 1902) from the
Project Gutenberg LaTeX source (eBook #17384, `17384-t.tex`) into `data/foundations.json`.

Usage: python scripts/extract_source.py path/to/17384-t.tex

The output records:
* the translator's preface, Hilbert's introduction, the conclusion and the appendix;
* the seven chapters and the 39 sections, with their text;
* every statement Hilbert labels: the axioms (I, 1 … V, the axiom of completeness, and the
  appendix's axioms I–III of the plane) and Theorems 1–44, with the section they occur in.

Clean-up: page-scan markers, figures (replaced by `[Fig. N]`), layout commands and the Gutenberg
licence are removed; footnotes are inlined as `[Note: …]`; emphasis becomes `*…*`; mathematics
stays as TeX. One transcription slip is repaired: the label "IV, I." of the first axiom of
congruence is printed "IV, 1." here.
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def brace_end(s: str, i: int) -> int:
    """Index just after the group that opens at s[i] == '{'."""
    depth = 0
    for j in range(i, len(s)):
        c = s[j]
        if c in '{}' and j > 0 and s[j - 1] == '\\':
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return j + 1
    raise ValueError('unbalanced braces at %d' % i)


def replace_cmd(s: str, cmd: str, fn) -> str:
    """Replace every `\\cmd{arg}` by fn(arg) (handles nested groups)."""
    pat = '\\' + cmd + '{'
    while True:
        i = s.find(pat)
        if i < 0:
            return s
        j = brace_end(s, i + len(pat) - 1)
        s = s[:i] + fn(s[i + len(pat):j - 1]) + s[j:]


def clean(t: str) -> str:
    t = re.sub(r'%%-----File:[^\n]*\n', '', t)
    t = re.sub(r'(?m)^%.*\n', '', t)

    def fig(m):
        n = re.search(r'Fig\.\s*(\d+)', m.group(0))
        return f' [Fig. {n.group(1)}] ' if n else ' [Figure] '
    t = re.sub(r'\\begin\{figure\}.*?\\end\{figure\}', fig, t, flags=re.S)
    t = re.sub(r'\\begin\{wrapfigure\}.*?\\end\{wrapfigure\}', fig, t, flags=re.S)
    t = replace_cmd(t, 'footnote', lambda a: ' [Note: ' + a.strip() + ']')
    for c in ('emph', 'textit', 'textbf'):
        t = replace_cmd(t, c, lambda a: '*' + a + '*')
    for c in ('small', 'textsc', 'mbox'):
        t = replace_cmd(t, c, lambda a: a)
    t = re.sub(r'\{\\textit\s+([^{}]*)\}', r'*\1*', t)
    t = re.sub(r'\{\\scshape\s+([^{}]*)\}', r'\1', t)
    t = re.sub(r'\{\\(?:em|it|sc|bf)\s+([^{}]*)\}', r'\1', t)
    t = re.sub(r'\\label\{[^}]*\}', '', t)
    t = re.sub(r'\\(?:newpage|clearpage|bigskip|medskip|smallskip|noindent|par|rfb|centering|small|scshape|'
               r'large|Large|normalsize|footnotesize)\b\s*', ' ', t)
    t = re.sub(r'\\(?:begin|end)\{(?:description|itemize|enumerate|quote|center|flushleft|flushright|minipage)\}'
               r'(?:\{[^}]*\})?', '\n\n', t)
    t = re.sub(r'\\item\s*\[\s*\]\s*', '\n\n', t)
    t = re.sub(r'\\item\s*\[([^\]]*)\]\s*', r'\n\n\1 ', t)
    t = re.sub(r'\\item\b\s*', '\n\n', t)
    t = re.sub(r'\\vspace\*?\{[^}]*\}|\\hspace\*?\{[^}]*\}', ' ', t)
    # typographic quotes and dashes outside mathematics only (A'' is a double prime)
    pieces = re.split(r'(\$[^$]*\$|\\\[.*?\\\])', t, flags=re.S)
    for k in range(0, len(pieces), 2):
        pieces[k] = pieces[k].replace('``', '“').replace("''", '”').replace('---', '—').replace('--', '–')
    t = ''.join(pieces)
    t = re.sub(r'\\(?:begin|end)\{small\}', ' ', t)
    t = re.sub(r'\\S\\!\s*~?', '§ ', t)
    t = t.replace('\\S~', '§ ').replace('\\S ', '§ ')
    t = t.replace('~', ' ').replace('\\@', '').replace('\\ ', ' ')
    for a, b in (('u', 'ü'), ('a', 'ä'), ('o', 'ö')):
        t = re.sub(r'\\"\{?' + a + r'\}?', b, t)
    t = re.sub(r"\\'\{?e\}?", 'é', t)
    t = re.sub(r'[ \t]+', ' ', t)
    t = re.sub(r' *\n *', '\n', t)
    t = re.sub(r'(?<!\n)\n(?!\n)', ' ', t)          # unwrap lines inside paragraphs
    t = re.sub(r'\n{2,}', '\n\n', t)
    return t.strip()


def main() -> int:
    sys.stdout.reconfigure(encoding='utf-8')
    src = Path(sys.argv[1]).read_text(encoding='latin-1')
    body = src[src.index('\\rfa{INTRODUCTION.}'):src.index('*** END OF THE PROJECT GUTENBERG')]
    out = {'source': "David Hilbert, The Foundations of Geometry, authorized translation by E. J. Townsend "
                     "(Open Court, Chicago, 1902), from the first German edition (Festschrift, Leipzig, 1899) "
                     "with Hilbert's additions for the French translation. Project Gutenberg eBook #17384."}
    m = re.search(r'\{\\Large PREFACE\.\}\\end\{center\}(.*?)\\rfa\{CONTENTS\}', src, re.S)
    out['preface'] = clean(m.group(1)) if m else ''

    # chapters and section titles from the table of contents
    toc = src[src.index('\\rfa{CONTENTS}'):src.index('\\rfa{INTRODUCTION.}')]
    chapters = []
    for m in re.finditer(r'CHAPTER ([IVX]+)\.\}\\\\\s*\\multicolumn\{4\}\{c\}\{\\small ([^}]*)\}', toc):
        chapters.append({'chapter': m.group(1), 'title': m.group(2).strip(' .').capitalize()})
    for c, f in zip(chapters, [1, 9, 13, 18, 22, 31, 36]):
        c['first_section'] = f
    titles = {}
    for r in toc.split('\\S &')[1:]:
        m = re.match(r'(\d+)\. &(.*?)~\\dotfill', r, re.S)
        if m:
            tt = re.sub(r'&\\\\\s*&&|&\\\\|&&|&', ' ', m.group(2))
            titles[int(m.group(1))] = re.sub(r'\s+', ' ', tt).strip()

    # split the body at the \rfa headings
    heads = list(re.finditer(r'\\rfa\{', body))
    sections = []
    for k, h in enumerate(heads):
        te = brace_end(body, h.end() - 1)
        raw_title = body[h.end():te - 1]
        text = body[te:heads[k + 1].start() if k + 1 < len(heads) else len(body)]
        text = re.sub(r'\\begin\{center\}\{\\Large[^{}]*\}\\end\{center\}', '', text)
        text = re.sub(r'\\begin\{center\}\{\\Large[^{}]*\{[^{}]*\}[^{}]*\}\\end\{center\}', '', text)
        sm = re.match(r'\\S\\!\s*~(\d+)\.', raw_title)
        txt = clean(text)
        txt = re.sub(r'\s*CHAPTER [IVX]+\.?\s*[A-Z’\'.,: –-]*$', '', txt)
        if sm:
            n = int(sm.group(1))
            txt = re.sub(r'(?m)^IV, I\.', 'IV, 1.', txt)
            notes = re.findall(r'\\footnote', raw_title)
            head_note = ''
            fn = raw_title.find('\\footnote')
            if fn >= 0:
                head_note = clean(raw_title[fn:])
            sections.append({'section': n, 'title': titles.get(n, ''),
                             'chapter': [c['chapter'] for c in chapters if c['first_section'] <= n][-1],
                             'text': (head_note + '\n\n' + txt).strip() if head_note else txt})
        else:
            key = clean(raw_title).split()[0].lower().strip('.')
            fn = raw_title.find('\\footnote')
            out[key] = ((clean(raw_title[fn:]) + '\n\n') if fn >= 0 else '') + txt
    out['chapters'] = chapters
    out['sections'] = sections

    # labelled statements
    stmts = []
    for s in sections:
        t = s['text']
        for m in re.finditer(r'(?:^|\n)((?:I|II|IV), \d)\. (.*?)(?=\n\n|$)', t, re.S):
            stmts.append({'kind': 'axiom', 'label': 'Axiom ' + m.group(1), 'section': s['section'],
                          'text': m.group(2).strip()})
        for m in re.finditer(r'(?:^|\n)(\*?)(III|V)\. (.*?)(?=\n\n|$)', t, re.S):
            stmts.append({'kind': 'axiom', 'label': 'Axiom ' + m.group(2), 'section': s['section'],
                          'text': (m.group(1) + m.group(3)).strip()})
        for m in re.finditer(r'(?:^|\n)Axiom of Completeness\. (.*?)(?=\n\n|$)', t, re.S):
            stmts.append({'kind': 'axiom', 'label': 'Axiom of Completeness', 'section': s['section'],
                          'text': m.group(1).strip()})
        for m in re.finditer(r'(?:^|\n)Theorem (\d+)\. (.*?)(?=\n\n|$)', t, re.S):
            stmts.append({'kind': 'theorem', 'label': 'Theorem ' + m.group(1), 'section': s['section'],
                          'text': m.group(2).strip()})
    for m in re.finditer(r'(?:^|\n)Axiom (I{1,3})\. (\*.*?)(?=\n\n|$)', out.get('appendix', ''), re.S):
        stmts.append({'kind': 'axiom', 'label': 'Appendix, Axiom ' + m.group(1), 'section': 'appendix',
                      'text': m.group(2).strip()})
    out['statements'] = stmts

    dst = ROOT / 'data' / 'foundations.json'
    dst.parent.mkdir(exist_ok=True)
    dst.write_text(json.dumps(out, ensure_ascii=False, indent=1), encoding='utf-8', newline='\n')
    nums = [int(x['label'].split()[1]) for x in stmts if x['kind'] == 'theorem']
    print(f'sections: {len(sections)}; chapters: {len(chapters)}; statements: {len(stmts)}')
    print('theorems:', nums)
    print('axioms:', [x['label'] for x in stmts if x['kind'] == 'axiom'])
    print('parts:', [k for k in out if k not in ('sections', 'statements', 'chapters')])
    return 0


if __name__ == '__main__':
    sys.exit(main())
