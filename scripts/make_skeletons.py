#!/usr/bin/env python3
"""Generate the Lean files of the formalization from data/foundations.json (run once; refuses to
overwrite). Each file covers some sections of the book; it gets a header naming them and, for
each axiom and theorem Hilbert labels in them, a unit block with the verbatim text and
placeholders."""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# module -> (sections, imports, English description)
FILES = {
    'Basic': ([1, 2, 3, 5, 6, 8], [], 'The elements of geometry and the five groups of axioms (§§ 1–3, 5, 6, 8)'),
    'Order': ([2, 3, 4, 5], ['Basic'], 'Consequences of the axioms of connection and order (Theorems 1–8)'),
    'Congruence': ([6, 7], ['Order'], 'Consequences of the axioms of congruence (Theorems 9–20)'),
    'Analytic': ([9, 13], ['Basic'], 'Compatibility of the axioms; complex number-systems (§§ 9, 13)'),
    'Independence': ([10, 11, 12], ['Analytic'], 'Independence of the axioms (§§ 10–12)'),
    'Pascal': ([14], ['Congruence'], "Demonstration of Pascal's theorem (§ 14, Theorem 21)"),
    'Proportion': ([15, 16, 17], ['Pascal'], 'Algebra of segments, proportion, equations of lines and planes (§§ 15–17)'),
    'Areas': ([18, 19, 20, 21], ['Proportion'], 'The theory of plane areas (§§ 18–21, Theorems 24–31)'),
    'Desargues': ([22], ['Proportion'], "Desargues's theorem from the axioms of congruence (§ 22, Theorem 32)"),
    'NonDesargues': ([23], ['Analytic'], "A plane geometry in which Desargues's theorem fails (§ 23, Theorem 33)"),
    'DesarguesAlgebra': ([24, 25, 26, 27, 28, 29, 30], ['Order', 'Analytic'],
                         "The algebra of segments based on Desargues's theorem (§§ 24–30, Theorems 34–35)"),
    'NonPascal': ([31, 32, 33, 34, 35], ['DesarguesAlgebra'], "Pascal's theorem and non-pascalian geometry (§§ 31–35, Theorems 36–39)"),
    'Constructions': ([36, 37, 38, 39], ['Congruence', 'Analytic'],
                      'Constructions with straight-edge and transferer of segments (§§ 36–39, Theorems 40–44)'),
    'Commentary': ([], ['Analytic'], 'The introduction, the conclusion and the appendix'),
}


def quote(t: str) -> str:
    t = t.replace('-/', '- /').replace('/-', '/ -')
    return '\n>\n'.join('> ' + p for p in t.split('\n\n') if p.strip())


def unit_id(st) -> str:
    if st['kind'] == 'theorem':
        return 'th.' + st['label'].split()[1]
    lab = st['label']
    if lab.startswith('Appendix'):
        return 'app.axiom' + {'I': '1', 'II': '2', 'III': '3'}[lab.split()[-1]]
    if lab == 'Axiom of Completeness':
        return 'ax.completeness'
    m = re.match(r'Axiom ([IV]+)(?:, (\d))?', lab)
    return 'ax.' + m.group(1) + (m.group(2) or '')


def home(st) -> str:
    """Module that holds the unit of a labelled statement."""
    if st['section'] == 'appendix':
        return 'Commentary'
    if st['kind'] == 'axiom':
        return 'Basic'
    for mod, (secs, _, _) in FILES.items():
        if mod != 'Basic' and st['section'] in secs:
            return mod
    raise KeyError(st)


def main() -> int:
    data = json.loads((ROOT / 'data' / 'foundations.json').read_text(encoding='utf-8'))
    secs = {s['section']: s for s in data['sections']}
    for mod, (sections, imports, english) in FILES.items():
        path = ROOT / 'HilbertFoundations' / (mod + '.lean')
        if path.exists():
            print('exists, skipping', path.name); continue
        path.parent.mkdir(parents=True, exist_ok=True)
        ns = 'HilbertFoundations'
        lines = [f'import HilbertFoundations.{i}' for i in imports] or ['import Mathlib']
        lines += ['', '/-!', f'# {english}', '']
        if sections:
            lines += ['Sections of Hilbert\'s text covered here (full text in `data/foundations.json`):', '']
            lines += [f'* § {n}. {secs[n]["title"]}' for n in sections]
        else:
            lines += ['Covers `introduction`, `conclusion` and `appendix` of `data/foundations.json`.']
        lines += ['-/', '', f'namespace {ns}', '']
        for st in data['statements']:
            if home(st) != mod:
                continue
            uid = unit_id(st)
            loc = f'§ {st["section"]}' if st['section'] != 'appendix' else 'Appendix'
            lines += ['/-!', f'## [{uid}] {st["label"]}', '', f'*({loc})*', '', quote(st['text']), '',
                      '**Lean reading.** TODO', '', '**Status.** TODO', '-/', '', f'-- TODO({uid})', '']
        lines += ['-- TODO: add a unit block for every further claim Hilbert makes in these sections.', '',
                  f'end {ns}', '']
        path.write_text('\n'.join(lines), encoding='utf-8', newline='\n')
        print('wrote', path.relative_to(ROOT))
    return 0


if __name__ == '__main__':
    sys.exit(main())
