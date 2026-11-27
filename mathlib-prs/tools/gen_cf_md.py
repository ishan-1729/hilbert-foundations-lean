import json
import re

v = json.load(open('D:/Projects/mathlib-prs/out/run3/ml_verify_lagrange.json', encoding='utf-8'))
TITLES = {
    'cf-of-den-pos-of-injective': 'feat(Algebra/ContinuedFractions): positivity of denominators and injectivity of `GenContFract.of`',
    'cf-complete-quotient': 'feat(Algebra/ContinuedFractions): complete quotients of a continued fraction',
    'cf-periodic': 'feat(Algebra/ContinuedFractions): eventually periodic and purely periodic continued fractions',
    'cf-periodic-quadratic-irrational': 'feat(NumberTheory/ContinuedFractions): eventually periodic continued fractions are quadratic irrationals',
    'cf-lagrange': 'feat(NumberTheory/ContinuedFractions): quadratic irrationals have eventually periodic continued fractions',
    'cf-galois-purely-periodic': 'feat(NumberTheory/ContinuedFractions): purely periodic continued fractions and reduced quadratic irrationals',
    'cf-galois-reversed-period': 'feat(NumberTheory/ContinuedFractions): the reversed period of a purely periodic continued fraction',
}
WHAT = {
    'cf-of-den-pos-of-injective': 'two small lemmas the rest needs',
    'cf-complete-quotient': 'the complete quotients `vₙ` of a continued fraction and their basic API',
    'cf-periodic': 'the definitions `IsEventuallyPeriodic` and `IsPurelyPeriodic`',
    'cf-periodic-quadratic-irrational': "Euler's theorem: eventually periodic implies quadratic irrational",
    'cf-lagrange': "Lagrange's theorem and the \"if and only if\"",
    'cf-galois-purely-periodic': "Galois's theorem: purely periodic if and only if reduced",
    'cf-galois-reversed-period': "Galois's theorem on the reversed period",
}
AI = ('AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of '
      "Galois's paper on periodic continued fractions that I had made the same way, and to check them "
      "against mathlib's conventions. I have gone through each proof and can explain every step.")
prs = v['prs']
out = ['# PR 6: periodic continued fractions (a stack of seven)', '',
       '**Status:** all seven branches are pushed; no PR is opened.', '',
       'The stack proves, for the regular continued fraction `GenContFract.of v` of an element `v` of a linearly ordered floor field: '
       "Euler's theorem (eventually periodic implies quadratic irrational), Lagrange's theorem (the converse), and Galois's two theorems "
       '(purely periodic if and only if reduced; the conjugate has the reversed period). Mathlib has none of this, and neither does Tau Ceti.', '',
       'Read [NOTES-continued-fractions-stack.md](NOTES-continued-fractions-stack.md) before opening anything.', '',
       '## The stack', '', '| # | Branch | Adds | Lines | Depends on |', '|---|---|---|---|---|']
for i, p in enumerate(prs, 1):
    out.append(f"| 6.{i} | `{p['branch_name']}` | {WHAT[p['branch_name']]} | +{p['lines_added']} | {('6.%d' % (i - 1)) if i > 1 else 'nothing'} |")
out += ['', '## How to open a stack on mathlib', '',
        '- Each branch contains the commits of the ones before it. A PR from a fork can only target `master`, so until the earlier PRs are merged, a later PR shows their changes too.',
        '- Mathlib handles this with a line in the description: `- [ ] depends on: #NNNN`, one per PR it depends on. A bot then labels the PR `blocked-by-other-PR` and removes the label when the dependency merges.',
        '- **Open 6.1 first, alone.** It is 18 lines and tests whether the maintainers want this material. Open 6.2 once 6.1 has had a first review, and so on. Opening all seven at once as a new contributor with three PRs already open is likely to be read as flooding.',
        '- When an earlier PR changes in review, the later branches must be rebuilt on top of it. Ask me and I will redo the stack.',
        '- After opening each PR, post a comment containing only the line `LLM-generated`.', '']
for i, p in enumerate(prs, 1):
    b = p['branch_name']
    dep = '' if i == 1 else f"- [ ] depends on: #NNNN  (replace NNNN with the number of PR 6.{i - 1})\n\n"
    out += [f'## 6.{i} `{b}`', '',
            f'Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:{b}?expand=1', '',
            'Title:', '', '```text', TITLES[b], '```', '', 'Description (draft; put it in your own words where you can):', '',
            '```text', dep + p['pr_facts'].strip() + '\n\n' + AI, '```', '']
out += ['## What was checked', '',
        f"- All modules of the stack build together without warnings; the style linter and `#lint` pass; the main theorems use only the standard axioms.",
        '- The cut-down `PurelyPeriodic.lean` of 6.6 was built and linted as a module on its own.',
        '- Not done: building each branch separately, the full mathlib build, `lake exe mk_all --check`, `lake exe shake`. Mathlib CI runs all of these on each PR.', '',
        '## Points the final check left open', '']
out += [
    '- No branch was built on its own: only the whole stack, and the 6.6 version of `PurelyPeriodic.lean`. Each file imports only earlier ones, so the risk is low, and CI builds each PR.',
    '- 6.5 has 238 lines of Lean (253 with the import line and the bibliography entry), at the edge of the usual PR size. It contains one terminal `nlinarith` with explicit hints (`Lagrange.lean`, line 182).',
    '- The private `isIntegral_of_adjoin_simple_eq` in `QuadraticIrrational.lean` is a general field-theory fact. A reviewer may ask to move it to `FieldTheory/IntermediateField/Adjoin/Basic.lean`, the file PR 5 edits.',
    '- The docstring of `Lagrange.lean` says the proof follows Steinig (Arch. Math. 59 (1992), 21-23). The bibliographic data was checked against Crossref, but the paper itself was not read; read it (three pages) before you defend that sentence.',
    "- Galois's theorem cites only Galois's own paper (Annales de Gergonne 19 (1828-1829), 294-301). No textbook reference was verified.",
    '- A reviewer may ask for `1 ≤ (of v).dens n` instead of `of_den_pos`, or for 6.1 to be split into two one-lemma PRs. Both are trivial changes.',
    '- The two new entries of `docs/references.bib` were not run through `bibtool`.',
]
open('D:/Projects/mathlib-prs/PR6-continued-fractions-stack.md', 'w', encoding='utf-8', newline='\n').write('\n'.join(out) + '\n')

notes = ['# Notes for PR 6: periodic continued fractions', '',
         'One section per PR of the stack, in order. For each: what is stated, how it is proved step by step, and why the names, assumptions and file were chosen.', '']
for i, p in enumerate(prs, 1):
    body = p['notes_md'].strip().replace('\n## ', '\n### ')
    body = body.replace('Submitter checklist', 'Before you open it')
    body = '\n'.join(l for l in body.split('\n') if 'shared working tree also contains' not in l)
    body = body.replace(" The working tree's Mathlib.lean also has lines of later PRs and of another task.",
                        ' The branch already contains exactly this line.')
    body = body.replace("The shared tree's `FieldTheory/IntermediateField/Adjoin/Basic.lean` carries another task's edits; this file uses",
                        'This file uses')
    body = re.sub(r"#+ How to cut this PR from the working tree\n[^\n]*\n",
                  "## One file, two PRs\n`PurelyPeriodic.lean` is shared with 6.7. The branch of 6.6 contains the first 211 lines' worth "
                  "(the theorem \"purely periodic if and only if reduced\"); 6.7 adds the section on the reversed period and three "
                  "sentences of the module docstring. The 6.6 version was built and linted as a module on its own.\n", body)
    if body.startswith('## '):
        body = '### ' + body[3:]
    notes += [f"## 6.{i} `{p['branch_name']}`: {WHAT[p['branch_name']]}", '', body, '']
notes += ['## Overlap with Tau Ceti', '', v['tauceti_overlap'].strip(), '']
open('D:/Projects/mathlib-prs/NOTES-continued-fractions-stack.md', 'w', encoding='utf-8', newline='\n').write('\n'.join(notes) + '\n')
print('written', len('\n'.join(out)), len('\n'.join(notes)))
