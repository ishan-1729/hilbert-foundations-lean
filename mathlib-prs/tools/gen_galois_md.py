import json
import re

v = json.load(open('D:/Projects/mathlib-prs/out/run3/mlg_verify_galois-prime-degree.json', encoding='utf-8'))
BR = ['galois-prime-degree-group', 'galois-prime-degree-polynomial', 'galois-prime-degree-affine']
TITLES = [
    'feat(GroupTheory/GroupAction/PrimeDegree): solvable transitive groups of prime degree',
    'feat(FieldTheory/Galois/PrimeDegree): solvability of irreducible polynomials of prime degree',
    'feat(GroupTheory/GroupAction/PrimeDegree): solvable transitive groups of prime degree act by affine maps of `ZMod p`',
]
WHAT = ["Galois's criterion for groups: solvable if and only if no non-identity element fixes two points",
        "Galois's criterion for equations: solvable if and only if any two roots generate the splitting field",
        'optional: solvable if and only if the group acts by maps `k ↦ a * k + b` of `ZMod p`']
DEP = ['nothing', '7.1', '7.1']
AI = ('AI use: I used Claude Code (Anthropic) to write these proofs, starting from a formalization of '
      "Galois's works that I had made the same way, and to check them against mathlib's conventions. "
      'I have gone through each proof and can explain every step.')


def facts(t):
    paras = [p for p in t.strip().split('\n\n') if not p.startswith('EXACT CONTENT OF THE FILE')]
    t = '\n\n'.join(paras)
    t = t.replace('OPTIONAL PR. ', '').replace('WHAT IS ADDED. ', '')
    t = re.sub(r'WHAT WAS CHECKED \([^)]*\)\.', 'Checked locally.', t)
    t = t.replace(' After this PR the file is exactly the working-tree file (314 lines).', '')
    t = t.replace(' The PR-1 cut compiled on its own as a module file.', '')
    return re.sub(r'(?m)^([A-Z][A-Z \-]{3,})\.', lambda m: m.group(1).capitalize() + '.', t)


def notes(t):
    paras = [p for p in t.strip().split('\n\n') if not p.startswith('**How to cut it.**')]
    t = '\n\n'.join(paras).replace('\n## ', '\n### ')
    return re.sub(r'^## [^\n]*\n+', '', t)


prs = v['prs']
out = ['# PR 7: Galois\'s criterion in prime degree (three PRs)', '',
       '**Status:** all three branches are pushed; no PR is opened.', '',
       'For a group acting faithfully and transitively on a set with a prime number `p` of elements: the group is solvable if and only if it has '
       'a normal subgroup of order `p`, if and only if no element other than the identity fixes two points (7.1). For an irreducible polynomial '
       'of prime degree this gives: its Galois group is solvable if and only if any two of its roots generate the splitting field (7.2). '
       'Mathlib has none of this. Tau Ceti has the criterion for `p = 5` only.', '',
       'Read [NOTES-galois-prime-degree.md](NOTES-galois-prime-degree.md) before opening anything.', '',
       '## The three PRs', '', '| # | Branch | Adds | Lines | Depends on |', '|---|---|---|---|---|']
for i, p in enumerate(prs):
    out.append(f"| 7.{i + 1} | `{BR[i]}` | {WHAT[i]} | +{p['lines_added']} | {DEP[i]} |")
out += ['',
        '- Open 7.1 first. 7.2 and 7.3 each contain the commit of 7.1, and each needs the line `- [ ] depends on: #NNNN` with the number of 7.1 in its description.',
        '- 7.3 is optional. A reviewer may ask for its statement to go through mathlib\'s `AffineEquiv`; open it only if you want that discussion.',
        '- After opening each PR, post a comment containing only the line `LLM-generated`.', '']
for i, p in enumerate(prs):
    dep = '' if i == 0 else '- [ ] depends on: #NNNN  (replace NNNN with the number of PR 7.1)\n\n'
    out += [f'## 7.{i + 1} `{BR[i]}`', '',
            f'Open: https://github.com/leanprover-community/mathlib4/compare/master...ishan-1729:mathlib4:{BR[i]}?expand=1', '',
            'Title:', '', '```text', TITLES[i], '```', '', 'Description (draft; put it in your own words where you can):', '',
            '```text', dep + facts(p['pr_facts']) + '\n\n' + AI, '```', '']
out += ['## What was checked', '',
        '- Both modules build without warnings, the style linter and `#lint` pass, and the main theorems use only the standard axioms.',
        '- The 7.1 version of the group file (without the affine section) was built and linted as a module, with the 7.2 file on top of it.',
        '- A mathematical review tested the statements on `S₃`, the affine group of `ZMod 5`, `A₅`, and `X³ − 2`; it found no error.',
        '- Not done: the full mathlib build, `lake exe mk_all --check`, `lake exe shake`, `bibtool` on the new bibliography entry. Mathlib CI runs these.', '',
        '## Points to know before review', '',
        '- Several general lemmas are private on purpose, because Tau Ceti has public versions of three of them (a centralizing element that fixes a point is 1; a commutative transitive subgroup acts freely; a nontrivial normal subgroup of a primitive group is transitive). A reviewer may ask to make them public. That is your call, case by case; the notes list them.',
        '- 7.2 is about solvability of the Galois group, not solvability by radicals. The module docstring says so. Calling it "Galois\'s criterion (Proposition VIII)" may draw a comment.',
        '- Not checked against the sources: the section number in the citation of Wielandt\'s *Finite permutation groups* (§11), and the page range 417-433 of the new bibliography entry `galois1846`.',
        '- The hypotheses have two shapes: `(hp : (Nat.card X).Prime)` in 7.1 and `{p} [Fact p.Prime] (hX : Nat.card X = p)` in 7.3. The notes explain why.', '']
open('D:/Projects/mathlib-prs/PR7-galois-prime-degree.md', 'w', encoding='utf-8', newline='\n').write('\n'.join(out) + '\n')

n = ['# Notes for PR 7: Galois\'s criterion in prime degree', '',
     'One section per PR. For each: what is stated, how it is proved step by step, and why the names, assumptions and file were chosen.', '']
for i, p in enumerate(prs):
    n += [f'## 7.{i + 1} `{BR[i]}`: {WHAT[i]}', '', notes(p['notes_md']), '']
n += ['## Overlap with Tau Ceti', '',
      v['tauceti_overlap'].strip().replace(' (D:/Projects/tauceti-ref/TauCeti/TauCeti, re-searched with rg)', ''), '']
open('D:/Projects/mathlib-prs/NOTES-galois-prime-degree.md', 'w', encoding='utf-8', newline='\n').write('\n'.join(n) + '\n')
print('written')
