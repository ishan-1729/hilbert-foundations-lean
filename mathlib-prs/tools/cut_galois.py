"""Cut the Galois prime-degree stack into branches of D:/Projects/mathlib4 without touching the
working tree. Branch 1: group form. Branch 2 (on 1): equation form. Branch 3 (on 1): affine form."""
import os, re, subprocess, sys, tempfile

ML = 'D:/Projects/mathlib4'
G = 'Mathlib/GroupTheory/GroupAction/PrimeDegree.lean'
E = 'Mathlib/FieldTheory/Galois/PrimeDegree.lean'
CUT = 'D:/Projects/mathlib-prs/scratch/galois-prime-degree/PR1/PrimeDegree.lean'
GFULL = sys.argv[1] if len(sys.argv) > 1 else f'{ML}/{G}'


def git(*args, env=None, inp=None):
    e = dict(os.environ)
    if env:
        e.update(env)
    r = subprocess.run(['git', '-C', ML, *args], capture_output=True, input=inp, env=e)
    if r.returncode:
        sys.exit(f"git {' '.join(args)} failed: {r.stderr.decode()}")
    return r.stdout


def mathlib_lean(allowed):
    old = set(git('show', 'master:Mathlib.lean').decode().splitlines())
    out = [l for l in open(f'{ML}/Mathlib.lean', encoding='utf-8').read().splitlines()
           if l in old or l.split()[-1] in allowed]
    assert len(out) == len(old) + len(allowed)
    return ('\n'.join(out) + '\n').encode()


def bib(keys):
    text = open(f'{ML}/docs/references.bib', encoding='utf-8', newline='').read()
    for k in ('galois1829', 'galois1846', 'steinig1992'):
        if k in keys:
            assert f'{k},' in text, k
            continue
        text, n = re.subn(r'@\w+\{\s*' + k + r',\n(?:.*\n)*?\}\n\n', '', text)
        assert n <= 1
    return text.encode()


def hygiene(path, data):
    assert b'\r' not in data, f'CR in {path}'
    assert data.endswith(b'\n') and not data.endswith(b'\n\n'), f'final newline {path}'
    if path.endswith('.lean') and path != 'Mathlib.lean':
        for i, l in enumerate(data.decode().split('\n'), 1):
            assert len(l) <= 100, f'{path}:{i} long line'
            assert l == l.rstrip(), f'{path}:{i} trailing whitespace'


def commit(parent, title, files):
    idx = os.path.join(tempfile.gettempdir(), 'idx_gal')
    if os.path.exists(idx):
        os.remove(idx)
    env = {'GIT_INDEX_FILE': idx}
    git('read-tree', parent, env=env)
    for path, data in files.items():
        hygiene(path, data)
        blob = git('hash-object', '-w', '--stdin', inp=data).decode().strip()
        git('update-index', '--add', '--cacheinfo', f'100644,{blob},{path}', env=env)
    tree = git('write-tree', env=env).decode().strip()
    os.remove(idx)
    return git('commit-tree', tree, '-p', parent, '-m', title).decode().strip()


GM, EM = 'Mathlib.GroupTheory.GroupAction.PrimeDegree', 'Mathlib.FieldTheory.Galois.PrimeDegree'
c1 = commit(git('rev-parse', 'master').decode().strip(),
            'feat(GroupTheory/GroupAction/PrimeDegree): solvable transitive groups of prime degree',
            {G: open(CUT, 'rb').read(), 'Mathlib.lean': mathlib_lean({GM})})
c2 = commit(c1, 'feat(FieldTheory/Galois/PrimeDegree): solvability of irreducible polynomials of prime degree',
            {E: open(f'{ML}/{E}', 'rb').read(), 'Mathlib.lean': mathlib_lean({GM, EM}),
             'docs/references.bib': bib({'galois1846'})})
c3 = commit(c1, 'feat(GroupTheory/GroupAction/PrimeDegree): solvable transitive groups of prime degree act by affine maps of `ZMod p`',
            {G: open(GFULL, 'rb').read()})
for name, c in (('galois-prime-degree-group', c1), ('galois-prime-degree-polynomial', c2), ('galois-prime-degree-affine', c3)):
    git('branch', '-f', name, c)
    print(name, c[:10], '|', git('diff', '--shortstat', f'{name}~1', name).decode().strip())
