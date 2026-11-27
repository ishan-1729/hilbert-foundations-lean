"""Cut the continued-fraction stack into branches of D:/Projects/mathlib4 without touching the
working tree: each stage is one commit on top of the previous stage (git plumbing, temp index)."""
import os, re, subprocess, sys, tempfile

ML = 'D:/Projects/mathlib4'
V = 'D:/Projects/mathlib-prs/scratch/lagrange/verify'
CF = 'Mathlib/Algebra/ContinuedFractions'
NT = 'Mathlib/NumberTheory/ContinuedFractions'


def git(*args, env=None, inp=None):
    e = dict(os.environ)
    if env:
        e.update(env)
    r = subprocess.run(['git', '-C', ML, *args], capture_output=True, input=inp, env=e)
    if r.returncode:
        sys.exit(f"git {' '.join(args)} failed: {r.stderr.decode()}")
    return r.stdout


def work(path):
    return open(f'{ML}/{path}', 'rb').read()


def master(path):
    return git('show', f'master:{path}')


def mathlib_lean(allowed):
    old = set(master('Mathlib.lean').decode().splitlines())
    out = []
    for line in work('Mathlib.lean').decode().splitlines():
        if line in old or line.split()[-1] in allowed:
            out.append(line)
    text = '\n'.join(out) + '\n'
    return text.encode()


def bib(keys):
    text = work('docs/references.bib').decode()
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


M = lambda *mods: mathlib_lean(set(mods))
STAGES = [
    ('cf-of-den-pos-of-injective',
     'feat(Algebra/ContinuedFractions): positivity of denominators and injectivity of `GenContFract.of`',
     {f'{CF}/Computation/Approximations.lean': lambda: work(f'{CF}/Computation/Approximations.lean'),
      f'{CF}/Computation/ApproximationCorollaries.lean': lambda: work(f'{CF}/Computation/ApproximationCorollaries.lean')}),
    ('cf-complete-quotient',
     'feat(Algebra/ContinuedFractions): complete quotients of a continued fraction',
     {f'{CF}/Computation/CompleteQuotient.lean': lambda: work(f'{CF}/Computation/CompleteQuotient.lean'),
      'Mathlib.lean': lambda: M('Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient')}),
    ('cf-periodic',
     'feat(Algebra/ContinuedFractions): eventually periodic and purely periodic continued fractions',
     {f'{CF}/Periodic.lean': lambda: work(f'{CF}/Periodic.lean'),
      'Mathlib.lean': lambda: M('Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient',
                                'Mathlib.Algebra.ContinuedFractions.Periodic')}),
    ('cf-periodic-quadratic-irrational',
     'feat(NumberTheory/ContinuedFractions): eventually periodic continued fractions are quadratic irrationals',
     {f'{NT}/QuadraticIrrational.lean': lambda: work(f'{NT}/QuadraticIrrational.lean'),
      'Mathlib.lean': lambda: M('Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient',
                                'Mathlib.Algebra.ContinuedFractions.Periodic',
                                'Mathlib.NumberTheory.ContinuedFractions.QuadraticIrrational')}),
    ('cf-lagrange',
     'feat(NumberTheory/ContinuedFractions): quadratic irrationals have eventually periodic continued fractions',
     {f'{NT}/Lagrange.lean': lambda: work(f'{NT}/Lagrange.lean'),
      'docs/references.bib': lambda: bib({'steinig1992'}),
      'Mathlib.lean': lambda: M('Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient',
                                'Mathlib.Algebra.ContinuedFractions.Periodic',
                                'Mathlib.NumberTheory.ContinuedFractions.QuadraticIrrational',
                                'Mathlib.NumberTheory.ContinuedFractions.Lagrange')}),
    ('cf-galois-purely-periodic',
     'feat(NumberTheory/ContinuedFractions): purely periodic continued fractions and reduced quadratic irrationals',
     {f'{NT}/PurelyPeriodic.lean': lambda: open(f'{V}/PurelyPeriodic_pr5.lean', 'rb').read(),
      'docs/references.bib': lambda: bib({'steinig1992', 'galois1829'}),
      'Mathlib.lean': lambda: M('Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient',
                                'Mathlib.Algebra.ContinuedFractions.Periodic',
                                'Mathlib.NumberTheory.ContinuedFractions.QuadraticIrrational',
                                'Mathlib.NumberTheory.ContinuedFractions.Lagrange',
                                'Mathlib.NumberTheory.ContinuedFractions.PurelyPeriodic')}),
    ('cf-galois-reversed-period',
     'feat(NumberTheory/ContinuedFractions): the reversed period of a purely periodic continued fraction',
     {f'{NT}/PurelyPeriodic.lean': lambda: open(f'{V}/PurelyPeriodic_full.lean', 'rb').read()}),
]

parent = git('rev-parse', 'master').decode().strip()
idx = os.path.join(tempfile.gettempdir(), 'idx_cf')
if os.path.exists(idx):
    os.remove(idx)
env = {'GIT_INDEX_FILE': idx}
git('read-tree', 'master', env=env)
for name, title, files in STAGES:
    for path, get in files.items():
        data = get()
        hygiene(path, data)
        blob = git('hash-object', '-w', '--stdin', inp=data).decode().strip()
        git('update-index', '--add', '--cacheinfo', f'100644,{blob},{path}', env=env)
    tree = git('write-tree', env=env).decode().strip()
    parent = git('commit-tree', tree, '-p', parent, '-m', title).decode().strip()
    git('branch', '-f', name, parent)
    stat = git('diff', '--shortstat', f'{name}~1', name).decode().strip()
    print(f'{name}: {parent[:10]} | {stat}')
os.remove(idx)
