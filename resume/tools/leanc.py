"""Compile ONE Lean file of this project directly (no `lake build`, which takes ~20 minutes to start
on this machine and would rebuild a hundred modules).

  python .lake-local/leanc.py <path/to/File.lean> [--olean] [-Dname=value ...]

Without --olean: type-check only (for scratch files and final checks).
With --olean: also write .lake/build/lib/lean/<Module/Path>.olean and .ilean, so that other files can
import the module (the module name is the path relative to the project root, e.g.
JordanPick/JordanCurve/Arcs.lean -> JordanPick.JordanCurve.Arcs). Compile imports first, in order.
Uses the shared slot lock (at most 3 Lean processes on the machine) and retries transient
'failed to read file' errors (memory pressure). Project options autoImplicit=false and
pp.unicode.fun=true are always passed; add others with -D."""
import json, os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import check

args = sys.argv[1:]
want_olean = '--olean' in args
dopts = [a for a in args if a.startswith('-D')]
files = [a for a in args if not a.startswith('-')]
assert len(files) == 1, __doc__
src = Path(files[0]).resolve()
cmd = ['lean', '-DautoImplicit=false', '-Dpp.unicode.fun=true', *dopts]
if want_olean:
    rel = src.relative_to(ROOT).with_suffix('')
    o = ROOT / '.lake' / 'build' / 'lib' / 'lean' / rel.with_suffix('.olean')
    o.parent.mkdir(parents=True, exist_ok=True)
    cmd += ['-o', str(o), '-i', str(o.with_suffix('.ilean'))]
cmd.append(str(src))
envf = ROOT / '.lake-local' / 'lake_env.json'
if not envf.exists() or time.time() - envf.stat().st_mtime > 6 * 3600:
    out = subprocess.run(['lake', 'env', sys.executable, '-c', 'import os,json;print(json.dumps(dict(os.environ)))'],
                         cwd=ROOT, capture_output=True, text=True).stdout
    envf.write_text(out, encoding='utf-8')
env = json.loads(envf.read_text(encoding='utf-8'))
sys.stdout.reconfigure(encoding='utf-8')
for attempt in range(1, 5):
    slot = check.acquire('slot', 3)
    t0 = time.time()
    try:
        r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
    finally:
        slot.unlink(missing_ok=True)
    out = (r.stdout + r.stderr).strip()
    if r.returncode != 0 and ('failed to read file' in out or not out):
        print(f'[retry {attempt}] transient failure: {out[:200]}', flush=True)
        time.sleep(60)
        continue
    break
print(out[-15000:])
print(f"[{'OK' if r.returncode == 0 else 'FAIL'}] {src.relative_to(ROOT) if src.is_relative_to(ROOT) else src} ({time.time() - t0:.0f}s)")
sys.exit(r.returncode)
