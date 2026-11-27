"""Make compiled Tau Ceti modules available locally (restored from Tau Ceti's public build cache
through Lake's artifact cache; compiled from source only if the cache misses).

  python .lake-local/tc_modules.py TauCeti.Some.Module [TauCeti.Other.Module ...]

Runs ONE `lake build <modules>` for the given Tau Ceti modules (and their imports) with the cache
settings, under the shared build lock. Lake needs 10-20 minutes to start on this machine, so ask
for all the modules you need in one call. Do not use it for modules of this project."""
import os, subprocess, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
import check

mods = sys.argv[1:]
assert mods and all(m.startswith('TauCeti.') for m in mods), __doc__
env = dict(os.environ)
env.update(LAKE_CONFIG=str(ROOT / '.lake-local' / 'lake-cache.toml'), LAKE_CACHE_DIR=str(ROOT / '.lake' / 'cache'),
           LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='true', LEAN_NUM_THREADS='2')
lock = check.acquire('build', 1)
slot = check.acquire('slot', 3)
t0 = time.time()
try:
    r = subprocess.run(['lake', 'build', *mods], cwd=ROOT, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
finally:
    slot.unlink(missing_ok=True)
    lock.unlink(missing_ok=True)
sys.stdout.reconfigure(encoding='utf-8')
out = '\n'.join(l for l in (r.stdout + r.stderr).splitlines() if 'error' in l.lower() or 'Build completed' in l or l.startswith('✖'))
print(out[-6000:])
print(f"[{'OK' if r.returncode == 0 else 'FAIL'}] lake build of {len(mods)} Tau Ceti module(s) ({time.time() - t0:.0f}s)")
sys.exit(r.returncode)
