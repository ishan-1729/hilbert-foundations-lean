#!/usr/bin/env python3
"""Run Lean commands in the mathlib checkout, sharing this machine's 3 Lean slots.

Usage (from anywhere):
  python D:/Projects/mathlib-prs/tools/mlrun.py build Mathlib.Foo.Bar [more modules]
  python D:/Projects/mathlib-prs/tools/mlrun.py lean  path/to/Scratch.lean
  python D:/Projects/mathlib-prs/tools/mlrun.py lint            # lake exe lint-style
`build` holds a lock so that only one `lake build` runs in the checkout at a time.
"""
import os, subprocess, sys, time
from pathlib import Path

ML = Path(r'D:/Projects/mathlib4')
SLOT_DIR = Path(os.environ.get('TEMP', '/tmp')) / 'lean_slots_shared'
sys.path.insert(0, r'D:/Projects/hilbert-foundations-lean/scripts')
import check  # pid_alive / stale / acquire, shared slot directory


def main() -> int:
    sys.stdout.reconfigure(encoding='utf-8')
    mode, args = sys.argv[1], sys.argv[2:]
    held = []
    try:
        if mode == 'build':
            held.append(check.acquire('mlbuild', 1))
            cmd = ['lake', 'build', *args]
        elif mode == 'lean':
            cmd = ['lake', 'env', 'lean', *[str(Path(a).resolve()) for a in args]]
        elif mode == 'lint':
            held.append(check.acquire('mlbuild', 1))
            cmd = ['lake', 'exe', 'lint-style', *args]
        else:
            print('unknown mode', mode); return 2
        held.append(check.acquire('slot', 3))
        t0 = time.time()
        r = subprocess.run(cmd, cwd=ML, capture_output=True, text=True, encoding='utf-8', errors='replace')
    finally:
        for h in held:
            h.unlink(missing_ok=True)
    out = (r.stdout + r.stderr)
    if mode == 'build':  # keep errors/warnings and the summary, drop progress noise
        keep = [l for l in out.splitlines() if not l.startswith(('✔', 'ℹ')) and 'Replayed' not in l and not l.startswith('trace:')]
        out = '\n'.join(keep)
    print(out[-12000:])
    print(f"[{'OK' if r.returncode == 0 else 'FAIL'}] {mode} {' '.join(args)} ({time.time() - t0:.0f}s)")
    return r.returncode


if __name__ == '__main__':
    sys.exit(main())
