import sys, subprocess, time
sys.path.insert(0, r'D:/Projects/hilbert-foundations-lean/scripts')
import check
lock = check.acquire('build', 1); s = check.acquire('slot', 3)
try:
    t0 = time.time()
    r = subprocess.run(sys.argv[2:], cwd=sys.argv[1], capture_output=True, text=True, encoding='utf-8', errors='replace')
finally:
    s.unlink(missing_ok=True); lock.unlink(missing_ok=True)
sys.stdout.reconfigure(encoding='utf-8')
out = '\n'.join(l for l in (r.stdout + r.stderr).splitlines() if 'error' in l.lower() or 'Build completed' in l or 'checked' in l or 'sorry' in l or l.startswith('✖'))
print(out[-6000:]); print('rc', r.returncode, f'{time.time()-t0:.0f}s')
