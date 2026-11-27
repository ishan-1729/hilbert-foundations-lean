import subprocess, sys, re

BS = chr(92)


def strip(s):
    out = []
    i = 0
    n = len(s)
    depth = 0
    while i < n:
        if depth == 0 and s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == BS else 1
            out.append(s[i:j + 1])
            i = j + 1
            continue
        if s.startswith('/-', i):
            depth += 1
            i += 2
            continue
        if depth > 0 and s.startswith('-/', i):
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if s.startswith('--', i):
            j = s.find('\n', i)
            i = n if j < 0 else j
            continue
        out.append(s[i])
        i += 1
    return re.sub(r'\s+', ' ', ''.join(out)).strip(), depth


bad = 0
for f in sys.argv[1:]:
    old = subprocess.run(['git', 'show', 'HEAD:' + f], capture_output=True).stdout.decode('utf-8').replace('\r\n', '\n')
    new = open(f, 'rb').read().decode('utf-8').replace('\r\n', '\n')
    (a, _), (b, d) = strip(old), strip(new)
    same = a == b and d == 0
    print(('OK  ' if same else 'DIFF'), f, 'final comment depth', d)
    bad += not same
sys.exit(bad)
