# Maintaining this wiki

[Home](Home.md)

## Principles

* Keep every number and status traceable: link the memo, script or result file.
* Corrections win over earlier claims. When something changes, update the [ledger](Results-Ledger.md) and add a [Corrections](Corrections.md) entry.
* Mark unfinished areas "as of <commit>, in progress", and update the table on [Home](Home.md).
* This is Markdown only. Keep files small, and do not add binaries.

## Folding in the running branches

| Branch | When it lands, update |
|---|---|
| `w22-speed` (`624be06`) | [Software](Software.md) module list and pipelines; [Benchmarks](Benchmarks.md) progression and tables; [Timeline](Timeline.md); test count |
| `w23-speed2` (`4742c66`) | [Software](Software.md) and [Benchmarks](Benchmarks.md) kernel section; [Timeline](Timeline.md) |
| `w18-latin` (merged; `8047173`) | when its red-team lands, update [Moonshots](Moonshots.md), [Barriers](Math-Barriers.md), [Results ledger](Results-Ledger.md). Replace the backticked references to `docs/w18-latin.md` by links after merging master into this branch |
| `w24-video-review` (`08fd28a`) | [Reproduce](Reproduce.md#the-video); [Corrections](Corrections.md) for any factual fixes to the video |

After merging: search this directory for "in progress" and "as of", and update the "Work still in progress" table.

## Link check

Save this as `check_links.py` outside `wiki/` (the wiki itself stays Markdown) and run it from the repository root with `python3 check_links.py wiki`. It checks that relative links resolve, and that `#anchors` in links to Markdown files match a heading, using GitHub's slug rule approximately. It also flags table rows with the wrong number of cells, which an unescaped `|` causes.

```python
import os, re, sys
root = sys.argv[1]
md = [f for f in os.listdir(root) if f.endswith('.md')]
link = re.compile(r'\[[^\]]*\]\(([^)\s]+)\)')
def slug(h):
    h = re.sub(r'[`*]', '', h.strip().lower())
    h = re.sub(r'[^\w\- ]', '', h)
    return h.replace(' ', '-')
def anchors(path):
    out = set()
    for l in open(path, encoding='utf8'):
        m = re.match(r'#+\s+(.*)', l)
        if m:
            out.add(slug(m.group(1)))
    return out
bad = []
for f in sorted(md):
    src = os.path.join(root, f)
    text = open(src, encoding='utf8').read()
    in_code = False
    lines = []
    for ln, line in enumerate(text.splitlines(), 1):
        if line.startswith(chr(96) * 3):
            in_code = not in_code
            continue
        if not in_code:
            lines.append((ln, line))
    for ln, line in lines:
        for target in link.findall(line):
            if re.match(r'[a-z]+:', target) or target.startswith('#'):
                continue
            path, _, frag = target.partition('#')
            full = os.path.normpath(os.path.join(root, path))
            if not os.path.exists(full):
                bad.append(f'{f}:{ln}: missing {target}')
            elif frag and full.endswith('.md') and frag.lower() not in anchors(full):
                bad.append(f'{f}:{ln}: no anchor {target}')
    expect = None
    for ln, line in lines:
        if line.startswith('|'):
            n = len(re.findall(r'(?<!\\)\|', line))
            if expect is None:
                expect = n
            elif n != expect:
                bad.append(f'{f}:{ln}: table row has {n} pipes, expected {expect}')
        else:
            expect = None
print('\n'.join(bad) if bad else 'all links and tables ok')
sys.exit(1 if bad else 0)
```
