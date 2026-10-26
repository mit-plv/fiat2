"""Second pass: the nested-loop equijoin written as a STREAM or a GENERATOR.

The first pass looked for a `for` inside a `for`.  Modern code usually does
not write the inner loop that way -- it writes

    Java    for (A a : coll) { ... coll2.stream().filter(b -> b.getY().equals(a.getX())) ... }
            for (A a : coll) { ... coll2.stream().anyMatch(b -> b.getY() == a.getX()) ... }
    Python  for a in coll:   ... any(b["y"] == a["x"] for b in coll2) ...
            for a in coll:   ... [b for b in coll2 if b.y == a.x] ...

which is the same quadratic nested loop with the inner one spelled as a
pipeline.  Missing these would make a low count a fact about the regex
rather than about the corpus, so they are searched for separately here.

The test is the same discriminating one as before: inside the outer loop's
body, a lambda or comprehension that BINDS ITS OWN VARIABLE over something
and compares a member of that variable against a member of the outer loop's
variable.  Printed with evidence, judged by hand.
"""
import io, os, re, sys

JAVA_FOR = re.compile(r'\bfor\s*\(\s*(?:final\s+)?[\w.<>\[\],\s]+?\s+(\w+)\s*:\s*([^){;]+)\)')
PY_FOR   = re.compile(r'^(\s*)for\s+(\w+)\s+in\s+([^:]+):')

# b -> ... b.y ... a.x ...   (Java lambda)
JAVA_LAMBDA = re.compile(r'\(?\s*(\w+)\s*\)?\s*->')
# for b in COLL   inside a comprehension or generator, on one line
PY_GEN = re.compile(r'for\s+(\w+)\s+in\s+([\w.\[\]()"\']+)')

def member(var):
    return re.compile(r'\b' + re.escape(var) + r'\s*(?:\.\s*\w+\s*(?:\(\s*\))?|\[)')

def relates(line, outer, inner):
    mo, mi = member(outer), member(inner)
    if not (mo.search(line) and mi.search(line)): return False
    if not re.search(r'==|\.equals\s*\(', line): return False
    # reject bare-variable comparisons and self-identity
    if re.search(r'\b%s\s*(?:==|\.equals\s*\()\s*%s\b' % (re.escape(outer), re.escape(inner)), line):
        return False
    if re.search(r'\b%s\s*(?:==|\.equals\s*\()\s*%s\b' % (re.escape(inner), re.escape(outer)), line):
        return False
    return True

BODY = 18

def scan(path, lines, is_java):
    hits = []
    forre = JAVA_FOR if is_java else PY_FOR
    for i, line in enumerate(lines):
        m = forre.search(line) if is_java else forre.match(line)
        if not m: continue
        outer = m.group(1) if is_java else m.group(2)
        osrc  = (m.group(2) if is_java else m.group(3)).strip()
        for j in range(i + 1, min(i + 1 + BODY, len(lines))):
            cand = lines[j]
            if is_java:
                binders = [(mm.group(1), "lambda") for mm in JAVA_LAMBDA.finditer(cand)]
                # only interesting when a stream/collection pipeline is involved
                if not re.search(r'\.(stream|filter|anyMatch|noneMatch|allMatch|findFirst|removeIf)\s*\(', cand):
                    binders = []
            else:
                binders = [(mm.group(1), "gen over " + mm.group(2)) for mm in PY_GEN.finditer(cand)]
            for inner, how in binders:
                if inner == outer: continue
                if relates(cand, outer, inner):
                    hits.append((i + 1, outer, osrc, inner, how, cand.strip()))
    return hits

root = sys.argv[1]
nfiles = 0; out = []
for dirpath, _, names in os.walk(root):
    for n in names:
        if not (n.endswith(".java") or n.endswith(".py")): continue
        p = os.path.join(dirpath, n)
        try: lines = io.open(p, encoding="utf-8", errors="replace").read().split("\n")
        except Exception: continue
        nfiles += 1
        for h in scan(p, lines, n.endswith(".java")):
            out.append((os.path.relpath(p, root),) + h)

print(f"# files scanned: {nfiles}")
print(f"# candidates (stream/generator inner loop): {len(out)}")
for rel, ln, o, osrc, i2, how, src in out:
    print(f"\n{rel}:{ln}")
    print(f"    outer {o:10s} <- {osrc[:58]}")
    print(f"    inner {i2:10s} ({how[:34]})")
    print(f"    {src[:110]}")
