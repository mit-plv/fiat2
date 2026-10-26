"""Find NESTED-LOOP EQUIJOINS in a source corpus.

What we are looking for, and why exactly this shape.  Ex_Family's cost is
quadratic because it iterates one collection inside another and keeps the
pairs whose attributes match:

    for a in coll:            for (A a : coll)
      for b in coll:            for (A b : coll)
        if a.x == b.y:            if (a.getX().equals(b.getY()))

An index on the inner collection's attribute turns the inner loop into a
probe, which is what takes the cost from n^2 to n.  So a hit must have all
three of:

  1. a loop binding an outer variable over something,
  2. a loop nested inside it binding a different variable, and
  3. an equality, inside the inner body, that mentions a MEMBER of the outer
     variable and a MEMBER of the inner variable.

Condition 3 is the discriminating one.  A nested loop whose condition does
not relate the two variables is not a join, and a nested loop comparing the
variables themselves (a == b) is a duplicate check, not an equijoin on an
attribute -- neither is counted.

PRECISION.  This is regex over text, not a parser: it does not know scope,
so an inner loop found by look-ahead may not really be inside the outer
body, and it cannot tell a collection from an array or a short constant
list.  Every hit is therefore printed with its file, line and the three
matched lines so that each can be read and judged by hand; the counts below
are candidates, not findings.
"""
import io, os, re, sys

JAVA_FOR = re.compile(r'\bfor\s*\(\s*(?:final\s+)?[\w.<>\[\],\s]+?\s+(\w+)\s*:\s*([^){;]+)\)')
PY_FOR   = re.compile(r'^(\s*)for\s+(\w+)\s+in\s+([^:]+):')
PY_COMP  = re.compile(r'for\s+(\w+)\s+in\s+(.+?)\s+for\s+(\w+)\s+in\s+(.+?)\s+if\s+(.+)')

def member(var):
    """`var.field`, `var.getField()`, `var[...]` -- a member of var."""
    return re.compile(r'\b' + re.escape(var) + r'\s*(?:\.\s*\w+\s*(?:\(\s*\))?|\[)')

def equality_joins(text, outer, inner):
    """an equality in `text` relating a member of outer to a member of inner"""
    mo, mi = member(outer), member(inner)
    out = []
    for line in text.split("\n"):
        if not (mo.search(line) and mi.search(line)):
            continue
        # == , != are both relational; .equals( is Java's
        if re.search(r'==|\.equals\s*\(', line):
            # reject the bare-variable comparison: a == b, a.equals(b)
            if re.search(r'\b' + re.escape(outer) + r'\s*(?:==|\.equals\s*\()\s*' +
                         re.escape(inner) + r'\b', line):
                continue
            if re.search(r'\b' + re.escape(inner) + r'\s*(?:==|\.equals\s*\()\s*' +
                         re.escape(outer) + r'\b', line):
                continue
            out.append(line.strip())
    return out

LOOKAHEAD_INNER = 6      # lines from the outer loop to the inner one
LOOKAHEAD_BODY  = 14     # lines of inner body to search for the condition

def scan_java(path, lines):
    hits = []
    for i, line in enumerate(lines):
        m = JAVA_FOR.search(line)
        if not m: continue
        outer, outer_src = m.group(1), m.group(2).strip()
        for j in range(i + 1, min(i + 1 + LOOKAHEAD_INNER, len(lines))):
            m2 = JAVA_FOR.search(lines[j])
            if not m2: continue
            inner, inner_src = m2.group(1), m2.group(2).strip()
            if inner == outer: continue
            body = "\n".join(lines[j + 1 : j + 1 + LOOKAHEAD_BODY])
            for cond in equality_joins(body, outer, inner):
                hits.append((i + 1, outer, outer_src, inner, inner_src, cond))
            break
    return hits

def scan_py(path, lines):
    hits = []
    for i, line in enumerate(lines):
        m = PY_FOR.match(line)
        if m:
            ind, outer, outer_src = m.group(1), m.group(2), m.group(3).strip()
            for j in range(i + 1, min(i + 1 + LOOKAHEAD_INNER, len(lines))):
                m2 = PY_FOR.match(lines[j])
                if not m2: continue
                if len(m2.group(1)) <= len(ind): break      # dedented: not nested
                inner, inner_src = m2.group(2), m2.group(3).strip()
                if inner == outer: continue
                body = "\n".join(lines[j + 1 : j + 1 + LOOKAHEAD_BODY])
                for cond in equality_joins(body, outer, inner):
                    hits.append((i + 1, outer, outer_src, inner, inner_src, cond))
                break
        c = PY_COMP.search(line)
        if c:
            outer, outer_src, inner, inner_src, cond = c.groups()
            if outer != inner and equality_joins(cond, outer, inner):
                hits.append((i + 1, outer, outer_src.strip(), inner,
                             inner_src.strip(), cond.strip()))
    return hits

root = sys.argv[1]
total_files = 0
all_hits = []
for dirpath, _, names in os.walk(root):
    for n in names:
        if not (n.endswith(".java") or n.endswith(".py")): continue
        p = os.path.join(dirpath, n)
        try:
            lines = io.open(p, encoding="utf-8", errors="replace").read().split("\n")
        except Exception:
            continue
        total_files += 1
        hits = scan_java(p, lines) if n.endswith(".java") else scan_py(p, lines)
        for h in hits:
            all_hits.append((os.path.relpath(p, root), ) + h)

print(f"# files scanned: {total_files}")
print(f"# candidate nested-loop equijoins: {len(all_hits)}")
for rel, ln, o, osrc, i2, isrc, cond in all_hits:
    print(f"\n{rel}:{ln}")
    print(f"    outer  {o:12s} <- {osrc[:62]}")
    print(f"    inner  {i2:12s} <- {isrc[:62]}")
    print(f"    cond   {cond[:100]}")
