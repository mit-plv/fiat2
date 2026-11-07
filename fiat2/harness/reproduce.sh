#!/bin/sh
# Regenerate the measurements the paper quotes, into results/.
#
# Each output file begins with the exact command that produced it, so a table
# in the paper can be traced to a command and a command to a file.
#
#   ./reproduce.sh checks   correctness only: the differential test and the
#                           compiled checks under all three settings.  Run this
#                           first; a number from a tree that does not pass it
#                           means nothing.            (~6 min)
#   ./reproduce.sh counted  the tables that are PURELY counted.  The counters are
#                           exact and deterministic, so these four files are
#                           regression tests: re-run on an unchanged tree and
#                           `git diff` is EMPTY.                     (~9 min)
#   ./reproduce.sh compare  the three-column and fair-baseline tables.  These
#                           print counted AND seconds columns in one row, which
#                           is the point of them -- so the FILE does not diff
#                           clean even though its counted columns do. (~12 min)
#   ./reproduce.sh timed    the tables that are about seconds.  Never reproduces
#                           itself.                                  (~25 min)
#   ./reproduce.sh slow     the write-fraction sweep, the scale ladder and the
#                           stationarity check.  Hours, mostly because
#                           dependent_plugins' source form is quadratic.
#   ./reproduce.sh all      counted + compare + timed
#
# The tiers are drawn by WHAT IS IN THE FILE, not by what the table is for.
# `counted` claiming to be byte-stable is checkable, and it was wrong once:
# `threeway` and `indexed` print a seconds column beside their counted one, so
# they are `compare`, not `counted`.
#
# PREREQUISITE, and it is not optional: `make` at the repository root.  The
# harness consumes terms extracted by the Rocq build, so `dune build` before a
# `make` fails with a missing module, which is the intended failure.
set -e

HERE=$(cd "$(dirname "$0")" && pwd)
OUT="$HERE/results"
mkdir -p "$OUT"
cd "$HERE"
dune build 2>&1 | head -40

M=./_build/default/main.exe
C=./_build/default/compiled/compiled.exe

# run <file> <binary> <args...>  -- records the command in the file it produced
run() {
  f="$OUT/$1"; shift
  b="$1"; shift
  printf '$ %s %s\n\n' "$(basename "$b")" "$*" > "$f"
  "$b" "$@" >> "$f" 2>&1
  echo "  wrote results/$(basename "$f")"
}

# append a second command's output to the same file, for a table that is one
# table per setting or per workload parameter
add() {
  f="$OUT/$1"; shift
  b="$1"; shift
  printf '\n$ %s %s\n\n' "$(basename "$b")" "$*" >> "$f"
  "$b" "$@" >> "$f" 2>&1
}

do_checks() {
  run check-differential.txt      $M check share=8
  run check-compiled.txt          $C
}

do_counted() {
  # --- every subject, every setting: the check that no performance claim is
  #     hiding a pathology at a storage nobody measured
  run settings-all-subjects.txt   $C work typed 800
  add settings-all-subjects.txt   $C work trees 800
  add settings-all-subjects.txt   $C work hashes 800

  # --- the derived read against the query as WRITTEN (no index)
  for k in 2 128 2048; do
    if [ "$k" = 2 ]; then run src-vs-opt-fuzzy.txt $C work only=fuzzy_search share=$k 6400
    else add src-vs-opt-fuzzy.txt $C work only=fuzzy_search share=$k 6400; fi
  done

  # --- one rule change at a time, and the two language limits beyond them
  first=1
  for st in typed trees hashes; do
    for k in 2 128 2048; do
      if [ $first = 1 ]; then run rule-by-rule.txt $C shapes $st share=$k 6400; first=0
      else add rule-by-rule.txt $C shapes $st share=$k 6400; fi
    done
  done

  # --- WHICH COUNTER the residual lives in, at `typed` and at a common storage
  run residual-breakdown.txt      $C breakdown typed share=2 6400
  add residual-breakdown.txt      $C breakdown trees share=2 6400
}

# The author comparisons.  Each row carries counted AND seconds columns, so
# these files are not byte-stable even though every counted figure in them is.
do_compare() {
  # --- the derived read against the AUTHOR'S OWN CODE (a scan)
  for k in 2 128 2048; do
    if [ "$k" = 2 ]; then run author-scan-fuzzy.txt $C threeway only=fuzzy_search share=$k 6400
    else add author-scan-fuzzy.txt $C threeway only=fuzzy_search share=$k 6400; fi
  done

  # --- the FAIR baseline: the same author, GIVEN a hand-built GIN index
  for k in 2 128 2048; do
    if [ "$k" = 2 ]; then run fair-baseline-fuzzy.txt $C indexed only=fuzzy_search share=$k 6400
    else add fair-baseline-fuzzy.txt $C indexed only=fuzzy_search share=$k 6400; fi
  done
  run fair-baseline-user-search.txt $C indexed only=user_search share=8 6400
}

do_timed() {
  # the residual in SECONDS.  Uses one op count per cell satisfying every
  # column, with the ops phase required to dominate the build; scaling each
  # column to its own count is what biased an earlier table by 29-88%.
  run residual-seconds.txt        $C shapesec typed share=2 6400
  add residual-seconds.txt        $C shapesec trees share=2 6400
  for k in 128 2048; do add residual-seconds.txt $C shapesec typed share=$k 6400; done

  first=1
  for k in 2 128 2048; do
    if [ $first = 1 ]; then run seconds-per-read-kind.txt $C kinds only=fuzzy_search share=$k 6400; first=0
    else add seconds-per-read-kind.txt $C kinds only=fuzzy_search share=$k 6400; fi
  done
}

do_slow() {
  run sweep-write-fraction.txt    $C sweep
  run scale-ladder.txt            $C scale
  run stationarity.txt            $C stationary
  run matched-storage.txt         $C matched
}

case "${1:-all}" in
  checks)  do_checks ;;
  counted) do_counted ;;
  compare) do_compare ;;
  timed)   do_timed ;;
  slow)    do_slow ;;
  all)     do_counted; do_compare; do_timed ;;
  *) echo "usage: $0 [checks|counted|compare|timed|slow|all]" >&2; exit 2 ;;
esac
