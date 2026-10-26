#!/bin/zsh
# $1 = hard wall-clock seconds; $2.. = command
cap=$1; shift
"$@" & pid=$!
( sleep $cap; kill -9 $pid 2>/dev/null; pkill -9 -P $pid 2>/dev/null ) & wd=$!
wait $pid; st=$?
kill $wd 2>/dev/null
exit $st
