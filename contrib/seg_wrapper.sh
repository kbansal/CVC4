#!/bin/bash
ulimit -c unlimited
"$@"
ret=$?
if test $ret -eq 134  -o $ret -eq 139; then
    echo -ne "backtrace\nexit\n" | gdb -q $1 core
fi
exit $ret
