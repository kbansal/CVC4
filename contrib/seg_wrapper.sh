#!/bin/bash
echo -ne "run\nbacktrace\ninfo threads\nthread 1\nbacktrace\nthread 2\nbacktrace\nthread 3\nbacktrace\nthread 0\nbacktrace\nexit\n" | gdb --args $@
