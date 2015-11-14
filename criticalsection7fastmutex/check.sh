#!/bin/sh

# Set your CLASSPATH variable to the directory where the TLA+ tools are
# installed.

# Number of worker threads
WORKERS=1

java tlc2.TLC criticalsection7fastmutex.tla -config criticalsection7fastmutex.cfg -workers $WORKERS -modelcheck -deadlock
