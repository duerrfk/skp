#!/bin/sh

# Set your CLASSPATH variable to the directory where the TLA+ tools are
# installed.

# Number of worker threads
WORKERS=1

java tlc2.TLC criticalsection4.tla -config criticalsection4.cfg -workers $WORKERS -modelcheck -deadlock
