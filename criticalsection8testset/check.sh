#!/bin/sh

# Set your CLASSPATH variable to the directory where the TLA+ tools are
# installed.

# Number of worker threads
WORKERS=1

java tlc2.TLC criticalsection8testset.tla -config criticalsection8testset.cfg -workers $WORKERS -modelcheck -deadlock
