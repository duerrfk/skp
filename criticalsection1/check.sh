#!/bin/sh

# Set your CLASSPATH variable to the directory where the TLA+ tools are
# installed.

# Number of worker threads
WORKERS=1

java tlc2.TLC criticalsection1.tla -config criticalsection1.cfg -workers $WORKERS -modelcheck -deadlock
