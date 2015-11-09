#!/bin/sh

# Set your CLASSPATH variable to the directory where the TLA+ tools are
# installed.

# Number of worker threads
WORKERS=4

java tlc2.TLC criticalsection6bakery.tla -config criticalsection6bakery.cfg -workers $WORKERS -modelcheck -deadlock
