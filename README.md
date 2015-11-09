This repository contains a number of algorithm implementations for the PlusCal algorithm language [1]. These implementations were written for the lecture "System concepts and programming" at University of Stuttgart, to demonstrate how to verify concurrent algorithms using model checking. 

The examples focus on the critical section problem (mutual exclusion, freedom from deadlocks and starvation). The algorithms were taken from the popular text book "Principles of Concurrent and Distributed Programming" (second edition) by M. Ben-Ari. Examples include Dekker's algorithm and Lamport's Bakery Algorithm. References to the algorithms described in the book can be found in the source code (.tla files).

# Prerequisite

To model-check the examples, you need the TLC model checker and the PlusCal translator, both included with the TLA+ tools. The TLA+ tools can be downloaded from the following link:

http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html

The tools are implemented in Java. For your convenience, we have provided scripts to call these tools with each example. To use these scripts, you need to set your Java CLASSPATH to the directory where you installed the TLA+ tools.

# Performing Model Checking

1. Change to the directory of the algorithm you want to check.
2. Translate the PlusCal algorithm description to TLA+ by calling the script ```compile.sh```.
3. Start model checking using the TLC model checker by calling the script ```check.sh```.

# Algorithms

Algorithms criticalsection1 to criticalsection4 are initial tries to solve the critical section problem. Intentionally, all of these examples have some problem and fail to implement at least one of the desired properties of the critical section problem (mutual exclusion, freedom from deadlocks or starvation). These imperfect algorithms are used to demonstrate how model checking can help to reveal these problems.

Algorithm criticalsection5dekker is Dekker's algorithm, which provides a complete solution for the critical section problem with two processes.

Algorithm criticalsection5bakery is Lamport's Bakery algorithm for n processes. This example is used to demonstrate the limitations of model checking. The Bakery algorithm has an infinite number of different states (token numbers can theoretically grow infinitely). Thus, model checking will never reach an end where all states have been checked. If we artificially limit the grows of token numbers to a maximum, the algorithm is not starvation free anymore, as can be demonstrated with model checking. 

# License

All implementation are covered by the liberal Apache 2 license hoping these examples might be useful for others.

# References

    [1] Leslie Lamport: The PlusCal Algorithm Language. Theoretical Aspects of Computing (ICTAC 2009), Lecture Notes in Computer Science 5684, pp. 36-60, 2009
