This repository contains PlusCal [1] formulations of various solutions of the critical section problem like Lamport's Fast Mutual Exclusion algorithm or Dekker's algorithm to perform model checking on these algorithms. Originally, these examples were written for the lecture _System concepts and programming_ at University of Stuttgart, to demonstrate how to verify concurrent algorithms using model checking to verify desired properties like mutual exclusion, freedom from deadlocks, and freedom from starvation. 

Examples include Dekker's algorithm and Lamport's Bakery and Fast Mutual Exclusion Algorithm as well as several teaching examples from the popular text book _Principles of Concurrent and Distributed Programming (second edition)_ by M. Ben-Ari to demonstrate different problems and how to find them using model checking. References to the algorithms described in the papers and book can be found in the source code (.tla files).

# Prerequisite

To perform model checking on the examples, you need the TLC model checker and the PlusCal translator, both included with the TLA+ tools. The TLA+ tools can be downloaded from the following link:

http://research.microsoft.com/en-us/um/people/lamport/tla/tools.html

The tools are implemented in Java. For your convenience, we have provided scripts to call these tools with each example. To use these scripts, you need to set your Java CLASSPATH to the directory where you installed the TLA+ tools.

# Performing Model Checking

1. Change to the directory of the algorithm you want to check.
2. Translate the PlusCal formulation to TLA+ by calling the script ```compile.sh```.
3. Start model checking using the TLC model checker by calling the script ```check.sh```.

# Algorithms

The algorithms _criticalsection1_ to _criticalsection4_ are initial attempts to solve the critical section problem. Intentionally, all of these examples have some problem and fail to implement at least one of the desired properties of the critical section problem (mutual exclusion, freedom from deadlocks, freedom from starvation). These imperfect algorithms are used to demonstrate how model checking can help to reveal these problems.

Algorithm _criticalsection5dekker_ is **Dekker's algorithm**, which provides a complete solution for the critical section problem guaranteeing mutual exclusion, freedom from deadlocks, and freedom from starvation with two processes.

Algorithm _criticalsection6bakery_ is **Lamport's Bakery algorithm** [2], which guarantees mutual exclusion, freedom from deadlocks, and freedom from starvation for _N_ processes. This example is used to demonstrate the limitations of model checking. The Bakery algorithm might go through an infinite number of different states since token numbers can theoretically grow infinitely. Thus, model checking will never reach an end where all states have been checked. If we artificially limit token numbers to a pre-defined maximum value, the algorithm is not starvation free anymore, as can be demonstrated with model checking. 

Algorithm _criticalsection7fastmutex_ is **Lamport's Fast Mutual Exclusion** algorithm for _N_ processes [3]. This algorithm guarantees mutual exclusion, and it is free from deadlocks. However, it trades off starvation freedom for faster entry into the critical section in scenarios without contention: The Fast Mutual Exclusion algorithm requires O(1) operations if only a single process wants to enter the critical section. For a comparison, the Bakery algorithm always requires O(N) operations, also in scenarios without contention (however, the Bakery algorithm is starvation free). 

Algorithm _criticalsection8testset_ uses an atomic test and set operation to guarantee mutual exclusion. This implementation is deadlock free, however, processes might starve.

# License

All implementation are covered by the liberal Apache 2 license hoping these examples might be useful for others.

# References

[1] Leslie Lamport: The PlusCal Algorithm Language. Theoretical Aspects of Computing (ICTAC 2009), Lecture Notes in Computer Science 5684, pp. 36-60, 2009

[2] Leslie Lamport: A New Solution of Dijkstra's Concurrent Programming Problem. Communications of the ACM, 17(8), pp. 453-455, August 1974.

[3] Leslie Lamport: A fast mutual exclusion algorithm. ACM Transactions on Computer Systems (TOCS), 5(1), February 1987.
