-------------------- MODULE criticalsection7fastmutex ------------------------

(****************************************************************************)
(* Copyright 2015 University of Stuttgart                                   *)
(* Author: Frank Duerr (frank.duerr@ipvs.uni-stuttgart.de)                  *) 
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License");          *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(* http://www.apache.org/licenses/LICENSE-2.0                               *)
(*                                                                          *) 
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

(****************************************************************************)
(* PlusCal implementation of Lamport's Fast Mutex Algorithm described in    *)
(* Leslie Lamport: A fast mutual exclusion algorithm. ACM Transactions on   *)
(* Computer Systems (TOCS), 5(1), February 1987.                            *)
(*                                                                          *)
(* This algorithm guarantees mutual exclusion with n processes. It is       *)
(* deadlock free. However, it trades freedom from starvation for fast entry *)
(* into the critical section with little contention.                        *)
(****************************************************************************)

EXTENDS Integers, Sequences

CONSTANT N

(*

--algorithm criticalsection7fastmutex
{
    \* Global variables
    variables gate1 = 0; gate2 = 0; choosing = [x \in 1..N |-> FALSE]; 

    \* The non-critical section.
    \* For checking for freedom from starvation, it is important that
    \* a process might stay in the non-critical section forever (however,
    \* each process must leave the critical section). 
    \* This procedure covers both cases: finite and infinite execution 
    \* of the non-critical section. 
    procedure NCS()
        variable isEndless;
    {
	\* Non-deterministically choose whether the procedure will
	\* be endless or finite.
        ncs0: with (x \in {0,1}) {
                  isEndless := x;
              };
        ncs1: if (isEndless = 1) {
                  ncs2: while (TRUE) {
                      ncs3: skip;
                  }
              } else {
                  ncs4: return;
              }
    }

    \* Process 1 to N
    process(P \in 1..N) 
        variables procs, i;
    {
        
        p0: while (TRUE) {
                p1: call NCS(); \* non-critical section
                p2: choosing[self] := TRUE; 
                p3: gate1 := self;
                p4: if (gate2 # 0) {
                        p5: choosing[self] := FALSE;
                        p6: await (gate2 = 0);
                        p7: goto p2;
                    };
                p8: gate2 := self;
                p9: if (gate1 # self) {
                        p10: choosing[self] := FALSE;
                        \* For all processes i: await (choosing[i] = FALSE)
                        \* Note that the iteration over all elements in choosing
                        \* is deliberately non-atomic. Even the order in which
                        \* elements are accesses is non-deterministic.
                        p11a: procs := 1..N;
                        p11b: while (procs # {}) {
                                  \* Choose one process randomly as i
                                  with (proc \in procs) {
                                      i := proc;
                                  };
                                  procs := procs \ {i};
                                  p11c: await (choosing[i] = FALSE);
                              }; 
                        p12: if (gate2 # self) {
                                 p13: await (gate2 = 0);
                                 p14: goto p2;
                             };
                    };
	        p15: skip; \* critical section
	        p16: gate2 := 0; 
                p17: choosing[self] := FALSE;
            } 
    }

}

*)

\*** The PlusCal translator will insert the TLA code into the following block
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES gate1, gate2, choosing, pc, stack, isEndless, procs, i

vars == << gate1, gate2, choosing, pc, stack, isEndless, procs, i >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ gate1 = 0
        /\ gate2 = 0
        /\ choosing = [x \in 1..N |-> FALSE]
        (* Procedure NCS *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        (* Process P *)
        /\ procs = [self \in 1..N |-> defaultInitValue]
        /\ i = [self \in 1..N |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p0"]

ncs0(self) == /\ pc[self] = "ncs0"
              /\ \E x \in {0,1}:
                   isEndless' = [isEndless EXCEPT ![self] = x]
              /\ pc' = [pc EXCEPT ![self] = "ncs1"]
              /\ UNCHANGED << gate1, gate2, choosing, stack, procs, i >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                              i >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                              i >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                              i >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << gate1, gate2, choosing, procs, i >>

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, i >>

p1(self) == /\ pc[self] = "p1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "NCS",
                                                     pc        |->  "p2",
                                                     isEndless |->  isEndless[self] ] >>
                                                 \o stack[self]]
            /\ isEndless' = [isEndless EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ncs0"]
            /\ UNCHANGED << gate1, gate2, choosing, procs, i >>

p2(self) == /\ pc[self] = "p2"
            /\ choosing' = [choosing EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p3"]
            /\ UNCHANGED << gate1, gate2, stack, isEndless, procs, i >>

p3(self) == /\ pc[self] = "p3"
            /\ gate1' = self
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << gate2, choosing, stack, isEndless, procs, i >>

p4(self) == /\ pc[self] = "p4"
            /\ IF gate2 # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "p5"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p8"]
            /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, i >>

p5(self) == /\ pc[self] = "p5"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "p6"]
            /\ UNCHANGED << gate1, gate2, stack, isEndless, procs, i >>

p6(self) == /\ pc[self] = "p6"
            /\ (gate2 = 0)
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, i >>

p7(self) == /\ pc[self] = "p7"
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, i >>

p8(self) == /\ pc[self] = "p8"
            /\ gate2' = self
            /\ pc' = [pc EXCEPT ![self] = "p9"]
            /\ UNCHANGED << gate1, choosing, stack, isEndless, procs, i >>

p9(self) == /\ pc[self] = "p9"
            /\ IF gate1 # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "p10"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p15"]
            /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, i >>

p10(self) == /\ pc[self] = "p10"
             /\ choosing' = [choosing EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "p11a"]
             /\ UNCHANGED << gate1, gate2, stack, isEndless, procs, i >>

p11a(self) == /\ pc[self] = "p11a"
              /\ procs' = [procs EXCEPT ![self] = 1..N]
              /\ pc' = [pc EXCEPT ![self] = "p11b"]
              /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, i >>

p11b(self) == /\ pc[self] = "p11b"
              /\ IF procs[self] # {}
                    THEN /\ \E proc \in procs[self]:
                              i' = [i EXCEPT ![self] = proc]
                         /\ procs' = [procs EXCEPT ![self] = procs[self] \ {i'[self]}]
                         /\ pc' = [pc EXCEPT ![self] = "p11c"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "p12"]
                         /\ UNCHANGED << procs, i >>
              /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless >>

p11c(self) == /\ pc[self] = "p11c"
              /\ (choosing[i[self]] = FALSE)
              /\ pc' = [pc EXCEPT ![self] = "p11b"]
              /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                              i >>

p12(self) == /\ pc[self] = "p12"
             /\ IF gate2 # self
                   THEN /\ pc' = [pc EXCEPT ![self] = "p13"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "p15"]
             /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                             i >>

p13(self) == /\ pc[self] = "p13"
             /\ (gate2 = 0)
             /\ pc' = [pc EXCEPT ![self] = "p14"]
             /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                             i >>

p14(self) == /\ pc[self] = "p14"
             /\ pc' = [pc EXCEPT ![self] = "p2"]
             /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                             i >>

p15(self) == /\ pc[self] = "p15"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "p16"]
             /\ UNCHANGED << gate1, gate2, choosing, stack, isEndless, procs, 
                             i >>

p16(self) == /\ pc[self] = "p16"
             /\ gate2' = 0
             /\ pc' = [pc EXCEPT ![self] = "p17"]
             /\ UNCHANGED << gate1, choosing, stack, isEndless, procs, i >>

p17(self) == /\ pc[self] = "p17"
             /\ choosing' = [choosing EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "p0"]
             /\ UNCHANGED << gate1, gate2, stack, isEndless, procs, i >>

P(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3(self) \/ p4(self)
              \/ p5(self) \/ p6(self) \/ p7(self) \/ p8(self) \/ p9(self)
              \/ p10(self) \/ p11a(self) \/ p11b(self) \/ p11c(self)
              \/ p12(self) \/ p13(self) \/ p14(self) \/ p15(self)
              \/ p16(self) \/ p17(self)

Next == (\E self \in ProcSet: NCS(self))
           \/ (\E self \in 1..N: P(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(P(self)) /\ WF_vars(NCS(self))

\* END TRANSLATION

\*** Mutual exclusion
\* For mutual exclusion, two processes must never be in the critical section
\* at the same time.
MutualExclusion == [] \A proc1, proc2 \in 1..N : (proc1 # proc2) => ~ (pc[proc1] = "p15" /\ pc[proc2] = "p15")

\*** No deadlocks
\* If all processes want to enter the critical section, eventually
\* one of these processes will enter the critical section.
NoDeadlock == (\A proc1 \in 1..N : pc[proc1] = "p2") ~> (\E proc2 \in 1..N : pc[proc2] = "p15")

\*** No starvation
\* If one process wants to enter the critical section, this process will 
\* eventually enter the critical section.
NoStarvation == \A proc \in 1..N : (pc[proc] = "p2") ~> (pc[proc] = "p15")

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

=============================================================================
