----------------------- MODULE criticalsection1 -----------------------------

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
(* PlusCal implementation of Algorithm 3.1 from M. Ben-Ari: Principles of   *)
(* Concurrent and Distributed Programming. Second Edition, page 48, 2006.   *)
(*                                                                          *)
(* A simple mutual exclusion algorithm for critical sections.               *)
(*                                                                          *) 
(* This algorithm implements mutual exclusion and is deadlock free          *)
(* but it is *not* starvation free.                                         *)
(****************************************************************************)

EXTENDS Integers, Sequences

(*

--algorithm criticalsection1
{
    \* Global variables
    variables turn = 1; 

    \* The non-critical section.
    \* For checking for freedom from starvation, it is important that
    \* a process might stay in the non-critical section forever (however,
    \* each process must leave the critical section). 
    \* This procedure covers both cases: finite and infinite execution 
    \* of the non-critical section. 
    procedure NCS()
        variable isEndless;
    {
	\* Non-deterministically, choose whether the procedure will
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

    \* First process (name P, pid 1)
    process(P = 1) {
        p0: while (TRUE) {
	    p1: call NCS(); \* non-critical section
	    p2: await turn = 1;
	    p3: skip; \* critical section
	    p4: turn := 2;
         } 
    }

    \* Second process (name Q, pid 2)
    process(Q = 2) {
        q0: while (TRUE) {
	    q1: call NCS(); \* non-critical section
	    q2: await turn = 2;
	    q3: skip; \* critical section
	    q4: turn := 1; 
        } 
    }

}

*)

\*** The PlusCal translator will insert the TLA code into the following block
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES turn, pc, stack, isEndless

vars == << turn, pc, stack, isEndless >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ turn = 1
        (* Procedure NCS *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "p0"
                                        [] self = 2 -> "q0"]

ncs0(self) == /\ pc[self] = "ncs0"
              /\ \E x \in {0,1}:
                   isEndless' = [isEndless EXCEPT ![self] = x]
              /\ pc' = [pc EXCEPT ![self] = "ncs1"]
              /\ UNCHANGED << turn, stack >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << turn, stack, isEndless >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << turn, stack, isEndless >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << turn, stack, isEndless >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ turn' = turn

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

p0 == /\ pc[1] = "p0"
      /\ pc' = [pc EXCEPT ![1] = "p1"]
      /\ UNCHANGED << turn, stack, isEndless >>

p1 == /\ pc[1] = "p1"
      /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "NCS",
                                            pc        |->  "p2",
                                            isEndless |->  isEndless[1] ] >>
                                        \o stack[1]]
      /\ isEndless' = [isEndless EXCEPT ![1] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![1] = "ncs0"]
      /\ turn' = turn

p2 == /\ pc[1] = "p2"
      /\ turn = 1
      /\ pc' = [pc EXCEPT ![1] = "p3"]
      /\ UNCHANGED << turn, stack, isEndless >>

p3 == /\ pc[1] = "p3"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "p4"]
      /\ UNCHANGED << turn, stack, isEndless >>

p4 == /\ pc[1] = "p4"
      /\ turn' = 2
      /\ pc' = [pc EXCEPT ![1] = "p0"]
      /\ UNCHANGED << stack, isEndless >>

P == p0 \/ p1 \/ p2 \/ p3 \/ p4

q0 == /\ pc[2] = "q0"
      /\ pc' = [pc EXCEPT ![2] = "q1"]
      /\ UNCHANGED << turn, stack, isEndless >>

q1 == /\ pc[2] = "q1"
      /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "NCS",
                                            pc        |->  "q2",
                                            isEndless |->  isEndless[2] ] >>
                                        \o stack[2]]
      /\ isEndless' = [isEndless EXCEPT ![2] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![2] = "ncs0"]
      /\ turn' = turn

q2 == /\ pc[2] = "q2"
      /\ turn = 2
      /\ pc' = [pc EXCEPT ![2] = "q3"]
      /\ UNCHANGED << turn, stack, isEndless >>

q3 == /\ pc[2] = "q3"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "q4"]
      /\ UNCHANGED << turn, stack, isEndless >>

q4 == /\ pc[2] = "q4"
      /\ turn' = 1
      /\ pc' = [pc EXCEPT ![2] = "q0"]
      /\ UNCHANGED << stack, isEndless >>

Q == q0 \/ q1 \/ q2 \/ q3 \/ q4

Next == P \/ Q
           \/ (\E self \in ProcSet: NCS(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(P) /\ WF_vars(NCS(1))
        /\ WF_vars(Q) /\ WF_vars(NCS(2))

\* END TRANSLATION

\*** Mutual exclusion
\* For mutual exclusion, process 1 and process 2 must never be in the 
\* critical section (lines p3 and q3) at the same time.
MutualExclusion == [] ~ (pc[1] = "p3" /\ pc[2] = "q3")

\*** Deadlock free
\* If P and Q wait to enter the critical section, one of them will
\* eventually enter the critical section
NoDeadlock == /\ pc[1] = "p2"
              /\ pc[2] = "q2"
              ~>
              \/ pc[1] = "p3"
              \/ pc[2] = "q3"
 
\*** Starvation free
\* If P waits to enter the critical section, P will eventually enter
\* the critical section. The same must hold for Q.
NoStarvationP == (pc[1] = "p2") ~> (pc[1] = "p3") 
NoStarvationQ == (pc[2] = "q2") ~> (pc[2] = "q3") 
NoStarvation == /\ NoStarvationP
                /\ NoStarvationQ

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

=============================================================================
