----------------------- MODULE criticalsection2 -----------------------------

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
(* PlusCal implementation of Algorithm 3.6 from M. Ben-Ari: Principles of   *)
(* Concurrent and Distributed Programming. Second Edition, page 56, 2006.   *)
(*                                                                          *)
(* This algorithm tries to implement mutual exclusion, but fails to do so.  *)
(* It is deadlock free. It is starvation free only under strongly fair      *)
(* scheduling but not for weakly fair scheduling.                           *)
(****************************************************************************)

EXTENDS Integers, Sequences

(*

--algorithm criticalsection2
{
    \* Global variables
    variables wantp = FALSE; wantq = FALSE; 

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

    \* First process (name P, pid 1)
    process(P = 1) {
        p0: while (TRUE) {
            p1: call NCS(); \* non-critical section
            p2: await wantq = FALSE;
            p3: wantp := TRUE; 
	    p4: skip; \* critical section
	    p5: wantp := FALSE;
        } 
    }

    \* Second process (name Q, pid 2)
    process(Q = 2) {
        q0: while (TRUE) {
            q1: call NCS(); \* non-critical section
            q2: await wantp = FALSE;
            q3: wantq := TRUE; 
	    q4: skip; \* critical section
	    q5: wantq := FALSE;
        } 
    }

}

*)

\*** The PlusCal translator will insert the TLA code into the following block
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES wantp, wantq, pc, stack, isEndless

vars == << wantp, wantq, pc, stack, isEndless >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ wantp = FALSE
        /\ wantq = FALSE
        (* Procedure NCS *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "p0"
                                        [] self = 2 -> "q0"]

ncs0(self) == /\ pc[self] = "ncs0"
              /\ \E x \in {0,1}:
                   isEndless' = [isEndless EXCEPT ![self] = x]
              /\ pc' = [pc EXCEPT ![self] = "ncs1"]
              /\ UNCHANGED << wantp, wantq, stack >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << wantp, wantq, stack, isEndless >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << wantp, wantq, stack, isEndless >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << wantp, wantq, stack, isEndless >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << wantp, wantq >>

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

p0 == /\ pc[1] = "p0"
      /\ pc' = [pc EXCEPT ![1] = "p1"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

p1 == /\ pc[1] = "p1"
      /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "NCS",
                                            pc        |->  "p2",
                                            isEndless |->  isEndless[1] ] >>
                                        \o stack[1]]
      /\ isEndless' = [isEndless EXCEPT ![1] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![1] = "ncs0"]
      /\ UNCHANGED << wantp, wantq >>

p2 == /\ pc[1] = "p2"
      /\ wantq = FALSE
      /\ pc' = [pc EXCEPT ![1] = "p3"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

p3 == /\ pc[1] = "p3"
      /\ wantp' = TRUE
      /\ pc' = [pc EXCEPT ![1] = "p4"]
      /\ UNCHANGED << wantq, stack, isEndless >>

p4 == /\ pc[1] = "p4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "p5"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

p5 == /\ pc[1] = "p5"
      /\ wantp' = FALSE
      /\ pc' = [pc EXCEPT ![1] = "p0"]
      /\ UNCHANGED << wantq, stack, isEndless >>

P == p0 \/ p1 \/ p2 \/ p3 \/ p4 \/ p5

q0 == /\ pc[2] = "q0"
      /\ pc' = [pc EXCEPT ![2] = "q1"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

q1 == /\ pc[2] = "q1"
      /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "NCS",
                                            pc        |->  "q2",
                                            isEndless |->  isEndless[2] ] >>
                                        \o stack[2]]
      /\ isEndless' = [isEndless EXCEPT ![2] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![2] = "ncs0"]
      /\ UNCHANGED << wantp, wantq >>

q2 == /\ pc[2] = "q2"
      /\ wantp = FALSE
      /\ pc' = [pc EXCEPT ![2] = "q3"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

q3 == /\ pc[2] = "q3"
      /\ wantq' = TRUE
      /\ pc' = [pc EXCEPT ![2] = "q4"]
      /\ UNCHANGED << wantp, stack, isEndless >>

q4 == /\ pc[2] = "q4"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "q5"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

q5 == /\ pc[2] = "q5"
      /\ wantq' = FALSE
      /\ pc' = [pc EXCEPT ![2] = "q0"]
      /\ UNCHANGED << wantp, stack, isEndless >>

Q == q0 \/ q1 \/ q2 \/ q3 \/ q4 \/ q5

Next == P \/ Q
           \/ (\E self \in ProcSet: NCS(self))

Spec == /\ Init /\ [][Next]_vars
        /\ SF_vars(P) /\ SF_vars(NCS(1))
        /\ SF_vars(Q) /\ SF_vars(NCS(2))

\* END TRANSLATION

\*** Mutual exclusion
\* For mutual exclusion, process 1 and process 2 must never be in the 
\* critical section at the same time.
MutualExclusion == [] ~ (pc[1] = "p4" /\ pc[2] = "q4")

\*** Deadlock free
\* If P and Q wait to enter the critical section, one of them will
\* eventually enter the critical section
NoDeadlock == /\ pc[1] = "p2"
              /\ pc[2] = "q2"
              ~>
              \/ pc[1] = "p4"
              \/ pc[2] = "q4"
 
\*** Starvation free
\* If P waits to enter the critical section, P will eventually enter
\* the critical section. The same must hold for Q.
NoStarvationP == (pc[1] = "p2") ~> (pc[1] = "p4") 
NoStarvationQ == (pc[2] = "q2") ~> (pc[2] = "q4") 
NoStarvation == /\ NoStarvationP
                /\ NoStarvationQ

\* Assume weakly fair scheduling of all commands
(* PlusCal options (sf) *)

=============================================================================
