---------------------- MODULE criticalsection5dekker ------------------------

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
(* PlusCal implementation of Algorithm 3.10 from M. Ben-Ari: Principles of  *)
(* Concurrent and Distributed Programming. Second Edition, page 60, 2006.   *)
(*                                                                          *)
(* Dekker's algorithm for mutual exclusion.                                 *)
(* This algorithms guarantees mutual exclusion and it is deadlock and       *) 
(* starvation free.                                                         *)
(****************************************************************************)

EXTENDS Integers, Sequences

(*

--algorithm criticalsection5dekker
{
    \* Global variables
    variables turn = 1; wantp = FALSE; wantq = FALSE; 

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
                p2: wantp := TRUE; 
                p3: while (wantq = TRUE) {
                        p4: if (turn = 2) {
                                p5: wantp := FALSE;
                                p6: await turn = 1;
                                p7: wantp := TRUE;
                            };
                    };
	        p8: skip; \* critical section
	        p9: turn := 2; 
                p10: wantp := FALSE;
            } 
    }

    \* First process (name P, pid 1)
    process(Q = 2) {
        q0: while (TRUE) {
                q1: call NCS(); \* non-critical section
                q2: wantq := TRUE; 
                q3: while (wantp = TRUE) {
                        q4: if (turn = 1) {
                                q5: wantq := FALSE;
                                q6: await turn = 2;
                                q7: wantq := TRUE;
                            };
                    };
	        q8: skip; \* critical section
	        q9: turn := 1; 
                q10: wantq := FALSE;
            } 
    }

}

*)

\*** The PlusCal translator will insert the TLA code into the following block
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES turn, wantp, wantq, pc, stack, isEndless

vars == << turn, wantp, wantq, pc, stack, isEndless >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ turn = 1
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
              /\ UNCHANGED << turn, wantp, wantq, stack >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << turn, wantp, wantq >>

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

p0 == /\ pc[1] = "p0"
      /\ pc' = [pc EXCEPT ![1] = "p1"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

p1 == /\ pc[1] = "p1"
      /\ stack' = [stack EXCEPT ![1] = << [ procedure |->  "NCS",
                                            pc        |->  "p2",
                                            isEndless |->  isEndless[1] ] >>
                                        \o stack[1]]
      /\ isEndless' = [isEndless EXCEPT ![1] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![1] = "ncs0"]
      /\ UNCHANGED << turn, wantp, wantq >>

p2 == /\ pc[1] = "p2"
      /\ wantp' = TRUE
      /\ pc' = [pc EXCEPT ![1] = "p3"]
      /\ UNCHANGED << turn, wantq, stack, isEndless >>

p3 == /\ pc[1] = "p3"
      /\ IF wantq = TRUE
            THEN /\ pc' = [pc EXCEPT ![1] = "p4"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "p8"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

p4 == /\ pc[1] = "p4"
      /\ IF turn = 2
            THEN /\ pc' = [pc EXCEPT ![1] = "p5"]
            ELSE /\ pc' = [pc EXCEPT ![1] = "p3"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

p5 == /\ pc[1] = "p5"
      /\ wantp' = FALSE
      /\ pc' = [pc EXCEPT ![1] = "p6"]
      /\ UNCHANGED << turn, wantq, stack, isEndless >>

p6 == /\ pc[1] = "p6"
      /\ turn = 1
      /\ pc' = [pc EXCEPT ![1] = "p7"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

p7 == /\ pc[1] = "p7"
      /\ wantp' = TRUE
      /\ pc' = [pc EXCEPT ![1] = "p3"]
      /\ UNCHANGED << turn, wantq, stack, isEndless >>

p8 == /\ pc[1] = "p8"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "p9"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

p9 == /\ pc[1] = "p9"
      /\ turn' = 2
      /\ pc' = [pc EXCEPT ![1] = "p10"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

p10 == /\ pc[1] = "p10"
       /\ wantp' = FALSE
       /\ pc' = [pc EXCEPT ![1] = "p0"]
       /\ UNCHANGED << turn, wantq, stack, isEndless >>

P == p0 \/ p1 \/ p2 \/ p3 \/ p4 \/ p5 \/ p6 \/ p7 \/ p8 \/ p9 \/ p10

q0 == /\ pc[2] = "q0"
      /\ pc' = [pc EXCEPT ![2] = "q1"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

q1 == /\ pc[2] = "q1"
      /\ stack' = [stack EXCEPT ![2] = << [ procedure |->  "NCS",
                                            pc        |->  "q2",
                                            isEndless |->  isEndless[2] ] >>
                                        \o stack[2]]
      /\ isEndless' = [isEndless EXCEPT ![2] = defaultInitValue]
      /\ pc' = [pc EXCEPT ![2] = "ncs0"]
      /\ UNCHANGED << turn, wantp, wantq >>

q2 == /\ pc[2] = "q2"
      /\ wantq' = TRUE
      /\ pc' = [pc EXCEPT ![2] = "q3"]
      /\ UNCHANGED << turn, wantp, stack, isEndless >>

q3 == /\ pc[2] = "q3"
      /\ IF wantp = TRUE
            THEN /\ pc' = [pc EXCEPT ![2] = "q4"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "q8"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

q4 == /\ pc[2] = "q4"
      /\ IF turn = 1
            THEN /\ pc' = [pc EXCEPT ![2] = "q5"]
            ELSE /\ pc' = [pc EXCEPT ![2] = "q3"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

q5 == /\ pc[2] = "q5"
      /\ wantq' = FALSE
      /\ pc' = [pc EXCEPT ![2] = "q6"]
      /\ UNCHANGED << turn, wantp, stack, isEndless >>

q6 == /\ pc[2] = "q6"
      /\ turn = 2
      /\ pc' = [pc EXCEPT ![2] = "q7"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

q7 == /\ pc[2] = "q7"
      /\ wantq' = TRUE
      /\ pc' = [pc EXCEPT ![2] = "q3"]
      /\ UNCHANGED << turn, wantp, stack, isEndless >>

q8 == /\ pc[2] = "q8"
      /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "q9"]
      /\ UNCHANGED << turn, wantp, wantq, stack, isEndless >>

q9 == /\ pc[2] = "q9"
      /\ turn' = 1
      /\ pc' = [pc EXCEPT ![2] = "q10"]
      /\ UNCHANGED << wantp, wantq, stack, isEndless >>

q10 == /\ pc[2] = "q10"
       /\ wantq' = FALSE
       /\ pc' = [pc EXCEPT ![2] = "q0"]
       /\ UNCHANGED << turn, wantp, stack, isEndless >>

Q == q0 \/ q1 \/ q2 \/ q3 \/ q4 \/ q5 \/ q6 \/ q7 \/ q8 \/ q9 \/ q10

Next == P \/ Q
           \/ (\E self \in ProcSet: NCS(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(P) /\ WF_vars(NCS(1))
        /\ WF_vars(Q) /\ WF_vars(NCS(2))

\* END TRANSLATION

\*** Mutual exclusion
\* For mutual exclusion, process 1 and process 2 must never be in the 
\* critical section at the same time.
MutualExclusion == [] ~ (pc[1] = "p8" /\ pc[2] = "q8")

\*** Deadlock free
\* If P and Q both want to enter the critical section, one of them will
\* eventually enter the critical section. 
NoDeadlock == /\ pc[1] = "p2"
              /\ pc[2] = "q2"
              ~>
              \/ pc[1] = "p8"
              \/ pc[2] = "q8"

\*** Starvation free
\* If P wants to enter the critical section, P will eventually enter
\* the critical section. The same must hold for Q.
NoStarvationP == (pc[1] = "p2") ~> (pc[1] = "p8") 
NoStarvationQ == (pc[2] = "q2") ~> (pc[2] = "q8") 
NoStarvation == /\ NoStarvationP
                /\ NoStarvationQ

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

=============================================================================
