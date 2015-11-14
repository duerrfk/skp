------------------- MODULE criticalsection8testset ---------------------------

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
(* Protecting critical sections with an atomic test & set primitive.        *)
(*                                                                          *)
(* This implementation guarantees mutual exclusion and freedom from         *)
(* deadlocks. However, processes might starve.                              *)
(****************************************************************************)

EXTENDS Integers, Sequences

\* N denotes the number of processes. N is defined in the configuration file.
CONSTANT N

(*

--algorithm criticalsection8testset
{
    \* Global variables
    variables common = 0; testsetret = [x \in 1..N |-> FALSE]; 

    \* Atomic test&set operation.
    \* Note that the test operation i = 0 and set operation i := 1 
    \* are performed atomically in one step since the whole macro is 
    \* expanded under one label.
    macro TestSet(i) {
        if (i = 0) {
            i := 1;
            testsetret[self] := TRUE;
        } else {
            testsetret[self] := FALSE;
        }
    }

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

    \* Processes 1 to N
    process(Proc \in 1..N) {
        p0: while (TRUE) {
                p1: call NCS(); \* non-critical section
                p2a: TestSet(common);
                p2b: while (testsetret[self] = FALSE) {
                         p2c: TestSet(common);
                     };
                p3: skip; \* critical section
                p4: common := 0;
            };
    }

}

*)

\*** The PlusCal translator will insert the TLA code into the following block
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES common, testsetret, pc, stack, isEndless

vars == << common, testsetret, pc, stack, isEndless >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ common = 0
        /\ testsetret = [x \in 1..N |-> FALSE]
        (* Procedure NCS *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p0"]

ncs0(self) == /\ pc[self] = "ncs0"
              /\ \E x \in {0,1}:
                   isEndless' = [isEndless EXCEPT ![self] = x]
              /\ pc' = [pc EXCEPT ![self] = "ncs1"]
              /\ UNCHANGED << common, testsetret, stack >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << common, testsetret, stack, isEndless >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << common, testsetret, stack, isEndless >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << common, testsetret, stack, isEndless >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << common, testsetret >>

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << common, testsetret, stack, isEndless >>

p1(self) == /\ pc[self] = "p1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "NCS",
                                                     pc        |->  "p2a",
                                                     isEndless |->  isEndless[self] ] >>
                                                 \o stack[self]]
            /\ isEndless' = [isEndless EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ncs0"]
            /\ UNCHANGED << common, testsetret >>

p2a(self) == /\ pc[self] = "p2a"
             /\ IF common = 0
                   THEN /\ common' = 1
                        /\ testsetret' = [testsetret EXCEPT ![self] = TRUE]
                   ELSE /\ testsetret' = [testsetret EXCEPT ![self] = FALSE]
                        /\ UNCHANGED common
             /\ pc' = [pc EXCEPT ![self] = "p2b"]
             /\ UNCHANGED << stack, isEndless >>

p2b(self) == /\ pc[self] = "p2b"
             /\ IF testsetret[self] = FALSE
                   THEN /\ pc' = [pc EXCEPT ![self] = "p2c"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "p3"]
             /\ UNCHANGED << common, testsetret, stack, isEndless >>

p2c(self) == /\ pc[self] = "p2c"
             /\ IF common = 0
                   THEN /\ common' = 1
                        /\ testsetret' = [testsetret EXCEPT ![self] = TRUE]
                   ELSE /\ testsetret' = [testsetret EXCEPT ![self] = FALSE]
                        /\ UNCHANGED common
             /\ pc' = [pc EXCEPT ![self] = "p2b"]
             /\ UNCHANGED << stack, isEndless >>

p3(self) == /\ pc[self] = "p3"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p4"]
            /\ UNCHANGED << common, testsetret, stack, isEndless >>

p4(self) == /\ pc[self] = "p4"
            /\ common' = 0
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << testsetret, stack, isEndless >>

Proc(self) == p0(self) \/ p1(self) \/ p2a(self) \/ p2b(self) \/ p2c(self)
                 \/ p3(self) \/ p4(self)

Next == (\E self \in ProcSet: NCS(self))
           \/ (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self)) /\ WF_vars(NCS(self))

\* END TRANSLATION


\*** Mutual exclusion
\* For mutual exclusion, process 1 and process 2 must never be in the 
\* critical section at the same time.
MutualExclusion == [] \A proc1, proc2 \in 1..N : (proc1 # proc2) => ~ (pc[proc1] = "p3" /\ pc[proc2] = "p3")

\*** No deadlock
\* If all processes want to enter the critical section, eventually
\* one of these processes will enter the critical section.
NoDeadlock == (\A proc1 \in 1..N : pc[proc1] = "p2a") ~> (\E proc2 \in 1..N : pc[proc2] = "p3")

\*** No starvation
\* If one process wants to enter the critical section, this process will 
\* eventually enter the critical section.
NoStarvation == \A proc \in 1..N : (pc[proc] = "p2a") ~> (pc[proc] = "p3") 

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

=============================================================================
