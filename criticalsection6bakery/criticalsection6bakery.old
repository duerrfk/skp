---------------------- MODULE criticalsection6bakery ------------------------

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
(* PlusCal implementation of Algorithm 5.3 from M. Ben-Ari: Principles of   *)
(* Concurrent and Distributed Programming. Second Edition, page 60, 2006.   *)
(*                                                                          *)
(* Lamports's Bakery algorithm.                                             *)
(* This algorithms guarantees mutual exclusion, and it is deadlock and      *) 
(* starvation free.                                                         *)
(*                                                                          *)
(* However, it is hard to check since it contains an infinite number of     *)
(* states since token numbers can grow ad infinitum. If we artificially     *)
(* limit the grows of tokens numbers, the algorithm is not starvation free  *)
(* anymore as demonstrated through model checking                           *)
(*                                                                          *)
(* In the implementation, we only assume atomic access to basic variables   *)
(* like a single integer or boolean.                                        *)
(****************************************************************************)

EXTENDS Integers, Sequences

\* N denotes the number of processes. N is defined in the configuration file.
CONSTANT N, 

\* Artificial limit to the token number.
\* Without this limit, token numbers might grow infinitely,
\* which makes it impossible to model-check the algorithm due to
\* an infinite number of different states. However, this change 
\* will make the algorithm non starvation-free (as can be shown
\* through model checking). 
MaxTokenNumber

(*

--algorithm criticalsection6bakery
{
    \* Global variables.
    \* Variables named ...ret are return values of procedures.
    variables choosing = [x \in 1..N |-> FALSE]; number = [x \in 1..N |-> 0];
        lesslessret = [x \in 1..N |-> FALSE]; maxret = [x \in 1..N |-> 0];

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

    \* Total order relation taking into account token numbers and process ids.
    \* Intentionally, only the access to a single entry in the number array is 
    \* assumed to be atomic. Multiple accesses are not atomic. 
    procedure lessless(i__, j__) 
        variables numberi__, numberj__
    {
        ll1: numberi__ := number[i__];
	ll2: numberj__ := number[j__];
        ll3: if (numberi__ < numberj__) {
                 \* number[i] < number[j]
                 lesslessret[i__] := TRUE;
                 return;
             };
        ll4: if (numberi__ = numberj__ /\ i__ < j__) {
	         \* number[i] = number[j] and i < j
                 lesslessret[i__] := TRUE;
                 return;
             };
        \* number[i] > number[j] or (number[i] = number[j] and i >= j)
        ll5: lesslessret[i__] := FALSE; 
             return;
    }

    \* Returns the maximum token number from the global number array.
    \* Intentionally, only the access to a single entry in the number array is
    \* assumed to be atomic. Multiple accesses are not atomic.
    procedure max() 
        variables m = -1; k = 1; temp;
    {
        max1: while (k <= N) {
            max2: temp := number[k];
            max3: if (temp > m) {
                      m := temp;
                  };
       	          k := k+1;     
        };
        max4: maxret[self] := m;
              return;  
    }

   \* Implentation of the following wait statement:
   \* await (number[j] = 0) \/ (number[i] << number[j])
   \* Intentionally, multiple accesses to the number array are not assumed to
   \* be atomic. 
   procedure wait(i_, j_) 
       variables numberi_; numberj_;
   {
       wait1: while (TRUE) {
                  wait2: numberi_ := number[i_];
                  wait3: numberj_ := number[j_];
                         call lessless(i_,j_);
                  wait4: if (numberi_ = 0 \/ lesslessret[i_]) {
                             return;
                         };
              };
   }

    \* Processes 1 to N
    process(Proc \in 1..N) 
        variables i = self; j; otherprocesses;
    {
        p0: while (TRUE) {
                p1: call NCS(); \* non-critical section
                p2: choosing[i] := TRUE;
                \* Note that max() is non-atomic! 
                p3a: call max();                 
                \* The following statement cannot be found in the original 
                \* Bakery algorithm. It artificially limits the maximum 
                \* token number. Without this statement, token numbers 
                \* might grow infinitely, which makes it impossible to 
                \* model-check the algorithm due to an infinite number of 
                \* different states. However, this change will make the 
                \* algorithm non-starvation-free (as can be shown through 
                \* model checking).
                p3b: if (maxret[self] = MaxTokenNumber) {
                    maxret[self] := MaxTokenNumber-1;
                };
                p3c: number[i] := 1 + maxret[self];
                p4: choosing[self] := FALSE;
                    otherprocesses := 1..N \ {i};
                p5: while (otherprocesses # {}) {
                       \* Choose another random process as j 
                        with (proc \in otherprocesses) {
                            j := proc;
                        };
                        otherprocesses := otherprocesses \ {j};
                        p6: await choosing[j] = FALSE;
                        \* procedure wait() implements the following await 
                        \* statement:
                        \* await (number[j] = 0) \/ (number[i] << number[j]) 
                        p7: call wait(i,j);
                    };
                p8: skip; \* critical section
                p9: number[i] := 0; 
            };
    }

}

*)

\*** The PlusCal translator will insert the TLA code into the following block
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES choosing, number, lesslessret, maxret, pc, stack, isEndless, i__, 
          j__, numberi__, numberj__, m, k, temp, i_, j_, numberi_, numberj_, 
          i, j, otherprocesses

vars == << choosing, number, lesslessret, maxret, pc, stack, isEndless, i__, 
           j__, numberi__, numberj__, m, k, temp, i_, j_, numberi_, numberj_, 
           i, j, otherprocesses >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ choosing = [x \in 1..N |-> FALSE]
        /\ number = [x \in 1..N |-> 0]
        /\ lesslessret = [x \in 1..N |-> FALSE]
        /\ maxret = [x \in 1..N |-> 0]
        (* Procedure NCS *)
        /\ isEndless = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure lessless *)
        /\ i__ = [ self \in ProcSet |-> defaultInitValue]
        /\ j__ = [ self \in ProcSet |-> defaultInitValue]
        /\ numberi__ = [ self \in ProcSet |-> defaultInitValue]
        /\ numberj__ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure max *)
        /\ m = [ self \in ProcSet |-> -1]
        /\ k = [ self \in ProcSet |-> 1]
        /\ temp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure wait *)
        /\ i_ = [ self \in ProcSet |-> defaultInitValue]
        /\ j_ = [ self \in ProcSet |-> defaultInitValue]
        /\ numberi_ = [ self \in ProcSet |-> defaultInitValue]
        /\ numberj_ = [ self \in ProcSet |-> defaultInitValue]
        (* Process Proc *)
        /\ i = [self \in 1..N |-> self]
        /\ j = [self \in 1..N |-> defaultInitValue]
        /\ otherprocesses = [self \in 1..N |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "p0"]

ncs0(self) == /\ pc[self] = "ncs0"
              /\ \E x \in {0,1}:
                   isEndless' = [isEndless EXCEPT ![self] = x]
              /\ pc' = [pc EXCEPT ![self] = "ncs1"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              i__, j__, numberi__, numberj__, m, k, temp, i_, 
                              j_, numberi_, numberj_, i, j, otherprocesses >>

ncs1(self) == /\ pc[self] = "ncs1"
              /\ IF isEndless[self] = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "ncs2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "ncs4"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i__, j__, numberi__, numberj__, m, k, 
                              temp, i_, j_, numberi_, numberj_, i, j, 
                              otherprocesses >>

ncs2(self) == /\ pc[self] = "ncs2"
              /\ pc' = [pc EXCEPT ![self] = "ncs3"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i__, j__, numberi__, numberj__, m, k, 
                              temp, i_, j_, numberi_, numberj_, i, j, 
                              otherprocesses >>

ncs3(self) == /\ pc[self] = "ncs3"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![self] = "ncs2"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i__, j__, numberi__, numberj__, m, k, 
                              temp, i_, j_, numberi_, numberj_, i, j, 
                              otherprocesses >>

ncs4(self) == /\ pc[self] = "ncs4"
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ isEndless' = [isEndless EXCEPT ![self] = Head(stack[self]).isEndless]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, i__, j__, 
                              numberi__, numberj__, m, k, temp, i_, j_, 
                              numberi_, numberj_, i, j, otherprocesses >>

NCS(self) == ncs0(self) \/ ncs1(self) \/ ncs2(self) \/ ncs3(self)
                \/ ncs4(self)

ll1(self) == /\ pc[self] = "ll1"
             /\ numberi__' = [numberi__ EXCEPT ![self] = number[i__[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ll2"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                             isEndless, i__, j__, numberj__, m, k, temp, i_, 
                             j_, numberi_, numberj_, i, j, otherprocesses >>

ll2(self) == /\ pc[self] = "ll2"
             /\ numberj__' = [numberj__ EXCEPT ![self] = number[j__[self]]]
             /\ pc' = [pc EXCEPT ![self] = "ll3"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                             isEndless, i__, j__, numberi__, m, k, temp, i_, 
                             j_, numberi_, numberj_, i, j, otherprocesses >>

ll3(self) == /\ pc[self] = "ll3"
             /\ IF numberi__[self] < numberj__[self]
                   THEN /\ lesslessret' = [lesslessret EXCEPT ![i__[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ numberi__' = [numberi__ EXCEPT ![self] = Head(stack[self]).numberi__]
                        /\ numberj__' = [numberj__ EXCEPT ![self] = Head(stack[self]).numberj__]
                        /\ i__' = [i__ EXCEPT ![self] = Head(stack[self]).i__]
                        /\ j__' = [j__ EXCEPT ![self] = Head(stack[self]).j__]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ll4"]
                        /\ UNCHANGED << lesslessret, stack, i__, j__, 
                                        numberi__, numberj__ >>
             /\ UNCHANGED << choosing, number, maxret, isEndless, m, k, temp, 
                             i_, j_, numberi_, numberj_, i, j, otherprocesses >>

ll4(self) == /\ pc[self] = "ll4"
             /\ IF numberi__[self] = numberj__[self] /\ i__[self] < j__[self]
                   THEN /\ lesslessret' = [lesslessret EXCEPT ![i__[self]] = TRUE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ numberi__' = [numberi__ EXCEPT ![self] = Head(stack[self]).numberi__]
                        /\ numberj__' = [numberj__ EXCEPT ![self] = Head(stack[self]).numberj__]
                        /\ i__' = [i__ EXCEPT ![self] = Head(stack[self]).i__]
                        /\ j__' = [j__ EXCEPT ![self] = Head(stack[self]).j__]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "ll5"]
                        /\ UNCHANGED << lesslessret, stack, i__, j__, 
                                        numberi__, numberj__ >>
             /\ UNCHANGED << choosing, number, maxret, isEndless, m, k, temp, 
                             i_, j_, numberi_, numberj_, i, j, otherprocesses >>

ll5(self) == /\ pc[self] = "ll5"
             /\ lesslessret' = [lesslessret EXCEPT ![i__[self]] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ numberi__' = [numberi__ EXCEPT ![self] = Head(stack[self]).numberi__]
             /\ numberj__' = [numberj__ EXCEPT ![self] = Head(stack[self]).numberj__]
             /\ i__' = [i__ EXCEPT ![self] = Head(stack[self]).i__]
             /\ j__' = [j__ EXCEPT ![self] = Head(stack[self]).j__]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << choosing, number, maxret, isEndless, m, k, temp, 
                             i_, j_, numberi_, numberj_, i, j, otherprocesses >>

lessless(self) == ll1(self) \/ ll2(self) \/ ll3(self) \/ ll4(self)
                     \/ ll5(self)

max1(self) == /\ pc[self] = "max1"
              /\ IF k[self] <= N
                    THEN /\ pc' = [pc EXCEPT ![self] = "max2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "max4"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i__, j__, numberi__, numberj__, m, k, 
                              temp, i_, j_, numberi_, numberj_, i, j, 
                              otherprocesses >>

max2(self) == /\ pc[self] = "max2"
              /\ temp' = [temp EXCEPT ![self] = number[k[self]]]
              /\ pc' = [pc EXCEPT ![self] = "max3"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i__, j__, numberi__, numberj__, m, k, 
                              i_, j_, numberi_, numberj_, i, j, otherprocesses >>

max3(self) == /\ pc[self] = "max3"
              /\ IF temp[self] > m[self]
                    THEN /\ m' = [m EXCEPT ![self] = temp[self]]
                    ELSE /\ TRUE
                         /\ m' = m
              /\ k' = [k EXCEPT ![self] = k[self]+1]
              /\ pc' = [pc EXCEPT ![self] = "max1"]
              /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                              isEndless, i__, j__, numberi__, numberj__, temp, 
                              i_, j_, numberi_, numberj_, i, j, otherprocesses >>

max4(self) == /\ pc[self] = "max4"
              /\ maxret' = [maxret EXCEPT ![self] = m[self]]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ m' = [m EXCEPT ![self] = Head(stack[self]).m]
              /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
              /\ temp' = [temp EXCEPT ![self] = Head(stack[self]).temp]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << choosing, number, lesslessret, isEndless, i__, 
                              j__, numberi__, numberj__, i_, j_, numberi_, 
                              numberj_, i, j, otherprocesses >>

max(self) == max1(self) \/ max2(self) \/ max3(self) \/ max4(self)

wait1(self) == /\ pc[self] = "wait1"
               /\ pc' = [pc EXCEPT ![self] = "wait2"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                               isEndless, i__, j__, numberi__, numberj__, m, k, 
                               temp, i_, j_, numberi_, numberj_, i, j, 
                               otherprocesses >>

wait2(self) == /\ pc[self] = "wait2"
               /\ numberi_' = [numberi_ EXCEPT ![self] = number[i_[self]]]
               /\ pc' = [pc EXCEPT ![self] = "wait3"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                               isEndless, i__, j__, numberi__, numberj__, m, k, 
                               temp, i_, j_, numberj_, i, j, otherprocesses >>

wait3(self) == /\ pc[self] = "wait3"
               /\ numberj_' = [numberj_ EXCEPT ![self] = number[j_[self]]]
               /\ /\ i__' = [i__ EXCEPT ![self] = i_[self]]
                  /\ j__' = [j__ EXCEPT ![self] = j_[self]]
                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "lessless",
                                                           pc        |->  "wait4",
                                                           numberi__ |->  numberi__[self],
                                                           numberj__ |->  numberj__[self],
                                                           i__       |->  i__[self],
                                                           j__       |->  j__[self] ] >>
                                                       \o stack[self]]
               /\ numberi__' = [numberi__ EXCEPT ![self] = defaultInitValue]
               /\ numberj__' = [numberj__ EXCEPT ![self] = defaultInitValue]
               /\ pc' = [pc EXCEPT ![self] = "ll1"]
               /\ UNCHANGED << choosing, number, lesslessret, maxret, 
                               isEndless, m, k, temp, i_, j_, numberi_, i, j, 
                               otherprocesses >>

wait4(self) == /\ pc[self] = "wait4"
               /\ IF numberi_[self] = 0 \/ lesslessret[i_[self]]
                     THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ numberi_' = [numberi_ EXCEPT ![self] = Head(stack[self]).numberi_]
                          /\ numberj_' = [numberj_ EXCEPT ![self] = Head(stack[self]).numberj_]
                          /\ i_' = [i_ EXCEPT ![self] = Head(stack[self]).i_]
                          /\ j_' = [j_ EXCEPT ![self] = Head(stack[self]).j_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "wait1"]
                          /\ UNCHANGED << stack, i_, j_, numberi_, numberj_ >>
               /\ UNCHANGED << choosing, number, lesslessret, maxret, 
                               isEndless, i__, j__, numberi__, numberj__, m, k, 
                               temp, i, j, otherprocesses >>

wait(self) == wait1(self) \/ wait2(self) \/ wait3(self) \/ wait4(self)

p0(self) == /\ pc[self] = "p0"
            /\ pc' = [pc EXCEPT ![self] = "p1"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i__, j__, numberi__, numberj__, m, k, 
                            temp, i_, j_, numberi_, numberj_, i, j, 
                            otherprocesses >>

p1(self) == /\ pc[self] = "p1"
            /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "NCS",
                                                     pc        |->  "p2",
                                                     isEndless |->  isEndless[self] ] >>
                                                 \o stack[self]]
            /\ isEndless' = [isEndless EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "ncs0"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, i__, j__, 
                            numberi__, numberj__, m, k, temp, i_, j_, numberi_, 
                            numberj_, i, j, otherprocesses >>

p2(self) == /\ pc[self] = "p2"
            /\ choosing' = [choosing EXCEPT ![i[self]] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "p3a"]
            /\ UNCHANGED << number, lesslessret, maxret, stack, isEndless, i__, 
                            j__, numberi__, numberj__, m, k, temp, i_, j_, 
                            numberi_, numberj_, i, j, otherprocesses >>

p3a(self) == /\ pc[self] = "p3a"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "max",
                                                      pc        |->  "p3b",
                                                      m         |->  m[self],
                                                      k         |->  k[self],
                                                      temp      |->  temp[self] ] >>
                                                  \o stack[self]]
             /\ m' = [m EXCEPT ![self] = -1]
             /\ k' = [k EXCEPT ![self] = 1]
             /\ temp' = [temp EXCEPT ![self] = defaultInitValue]
             /\ pc' = [pc EXCEPT ![self] = "max1"]
             /\ UNCHANGED << choosing, number, lesslessret, maxret, isEndless, 
                             i__, j__, numberi__, numberj__, i_, j_, numberi_, 
                             numberj_, i, j, otherprocesses >>

p3b(self) == /\ pc[self] = "p3b"
             /\ IF maxret[self] = MaxTokenNumber
                   THEN /\ maxret' = [maxret EXCEPT ![self] = MaxTokenNumber-1]
                   ELSE /\ TRUE
                        /\ UNCHANGED maxret
             /\ pc' = [pc EXCEPT ![self] = "p3c"]
             /\ UNCHANGED << choosing, number, lesslessret, stack, isEndless, 
                             i__, j__, numberi__, numberj__, m, k, temp, i_, 
                             j_, numberi_, numberj_, i, j, otherprocesses >>

p3c(self) == /\ pc[self] = "p3c"
             /\ number' = [number EXCEPT ![i[self]] = 1 + maxret[self]]
             /\ pc' = [pc EXCEPT ![self] = "p4"]
             /\ UNCHANGED << choosing, lesslessret, maxret, stack, isEndless, 
                             i__, j__, numberi__, numberj__, m, k, temp, i_, 
                             j_, numberi_, numberj_, i, j, otherprocesses >>

p4(self) == /\ pc[self] = "p4"
            /\ choosing' = [choosing EXCEPT ![self] = FALSE]
            /\ otherprocesses' = [otherprocesses EXCEPT ![self] = 1..N \ {i[self]}]
            /\ pc' = [pc EXCEPT ![self] = "p5"]
            /\ UNCHANGED << number, lesslessret, maxret, stack, isEndless, i__, 
                            j__, numberi__, numberj__, m, k, temp, i_, j_, 
                            numberi_, numberj_, i, j >>

p5(self) == /\ pc[self] = "p5"
            /\ IF otherprocesses[self] # {}
                  THEN /\ \E proc \in otherprocesses[self]:
                            j' = [j EXCEPT ![self] = proc]
                       /\ otherprocesses' = [otherprocesses EXCEPT ![self] = otherprocesses[self] \ {j'[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "p6"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "p8"]
                       /\ UNCHANGED << j, otherprocesses >>
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i__, j__, numberi__, numberj__, m, k, 
                            temp, i_, j_, numberi_, numberj_, i >>

p6(self) == /\ pc[self] = "p6"
            /\ choosing[j[self]] = FALSE
            /\ pc' = [pc EXCEPT ![self] = "p7"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i__, j__, numberi__, numberj__, m, k, 
                            temp, i_, j_, numberi_, numberj_, i, j, 
                            otherprocesses >>

p7(self) == /\ pc[self] = "p7"
            /\ /\ i_' = [i_ EXCEPT ![self] = i[self]]
               /\ j_' = [j_ EXCEPT ![self] = j[self]]
               /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "wait",
                                                        pc        |->  "p5",
                                                        numberi_  |->  numberi_[self],
                                                        numberj_  |->  numberj_[self],
                                                        i_        |->  i_[self],
                                                        j_        |->  j_[self] ] >>
                                                    \o stack[self]]
            /\ numberi_' = [numberi_ EXCEPT ![self] = defaultInitValue]
            /\ numberj_' = [numberj_ EXCEPT ![self] = defaultInitValue]
            /\ pc' = [pc EXCEPT ![self] = "wait1"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, isEndless, 
                            i__, j__, numberi__, numberj__, m, k, temp, i, j, 
                            otherprocesses >>

p8(self) == /\ pc[self] = "p8"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "p9"]
            /\ UNCHANGED << choosing, number, lesslessret, maxret, stack, 
                            isEndless, i__, j__, numberi__, numberj__, m, k, 
                            temp, i_, j_, numberi_, numberj_, i, j, 
                            otherprocesses >>

p9(self) == /\ pc[self] = "p9"
            /\ number' = [number EXCEPT ![i[self]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "p0"]
            /\ UNCHANGED << choosing, lesslessret, maxret, stack, isEndless, 
                            i__, j__, numberi__, numberj__, m, k, temp, i_, j_, 
                            numberi_, numberj_, i, j, otherprocesses >>

Proc(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3a(self) \/ p3b(self)
                 \/ p3c(self) \/ p4(self) \/ p5(self) \/ p6(self)
                 \/ p7(self) \/ p8(self) \/ p9(self)

Next == (\E self \in ProcSet:  \/ NCS(self) \/ lessless(self) \/ max(self)
                               \/ wait(self))
           \/ (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : /\ WF_vars(Proc(self))
                              /\ WF_vars(NCS(self))
                              /\ WF_vars(max(self))
                              /\ WF_vars(wait(self))
                              /\ WF_vars(lessless(self))

\* END TRANSLATION

\*** Mutual exclusion
\* For mutual exclusion, process 1 and process 2 must never be in the 
\* critical section at the same time.
MutualExclusion == [] \A proc1, proc2 \in 1..N : (proc1 # proc2) => ~ (pc[proc1] = "p8" /\ pc[proc2] = "p8")

\*** No deadlock
\* If all processes want to enter the critical section, eventually
\* one of these processes will enter the critical section.
NoDeadlock == (\A proc1 \in 1..N : pc[proc1] = "p2") ~> (\E proc2 \in 1..N : pc[proc2] = "p8")

\*** No starvation
\* If one process wants to enter the critical section, this process will 
\* eventually enter the critical section.
NoStarvation == \A proc \in 1..N : (pc[proc] = "p2") ~> (pc[proc] = "p8") 

\* Assume weakly fair scheduling of all commands
(* PlusCal options (wf) *)

=============================================================================
