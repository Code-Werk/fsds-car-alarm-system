-------------------------- MODULE Doors1 --------------------------

(***************************************************************************)
(* First refinement of the doors system:                              *)
(*                                                                         *)
(* TODO *)
(***************************************************************************)

EXTENDS Integers, Sequences, TLC

CONSTANT DoorCount
ASSUME DoorCount \in {2,4}

VARIABLES passengerDoors, isClosed

vars == <<passengerDoors, isClosed>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ \A pd \in passengerDoors :
                    /\ pd[1] \in 0..DoorCount
                    /\ pd[2] \in BOOLEAN

SafetyInvariant == /\ isClosed => \A pd \in passengerDoors: pd[2] = FALSE
                   /\ ~isClosed => \E pd \in passengerDoors: pd[2] = TRUE

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ passengerDoors = { <<i, TRUE>> : i \in 1..DoorCount }
        /\ isClosed = FALSE

Open == /\ \E door \in {pd \in passengerDoors : pd[2] = FALSE}:
            passengerDoors' = {x \in passengerDoors : x[1] /= door[1]} \union {<<door[1], TRUE>>}
        /\ isClosed'= FALSE

Close == /\ isClosed = FALSE
         /\ \E door \in {pd \in passengerDoors : pd[2] = TRUE}:
            passengerDoors' = {x \in passengerDoors : x[1] /= door[1]} \union {<<door[1], FALSE>>}
         /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
            THEN isClosed'=TRUE
            ELSE UNCHANGED<<isClosed>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Close
        \/ Open

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

THEOREM Spec => []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:48:38 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
