-------------------------- MODULE Doors1 --------------------------

(***************************************************************************)
(* First refinement of the doors system:                                   *)
(* Module that represents all doors of a car in the passenger area         *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT DoorCount
ASSUME DoorCount \in {2,4}

VARIABLES passengerDoors

vars == <<passengerDoors>>

(***************************************************************************)
(* Guards                                                                  *)
(***************************************************************************)

AreOpen == \E pd \in passengerDoors : pd[2] = TRUE
AreClosed == \A pd \in passengerDoors : pd[2] = FALSE

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ \A pd \in passengerDoors :
                    /\ pd[1] \in 0..DoorCount
                    /\ pd[2] \in BOOLEAN

SafetyInvariant == /\ AreClosed => \A pd \in passengerDoors: pd[2] = FALSE
                   /\ AreOpen => \E pd \in passengerDoors: pd[2] = TRUE

Invariant == /\ TypeInvariant /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ passengerDoors = { <<i, TRUE>> : i \in 1..DoorCount }

Open == /\ \E door \in {pd \in passengerDoors : pd[2] = FALSE}:
            passengerDoors' = {x \in passengerDoors : x[1] /= door[1]} \union {<<door[1], TRUE>>}

Close == /\ AreOpen
         /\ \E door \in {pd \in passengerDoors : pd[2] = TRUE}:
            passengerDoors' = {x \in passengerDoors : x[1] /= door[1]} \union {<<door[1], FALSE>>}

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Close \/ Open

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)
THEOREM Spec => []Invariant

=============================================================================
