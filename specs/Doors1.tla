-------------------------- MODULE Doors1 --------------------------

(***************************************************************************)
(* Module with a single refinement for a car's doors:                      *)
(*                                                                         *)
(* The module simply represents all doors of a car in the passenger area.  *)
(* It has actions to non-deterministically open and close doors and offers *)
(* guards to check if at least one door is open (=> car is open), or all   *)
(* doors are closed (=> car is closed).                                    *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT DoorCount                  \* Amount of the car's doors
ASSUME DoorCount \in {2,4}          \* DoorCount is set in the TLC
                                    \* has to either be 2 or 4 by requirement

VARIABLES passengerDoors            \* tuple representing the passenger doors
                                    \* consists of an index and a bool flag indicating
                                    \* if the door is open (flag is true), or closed (flag is false)

vars == <<passengerDoors>>

(***************************************************************************)
(* Guards                                                                  *)
(* Accessible outside to ease guard usage for the module if instantiated   *)
(***************************************************************************)

AreOpen == \E pd \in passengerDoors : pd[2] = TRUE          \* guard that is true if at least one door is open
AreClosed == \A pd \in passengerDoors : pd[2] = FALSE       \* guard that is true if all doors are closed

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ \A pd \in passengerDoors :
                    /\ pd[1] \in 0..DoorCount
                    /\ pd[2] \in BOOLEAN

\* car is either opened or closed, never both
SafetyInvariant == /\ \/ AreClosed
                      \/ AreOpen

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Initialize 2 or 4, depending on DoorCount, doors, that are open
Init == /\ passengerDoors = { <<i, TRUE>> : i \in 1..DoorCount }

\* Non-deterministically opens a closed door
Open == /\ \E door \in {pd \in passengerDoors : pd[2] = FALSE}:
            passengerDoors' =
                {x \in passengerDoors : x[1] /= door[1]}
                    \union {<<door[1], TRUE>>}

\* Non-deterministically closes an opened door
Close == /\ AreOpen
         /\ \E door \in {pd \in passengerDoors : pd[2] = TRUE}:
            passengerDoors' =
                {x \in passengerDoors : x[1] /= door[1]} 
                    \union {<<door[1], FALSE>>}

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
