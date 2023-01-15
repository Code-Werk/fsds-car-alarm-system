-------------------------- MODULE CarAlarmSystem1 --------------------------

(***************************************************************************)
(* First and base refinement of the car alarm system:                      *)
(*                                                                         *)
(* In this initial step we simply check that the car alarm system can      *)
(* switch between the state diagram's OpenAndUnlocked state and the        *)
(* ClosedAndLocked state. That means close/unlock open/unlock are always   *)
(* handled as one single step and there are no states in between. The idea *)
(* here is to model the very base function of a car lock: lock and unlock. *)
(*                                                                         *)
(* This refinement targets Requirements 1 - 3.                             *)
(***************************************************************************)

OpenAndUnlocked == 0            \* Car is open and unlocked
ClosedAndLocked == 1            \* Car is closed and locked

STATES ==                       \* Currently possible states
    {
        OpenAndUnlocked,
        ClosedAndLocked
    }

VARIABLES state                \* the current state in the state diagram

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == state \in STATES

(***************************************************************************)
(* Actions                                                                 *)
(* 1. state diagram starts in the OpenAndUnlocked state                    *)
(* 2. close the car and lock it                                            *)
(* 3. open the car and unlock it                                           *)
(***************************************************************************)

Init == /\ state = OpenAndUnlocked                         

Lock_And_Close == /\ state = OpenAndUnlocked            
                  /\ state' = ClosedAndLocked

Unlock_And_Open == /\ state = ClosedAndLocked           
                   /\ state' = OpenAndUnlocked

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Lock_And_Close
        \/ Unlock_And_Open

Spec == Init /\ [][Next]_state

(***************************************************************************)
(* Verified Specification                                                  *)
(***************************************************************************)

THEOREM Spec => []TypeInvariant

=============================================================================