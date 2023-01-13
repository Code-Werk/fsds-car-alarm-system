-------------------------- MODULE CarAlarmSystem1 --------------------------

(***************************************************************************)
(* First and base refinement of the car alarm system:                      *)
(*                                                                         *)
(* In this initial step we simply check that the car alarm system can      *)
(* switch between the state diagram's OpenAndUnlocked state and the        *)
(* ClosedAndLocked state. That means close/unlock open/unlock are always   *)
(* handled as one single step and there are no states in between. The idea *)
(* here is to model the very base function of a car lock: lock and unlock. *)
(***************************************************************************)

OpenAndUnlocked == 0
ClosedAndLocked == 1

STATES ==
    {
        OpenAndUnlocked,
        ClosedAndLocked
    }

VARIABLES state

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == state \in STATES

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == state = OpenAndUnlocked

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
\* Modification History
\* Last modified Tue Jan 10 16:01:15 CET 2023 by mitch
\* Last modified Sat Dec 31 09:01:42 CET 2022 by marian
\* Created Sat Dec 31 08:58:24 CET 2022 by marian
