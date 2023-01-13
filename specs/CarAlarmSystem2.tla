-------------------------- MODULE CarAlarmSystem2 --------------------------

(***************************************************************************)
(* Second refinement of the car alarm system:                              *)
(*                                                                         *)
(* In the second refinement we add the intermediate states between         *)
(* OpenAndUnlocked and ClosedAndLocked: OpenAndLocked & ClosedAndUnlocked. *)
(* Thus, open, close, lock and unlock are now 4 separate action. The base  *)
(* function is still the same, so the base refinement is still valid for   *)
(* this higher refinement. The problem is now less abstract and a bit more *)
(* detailed and concerns 4 of the states in the state diagram now.         *)
(*                                                                         *)
(* This refinement targets Requirements 1 - 3.                             *)
(***************************************************************************)

OpenAndUnlocked   == 0          \* Car is open and unlocked
ClosedAndLocked   == 1          \* Car is closed and locked
OpenAndLocked     == 2          \* Car is still open but already locked
ClosedAndUnlocked == 3          \* Car is not yet closed but already locked

STATES ==                       \* Currently possible states
    {
        OpenAndUnlocked,
        ClosedAndLocked,
        OpenAndLocked,
        ClosedAndUnlocked
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

Close == /\ \/ /\ state  = OpenAndUnlocked          \* close the car
               /\ state' = ClosedAndUnlocked
            \/ /\ state  = OpenAndLocked
               /\ state' = ClosedAndLocked

Lock == /\ \/ /\ state  = OpenAndUnlocked           \* lock the car
              /\ state' = OpenAndLocked
           \/ /\ state  = ClosedAndUnlocked
              /\ state' = ClosedAndLocked

Open == /\ \/ /\ state  = ClosedAndUnlocked         \* open the car
              /\ state' = OpenAndUnlocked
           \/ /\ state  = ClosedAndLocked
              /\ state' = OpenAndLocked
           
Unlock == /\ \/ /\ state  = ClosedAndLocked         \* unlock the car
                /\ state' = ClosedAndUnlocked
             \/ /\ state  = OpenAndLocked
                /\ state' = OpenAndUnlocked

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Close
        \/ Lock
        \/ Open
        \/ Unlock

Spec == Init /\ [][Next]_state

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem1 == INSTANCE CarAlarmSystem1

THEOREM Spec => /\ CarAlarmSystem1!Spec
                /\ []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Tue Jan 10 16:21:39 CET 2023 by mitch
\* Last modified Sat Dec 31 09:02:31 CET 2022 by marian
\* Created Sat Dec 31 09:02:11 CET 2022 by marian
