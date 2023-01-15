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

VARIABLES state                 \* the current state in the state diagram

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == state \in STATES
                 
(***************************************************************************)
(* Actions                                                                 *)
(* 1. state diagram starts in the OpenAndUnlocked state                    *)
(* 2. close the car                                                        *)
(* 3. lock the car                                                         *)
(* 4. open the car                                                         *)
(* 5. unlock the car                                                       *)
(***************************************************************************)

Init == state = OpenAndUnlocked

Close == /\ \/ /\ state  = OpenAndUnlocked
               /\ state' = ClosedAndUnlocked
            \/ /\ state  = OpenAndLocked
               /\ state' = ClosedAndLocked

Lock == /\ \/ /\ state  = OpenAndUnlocked
              /\ state' = OpenAndLocked
           \/ /\ state  = ClosedAndUnlocked
              /\ state' = ClosedAndLocked

Open == /\ \/ /\ state  = ClosedAndUnlocked
              /\ state' = OpenAndUnlocked
           \/ /\ state  = ClosedAndLocked
              /\ state' = OpenAndLocked
           
Unlock == /\ \/ /\ state  = ClosedAndLocked
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