-------------------------- MODULE CarAlarmSystem2 --------------------------

(***************************************************************************)
(* Second refinement for the car alarm system                              *)
(***************************************************************************)

OpenAndUnlocked   == 0
ClosedAndLocked   == 1
OpenAndLocked     == 2
ClosedAndUnlocked == 3

STATES == {OpenAndUnlocked, ClosedAndLocked, OpenAndLocked, ClosedAndUnlocked}

VARIABLES state

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == state \in STATES
                 
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == state = OpenAndUnlocked

Close ==  /\ \/ /\ state  = OpenAndUnlocked
                /\ state' = ClosedAndUnlocked
             \/ /\ state  = OpenAndLocked
                /\ state' = ClosedAndLocked

Lock ==   /\ \/ /\ state  = OpenAndUnlocked
                /\ state' = OpenAndLocked
             \/ /\ state  = ClosedAndUnlocked
                /\ state' = ClosedAndLocked

Open ==   /\ \/ /\ state  = ClosedAndUnlocked
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
(* Verified Refinement                                                     *)
(***************************************************************************)

CarAlarmSystem1 == INSTANCE CarAlarmSystem1

THEOREM Spec => /\ CarAlarmSystem1!Spec
                /\ []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Tue Jan 10 16:21:39 CET 2023 by mitch
\* Last modified Sat Dec 31 09:02:31 CET 2022 by marian
\* Created Sat Dec 31 09:02:11 CET 2022 by marian
