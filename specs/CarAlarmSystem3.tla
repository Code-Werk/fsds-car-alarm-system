-------------------------- MODULE CarAlarmSystem3 --------------------------

(***************************************************************************)
(* Third refinement of the car alarm system:                               *)
(*                                                                         *)
(* TODO *)
(***************************************************************************)

OpenAndUnlocked   == 0
ClosedAndLocked   == 1
OpenAndLocked     == 2
ClosedAndUnlocked == 3
Armed             == 4
Alarm             == 5
SilentAndOpen     == 6

STATES == 
    {
        OpenAndUnlocked, 
        ClosedAndLocked, 
        OpenAndLocked, 
        ClosedAndUnlocked, 
        Armed, 
        Alarm, 
        SilentAndOpen
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

Close == /\ \/ /\ state  = OpenAndUnlocked
               /\ state' = ClosedAndUnlocked
            \/ /\ state  = OpenAndLocked
               /\ state' = ClosedAndLocked
            \/ /\ state  = SilentAndOpen
               /\ state' = Armed

Lock == /\ \/ /\ state  = OpenAndUnlocked
              /\ state' = OpenAndLocked
           \/ /\ state  = ClosedAndUnlocked
              /\ state' = ClosedAndLocked

Open == /\ \/ /\ state  = ClosedAndUnlocked
              /\ state' = OpenAndUnlocked
           \/ /\ state  = ClosedAndLocked
              /\ state' = OpenAndLocked
           \/ /\ state  = Armed
              /\ state' = Alarm
           
Unlock == /\ \/ /\ state  = ClosedAndLocked
                /\ state' = ClosedAndUnlocked
             \/ /\ state  = OpenAndLocked
                /\ state' = OpenAndUnlocked
             \/ /\ state  = Armed
                /\ state' = ClosedAndUnlocked
             \/ /\ state  = Alarm
                /\ state' = OpenAndUnlocked
             \/ /\ state  = SilentAndOpen
                /\ state' = OpenAndUnlocked

Arming == /\ state  = ClosedAndLocked
          /\ state' = Armed

SilentAlarm == /\ state = Alarm
               /\ state' = SilentAndOpen

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Close 
        \/ Lock 
        \/ Open 
        \/ Unlock
        \/ Arming
        \/ SilentAlarm

Spec == Init /\ [][Next]_state

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem2 == INSTANCE CarAlarmSystem2

THEOREM Spec => /\ CarAlarmSystem2!Spec
                /\ []TypeInvariant

=============================================================================
\* Modification History
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
