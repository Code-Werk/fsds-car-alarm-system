-------------------------- MODULE CarAlarmSystem4 --------------------------

(***************************************************************************)
(* Fourth refinement for the car alarm system                              *)
(***************************************************************************)

EXTENDS Naturals

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

VARIABLES state, isArmed, flash, sound

vars == <<state, isArmed, flash, sound>>


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 
SafetyInvariant == /\ IF state = Armed 
                      THEN isArmed = TRUE
                      ELSE isArmed = FALSE
                   /\ state = Alarm => flash = TRUE

Invariant == /\ TypeInvariant
             /\ SafetyInvariant 

CarAlarm == INSTANCE CarAlarm1 WITH flash <- flash, sound <- sound

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED<<isArmed, flash, sound>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED<<isArmed, flash, sound>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED<<flash, sound>>

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED<<isArmed, flash, sound>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED<<isArmed, flash, sound>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED<<isArmed, flash, sound>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED<<isArmed, flash, sound>>

Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ CarAlarm!Activate

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ UNCHANGED<<isArmed, flash, sound>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<isArmed, flash, sound>>
             
Unlock_After_Armed == /\ state  = Armed
                      /\ state' = ClosedAndUnlocked
                      /\ isArmed' = FALSE
                      /\ UNCHANGED<<flash, sound>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ state' = OpenAndUnlocked
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<isArmed, flash, sound>>

Arming == /\ state  = ClosedAndLocked
          /\ state' = Armed
          /\ isArmed' = TRUE
          /\ UNCHANGED<<flash, sound>>

SilentAlarm == /\ state = Alarm
               /\ state' = SilentAndOpen
               /\ CarAlarm!Deactivate
               /\ UNCHANGED<<isArmed>>

DeactivateSound == /\ CarAlarm!DeactivateSound
                   /\ UNCHANGED<<state, isArmed>>   

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Close_After_OpenAndUnlocked
        \/ Close_After_OpenAndLocked
        \/ Close_After_SilentAndOpen
        \/ Lock_After_OpenAndUnlocked
        \/ Lock_After_ClosedAndUnlocked
        \/ Open_After_ClosedAndUnlocked
        \/ Open_After_ClosedAndLocked
        \/ Open_After_Armed
        \/ Unlock_After_ClosedAndLocked
        \/ Unlock_After_OpenAndLocked
        \/ Unlock_After_Armed
        \/ Unlock_After_Alarm
        \/ Unlock_After_SilentAndOpen
        \/ Arming
        \/ SilentAlarm
        \/ DeactivateSound

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

CarAlarmSystem3 == INSTANCE CarAlarmSystem3

THEOREM Spec => /\ CarAlarmSystem3!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
