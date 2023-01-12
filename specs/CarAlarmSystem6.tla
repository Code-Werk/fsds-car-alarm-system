-------------------------- MODULE CarAlarmSystem6 --------------------------

(***************************************************************************)
(* Sixth refinement for the car alarm system                                *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT ArmedDelay, AlarmDelay
ASSUME ArmedDelay \in Nat
ASSUME AlarmDelay \in Nat

ArmedRange == 0..ArmedDelay
AlarmRange == 0..AlarmDelay

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

VARIABLES state, isArmed, flash, sound, armedTimer, alarmTimer

vars == <<state, isArmed, flash, sound, armedTimer,alarmTimer>>
vars_without_state == <<isArmed, flash, sound, armedTimer,alarmTimer>>

CarAlarm == INSTANCE CarAlarm1 WITH flash <- flash, sound <- sound

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 
SafetyInvariant == /\ state = Alarm => flash = TRUE
                   /\ IF state = Alarm /\ alarmTimer > 269 
                        THEN sound = TRUE
                        ELSE sound = FALSE
                   /\ state = Armed => armedTimer = ArmedDelay /\ isArmed = TRUE
                   /\ state /= ClosedAndLocked => armedTimer = ArmedDelay
                   /\ state /= Alarm => alarmTimer = AlarmDelay

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED<<vars_without_state>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED<<vars_without_state>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED<<flash, sound, armedTimer, alarmTimer>>


Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED<<vars_without_state>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED<<vars_without_state>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED<<vars_without_state>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ armedTimer'= ArmedDelay
                              /\ UNCHANGED<<flash, sound, isArmed, alarmTimer>>

Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ CarAlarm!Activate
                    /\ UNCHANGED<<armedTimer, alarmTimer>>

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer'= ArmedDelay
                                /\ UNCHANGED<<flash, sound, isArmed, alarmTimer>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>
             
Unlock_After_Armed == /\ state  = Armed
                      /\ state' = ClosedAndUnlocked
                      /\ isArmed' = FALSE
                      /\ UNCHANGED<<flash, sound, armedTimer, alarmTimer>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ state' = OpenAndUnlocked
                      /\ alarmTimer' = AlarmDelay
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed, armedTimer>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ state' = Armed
          /\ isArmed' = TRUE
          /\ armedTimer'= ArmedDelay
          /\ UNCHANGED<<flash, sound, alarmTimer>>

SilentAlarm == /\ state = Alarm
               /\ state' = SilentAndOpen
               /\ alarmTimer' = AlarmDelay
               /\ CarAlarm!Deactivate
               /\ UNCHANGED<<isArmed, armedTimer>>

ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED<<state, isArmed, sound, flash, alarmTimer>>

AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE  UNCHANGED<<sound>>
               /\ UNCHANGED<<state, isArmed,flash, armedTimer>>

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
        \/ ArmingTicker
        \/ AlarmTicker

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

CarAlarmSystem5 == INSTANCE CarAlarmSystem5

THEOREM Spec => /\ CarAlarmSystem5!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
