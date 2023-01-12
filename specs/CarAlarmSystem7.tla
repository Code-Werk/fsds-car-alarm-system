-------------------------- MODULE CarAlarmSystem7 --------------------------

(***************************************************************************)
(* Seventh refinement for the car alarm system                             *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT ArmedDelay, AlarmDelay, MaxPinMissmatch
ASSUME ArmedDelay \in Nat
ASSUME AlarmDelay \in Nat
ASSUME MaxPinMissmatch \in Nat

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

VARIABLES state, isArmed, flash, sound, armedTimer, alarmTimer, missmatchCounter

vars == <<state, isArmed, flash, sound, armedTimer,alarmTimer, missmatchCounter>>
vars_without_state == <<isArmed, flash, sound, armedTimer, alarmTimer, missmatchCounter>>

CarAlarm == INSTANCE CarAlarm1 WITH flash <- flash, sound <- sound

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ missmatchCounter \in 0..MaxPinMissmatch
                 
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

\* Todo comment: 2 ways leaving alarm, 
\* 1. pin missmatch: after 300 seconds back to armed or proper unlock with physical key 
\* 2. open: after 300 seconds to silent open or proper unlock with physical key 


Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ missmatchCounter = 0

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED<<vars_without_state>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED<<vars_without_state>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED<<flash, sound, armedTimer, alarmTimer, missmatchCounter>>


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
                              /\ UNCHANGED<<flash, sound, isArmed, alarmTimer, missmatchCounter>>

Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ missmatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED<<armedTimer, alarmTimer>>

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer'= ArmedDelay
                                /\ UNCHANGED<<flash, sound, isArmed, alarmTimer, missmatchCounter>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>


CheckPin(nextState) == /\ \E b \in BOOLEAN:
                          IF b = TRUE
                          THEN /\ state' = nextState
                               /\ isArmed' = FALSE
                               /\ missmatchCounter' = 0
                          ELSE /\ missmatchCounter' = missmatchCounter + 1
                               /\ UNCHANGED<<state, isArmed>>
     
Unlock_After_Armed == /\ state  = Armed
                      /\ missmatchCounter < MaxPinMissmatch
                      /\ CheckPin(ClosedAndUnlocked)
                      /\ UNCHANGED<<flash, sound, armedTimer, alarmTimer>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ state' = OpenAndUnlocked
                      /\ alarmTimer' = AlarmDelay
                      /\ missmatchCounter' = 0
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed, armedTimer>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

SetArmed == /\ state' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer'= ArmedDelay
            /\ missmatchCounter' = 0

Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED<<flash, sound, alarmTimer>>

MissmatchAlarm == /\ state = Armed
                  /\ missmatchCounter = MaxPinMissmatch
                  /\ state' = Alarm
                  /\ isArmed' = FALSE
                  /\ CarAlarm!Activate
                  /\ UNCHANGED<<alarmTimer, armedTimer, missmatchCounter>>

AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ alarmTimer' = AlarmDelay
                 /\ CarAlarm!Deactivate
                 /\ UNCHANGED<<armedTimer>>
                 /\ IF missmatchCounter = MaxPinMissmatch
                    THEN /\ SetArmed
                    ELSE /\ state' = SilentAndOpen
                         /\ UNCHANGED<<isArmed, missmatchCounter>>

ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED<<state, isArmed, sound, flash, alarmTimer, missmatchCounter>>

AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED<<state, isArmed,flash, armedTimer, missmatchCounter>>

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
        \/ AlarmFinished
        \/ ArmingTicker
        \/ AlarmTicker
        \/ MissmatchAlarm

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

CarAlarmSystem6 == INSTANCE CarAlarmSystem6

THEOREM Spec => /\ CarAlarmSystem6!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
