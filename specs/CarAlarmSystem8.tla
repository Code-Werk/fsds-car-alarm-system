-------------------------- MODULE CarAlarmSystem8 --------------------------

(***************************************************************************)
(* Eighth refinement of the car alarm system:                              *)
(*                                                                         *)
(* TODO *)
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

AlarmTriggerStates ==
    {
        OpenAndUnlocked, 
        ClosedAndUnlocked, 
        Armed
    }
    
VARIABLES 
    state, 
    isArmed, 
    flash, 
    sound, 
    armedTimer, 
    alarmTimer, 
    missmatchCounter,
    alarmTrigger

vars == 
    <<
        state,
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        missmatchCounter,
        alarmTrigger
    >>
vars_without_state == 
    <<
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        missmatchCounter,
        alarmTrigger
    >>
timer_vars == <<armedTimer, alarmTimer>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

CarAlarm == INSTANCE CarAlarm1 WITH flash <- flash, sound <- sound

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ missmatchCounter \in 0..MaxPinMissmatch
                 /\ alarmTrigger \in AlarmTriggerStates \union {0}
                 
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
        /\ missmatchCounter = 0
        /\ alarmTrigger = 0


(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

CheckPin(nextState) == /\ \E b \in BOOLEAN:
                          IF b = TRUE
                          THEN /\ state' = nextState
                               /\ isArmed' = FALSE
                               /\ missmatchCounter' = 0
                          ELSE /\ missmatchCounter' = missmatchCounter + 1
                               /\ UNCHANGED<<state, isArmed>>


(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED<<vars_without_state>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED<<vars_without_state>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED(timer_vars)
                             /\ UNCHANGED<<flash, sound, missmatchCounter, alarmTrigger>>
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
                              /\ armedTimer' = ArmedDelay
                              /\ UNCHANGED<<flash, sound, isArmed, alarmTimer, missmatchCounter, alarmTrigger>>

Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ missmatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<alarmTrigger>>

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED<<flash, sound, isArmed, alarmTimer, missmatchCounter, alarmTrigger>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>
     
Unlock_After_Armed == /\ state  = Armed
                      /\ missmatchCounter < MaxPinMissmatch
                      /\ CheckPin(ClosedAndUnlocked)
                      /\ UNCHANGED(timer_vars)
                      /\ UNCHANGED<<flash, sound, alarmTrigger>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ state' = OpenAndUnlocked
                      /\ alarmTimer' = AlarmDelay
                      /\ missmatchCounter' = 0
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed, armedTimer, alarmTrigger>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

SetArmed == /\ state' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay
            /\ missmatchCounter' = 0

Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED<<flash, sound, alarmTimer, alarmTrigger>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

MissmatchAlarm == /\ state \in AlarmTriggerStates
                  /\ missmatchCounter = MaxPinMissmatch
                  /\ state' = Alarm
                  /\ isArmed' = FALSE
                  /\ alarmTrigger' = state
                  /\ CarAlarm!Activate
                  /\ UNCHANGED(timer_vars)
                  /\ UNCHANGED<<missmatchCounter>>

AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ alarmTimer' = AlarmDelay
                 /\ CarAlarm!Deactivate
                 /\ UNCHANGED<<armedTimer>>
                 /\ IF missmatchCounter = MaxPinMissmatch
                    THEN /\ alarmTrigger' = 0
                         /\ IF alarmTrigger = Armed 
                            THEN SetArmed 
                            ELSE /\ state' = alarmTrigger
                                 /\ UNCHANGED<<missmatchCounter, isArmed>>
                    ELSE /\ state' = SilentAndOpen
                         /\ UNCHANGED<<isArmed, missmatchCounter, alarmTrigger>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

SetNewPin == /\ state \in { OpenAndUnlocked, ClosedAndUnlocked}
             /\ missmatchCounter < MaxPinMissmatch
             /\ CheckPin(state)
             /\ UNCHANGED(timer_vars)
             /\ UNCHANGED<<flash, sound, alarmTrigger>>


(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED<<state, isArmed, sound, flash, alarmTimer, missmatchCounter, alarmTrigger>>

AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED<<state, isArmed, flash, armedTimer, missmatchCounter, alarmTrigger>>

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
        \/ SetNewPin

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem7 == INSTANCE CarAlarmSystem7

THEOREM Spec => /\ CarAlarmSystem7!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:48:38 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
