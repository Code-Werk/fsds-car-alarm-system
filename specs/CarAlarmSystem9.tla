-------------------------- MODULE CarAlarmSystem9 --------------------------

(***************************************************************************)
(* Ninth refinement of the car alarm system:                              *)
(*                                                                         *)
(* TODO *)
(***************************************************************************)

EXTENDS Integers, TLC

CONSTANT ArmedDelay, AlarmDelay, MaxPinMissmatch, DoorCount
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
    alarmTrigger,
    passengerDoors

vars == 
    <<
        state,
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        missmatchCounter,
        alarmTrigger,
        passengerDoors
    >>
vars_without_state == 
    <<
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        missmatchCounter,
        alarmTrigger,
        passengerDoors
    >>

alarm_vars == <<flash, sound, alarmTrigger, missmatchCounter>>
door_vars == <<passengerDoors>>
timer_vars == <<armedTimer, alarmTimer>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

CarAlarm == INSTANCE CarAlarm1
Doors == INSTANCE Doors1

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ missmatchCounter \in 0..MaxPinMissmatch
                 /\ alarmTrigger \in AlarmTriggerStates \union {-1}
                 /\ Doors!TypeInvariant
                 
SafetyInvariant == /\ state = Alarm => flash = TRUE
                   /\ IF state = Alarm /\ alarmTimer > 269 
                        THEN sound = TRUE
                        ELSE sound = FALSE
                   /\ state = Armed => armedTimer = ArmedDelay /\ isArmed = TRUE
                   /\ state /= ClosedAndLocked => armedTimer = ArmedDelay
                   /\ state /= Alarm => alarmTimer = AlarmDelay
                   /\ Doors!SafetyInvariant
                   /\ Doors!AreClosed => state \notin { OpenAndLocked, OpenAndUnlocked, SilentAndOpen }

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
        /\ alarmTrigger = -1
        /\ Doors!Init


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

SetArmed == /\ state' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay
            /\ missmatchCounter' = 0

TryCloseDoor(nextState) == /\ Doors!Close
                           /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                              THEN state' = nextState
                              ELSE UNCHANGED<<state>>

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)


Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ TryCloseDoor(ClosedAndUnlocked)
                               /\ UNCHANGED<<isArmed, alarm_vars, timer_vars>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked
                             /\ TryCloseDoor(ClosedAndLocked)
                             /\ UNCHANGED<<isArmed, alarm_vars, timer_vars>>

Close_After_SilentAndOpen == /\ state = SilentAndOpen
                             /\ TryCloseDoor(Armed)
                             /\ isArmed' = \A pd \in passengerDoors' : pd[2] = FALSE
                             /\ UNCHANGED<<alarm_vars, timer_vars>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ Doors!Open
                                /\ UNCHANGED<<isArmed, alarm_vars, timer_vars>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ Doors!Open
                              /\ armedTimer' = ArmedDelay
                              /\ UNCHANGED<<alarm_vars, isArmed, alarmTimer>>

Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ missmatchCounter' = 0
                    /\ Doors!Open
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<alarmTrigger>>

Open_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                              /\ Doors!Open
                              /\ UNCHANGED<<state, isArmed, alarm_vars, timer_vars>>

Open_After_OpenAndLocked == /\ state = OpenAndLocked
                              /\ Doors!Open
                              /\ UNCHANGED<<state, isArmed, alarm_vars, timer_vars>>

Open_After_SilentAndOpen == /\ state = SilentAndOpen
                            /\ Doors!Open
                            /\ UNCHANGED<<state, isArmed, alarm_vars, timer_vars>>

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ missmatchCounter' = 0
                              /\ UNCHANGED(door_vars)
                              /\ UNCHANGED(timer_vars)
                              /\ UNCHANGED<<isArmed, flash, sound, alarmTrigger>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ missmatchCounter' = 0
                                /\ UNCHANGED(door_vars)
                                /\ UNCHANGED(timer_vars)
                                /\ UNCHANGED<<isArmed, flash, sound, alarmTrigger>>

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED(door_vars)
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed, alarmTimer>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>
     
Unlock_After_Armed == /\ state  = Armed
                      /\ missmatchCounter < MaxPinMissmatch
                      /\ CheckPin(ClosedAndUnlocked)
                      /\ UNCHANGED(door_vars)
                      /\ UNCHANGED(timer_vars)
                      /\ UNCHANGED<<flash, sound, alarmTrigger>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ IF alarmTrigger = -1
                            THEN /\ state' = OpenAndUnlocked
                                 /\ UNCHANGED<<isArmed, armedTimer>>
                            ELSE IF alarmTrigger = Armed
                                 THEN SetArmed
                                 ELSE /\ state' = alarmTrigger
                                      /\ UNCHANGED<<isArmed, armedTimer>>
                      /\ alarmTimer' = AlarmDelay
                      /\ alarmTrigger' = -1
                      /\ missmatchCounter' = 0
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED(door_vars)

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED(door_vars)
          /\ UNCHANGED<<flash, sound, alarmTimer, alarmTrigger>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

MissmatchAlarm == /\ state \in AlarmTriggerStates
                  /\ missmatchCounter = MaxPinMissmatch
                  /\ alarmTrigger = -1
                  /\ state' = Alarm
                  /\ isArmed' = FALSE
                  /\ alarmTrigger' = state
                  /\ CarAlarm!Activate
                  /\ UNCHANGED(door_vars)
                  /\ UNCHANGED(timer_vars)
                  /\ UNCHANGED<<missmatchCounter>>


AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay
                 /\ UNCHANGED(door_vars)

AlarmFinished_Missmatch == /\ AlarmFinished
                           /\ alarmTrigger \in AlarmTriggerStates 
                           /\ missmatchCounter = MaxPinMissmatch
                           /\ alarmTrigger' = -1
                           /\ UNCHANGED<<armedTimer>>
                           /\ IF alarmTrigger = Armed 
                              THEN SetArmed 
                              ELSE /\ state' = alarmTrigger
                                   /\ missmatchCounter' = 0
                                   /\ UNCHANGED<<isArmed>>

AlarmFinished_Open == /\ AlarmFinished
                      /\ missmatchCounter = 0 
                      /\ alarmTrigger = -1
                      /\ state' = SilentAndOpen
                      /\ UNCHANGED<<isArmed, missmatchCounter, alarmTrigger, armedTimer>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

SetNewPin == /\ state \in { OpenAndUnlocked, ClosedAndUnlocked}
             /\ missmatchCounter < MaxPinMissmatch
             /\ CheckPin(state)
             /\ UNCHANGED(door_vars)
             /\ UNCHANGED(timer_vars)
             /\ UNCHANGED<<flash, sound, alarmTrigger>>


(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED(door_vars)
                /\ UNCHANGED(alarm_vars)
                /\ UNCHANGED<<state, isArmed, alarmTimer>>

AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED(door_vars)
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
        \/ AlarmFinished_Missmatch
        \/ AlarmFinished_Open
        \/ ArmingTicker
        \/ AlarmTicker
        \/ MissmatchAlarm
        \/ SetNewPin

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem8 == INSTANCE CarAlarmSystem8

THEOREM Spec => /\ CarAlarmSystem8!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:48:38 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
