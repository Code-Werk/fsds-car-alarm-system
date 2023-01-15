-------------------------- MODULE CarAlarmSystem8 --------------------------

(***************************************************************************)
(* Eighth refinement of the car alarm system:                              *)
(*                                                                         *)
(* TODO *)
(***************************************************************************)

EXTENDS Integers, TLC

CONSTANT ArmedDelay, AlarmDelay, MaxPinMismatch
ASSUME ArmedDelay \in Nat
ASSUME AlarmDelay \in Nat
ASSUME MaxPinMismatch \in Nat

ArmedRange == 0..ArmedDelay
AlarmRange == 0..AlarmDelay

OpenAndUnlocked   == 0          \* Car is open and unlocked
ClosedAndLocked   == 1          \* Car is closed and locked
OpenAndLocked     == 2          \* Car is still open but already locked
ClosedAndUnlocked == 3          \* Car is not yet closed but already locked
Armed             == 4          \* Car alarm system is armed (which means it is locked and closed and alarm could be triggered)
Alarm             == 5          \* Car alarm is on (which means an illegal action - car opened without unlocking - occurred in the armed state and the alarm was triggered)
SilentAndOpen     == 6          \* Car has been in alarm (or technically still is, but no flash and sound is on) but is now waiting to return to armed or unlocked (car is closed again or unlocked)

STATES ==                       \* Currently possible states
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
    mismatchCounter,
    alarmTrigger

vars == 
    <<
        state,
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        mismatchCounter,
        alarmTrigger
    >>
vars_without_state == 
    <<
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        mismatchCounter,
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
                 /\ mismatchCounter \in 0..MaxPinMismatch
                 /\ alarmTrigger \in AlarmTriggerStates \union {-1}
                 
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
        /\ mismatchCounter = 0
        /\ alarmTrigger = -1

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

CheckPin(nextState) == /\ \E b \in BOOLEAN:
                          IF b = TRUE
                          THEN /\ state' = nextState
                               /\ isArmed' = FALSE
                               /\ mismatchCounter' = 0
                          ELSE /\ mismatchCounter' = mismatchCounter + 1
                               /\ UNCHANGED<<state, isArmed>>

SetArmed == /\ state' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay
            /\ mismatchCounter' = 0

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
                             /\ UNCHANGED<<flash, sound, mismatchCounter, alarmTrigger>>

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ mismatchCounter' = 0
                              /\ UNCHANGED(timer_vars)
                              /\ UNCHANGED<<isArmed, flash, sound, alarmTrigger>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ mismatchCounter' = 0
                                /\ UNCHANGED(timer_vars)
                                /\ UNCHANGED<<isArmed, flash, sound, alarmTrigger>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED<<vars_without_state>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ armedTimer' = ArmedDelay
                              /\ UNCHANGED<<flash, sound, isArmed, alarmTimer, mismatchCounter, alarmTrigger>>
                              
Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<alarmTrigger>>

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED<<flash, sound, isArmed, alarmTimer, mismatchCounter, alarmTrigger>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>
     
Unlock_After_Armed == /\ state  = Armed
                      /\ mismatchCounter < MaxPinMismatch
                      /\ CheckPin(ClosedAndUnlocked)
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
                      /\ mismatchCounter' = 0
                      /\ CarAlarm!Deactivate

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED<<flash, sound, alarmTimer, alarmTrigger>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

MismatchAlarm == /\ state \in AlarmTriggerStates
                  /\ mismatchCounter = MaxPinMismatch
                  /\ alarmTrigger = -1
                  /\ state' = Alarm
                  /\ isArmed' = FALSE
                  /\ alarmTrigger' = state
                  /\ CarAlarm!Activate
                  /\ UNCHANGED(timer_vars)
                  /\ UNCHANGED<<mismatchCounter>>

AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

AlarmFinished_Mismatch == /\ AlarmFinished
                          /\ alarmTrigger \in AlarmTriggerStates 
                          /\ mismatchCounter = MaxPinMismatch
                          /\ alarmTrigger' = -1
                          /\ UNCHANGED<<armedTimer>>
                          /\ IF alarmTrigger = Armed
                                THEN SetArmed
                                ELSE /\ state' = alarmTrigger
                                     /\ mismatchCounter' = 0
                                     /\ UNCHANGED<<isArmed>>

AlarmFinished_Open == /\ AlarmFinished
                      /\ mismatchCounter = 0
                      /\ alarmTrigger = -1
                      /\ state' = SilentAndOpen
                      /\ UNCHANGED<<isArmed, mismatchCounter, alarmTrigger, armedTimer>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

SetNewPin == /\ state \in { OpenAndUnlocked, ClosedAndUnlocked}
             /\ mismatchCounter < MaxPinMismatch
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
                /\ UNCHANGED<<state, isArmed, sound, flash, alarmTimer, mismatchCounter, alarmTrigger>>

AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED<<state, isArmed, flash, armedTimer, mismatchCounter, alarmTrigger>>

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
        \/ AlarmFinished_Mismatch
        \/ AlarmFinished_Open
        \/ ArmingTicker
        \/ AlarmTicker
        \/ MismatchAlarm
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
