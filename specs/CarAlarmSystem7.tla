-------------------------- MODULE CarAlarmSystem7 --------------------------

(***************************************************************************)
(* Seventh refinement of the car alarm system:                             *)
(*                                                                         *)
(* TODO *)
(*                                                                         *)
(* This refinement targets Requirements 4.                                 *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT
    ArmedDelay,                 \* Time the car takes to switch into an armed state after it was locked (here: time to change the state from ClosedAndLocked to Armed)
    AlarmDelay,                 \* Time the car remains in a non-silent alarm state (here: time where flash and sound or only flash are on)
    MaxPinMismatch              \* Max. count until a pin mismatch alarm is triggered (here: how often can a key send a wrong pin)
ASSUME ArmedDelay \in Nat       \* ArmedDelay is set in the TLC, 20 sec by requirement
ASSUME AlarmDelay \in Nat       \* AlarmDelay is set in the TLC, 300 sec by requirement (=5 min)
ASSUME MaxPinMismatch \in Nat   \* MaxPinMismatch is set in the TLC, 3 tries by requirement

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

VARIABLES
    state,                      \* the current state in the state diagram
    isArmed,                    \* flag to indicate if the car is armed
    flash,                      \* flag to indicate if flash is on
    sound,                      \* flag to indicate if sound is on
    armedTimer,                 \* timer that counts from ArmedDelay to 0
    alarmTimer,                 \* timer that counts from AlarmDelay to 0
    mismatchCounter             \* tracks how many wrong pins were sent while in an armed state

vars == 
    <<
        state,
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        mismatchCounter
    >>
vars_without_state == 
    <<
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        mismatchCounter
    >>
alarm_vars == <<flash, sound>>
timer_vars == <<armedTimer, alarmTimer>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

CarAlarm == INSTANCE CarAlarm1      \* Refinement mapping through equal var names

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ mismatchCounter \in 0..MaxPinMismatch
                 
SafetyInvariant == /\ state = Alarm => flash = TRUE
                   /\ IF state = Alarm /\ alarmTimer > 269                  \* if the alarm is on, sound and flash should be on for the first 30 secs (alarm timer range: 270 - 300)
                        THEN sound = TRUE                                   \* afterwards, only the flash should be on and the sound off
                        ELSE sound = FALSE
                   /\ state = Armed                                         \* if the car is in an armed state indicate that by setting the isArmed flag
                        => armedTimer = ArmedDelay /\ isArmed = TRUE        \* the armed timer should be reset to the ArmedDelay when reaching this state
                   /\ state /= ClosedAndLocked => armedTimer = ArmedDelay   \* the only state where the armed timer should change is ClosedAndLocked, otherwise it's set to ArmedDelay
                   /\ state /= Alarm => alarmTimer = AlarmDelay

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Todo comment: 2 ways leaving alarm, 
\* 1. pin mismatch: after 300 seconds back to armed or proper unlock with physical key 
\* 2. open: after 300 seconds to silent open or proper unlock with physical key 

Init == /\ state = OpenAndUnlocked                                      \* state diagram starts in the OpenAndUnlocked state
        /\ isArmed = FALSE                                              \* the car is unarmed, armed timer is set to ArmedDelay
        /\ flash = FALSE                                                \* alarm indicators are off (alarm is deactivated) and alarm timer is set to AlarmDelay
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ mismatchCounter = 0                                          \* the mismatch counter starts at 0

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

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked               \* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED(vars_without_state)

Close_After_OpenAndLocked == /\ state  = OpenAndLocked                  \* Close the car from the OpenAndLocked state to get to ClosedAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED(vars_without_state)

Close_After_SilentAndOpen == /\ state  = SilentAndOpen                  \* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
                             /\ state' = Armed                          \* This arms the car again
                             /\ isArmed' = TRUE
                             /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED(timer_vars)
                             /\ UNCHANGED<<mismatchCounter>>

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked               \* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED(vars_without_state)

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked           \* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED(vars_without_state)

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked           \* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED(vars_without_state)

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked               \* Open the car from the ClosedAndLocked state to get to OpenAndLocked
                              /\ state' = OpenAndLocked                 \* reset the timer to ArmedDelay, since we are not counting down anymore in this state
                              /\ armedTimer' = ArmedDelay               \* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed, alarmTimer, mismatchCounter>>

Open_After_Armed == /\ state  = Armed                                   \* Open the car from an armed state
                    /\ state' = Alarm                                   \* this is an illegal action -> trigger alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked             \* Lock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
                                /\ state' = ClosedAndUnlocked           \* reset the timer to ArmedDelay, since we are not counting down anymore in this state
                                /\ armedTimer' = ArmedDelay             \* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed, alarmTimer, mismatchCounter>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked                 \* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(vars_without_state)

Unlock_After_Armed == /\ state  = Armed                                 \* Unlock the car from an armed state to get into an unarmed state
                      /\ mismatchCounter < MaxPinMismatch               \* so the car can be arbitrarily unlocked/locked and opened/closed
                      /\ CheckPin(ClosedAndUnlocked)                    \* and deactivates the alarm 
                      /\ UNCHANGED(alarm_vars)                          \*TODO
                      /\ UNCHANGED(timer_vars)

Unlock_After_Alarm == /\ state  = Alarm                                 \* Unlock the car after an alarm was triggered (car in alarm state)
                      /\ state' = OpenAndUnlocked                       \* this ends the path for an illegal action and puts the car in the OpenAndUnlocked state,
                      /\ alarmTimer' = AlarmDelay                       \* deactivates the alarm and resets the alarm timer
                      /\ mismatchCounter' = 0
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed, armedTimer>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen                 \* Similar to the Unlock_After_Alarm action, but puts the car into a valid
                              /\ state' = OpenAndUnlocked               \* state again after the alarm already turned silent, thus, the alarm was already deactivated
                              /\ UNCHANGED(vars_without_state)

Arming == /\ state  = ClosedAndLocked                                   \* car transitioning from closed and unlocked into an armed state
          /\ armedTimer = 0                                             \* the car should also show it is armed, so the flag is set to true to indicate that
          /\ SetArmed                                                   \* the armed delay timer reached 0, so the car can be armed and the timer needs to be reset
          /\ UNCHANGED(alarm_vars)
          /\ UNCHANGED<<alarmTimer>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

MismatchAlarm == /\ state = Armed
                  /\ mismatchCounter = MaxPinMismatch
                  /\ state' = Alarm
                  /\ isArmed' = FALSE
                  /\ CarAlarm!Activate
                  /\ UNCHANGED(timer_vars)
                  /\ UNCHANGED<<mismatchCounter>>

AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ alarmTimer' = AlarmDelay
                 /\ CarAlarm!Deactivate
                 /\ UNCHANGED<<armedTimer>>
                 /\ IF mismatchCounter = MaxPinMismatch
                    THEN /\ SetArmed
                    ELSE /\ state' = SilentAndOpen
                         /\ UNCHANGED<<isArmed, mismatchCounter>>

(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED<<state, isArmed, sound, flash, alarmTimer, mismatchCounter>>

AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED<<state, isArmed, flash, armedTimer, mismatchCounter>>

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
        \/ MismatchAlarm

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem6 == INSTANCE CarAlarmSystem6

THEOREM Spec => /\ CarAlarmSystem6!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:48:38 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
