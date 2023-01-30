-------------------------- MODULE CarAlarmSystem9 --------------------------

(***************************************************************************)
(* Ninth refinement of the car alarm system:                               *)
(*                                                                         *)
(* TODO *)
(***************************************************************************)

EXTENDS Integers

CONSTANT
    ArmedDelay,                 \* Time the car takes to switch into an armed state after 
                                \* it was locked (here: time to change the state from 
                                \* ClosedAndLocked to Armed)
    AlarmDelay,                 \* Time the car remains in a non-silent alarm state 
                                \* (here: time where flash and sound or only flash are on)
    MaxPinMismatch,             \* Max. count until a pin mismatch alarm is triggered 
                                \* (here: how often can a key send a wrong pin)
    DoorCount                   \* Amount of the car's doors
ASSUME ArmedDelay \in Nat       \* ArmedDelay is set in the TLC, 20 sec by requirement
ASSUME AlarmDelay \in Nat       \* AlarmDelay is set in the TLC, 300 sec by requirement (=5 min)
ASSUME MaxPinMismatch \in Nat   \* MaxPinMismatch is set in the TLC, 3 tries by requirement

ArmedRange == 0..ArmedDelay     \* Range for the armed timer, it counts down from the 
                                \* max value (= ArmedDelay) to 0
AlarmRange == 0..AlarmDelay     \* Range for the alarm timer, it counts down from the max
                                \* value (= AlarmDelay) to 0

OpenAndUnlocked   == 0          \* Car is open and unlocked
ClosedAndLocked   == 1          \* Car is closed and locked
OpenAndLocked     == 2          \* Car is still open but already locked
ClosedAndUnlocked == 3          \* Car is not yet closed but already locked
Armed             == 4          \* Car alarm system is armed (which means it is locked and
                                \*  closed and alarm could be triggered)
Alarm             == 5          \* Car alarm is on (which means an illegal action 
                                \* - car opened without unlocking - 
                                \* occurred in the armed state and the alarm was triggered)
SilentAndOpen     == 6          \* Car has been in alarm (or technically still is, but no
                                \* flash and sound is on) but is now waiting to return to 
                                \* armed or unlocked (car is closed again or unlocked)

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

AlarmTriggerStates ==           \* States that can trigger a mismatch alarm
    {
        OpenAndUnlocked,
        ClosedAndUnlocked,
        Armed
    }

VARIABLES 
    state,                      \* the current state in the state diagram
    isArmed,                    \* flag to indicate if the car is armed
    flash,                      \* flag to indicate if flash is on
    sound,                      \* flag to indicate if sound is on
    armedTimer,                 \* timer that counts from ArmedDelay to 0
    alarmTimer,                 \* timer that counts from AlarmDelay to 0
    mismatchCounter             \* tracks how many wrong pins were sent while in an armed state
                                \* or to change the pin in an unlocked state
    alarmTrigger,               \* variable to keep track of the state that triggered a mismatch alarm
    passengerDoors              \* tuple representing the passenger doors
                                \* consists of an index and a bool flag indicating
                                \* if the door is open (flag is true), or closed (flag is false)

vars == 
    <<
        state,
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        mismatchCounter,
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
        mismatchCounter,
        alarmTrigger,
        passengerDoors
    >>

alarm_vars == <<flash, sound>>
pin_vars == <<alarmTrigger, mismatchCounter>>
door_vars == <<passengerDoors>>
timer_vars == <<armedTimer, alarmTimer>>

alarm_system_vars == <<isArmed, alarm_vars, pin_vars, timer_vars>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

CarAlarm == INSTANCE CarAlarm1      \* Refinement mapping through equal var names
Doors == INSTANCE Doors1            \* Refinement mapping through equal var names

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ mismatchCounter \in 0..MaxPinMismatch
                 /\ alarmTrigger \in AlarmTriggerStates \union {-1}
                 /\ Doors!TypeInvariant

\* if the alarm is on, sound and flash should be on for the first 30 secs (alarm timer range: 270 - 300)
\* afterwards, only the flash should be on and the sound off
\* if the car is in an armed state indicate that by setting the isArmed flag
\* the armed timer should be reset to the ArmedDelay when reaching this state
\* the only state where the armed timer should change is ClosedAndLocked, otherwise it's set to ArmedDelay
\* the safety invariant for the doors needs to hold for the car alarm system safety invariant to hold
\* if the doors are closed, the car has to be in a closed state (not in an open state)
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

\* state diagram starts in the OpenAndUnlocked state
\* the car is unarmed, armed timer is set to ArmedDelay
\* alarm indicators are off (alarm is deactivated) and alarm timer is set to AlarmDelay
\* the mismatch counter starts at 0
\* alarm trigger starts with a no alarm value
\* the doors module needs to be initialized
Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ mismatchCounter = 0
        /\ alarmTrigger = -1
        /\ Doors!Init

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* Helper action that is called to non-deterministically check if a sent pin matches
\* and so can unlock the car or change the pin, or if the pin is incorrect
CheckPin(nextState) == /\ \E b \in BOOLEAN:
                          IF b = TRUE
                              THEN /\ state' = nextState
                                   /\ isArmed' = FALSE
                                   /\ mismatchCounter' = 0
                              ELSE /\ mismatchCounter' = mismatchCounter + 1
                                   /\ UNCHANGED<<state, isArmed>>

\* Helper action that sets the car into an armed state
SetArmed == /\ state' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay
            /\ mismatchCounter' = 0

\* TODO
TryCloseDoor(nextState) == /\ Doors!Close
                           /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                                  THEN state' = nextState
                                  ELSE UNCHANGED<<state>>

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
\* this tries to close the doors in the door module
Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ TryCloseDoor(ClosedAndUnlocked)
                               /\ UNCHANGED(alarm_system_vars)

\* Close the car from the OpenAndLocked state to get to ClosedAndLocked
\* this tries to close the doors in the door module
Close_After_OpenAndLocked == /\ state = OpenAndLocked
                             /\ TryCloseDoor(ClosedAndLocked)
                             /\ UNCHANGED(alarm_system_vars)

\* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
\* this tries to close the doors in the door module and arms the car again if all doors are closed
Close_After_SilentAndOpen == /\ state = SilentAndOpen
                             /\ TryCloseDoor(Armed)
                             /\ isArmed' = \A pd \in passengerDoors' : pd[2] = FALSE
                             /\ UNCHANGED<<alarm_vars, timer_vars>>

\* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
Open_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ Doors!Open
                                /\ UNCHANGED(alarm_system_vars)

\* Open the car from the ClosedAndLocked state to get to OpenAndLocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Open_After_ClosedAndLocked == /\ state = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ armedTimer' = ArmedDelay
                              /\ Doors!Open
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED(pin_vars)
                              /\ UNCHANGED(aux_vars)
                              /\ UNCHANGED<<isArmed, alarmTimer>>

\* Open the car from an armed state
\* this is an illegal action -> trigger alarm
\* the alarm was triggered my an unauthorized open, so reset the mismatch counter
Open_After_Armed == /\ state = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter' = 0
                    /\ Doors!Open
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<alarmTrigger>>

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
\* We are resetting the mismatch count here, since we are moving into a locked state
Lock_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ mismatchCounter' = 0
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED(door_vars)
                              /\ UNCHANGED(timer_vars)
                              /\ UNCHANGED<<isArmed, alarmTrigger>>

\* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
\* We are resetting the mismatch count here, since we are moving into a locked state
Lock_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ mismatchCounter' = 0
                                /\ UNCHANGED(door_vars)
                                /\ UNCHANGED(timer_vars)
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed, alarmTrigger>>

\* Lock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED(door_vars)
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED(pin_vars)
                                /\ UNCHANGED<<isArmed, alarmTimer>>

\* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
\* for this action we need to verify the pin when unlocking, which is only possible
\* until the mismatchCounter reaches the MaxPinMismatch number
Unlock_After_Armed == /\ state  = Armed
                      /\ mismatchCounter < MaxPinMismatch
                      /\ CheckPin(ClosedAndUnlocked)
                      /\ UNCHANGED(alarm_vars)
                      /\ UNCHANGED(door_vars)
                      /\ UNCHANGED(timer_vars)
                      /\ UNCHANGED<<alarmTrigger>>

\* Unlock the car after an alarm was triggered (car in alarm state)
\* this ends the path for an illegal action and puts the car in the OpenAndUnlocked state,
\* deactivates the alarm and resets the alarm timer and the mismatch counter
\* (= reset cause of the alarm)
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
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
                      /\ UNCHANGED(door_vars)

\* Similar to the Unlock_After_Alarm action, but puts the car into a valid
\* state again after the alarm already turned silent, thus, the alarm was already deactivated
Unlock_After_SilentAndOpen == /\ state = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

\* car transitioning from closed and unlocked into an armed state
\* the car should also show it is armed, so the flag is set to true to indicate that
\* the armed delay timer reached 0, so the car can be armed and the timer needs to be reset
Arming == /\ state = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED(alarm_vars)
          /\ UNCHANGED(door_vars)
          /\ UNCHANGED<<alarmTimer, alarmTrigger>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* action that triggers the car alarm after there were too many unlock attempts with
\* an invalid pin (mismatchCounter reached MaxPinMismatch)
\* this can occur if the car wrong pins are sent to unlock the car or to change the pin
MismatchAlarm == /\ state \in AlarmTriggerStates
                  /\ mismatchCounter = MaxPinMismatch
                  /\ alarmTrigger = -1
                  /\ state' = Alarm
                  /\ isArmed' = FALSE
                  /\ alarmTrigger' = state
                  /\ CarAlarm!Activate
                  /\ UNCHANGED(door_vars)
                  /\ UNCHANGED(timer_vars)
                  /\ UNCHANGED<<mismatchCounter>>

\* common action between both methods to exit an alarm after 5 mins of being
\* active without proper unlocking
AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay
                 /\ UNCHANGED(door_vars)

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to the originating state
\* since the alarm was due to too many pin mismatches
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

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to SilentAndOpen since the
\* alarm was due to an unauthorized open
AlarmFinished_Open == /\ AlarmFinished
                      /\ mismatchCounter = 0 
                      /\ alarmTrigger = -1
                      /\ state' = SilentAndOpen
                      /\ UNCHANGED<<isArmed, mismatchCounter, alarmTrigger, armedTimer>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

\* Action that allows changing the wireless key pin
\* This is possible in an unlocked state and requires the old and the new pin
\* to be provided
\* If the old (= current) pin is provided wrongly for three times, a mismatch alarm
\* will be triggered
SetNewPin == /\ state \in { OpenAndUnlocked, ClosedAndUnlocked}
             /\ mismatchCounter < MaxPinMismatch
             /\ CheckPin(state)
             /\ UNCHANGED(door_vars)
             /\ UNCHANGED(timer_vars)
             /\ UNCHANGED<<flash, sound, alarmTrigger>>

(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

\* count down of the armed timer from ArmedDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED(door_vars)
                /\ UNCHANGED(alarm_vars)
                /\ UNCHANGED<<state, isArmed, alarmTimer>>

\* count down of the alarm timer from AlarmDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
\* once the alarm timer leaves the sound range (30 secs, so timer < 270)
\* the sound is deactivated and only the flash continues
AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED(door_vars)
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

\* TODO refinement mapping + checking
\* instance of the lower refinement
CarAlarmSystem8 == INSTANCE CarAlarmSystem8

\* property to check the lower refinement in the TLC
CarAlarmSystem8Spec == /\ CarAlarmSystem8!Spec
                       /\ CarAlarmSystem8!SafetyInvariant
                       /\ CarAlarmSystem8!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

\* check that the doors module also holds in the TLC
DoorsSpec == /\ Doors!Spec
             /\ Doors!SafetyInvariant
             /\ Doors!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem8Spec
                /\ CarAlarmSpec
                /\ DoorsSpec
                /\ []Invariant

=============================================================================
