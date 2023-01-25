-------------------------- MODULE CarAlarmSystem8 --------------------------

(***************************************************************************)
(* Eighth refinement of the car alarm system:                              *)
(*                                                                         *)
(* This refinement adds another requirement connected to pins to unlock the*)
(* car. Here we add the possibility to change a key's pin when the car is  *)
(* in an unlocked state. The mismatch alarm logic is similar to the one in *)
(* the seventh refinement: If a wrong pin is provided three times in a row *)
(* when trying to change the pin, a mismatch alarm is triggered. Leaving   *)
(* the alarm stays the same as well, except that we return to the previous *)
(* state (armed or any of the unlocked states). To keep track of that, a   *)
(* new variable alarmTrigger is introduced. Checking the pin uses the same *)
(* non-deterministic action as before, since we still only care about if a *)
(* pin matches or not, not what the pin is exactly.                        *)
(***************************************************************************)

EXTENDS Integers

CONSTANT
    ArmedDelay,                 \* Time the car takes to switch into an armed state after 
                                \* it was locked (here: time to change the state from 
                                \* ClosedAndLocked to Armed)
    AlarmDelay,                 \* Time the car remains in a non-silent alarm state 
                                \* (here: time where flash and sound or only flash are on)
    MaxPinMismatch              \* Max. count until a pin mismatch alarm is triggered 
                                \* (here: how often can a key send a wrong pin)
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
    mismatchCounter,            \* tracks how many wrong pins were sent while in an armed state
    alarmTrigger,               \* variable to keep track of the state that triggered a mismatch alarm
                                \* so we can return to it later (-1 if there is no alarm or not a mismatch alarm)
    will_return_to_trigger,     \* auxiliary (prophecy) variable to distinguish between a finished
                                \* normal alarm and a finished mismatch alarm
                                \* (the first goes to SilentAndOpen, the latter goes back to armed)
    increased_change_mismatch            \*

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
alarm_vars == <<flash, sound>>
timer_vars == <<armedTimer, alarmTimer>>
aux_vars   == <<increased_change_mismatch, will_return_to_trigger>>
all_vars   == <<vars, aux_vars>>

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
                 /\ alarmTrigger \in AlarmTriggerStates \union {-1}
                 /\ will_return_to_trigger \in BOOLEAN
                 /\ increased_change_mismatch \in BOOLEAN

\* if the alarm is on, sound and flash should be on for the first 30 secs (alarm timer range: 270 - 300)
\* afterwards, only the flash should be on and the sound off
\* if the car is in an armed state indicate that by setting the isArmed flag
\* the armed timer should be reset to the ArmedDelay when reaching this state
\* the only state where the armed timer should change is ClosedAndLocked, otherwise it's set to ArmedDelay
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

\* state diagram starts in the OpenAndUnlocked state
\* the car is unarmed, armed timer is set to ArmedDelay
\* alarm indicators are off (alarm is deactivated) and alarm timer is set to AlarmDelay
\* the mismatch counter starts at 0
Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ mismatchCounter = 0
        /\ alarmTrigger = -1
        /\ will_return_to_trigger = FALSE
        /\ increased_change_mismatch = FALSE

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

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

\* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED(vars_without_state)
                               /\ UNCHANGED(aux_vars)

\* Close the car from the OpenAndLocked state to get to ClosedAndLocked
Close_After_OpenAndLocked == /\ state = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED(vars_without_state)
                             /\ UNCHANGED(aux_vars)

\* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
\* This arms the car again
Close_After_SilentAndOpen == /\ state = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED(timer_vars)
                             /\ UNCHANGED(aux_vars)
                             /\ UNCHANGED<<mismatchCounter, alarmTrigger>>

\* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
\* We are resetting the mismatch count here, since we are moving into a locked state
Lock_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ mismatchCounter' = 0
                              /\ increased_change_mismatch' = FALSE
                              /\ UNCHANGED(timer_vars)
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed, alarmTrigger>>
                              /\ UNCHANGED<<will_return_to_trigger>>

\* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
\* We are resetting the mismatch count here, since we are moving into a locked state
Lock_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ mismatchCounter' = 0
                                /\ increased_change_mismatch' = FALSE
                                /\ UNCHANGED(timer_vars)
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed, alarmTrigger>>
                                /\ UNCHANGED<<will_return_to_trigger>>

\* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
Open_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED(vars_without_state)
                                /\ UNCHANGED(aux_vars)

\* Open the car from the ClosedAndLocked state to get to OpenAndLocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Open_After_ClosedAndLocked == /\ state = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ armedTimer' = ArmedDelay
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED(aux_vars)
                              /\ UNCHANGED<<isArmed, alarmTimer, mismatchCounter, alarmTrigger>>

\* Open the car from an armed state
\* this is an illegal action -> trigger alarm
\* the alarm was triggered my an unauthorised open, so reset the mismatch counter
Open_After_Armed == /\ state = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED(aux_vars)
                    /\ UNCHANGED<<alarmTrigger>>

\* Lock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Unlock_After_ClosedAndLocked == /\ state = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED(aux_vars)
                                /\ UNCHANGED<<isArmed, alarmTimer, mismatchCounter, alarmTrigger>>

\* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
Unlock_After_OpenAndLocked == /\ state = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(vars_without_state)
                              /\ UNCHANGED(aux_vars)

\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
\* for this action we need to verify the pin when unlocking, which is only possible
\* until the mismatchCounter reaches the MaxPinMismatch number
Unlock_After_Armed == /\ state = Armed
                      /\ mismatchCounter < MaxPinMismatch
                      /\ CheckPin(ClosedAndUnlocked)
                      /\ UNCHANGED(alarm_vars)
                      /\ UNCHANGED(timer_vars)
                      /\ UNCHANGED(aux_vars)
                      /\ UNCHANGED<<alarmTrigger>>

\* Unlock the car after an alarm was triggered (car in alarm state)
\* this ends the path for an illegal action and puts the car in the OpenAndUnlocked state,
\* deactivates the alarm and resets the alarm timer and the mismatch counter
\* (= reset cause of the alarm)
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_Alarm == /\ state = Alarm
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
                      /\ UNCHANGED(aux_vars)

\* Similar to the Unlock_After_Alarm action, but puts the car into a valid
\* state again after the alarm already turned silent, thus, the alarm was already deactivated
Unlock_After_SilentAndOpen == /\ state = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>
                              /\ UNCHANGED(aux_vars)

\* car transitioning from closed and unlocked into an armed state
\* the car should also show it is armed, so the flag is set to true to indicate that
\* the armed delay timer reached 0, so the car can be armed and the timer needs to be reset
Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED(alarm_vars)
          /\ UNCHANGED(aux_vars)
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
                 /\ UNCHANGED(timer_vars)
                 /\ UNCHANGED(aux_vars)
                 /\ UNCHANGED<<mismatchCounter>>

\* common action between both methods to exit an alarm after 5 mins of being
\* active without proper unlocking
AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to the originating state
\* since the alarm was due to too many pin mismatches
AlarmFinished_Mismatch == /\ AlarmFinished
                          /\ alarmTrigger \in AlarmTriggerStates 
                          /\ mismatchCounter = MaxPinMismatch
                          /\ alarmTrigger' = -1
                          /\ will_return_to_trigger' = TRUE
                          /\ UNCHANGED<<armedTimer>>
                          /\ IF alarmTrigger = Armed
                                THEN SetArmed
                                ELSE /\ state' = alarmTrigger
                                     /\ mismatchCounter' = 0
                                     /\ UNCHANGED<<isArmed>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to SilentAndOpen since the
\* alarm was due to an unauthorised open
AlarmFinished_Open == /\ AlarmFinished
                      /\ mismatchCounter = 0
                      /\ alarmTrigger = -1
                      /\ state' = SilentAndOpen
                      /\ will_return_to_trigger' = FALSE
                      /\ UNCHANGED<<isArmed, mismatchCounter, alarmTrigger, armedTimer>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

\* Action that allows changing the wireless key pin
\* This is possible in an unlocked state and requires the old and the new pin
\* to be provided
\* If the old (= current) pin is provided wrongly for three times, a mismatch alarm
\* will be triggered
SetNewPin == /\ state \in { OpenAndUnlocked, ClosedAndUnlocked }
             /\ mismatchCounter < MaxPinMismatch
             /\ CheckPin(state)
             /\ IF mismatchCounter' /= mismatchCounter
                    THEN increased_change_mismatch' = TRUE
                    ELSE increased_change_mismatch' = FALSE
             /\ UNCHANGED(alarm_vars)
             /\ UNCHANGED(timer_vars)
             /\ UNCHANGED<<alarmTrigger>>
             /\ UNCHANGED<<will_return_to_trigger>>

(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

\* count down of the armed timer from ArmedDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
ArmingTicker == /\ state = ClosedAndLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d
                /\ UNCHANGED(alarm_vars)
                /\ UNCHANGED(aux_vars)
                /\ UNCHANGED<<state, isArmed, alarmTimer, alarmTrigger>>
                /\ UNCHANGED<<mismatchCounter>>

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
               /\ UNCHANGED(aux_vars)
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

Spec == Init /\ [][Next]_all_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

\* action to map the mismatch counter (that is now changed somewhere else as well)
\* to the higher abstraction mismatch counter
MismatchMapping == IF increased_change_mismatch = TRUE
                       THEN 0
                       ELSE mismatchCounter

\* TODO check why triggering the alarm from set new pin fails CAS7

\* instance of the lower refinement
CarAlarmSystem7 == INSTANCE CarAlarmSystem7
    WITH mismatchCounter <- MismatchMapping,
         will_return_to_armed <- will_return_to_trigger 

\* property to check the lower refinement in the TLC
CarAlarmSystem7Spec == /\ CarAlarmSystem7!Spec
                       /\ CarAlarmSystem7!SafetyInvariant
                       /\ CarAlarmSystem7!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem7Spec
                /\ CarAlarmSpec
                /\ []Invariant

=============================================================================
