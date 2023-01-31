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
(*                                                                         *)
(* This refinement targets Requirement 5.                                  *)
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

AlarmTriggerStates ==           \* States that can trigger a change mismatch alarm
    {
        OpenAndUnlocked,
        ClosedAndUnlocked
    }

VARIABLES
    state,                      \* the current state in the state diagram
    isArmed,                    \* flag to indicate if the car is armed
    flash,                      \* flag to indicate if flash is on
    sound,                      \* flag to indicate if sound is on
    armedTimer,                 \* timer that counts from ArmedDelay to 0
    alarmTimer,                 \* timer that counts from AlarmDelay to 0
    changeMismatchCounter,      \* tracks how many wrong pins were sent to change the pin in an unlocked state
    unlockMismatchCounter,      \* tracks how many wrong pins were sent while in an armed state
                                \* or to change the pin in an unlocked state
    alarmTrigger                \* variable to keep track of the state that triggered a mismatch alarm
                                \* so we can return to it later (-1 if there is no alarm or not a mismatch alarm)

vars == 
    <<
        state,
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        alarmTrigger,
        changeMismatchCounter,
        unlockMismatchCounter
    >>
vars_without_state == 
    <<
        isArmed,
        flash,
        sound,
        armedTimer,
        alarmTimer,
        changeMismatchCounter,
        unlockMismatchCounter,
        alarmTrigger
    >>
alarm_vars == <<flash, sound>>
pin_vars   == <<alarmTrigger, changeMismatchCounter, unlockMismatchCounter>>
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
                 /\ unlockMismatchCounter \in 0..MaxPinMismatch
                 /\ alarmTrigger \in AlarmTriggerStates \union {-1}
                 /\ changeMismatchCounter \in 0..MaxPinMismatch

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
                   /\ changeMismatchCounter > 0 => state \in { Alarm, OpenAndUnlocked, ClosedAndUnlocked }
                   /\ unlockMismatchCounter > 0 => state \in { Alarm, Armed }

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* state diagram starts in the OpenAndUnlocked state
\* the car is unarmed, armed timer is set to ArmedDelay
\* alarm indicators are off (alarm is deactivated) and alarm timer is set to AlarmDelay
\* the mismatch counters start at 0
\* alarm trigger starts with a no alarm value
Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ changeMismatchCounter = 0
        /\ unlockMismatchCounter = 0
        /\ alarmTrigger = -1

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* Helper action that is called to non-deterministically check if a sent pin matches
\* and so can unlock the car or change the pin, or if the pin is incorrect
CheckPin(nextState, mismatchVar) == 
    /\ \E b \in BOOLEAN:
        IF b = TRUE
            THEN /\ state' = nextState
                 /\ isArmed' = FALSE
                 /\ mismatchVar' = 0
            ELSE /\ mismatchVar' = mismatchVar + 1
                 /\ UNCHANGED<<state, isArmed>>


\* Helper action that sets the car into an armed state
SetArmed == /\ state' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay
            /\ unlockMismatchCounter' = 0

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

\* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED(vars_without_state)

\* Close the car from the OpenAndLocked state to get to ClosedAndLocked
Close_After_OpenAndLocked == /\ state = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED(vars_without_state)

\* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
\* This arms the car again
Close_After_SilentAndOpen == /\ state = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED(timer_vars)
                             /\ UNCHANGED(pin_vars)

\* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
\* We are resetting the mismatch count here, since we are moving into a locked state
Lock_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ changeMismatchCounter' = 0
                              /\ UNCHANGED(timer_vars)
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<
                                 isArmed, 
                                 alarmTrigger, 
                                 unlockMismatchCounter>>

\* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
\* We are resetting the mismatch count here, since we are moving into a locked state
Lock_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ changeMismatchCounter' = 0
                                /\ UNCHANGED(timer_vars)
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<
                                   isArmed, 
                                   alarmTrigger, 
                                   unlockMismatchCounter>>

\* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
Open_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED(vars_without_state)

\* Open the car from the ClosedAndLocked state to get to OpenAndLocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Open_After_ClosedAndLocked == /\ state = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ armedTimer' = ArmedDelay
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED(pin_vars)
                              /\ UNCHANGED<<isArmed, alarmTimer>>

\* Open the car from an armed state
\* this is an illegal action -> trigger alarm
\* the alarm was triggered by an unauthorized open, so reset the mismatch counter
Open_After_Armed == /\ state = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ unlockMismatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<alarmTrigger, changeMismatchCounter>>

\* Lock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Unlock_After_ClosedAndLocked == /\ state = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED(pin_vars)
                                /\ UNCHANGED<<isArmed, alarmTimer>>

\* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
Unlock_After_OpenAndLocked == /\ state = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(vars_without_state)

\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
\* for this action we need to verify the pin when unlocking, which is only possible
\* until the unlockMismatchCounter reaches the MaxPinMismatch number
Unlock_After_Armed == /\ state = Armed
                      /\ unlockMismatchCounter < MaxPinMismatch
                      /\ CheckPin(ClosedAndUnlocked, unlockMismatchCounter)
                      /\ UNCHANGED(alarm_vars)
                      /\ UNCHANGED(timer_vars)
                      /\ UNCHANGED<<alarmTrigger, changeMismatchCounter>>

\* Unlock the car after an alarm was triggered (car in alarm state) due to an unauthorized open
\* This ends the path for an illegal action and puts the car in the OpenAndUnlocked state
\* additionally, it deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_OpenAlarm == /\ state = Alarm
                          /\ changeMismatchCounter = 0
                          /\ unlockMismatchCounter = 0
                          /\ state' = OpenAndUnlocked
                          /\ alarmTimer' = AlarmDelay
                          /\ CarAlarm!Deactivate
                          /\ UNCHANGED(pin_vars)
                          /\ UNCHANGED<<isArmed, armedTimer>>

\* Unlock the car after an alarm was triggered (car in alarm state) by a change pin mismatch
\* This ends the path for an illegal action and puts the car in back in the previous state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_ChangeMismatchAlarm == /\ state = Alarm
                                    /\ changeMismatchCounter = MaxPinMismatch
                                    /\ unlockMismatchCounter = 0
                                    /\ state' = alarmTrigger
                                    /\ alarmTimer' = AlarmDelay
                                    /\ changeMismatchCounter' = 0
                                    /\ alarmTrigger' = -1
                                    /\ CarAlarm!Deactivate
                                    /\ UNCHANGED<<
                                       isArmed,
                                       armedTimer,
                                       unlockMismatchCounter>>

\* Unlock the car after an alarm was triggered (car in alarm state) after an unlock pin mismatch
\* This ends the path for an illegal action and puts the car in the ClosedAndUnlocked state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_UnlockMismatchAlarm == /\ state  = Alarm
                                    /\ unlockMismatchCounter = MaxPinMismatch
                                    /\ changeMismatchCounter = 0
                                    /\ state' = ClosedAndUnlocked
                                    /\ alarmTimer' = AlarmDelay
                                    /\ unlockMismatchCounter' = 0
                                    /\ CarAlarm!Deactivate
                                    /\ UNCHANGED<<
                                       isArmed,
                                       armedTimer,
                                       alarmTrigger,
                                       changeMismatchCounter>>

\* Similar to the Unlock_After_Alarm action, but puts the car into a valid
\* state again after the alarm already turned silent, thus, the alarm was already deactivated
\* this is only possible after an unauthorized open alarm was triggered
Unlock_After_SilentAndOpen == /\ state = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(vars_without_state)

\* car transitioning from closed and unlocked into an armed state
\* the car should also show it is armed, so the flag is set to true to indicate that
\* the armed delay timer reached 0, so the car can be armed and the timer needs to be reset
Arming == /\ state = ClosedAndLocked
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED(alarm_vars)
          /\ UNCHANGED<<alarmTimer, alarmTrigger, changeMismatchCounter>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* action that triggers the car alarm after there were too many change pin attempts with
\* an invalid pin (changeMismatchCounter reached MaxPinMismatch)
ChangeMismatchAlarm == /\ state \in AlarmTriggerStates
                       /\ changeMismatchCounter = MaxPinMismatch
                       /\ alarmTrigger = -1
                       /\ alarmTrigger' = state 
                       /\ state' = Alarm
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED<<
                          changeMismatchCounter,
                          isArmed, 
                          unlockMismatchCounter>>

\* action that triggers the car alarm after there were too many unlock attempts with
\* an invalid pin (unlockMismatchCounter reached MaxPinMismatch)
UnlockMismatchAlarm == /\ state = Armed
                       /\ unlockMismatchCounter = MaxPinMismatch
                       /\ state' = Alarm
                       /\ isArmed' = FALSE
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED(pin_vars)

\* common action to exit an alarm after 5 mins of being active without proper unlocking
AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to the originating state
\* since the alarm was due to too many pin mismatches when attempting to change the pin
AlarmFinished_ChangeMismatchAlarm == /\ AlarmFinished
                                     /\ alarmTrigger \in AlarmTriggerStates 
                                     /\ changeMismatchCounter = MaxPinMismatch
                                     /\ alarmTrigger' = -1
                                     /\ state' = alarmTrigger
                                     /\ changeMismatchCounter' = 0
                                     /\ UNCHANGED<<isArmed, unlockMismatchCounter, armedTimer>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go back into an armed state
\* since the alarm was due to too many unlock attempts
AlarmFinished_UnlockMismatch == /\ AlarmFinished
                                /\ unlockMismatchCounter = MaxPinMismatch
                                /\ SetArmed
                                /\ UNCHANGED<<armedTimer,alarmTrigger, changeMismatchCounter>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to SilentAndOpen since the
\* alarm was due to an unauthorized open
AlarmFinished_Open == /\ AlarmFinished
                      /\ changeMismatchCounter = 0
                      /\ unlockMismatchCounter = 0
                      /\ state' = SilentAndOpen
                      /\ UNCHANGED(pin_vars)
                      /\ UNCHANGED<<isArmed, armedTimer>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

\* Action that allows changing the wireless key pin
\* This is possible in an unlocked state and requires the old and the new pin
\* to be provided
\* If the old (= current) pin is provided incorrectly for three times, a mismatch alarm
\* will be triggered
SetNewPin == /\ state \in AlarmTriggerStates
             /\ changeMismatchCounter < MaxPinMismatch
             /\ CheckPin(state, changeMismatchCounter)
             /\ UNCHANGED(alarm_vars)
             /\ UNCHANGED(timer_vars)
             /\ UNCHANGED<<alarmTrigger, unlockMismatchCounter>>

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
                /\ UNCHANGED(pin_vars)
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
               /\ UNCHANGED(pin_vars)
               /\ UNCHANGED<<state, isArmed, flash, armedTimer>>

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
        \/ Unlock_After_OpenAlarm
        \/ Unlock_After_ChangeMismatchAlarm
        \/ Unlock_After_UnlockMismatchAlarm
        \/ Unlock_After_SilentAndOpen
        \/ Arming
        \/ AlarmFinished_ChangeMismatchAlarm
        \/ AlarmFinished_UnlockMismatch
        \/ AlarmFinished_Open
        \/ ArmingTicker
        \/ AlarmTicker
        \/ ChangeMismatchAlarm
        \/ UnlockMismatchAlarm
        \/ SetNewPin

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

\* predicate that is true, if the car reached a mismatch alarm through a change pin mismatch
\* this was added in this refinement and needs to be mapped accordingly to the lower refinement
IsChangePinMismatchAlarm == changeMismatchCounter = MaxPinMismatch /\ state = Alarm

\* action to map the state variable value to the higher abstraction one
StateMapping == IF IsChangePinMismatchAlarm
                    THEN alarmTrigger
                    ELSE state

\* action to map the flash variable value to the higher abstraction one
FlashMapping == IF IsChangePinMismatchAlarm
                    THEN FALSE
                    ELSE flash

\* action to map the sound variable value to the higher abstraction one
SoundMapping == IF IsChangePinMismatchAlarm
                    THEN FALSE
                    ELSE sound

\* action to map the alarm timer variable value to the higher abstraction one
AlarmTickerMapping == IF IsChangePinMismatchAlarm
                          THEN AlarmDelay
                          ELSE alarmTimer

\* instance of the lower refinement
CarAlarmSystem7 == INSTANCE CarAlarmSystem7
    WITH mismatchCounter <- unlockMismatchCounter,
         state <- StateMapping,
         flash <- FlashMapping,
         sound <- SoundMapping,
         alarmTimer <- AlarmTickerMapping

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
