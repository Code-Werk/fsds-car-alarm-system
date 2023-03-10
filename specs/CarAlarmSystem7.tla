-------------------------- MODULE CarAlarmSystem7 --------------------------

(***************************************************************************)
(* Seventh refinement of the car alarm system:                             *)
(*                                                                         *)
(* The seventh refinement adds the possibility to unlock the car using a   *)
(* wireless method by sending a pin. The car should unlock as previously   *)
(* when a correct pin is sent. In armed, the alarm should be triggered when*)
(* a wrong pin is provided for three times. This behavior was implemented  *)
(* here. Now there are two slightly different alarm states - mismatch and  *)
(* unauthorized open. They can both be deactivated via a physical unlock   *)
(* (physically turn key, no wireless unlocking possible), or they leave    *)
(* automatically after 5 mins (either into SilentAndOpen or back to Armed).*)
(*                                                                         *)
(* This refinement targets Requirement 4.                                  *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT
    ArmedDelay,                         \* Time the car takes to switch into an armed state after
                                        \* it was locked (here: time to change the state from
                                        \* ClosedAndLocked to Armed)
    SoundDuration,                      \* Time duration specifying how long the alarm sound should be on
                                        \* when the car is in an alarm state
    AlarmDelay,                         \* Time the car remains in a non-silent alarm state
                                        \* (here: time where flash and sound or only flash are on)
    MaxPinMismatch                      \* Max. count until a pin mismatch alarm is triggered
                                        \* (here: how often can a key send a wrong pin)
ASSUME ArmedDelay \in Nat               \* ArmedDelay is set in the TLC, 20 sec by requirement
ASSUME AlarmDelay \in Nat               \* AlarmDelay is set in the TLC, 300 sec by requirement (=5 min)
ASSUME MaxPinMismatch \in Nat           \* MaxPinMismatch is set in the TLC, 3 tries by requirement
ASSUME SoundDuration \in Nat            \* SoundDuration is set in the TLC, 30 sec by requirement
ASSUME SoundDuration <= AlarmDelay      \* SoundDuration needs to be less or equal to the active alarm duration

ArmedRange == 0..ArmedDelay             \* Range for the armed timer, it counts down from the 
                                        \* max value (= ArmedDelay) to 0
AlarmRange == 0..AlarmDelay             \* Range for the alarm timer, it counts down from the max
                                        \* value (= AlarmDelay) to 0

OpenAndUnlocked   == 0                  \* Car is open and unlocked
ClosedAndLocked   == 1                  \* Car is closed and locked
OpenAndLocked     == 2                  \* Car is still open but already locked
ClosedAndUnlocked == 3                  \* Car is not yet closed but already locked
Armed             == 4                  \* Car alarm system is armed (which means it is locked and
                                        \* closed and alarm could be triggered)
Alarm             == 5                  \* Car alarm is on (which means an illegal action
                                        \* - car opened without unlocking -
                                        \* occurred in the armed state and the alarm was triggered)
SilentAndOpen     == 6                  \* Car has been in alarm (or technically still is, but no
                                        \* flash and sound is on) but is now waiting to return to
                                        \* armed or unlocked (car is closed again or unlocked)

STATES ==                               \* Currently possible states
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
    state,                              \* the current state in the state diagram
    isArmed,                            \* flag to indicate if the car is armed
    flash,                              \* flag to indicate if flash is on
    sound,                              \* flag to indicate if sound is on
    armedTimer,                         \* timer that counts from ArmedDelay to 0
    alarmTimer,                         \* timer that counts from AlarmDelay to 0
    mismatchCounter                     \* tracks how many wrong pins were sent while in an armed state

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

\* if the alarm is on, sound and flash should be on during sound duration
\* afterwards, only the flash should be on and the sound off
\* if the car is in an armed state indicate that by setting the isArmed flag
\* the armed timer should be reset to the ArmedDelay when reaching this state
\* the only state where the armed timer should change is ClosedAndLocked, otherwise it's set to ArmedDelay
SafetyInvariant == /\ state = Alarm => flash = TRUE
                   /\ IF state = Alarm /\ alarmTimer >= AlarmDelay - SoundDuration
                          THEN sound = TRUE
                          ELSE sound = FALSE
                   /\ state = Armed
                        => armedTimer = ArmedDelay /\ isArmed = TRUE
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

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* Helper action that is called to non-deterministically check if a sent pin matches
\* and so can unlock the car or if the pin is incorrect
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
                             /\ UNCHANGED<<mismatchCounter>>

\* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
Lock_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED(vars_without_state)

\* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
Lock_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED(vars_without_state)

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
                              /\ UNCHANGED<<isArmed, alarmTimer, mismatchCounter>>

\* Open the car from an armed state
\* this is an illegal action -> trigger alarm
\* the alarm was triggered my an unauthorized open, so reset the mismatch counter
Open_After_Armed == /\ state = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter' = 0
                    /\ CarAlarm!Activate
                    /\ UNCHANGED(timer_vars)

\* Lock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
\* reset the timer to ArmedDelay, since we are not counting down anymore in this state
\* this is set when leaving ClosedAndLocked mainly to avoid unnecessary states in TLC
Unlock_After_ClosedAndLocked == /\ state = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed, alarmTimer, mismatchCounter>>

\* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
Unlock_After_OpenAndLocked == /\ state = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(vars_without_state)

\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
\* for this action we need to verify the pin when unlocking, which is only possible
\* until the mismatchCounter reaches the MaxPinMismatch number
Unlock_After_Armed == /\ state = Armed
                      /\ mismatchCounter < MaxPinMismatch
                      /\ CheckPin(ClosedAndUnlocked)
                      /\ UNCHANGED(alarm_vars)
                      /\ UNCHANGED(timer_vars)



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
          /\ UNCHANGED<<alarmTimer>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* action that triggers the car alarm after there were too many unlock attempts with
\* an invalid pin (mismatchCounter reached MaxPinMismatch)
\* transition from an armed state into the alarm state (alarm is activated)
MismatchAlarm == /\ state = Armed
                 /\ mismatchCounter = MaxPinMismatch
                 /\ state' = Alarm
                 /\ isArmed' = FALSE
                 /\ CarAlarm!Activate
                 /\ UNCHANGED(timer_vars)
                 /\ UNCHANGED<<mismatchCounter>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to SilentAndOpen if the
\* alarm was due to an unauthorized open or to Armed if it was a mismatch alarm
\* we also set the prophecy will_return_to_armed variable, so the transitions are
\* distinct and we can refinement check it (the less abstract refinement only knows
\* the way to SilentAndOpen to get out of the alarm after a timeout)
AlarmFinished == /\ state = Alarm
                 /\ alarmTimer = 0
                 /\ alarmTimer' = AlarmDelay
                 /\ CarAlarm!Deactivate
                 /\ UNCHANGED<<armedTimer>>
                 /\ IF mismatchCounter = MaxPinMismatch
                        THEN /\ SetArmed
                        ELSE /\ state' = SilentAndOpen
                             /\ UNCHANGED<<isArmed, mismatchCounter>>

\* Unlock the car after an alarm was triggered (car in alarm state) due to an unauthorized open
\* This ends the path for an illegal action and puts the car in the OpenAndUnlocked state
\* additionally, it deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_OpenAlarm == /\ state = Alarm
                          /\ mismatchCounter = 0
                          /\ state' = OpenAndUnlocked
                          /\ alarmTimer' = AlarmDelay
                          /\ mismatchCounter' = 0
                          /\ CarAlarm!Deactivate
                          /\ UNCHANGED<<isArmed, armedTimer>>

\* Unlock the car after an alarm was triggered (car in alarm state) after an unlock pin mismatch
\* This ends the path for an illegal action and puts the car in the ClosedAndUnlocked state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_MismatchAlarm == /\ state = Alarm
                              /\ mismatchCounter = MaxPinMismatch
                              /\ state' = ClosedAndUnlocked
                              /\ alarmTimer' = AlarmDelay
                              /\ mismatchCounter' = 0
                              /\ CarAlarm!Deactivate
                              /\ UNCHANGED<<isArmed, armedTimer>>

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
                /\ UNCHANGED<<state, isArmed, alarmTimer>>
                /\ UNCHANGED<<mismatchCounter>>

\* count down of the alarm timer from AlarmDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
\* once the alarm timer leaves the sound range (timer < AlarmDelay - SoundDuration)
\* the sound is deactivated and only the flash continues
AlarmTicker == /\ state = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < AlarmDelay - SoundDuration
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
        \/ Unlock_After_MismatchAlarm
        \/ Unlock_After_OpenAlarm
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

\* predicate that is true, if the car reached the alarm state through a mismatch
\* this was added in this refinement and needs to be mapped accordingly to the lower refinement
IsMismatchAlarm == mismatchCounter = MaxPinMismatch /\ state = Alarm

\* action to map the state variable value to the higher abstraction one
StateMapping == IF IsMismatchAlarm
                    THEN Armed
                    ELSE state

\* action to map the flash variable value to the higher abstraction one
FlashMapping == IF IsMismatchAlarm
                    THEN FALSE
                    ELSE flash

\* action to map the sound variable value to the higher abstraction one
SoundMapping == IF IsMismatchAlarm
                    THEN FALSE
                    ELSE sound

\* action to map the alarm timer variable value to the higher abstraction one
AlarmTickerMapping == IF IsMismatchAlarm
                          THEN AlarmDelay
                          ELSE alarmTimer

\* action to map the is armed flag value to the higher abstraction one
IsArmedMapping == IF IsMismatchAlarm
                      THEN TRUE
                      ELSE isArmed

\* instance of the lower refinement
CarAlarmSystem6 == INSTANCE CarAlarmSystem6
    WITH state <- StateMapping,
         flash <- FlashMapping,
         sound <- SoundMapping,
         alarmTimer <- AlarmTickerMapping,
         isArmed <- IsArmedMapping

\* property to check the lower refinement in the TLC
CarAlarmSystem6Spec == /\ CarAlarmSystem6!Spec
                       /\ CarAlarmSystem6!SafetyInvariant
                       /\ CarAlarmSystem6!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem6Spec
                /\ CarAlarmSpec
                /\ []Invariant

=============================================================================
