-------------------------- MODULE CarAlarmSystem11 --------------------------

(***************************************************************************)
(* Eleventh refinement of the car alarm system:                            *)
(*                                                                         *)
(* The eleventh refinement is the last refinement for the current state of *)
(* the car alarm system. It adds the last two requirements: automatic      *)
(* locking and unlocking of the car if the key is within or outside of a   *)
(* certain distance to the car. However, it should be possible to          *)
(* deactivate this feature. For this requirement we made two assumptions:  *)
(* 1.) Unlocking with the distance unlock feature is only possible to      *)
(* unlock the car from an armed state, and 2.) locking the car with this   *)
(* feature is only possible if the car is in an unarmed state. Furthermore,*)
(* deactivating the feature is done in the config. This is the equivalent  *)
(* of needing to (de)activate that feature not during runtime, but when    *)
(* configuring the car and it will only be functional after a restart of   *)
(* the system.                                                             *)
(*                                                                         *)
(* This refinement targets Requirements 10 and 11.                         *)
(***************************************************************************)

EXTENDS Integers

CONSTANT
    ArmedDelay,                         \* Time the car takes to switch into an armed state after
                                        \* it was locked (here: time to change the state from
                                        \* ClosedAndLocked to Armed)
    SoundDuration,                      \* Time duration specifying how long the alarm sound should be on
                                        \* when the car is in an alarm state
    AlarmDelay,                         \* Time the car remains in a non-silent alarm state
                                        \* (here: time where flash and sound or only flash are on)
    MaxPinMismatch,                     \* Max. count until a pin mismatch alarm is triggered
                                        \* (here: how often can a key send a wrong pin)
    DoorCount,                          \* Amount of the car's passenger doors
    MaxPins,                            \* Number of currently usable pins; Equivalent to the number of keys
    IsDistanceActive                    \* Flag that indicates if the distance locking and unlocking mechanism
                                        \* is enabled or disabled

ASSUME ArmedDelay \in Nat               \* ArmedDelay is set in the TLC, 20 sec by requirement
ASSUME AlarmDelay \in Nat               \* AlarmDelay is set in the TLC, 300 sec by requirement (=5 min)
ASSUME MaxPinMismatch \in Nat           \* MaxPinMismatch is set in the TLC, 3 tries by requirement
ASSUME MaxPins \in Nat                  \* MaxPins is set in the TLC, requirement does not specify a specific number
ASSUME SoundDuration \in Nat            \* SoundDuration is set in the TLC, 30 sec by requirement
ASSUME SoundDuration <= AlarmDelay      \* SoundDuration needs to be less or equal to the active alarm duration
ASSUME IsDistanceActive \in BOOLEAN     \* IsDistanceActive is set in the TLC to enable or disable the feature

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
Unarmed           == 7                  \* Car is in an unarmed state and can be arbitrarily locked/unlocked and opened/closed
 
ALARM_SYSTEM_STATES ==                  \* states connected to the alarm system
    {
        Armed, 
        Alarm, 
        SilentAndOpen,
        Unarmed
    }
    
VARIABLES
    alarmSystemState,                   \* variable holding the current state of the alarm system
    passengerAreaState,                 \* variable holding the current state of the passenger area module
    passengerDoors,                     \* tuple representing the passenger doors
                                        \* consists of an index and a bool flag indicating
                                        \* if the door is open (flag is true), or closed (flag is false)
    trunkState,                         \* variable holding the current state of the trunk module
    isArmed,                            \* flag to indicate if the car is armed
    flash,                              \* flag to indicate if flash is on
    sound,                              \* flag to indicate if sound is on
    armedTimer,                         \* timer that counts from ArmedDelay to 0
    alarmTimer,                         \* timer that counts from AlarmDelay to 0
    changeMismatchCounters,             \* tracks how many wrong pins were sent to change the pin in an unlocked state
    unlockMismatchCounters,             \* tracks how many wrong pins were sent while in an armed state to unlock the car
    trunkUnlockMismatchCounters         \* tracks how many wrong pins were sent while in an armed state to unlock the trunk alone

vars == 
    <<
        alarmSystemState,
        passengerAreaState, 
        passengerDoors, 
        trunkState,
        isArmed, 
        flash, 
        sound, 
        armedTimer, 
        alarmTimer,
        changeMismatchCounters,
        unlockMismatchCounters,
        trunkUnlockMismatchCounters
    >>

alarm_vars == <<flash, sound>>
car_vars   == <<passengerAreaState, passengerDoors, trunkState>>
pin_vars   == <<changeMismatchCounters, unlockMismatchCounters, trunkUnlockMismatchCounters>>
timer_vars == <<armedTimer, alarmTimer>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

Car == INSTANCE Car1                \* Refinement mapping through equal var names
CarAlarm == INSTANCE CarAlarm1      \* Refinement mapping through equal var names
Pins == INSTANCE Pins1              \* Refinement mapping through equal var names

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ alarmSystemState \in ALARM_SYSTEM_STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ Car!TypeInvariant
                 /\ CarAlarm!TypeInvariant
                 /\ Pins!TypeInvariant

\* the armed timer should be reset to the ArmedDelay when reaching this state
\* if the car is in an armed state indicate that by setting the isArmed flag
\* the car state should be ClosedAndLocked
\* the trunk can be unlocked in the armed state
ArmedInvariant == /\ armedTimer = ArmedDelay 
                  /\ isArmed = TRUE
                  /\ passengerAreaState = ClosedAndLocked
                  /\ ~(Car!IsTrunkOpen /\ Car!IsTrunkLocked)

\* if the alarm is on, sound and flash should be on during sound duration
\* afterwards, only the flash should be on and the sound off
\* if the alarm is on and was triggered by any mismatch, all doors should still be closed
\* if not, any of the doors need to be open since it was an unauthorized open alarm
AlarmInvariant == /\ flash = TRUE
                  /\ IF Pins!IsAnyMaxMismatch
                         THEN /\ \/ Car!IsCarUnlocked
                                 \/ passengerAreaState = ClosedAndLocked
                         ELSE /\ \/ Car!AreDoorsOpen
                                 \/ /\ Car!IsTrunkOpen 
                                    /\ Car!IsTrunkLocked
                  /\ IF alarmTimer >= AlarmDelay - SoundDuration
                         THEN sound = TRUE
                         ELSE sound = FALSE

\* in an alarm state the AlarmInvariants should hold, in an armed state the ArmedInvariant
\* the safety invariant for the doors needs to hold for the car alarm system safety invariant to hold
\* if the doors are closed, the car has to be in a closed state (not in an open state)
\* the armed timer should only change when the passenger area is closed and locked
\* the alarm timer should only change when the car is in an alarm state
SafetyInvariant == /\ alarmSystemState = Alarm => AlarmInvariant
                   /\ alarmSystemState = Armed => ArmedInvariant
                   /\ passengerAreaState /= ClosedAndLocked => armedTimer = ArmedDelay
                   /\ alarmSystemState /= Alarm => alarmTimer = AlarmDelay
                   /\ Car!SafetyInvariant
                   /\ CarAlarm!SafetyInvariant

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* alarm system starts in an unarmed state
\* the car is unarmed, armed timer is set to ArmedDelay
\* alarm indicators are off (alarm is deactivated) and alarm timer is set to AlarmDelay
\* the car module and pins module need to be initialized
Init == /\ alarmSystemState = Unarmed
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ Car!Init
        /\ Pins!Init

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* Helper action that sets the car into an armed state
SetArmed == /\ alarmSystemState' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay

\* Helper action that deactivates the alarm after the car was in an alarm state
AlarmFinished == /\ alarmSystemState = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* Action that calls the car module's next action if the alarm system is unarmed
\* and there is no pin mismatch
UnarmedCarActions == /\ alarmSystemState = Unarmed
                     /\ ~Pins!IsChangeMaxMismatch
                     /\ \/ /\ \/ Car!DoorActions
                              \/ Car!OpenTrunk
                              \/ Car!CloseTrunk
                              \/ Car!UnlockTrunk
                              \/ Car!UnlockCar
                           /\ UNCHANGED<<changeMismatchCounters>>
                        \/ /\ \/ Car!LockTrunk
                              \/ Car!LockCar
                           /\ Pins!ResetChangeCounters
                     /\ armedTimer' = ArmedDelay
                     /\ UNCHANGED(alarm_vars)
                     /\ UNCHANGED<<
                        alarmSystemState,
                        alarmTimer,
                        isArmed,
                        unlockMismatchCounters,
                        trunkUnlockMismatchCounters>>

\* Action combining the possible actions on the car's trunk
\* when the alarm system is in an armed state
ArmedTrunkActions == /\ alarmSystemState = Armed
                     /\ ~Pins!IsAnyMaxMismatch
                     /\ \/ /\ Car!IsTrunkUnlocked
                           /\ \/ Car!OpenTrunk
                              \/ Car!CloseTrunk
                              \/ /\ Car!IsTrunkClosed 
                                 /\ Car!LockTrunk
                           /\ UNCHANGED<<trunkUnlockMismatchCounters>>      
                        \/ /\ Car!IsTrunkLocked
                           /\ Pins!CheckTrunkUnlockMismatchCounters(
                              Car!UnlockTrunk,
                              UNCHANGED(car_vars))
                 /\ UNCHANGED(alarm_vars)
                 /\ UNCHANGED(timer_vars)
                 /\ UNCHANGED<<
                    alarmSystemState,
                    isArmed,
                    changeMismatchCounters,
                    unlockMismatchCounters>>

\* Action combining the possible car actions
CarActions == \/ UnarmedCarActions
              \/ ArmedTrunkActions

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

\* Action that allows changing the wireless key pin
\* This is possible in an unlocked state and requires the old and the new pin
\* to be provided
\* If the old (= current) pin is provided wrongly for three times, a mismatch alarm
\* will be triggered
SetNewPin == /\ Car!IsCarUnlocked
             /\ Pins!CheckChangeMismatchCounter(TRUE, TRUE)
             /\ UNCHANGED(alarm_vars)
             /\ UNCHANGED(car_vars)
             /\ UNCHANGED(timer_vars)
             /\ UNCHANGED<<
                alarmSystemState,
                isArmed,
                unlockMismatchCounters,
                trunkUnlockMismatchCounters>>

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

\* car transitioning from closed and unlocked into an armed state
\* the car should also show it is armed, so the flag is set to true to indicate that
\* the armed delay timer reached 0, so the car can be armed and the timer needs to be reset
Arming == /\ Car!IsCarLocked
          /\ Car!IsCarClosed
          /\ armedTimer = 0
          /\ SetArmed
          /\ Pins!ResetUnlockCounters
          /\ Pins!ResetTrunkCounters
          /\ UNCHANGED(alarm_vars)
          /\ UNCHANGED(car_vars)
          /\ UNCHANGED<<
            alarmTimer,
            changeMismatchCounters>>

\* Open the car from an armed state
\* this is an illegal action -> trigger alarm
\* the alarm was triggered by an unauthorized open, so reset the mismatch counters
Open_After_Armed == /\ alarmSystemState = Armed
                    /\ passengerAreaState = ClosedAndLocked
                    /\ alarmSystemState' = Alarm
                    /\ isArmed' = FALSE
                    /\ \/ Car!OpenDoor_From_Closed
                       \/ /\ Car!IsTrunkLocked
                          /\ Car!IsTrunkClosed
                          /\ Car!OpenTrunk
                    /\ CarAlarm!Activate
                    /\ Pins!ResetUnlockCounters
                    /\ Pins!ResetTrunkCounters
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<changeMismatchCounters>>

\* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
\* this tries to close the doors in the door module and arms the car again if all doors are closed
Close_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                             /\ \/ Car!CloseDoor
                                \/ Car!CloseTrunk
                             /\ IF /\ \A pd \in passengerDoors' : pd[2] = FALSE
                                   /\ trunkState' \in {ClosedAndLocked, ClosedAndUnlocked}
                                    THEN SetArmed
                                    ELSE /\ UNCHANGED(alarm_vars)
                                         /\ UNCHANGED<<alarmSystemState, armedTimer, isArmed>>
                             /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED(pin_vars)
                             /\ UNCHANGED<<alarmTimer>>

\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
\* for this action we need to verify the pin when unlocking, which is only possible
\* until the mismatchCounter reaches the MaxPinMismatch number
Unlock_After_Armed == /\ alarmSystemState = Armed
                      /\ ~Pins!IsAnyMaxMismatch
                      /\ Car!IsTrunkClosed
                      /\ Pins!CheckUnlockMismatchCounter(
                         /\ Car!UnlockCar
                         /\ alarmSystemState' = Unarmed
                         /\ isArmed' = FALSE
                         /\ Pins!ResetTrunkCounters
                         ,
                         /\ UNCHANGED<<
                            passengerAreaState, 
                            trunkState, 
                            alarmSystemState, 
                            isArmed,
                            trunkUnlockMismatchCounters>>)
                      /\ UNCHANGED(alarm_vars)
                      /\ UNCHANGED(timer_vars)
                      /\ UNCHANGED<<
                         passengerDoors,
                         changeMismatchCounters>>

\* Similar to the Unlock_After_Alarm action, but puts the car into a valid
\* state again after the alarm already turned silent, thus, the alarm was already deactivated
\* this is only possible after an unauthorized open alarm was triggered
Unlock_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                              /\ alarmSystemState' = Unarmed
                              /\ Car!UnlockCar
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED(pin_vars)
                              /\ UNCHANGED(timer_vars)
                              /\ UNCHANGED<<isArmed, passengerDoors>>

(***************************************************************************)
(* Locking and unlocking based on distance from car to key                 *)
(***************************************************************************)

\* Locks the car if the key is a specific distance away from the car automatically
\* This is only possible when the car is in an unarmed state and will set the car
\* into an arming state
\* for the model, it is non-deterministically decided if the key is within or outside
\* of the locking distance
DistanceLocking == /\ IsDistanceActive
                   /\ alarmSystemState = Unarmed
                   /\ ~Pins!IsChangeMaxMismatch
                   /\ \E bool \in BOOLEAN:
                      IF bool
                      THEN /\ Car!LockCar
                           /\ Pins!ResetChangeCounters
                           /\ armedTimer' = ArmedDelay
                      ELSE /\ UNCHANGED(car_vars)
                           /\ UNCHANGED<<changeMismatchCounters>>
                   /\ UNCHANGED(alarm_vars)
                   /\ UNCHANGED(timer_vars)
                   /\ UNCHANGED<<
                        alarmSystemState,
                        isArmed,
                        unlockMismatchCounters,
                        trunkUnlockMismatchCounters>>

\* unlocks the car if a correct key is within a specific distance to the car
\* this unlock is only possible when the car is in an armed state, since enabling it
\* in an unarmed state would result in an odd automatic locking/unlocking behavior
\* For this unlock method no pin is required (different type of unlocking), the car 
\* must recognize that it is a proper key by some other implementation specific mean
\* for the model, it is non-deterministically decided if the key is within or outside
\* of the unlocking distance
DistanceUnlocking == /\ IsDistanceActive
                     /\ alarmSystemState = Armed
                     /\ ~Pins!IsAnyMaxMismatch
                     /\ Car!IsTrunkClosed
                     /\ \E bool \in BOOLEAN:
                        IF bool
                        THEN /\ Car!UnlockCar
                             /\ alarmSystemState' = Unarmed
                             /\ isArmed' = FALSE
                             /\ Pins!ResetUnlockCounters
                             /\ Pins!ResetTrunkCounters
                        ELSE /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED(car_vars)
                             /\ UNCHANGED(pin_vars)
                             /\ UNCHANGED<<alarmSystemState, isArmed>>
                     /\ UNCHANGED(alarm_vars)
                     /\ UNCHANGED(timer_vars)
                     /\ UNCHANGED<<
                         passengerDoors,
                         changeMismatchCounters>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* action that triggers the car alarm after there were too many change pin attempts with
\* an invalid pin (changeMismatchCounter reached MaxPinMismatch)
ChangeMismatchAlarm == /\ alarmSystemState = Unarmed
                       /\ Pins!IsChangeMaxMismatch
                       /\ alarmSystemState' = Alarm
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(car_vars)
                       /\ UNCHANGED(pin_vars)
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED<<isArmed>>

\* action that triggers the car alarm after there were too many unlock attempts with
\* an invalid pin (unlockMismatchCounter reached MaxPinMismatch)
UnlockMismatchAlarm == /\ alarmSystemState = Armed
                       /\ Pins!IsUnlockMaxMismatch
                       /\ alarmSystemState' = Alarm
                       /\ isArmed' = FALSE
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(car_vars)
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED(pin_vars)

\* action that triggers the car alarm after there were too many unlock trunk attempts with
\* an invalid pin (trunkUnlockMismatchCounter reached MaxPinMismatch)
TrunkUnlockMismatchAlarm == /\ alarmSystemState = Armed
                            /\ Pins!IsTrunkMaxMismatch
                            /\ alarmSystemState' = Alarm
                            /\ isArmed' = FALSE
                            /\ CarAlarm!Activate
                            /\ UNCHANGED(car_vars)
                            /\ UNCHANGED(timer_vars)
                            /\ UNCHANGED(pin_vars)

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to the originating state
\* since the alarm was due to too many pin mismatches when attempting to change the pin
AlarmFinished_ChangeMismatchAlarm == /\ AlarmFinished
                                     /\ Pins!IsChangeMaxMismatch
                                     /\ alarmSystemState' = Unarmed
                                     /\ Pins!ResetChangeCounters
                                     /\ UNCHANGED<<
                                        isArmed,
                                        car_vars,
                                        unlockMismatchCounters, 
                                        trunkUnlockMismatchCounters, 
                                        armedTimer>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go back into an armed state
\* since the alarm was due to too many unlock attempts
AlarmFinished_UnlockMismatch == /\ AlarmFinished
                                /\ Pins!IsUnlockMaxMismatch
                                /\ SetArmed
                                /\ Pins!ResetUnlockCounters
                                /\ UNCHANGED(car_vars)
                                /\ UNCHANGED<<
                                   armedTimer,
                                   changeMismatchCounters,
                                   trunkUnlockMismatchCounters>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go back into an armed state
\* since the alarm was due to too many unlock trunk attempts
AlarmFinished_TrunkUnlockMismatch == /\ AlarmFinished
                                     /\ Pins!IsTrunkMaxMismatch
                                     /\ SetArmed
                                     /\ Pins!ResetTrunkCounters
                                     /\ UNCHANGED(car_vars)
                                     /\ UNCHANGED<<
                                        armedTimer,
                                        changeMismatchCounters,
                                        unlockMismatchCounters>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to SilentAndOpen since the
\* alarm was due to an unauthorized open
AlarmFinished_Open == /\ AlarmFinished
                      /\ Pins!IsNoMismatch
                      /\ alarmSystemState' = SilentAndOpen
                      /\ UNCHANGED(car_vars)
                      /\ UNCHANGED(pin_vars)
                      /\ UNCHANGED<<isArmed, armedTimer>>

\* Unlock the car after an alarm was triggered (car in alarm state) due to an unauthorized open
\* This ends the path for an illegal action and puts the alarm system in an unarmed state and the
\* car (passenger area and trunk) into the OpenAndUnlocked state
\* additionally, it deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_OpenAlarm == /\ alarmSystemState = Alarm
                          /\ Pins!IsNoMismatch
                          /\ Car!UnlockCar
                          /\ CarAlarm!Deactivate
                          /\ alarmSystemState' = Unarmed
                          /\ alarmTimer' = AlarmDelay
                          /\ UNCHANGED(pin_vars)
                          /\ UNCHANGED<<isArmed, armedTimer, passengerDoors>>

\* Unlock the car after an alarm was triggered (car in alarm state) by a change pin mismatch
\* This ends the path for an illegal action and puts the alarm system in an unarmed state and
\* the car in back in the previous state, resets the mismatch counter and deactivates the alarm
\* and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_ChangeMismatchAlarm == /\ alarmSystemState = Alarm
                                    /\ Pins!IsChangeMaxMismatch
                                    /\ Pins!IsUnlockNoMismatch
                                    /\ Pins!IsTrunkNoMismatch
                                    /\ Car!IsCarUnlocked
                                    /\ CarAlarm!Deactivate
                                    /\ alarmSystemState' = Unarmed
                                    /\ alarmTimer' = AlarmDelay
                                    /\ Pins!ResetChangeCounters
                                    /\ UNCHANGED(car_vars)
                                    /\ UNCHANGED<<
                                       isArmed,
                                       armedTimer,
                                       passengerDoors,
                                       unlockMismatchCounters,
                                       trunkUnlockMismatchCounters>>

\* Unlock the car after an alarm was triggered (car in alarm state) after an unlock pin mismatch
\* This ends the path for an illegal action and puts the alarm system in an unarmed state and the
\* car (passenger area and trunk) into the ClosedAndUnlocked state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_UnlockMismatchAlarm == /\ alarmSystemState = Alarm
                                    /\ Pins!IsUnlockMaxMismatch
                                    /\ Pins!IsChangeNoMismatch
                                    /\ ~Pins!IsTrunkMaxMismatch
                                    /\ Car!UnlockCar
                                    /\ CarAlarm!Deactivate
                                    /\ alarmSystemState' = Unarmed
                                    /\ alarmTimer' = AlarmDelay
                                    /\ Pins!ResetUnlockCounters
                                    /\ Pins!ResetTrunkCounters
                                    /\ UNCHANGED<<
                                       isArmed,
                                       passengerDoors,
                                       armedTimer,
                                       changeMismatchCounters>>

\* Unlock the car after an alarm was triggered (car in alarm state) after an unlock trunk pin mismatch
\* This ends the path for an illegal action and puts the alarm system in an unarmed state and the
\* car (passenger area and trunk) into the ClosedAndUnlocked state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_TrunkUnlockMismatchAlarm == /\ alarmSystemState = Alarm
                                         /\ Pins!IsTrunkMaxMismatch
                                         /\ ~Pins!IsUnlockMaxMismatch
                                         /\ Pins!IsChangeNoMismatch
                                         /\ Car!UnlockCar
                                         /\ CarAlarm!Deactivate
                                         /\ alarmSystemState' = Unarmed
                                         /\ alarmTimer' = AlarmDelay
                                         /\ Pins!ResetUnlockCounters
                                         /\ Pins!ResetTrunkCounters
                                         /\ UNCHANGED<<
                                            isArmed,
                                            passengerDoors,
                                            armedTimer,
                                            changeMismatchCounters>>

(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

\* count down of the armed timer from ArmedDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
ArmingTicker == /\ alarmSystemState = Unarmed
                /\ Car!IsCarClosed
                /\ Car!IsCarLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d
                /\ UNCHANGED(alarm_vars)
                /\ UNCHANGED(car_vars)
                /\ UNCHANGED(pin_vars)
                /\ UNCHANGED<<alarmSystemState, alarmTimer, isArmed>>

\* count down of the alarm timer from AlarmDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
\* once the alarm timer leaves the sound range (timer < AlarmDelay - SoundDuration)
\* the sound is deactivated and only the flash continues
AlarmTicker == /\ alarmSystemState = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < AlarmDelay - SoundDuration
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED(car_vars)
               /\ UNCHANGED(pin_vars)
               /\ UNCHANGED<<
                  alarmSystemState,
                  isArmed,
                  flash,
                  armedTimer>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ CarActions
        \/ Close_After_SilentAndOpen
        \/ Open_After_Armed
        \/ Unlock_After_Armed
        \/ Unlock_After_OpenAlarm
        \/ Unlock_After_ChangeMismatchAlarm
        \/ Unlock_After_UnlockMismatchAlarm
        \/ Unlock_After_TrunkUnlockMismatchAlarm
        \/ Unlock_After_SilentAndOpen
        \/ Arming
        \/ AlarmFinished_ChangeMismatchAlarm
        \/ AlarmFinished_UnlockMismatch
        \/ AlarmFinished_TrunkUnlockMismatch
        \/ AlarmFinished_Open
        \/ ArmingTicker
        \/ AlarmTicker
        \/ ChangeMismatchAlarm
        \/ UnlockMismatchAlarm
        \/ TrunkUnlockMismatchAlarm
        \/ SetNewPin
        \/ DistanceLocking
        \/ DistanceUnlocking

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

\* instance of the lower refinement
CarAlarmSystem10 == INSTANCE CarAlarmSystem10

\* property to check the lower refinement in the TLC
CarAlarmSystem10Spec == /\ CarAlarmSystem10!Spec
                        /\ CarAlarmSystem10!SafetyInvariant
                        /\ CarAlarmSystem10!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

\* check that the car module also holds in the TLC
CarSpec == /\ Car!SafetyInvariant
           /\ Car!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem10Spec
                /\ CarAlarmSpec
                /\ CarSpec
                /\ []Invariant

=============================================================================
