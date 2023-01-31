-------------------------- MODULE CarAlarmSystem9 --------------------------

(***************************************************************************)
(* Ninth refinement of the car alarm system:                               *)
(*                                                                         *)
(* This refinement adds the two requirements connected to the car's doors  *)
(* refinement. These state that a car should have either 2 or 4 passenger  *)
(* doors and a trunk. The car state now only is closed and ready to be     *)
(* armed, if all doors and the trunk are closed. Doors can now be opened   *)
(* individually. In the armed state, the trunk can be unlocked and opened  *)
(* without triggering the alarm in the armed state (If the trunk is opened *)
(* without being unlocked before, this is still an illegal action!).       *)
(* This refinement uses the car and the door modules to achieve the new    *)
(* requirements.                                                           *)
(*                                                                         *)
(* This refinement targets Requirements 6 and 7.                           *)
(***************************************************************************)

EXTENDS Integers

CONSTANT
    ArmedDelay,                     \* Time the car takes to switch into an armed state after 
                                    \* it was locked (here: time to change the state from 
                                    \* ClosedAndLocked to Armed)
    AlarmDelay,                     \* Time the car remains in a non-silent alarm state 
                                    \* (here: time where flash and sound or only flash are on)
    MaxPinMismatch,                 \* Max. count until a pin mismatch alarm is triggered 
                                    \* (here: how often can a key send a wrong pin)
    DoorCount                       \* Amount of the car's passenger doors
ASSUME ArmedDelay \in Nat           \* ArmedDelay is set in the TLC, 20 sec by requirement
ASSUME AlarmDelay \in Nat           \* AlarmDelay is set in the TLC, 300 sec by requirement (=5 min)
ASSUME MaxPinMismatch \in Nat       \* MaxPinMismatch is set in the TLC, 3 tries by requirement

ArmedRange == 0..ArmedDelay         \* Range for the armed timer, it counts down from the 
                                    \* max value (= ArmedDelay) to 0
AlarmRange == 0..AlarmDelay         \* Range for the alarm timer, it counts down from the max
                                    \* value (= AlarmDelay) to 0

OpenAndUnlocked   == 0              \* Car is open and unlocked
ClosedAndLocked   == 1              \* Car is closed and locked
OpenAndLocked     == 2              \* Car is still open but already locked
ClosedAndUnlocked == 3              \* Car is not yet closed but already locked

Armed             == 4              \* Car alarm system is armed (which means it is locked and
                                    \*  closed and alarm could be triggered)
Alarm             == 5              \* Car alarm is on (which means an illegal action 
                                    \* - car opened without unlocking - 
                                    \* occurred in the armed state and the alarm was triggered)
SilentAndOpen     == 6              \* Car has been in alarm (or technically still is, but no
                                    \* flash and sound is on) but is now waiting to return to 
                                    \* armed or unlocked (car is closed again or unlocked)
Unarmed           == 7              \* Car is in an unarmed state and can be arbitrarily locked/unlocked and opened/closed
 
ALARM_SYSTEM_STATES ==              \* states connected to the alarm system
    {
        Armed,
        Alarm,
        SilentAndOpen,
        Unarmed
    }
    
VARIABLES
    alarmSystemState,               \* variable holding the current state of the alarm system
    passengerAreaState,             \* variable holding the current state of the passenger area module
    passengerDoors,                 \* tuple representing the passenger doors
                                    \* consists of an index and a bool flag indicating
                                    \* if the door is open (flag is true), or closed (flag is false)
    trunkState,                     \* variable holding the current state of the trunk module
    changeMismatchCounter,          \* tracks how many wrong pins were sent to change the pin in an unlocked state
    unlockMismatchCounter,          \* tracks how many wrong pins were sent while in an armed state to unlock the car
    trunkUnlockMismatchCounter,     \* tracks how many wrong pins were sent while in an armed state to unlock the trunk alone
    isArmed,                        \* flag to indicate if the car is armed
    flash,                          \* flag to indicate if flash is on
    sound,                          \* flag to indicate if sound is on
    armedTimer,                     \* timer that counts from ArmedDelay to 0
    alarmTimer                      \* timer that counts from AlarmDelay to 0

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
        changeMismatchCounter,
        unlockMismatchCounter,
        trunkUnlockMismatchCounter
    >>

alarm_vars == <<alarmSystemState, flash, isArmed, sound>>
car_vars == <<passengerAreaState, passengerDoors, trunkState>>
timer_vars == <<armedTimer, alarmTimer>>
pin_vars   == <<changeMismatchCounter, unlockMismatchCounter, trunkUnlockMismatchCounter>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

Car == INSTANCE Car1                \* Refinement mapping through equal var names
CarAlarm == INSTANCE CarAlarm1      \* Refinement mapping through equal var names

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ alarmSystemState \in ALARM_SYSTEM_STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ Car!TypeInvariant
                 /\ CarAlarm!TypeInvariant

\* if the alarm is on, sound and flash should be on for the first 30 secs (alarm timer range: 270 - 300)
\* afterwards, only the flash should be on and the sound off
\* if the alarm is on and was triggered by any mismatch, all doors should still be closed
\* if not, any of the doors need to be open since it was an unauthorized open alarm
AlarmInvariant == /\ flash = TRUE
                  /\ IF \/ changeMismatchCounter = MaxPinMismatch 
                        \/ unlockMismatchCounter = MaxPinMismatch
                        \/ trunkUnlockMismatchCounter = MaxPinMismatch
                         THEN /\ \/ Car!IsCarUnlocked
                                 \/ passengerAreaState = ClosedAndLocked
                         ELSE /\ \/ Car!AreDoorsOpen
                                 \/ /\ Car!IsTrunkOpen 
                                    /\ Car!IsTrunkLocked
                  /\ IF alarmTimer > 269 
                         THEN sound = TRUE
                         ELSE sound = FALSE

\* the armed timer should be reset to the ArmedDelay when reaching this state
\* if the car is in an armed state indicate that by setting the isArmed flag
\* the car state should be ClosedAndLocked
\* the trunk can be unlocked in the armed state
ArmedInvariant == /\ armedTimer = ArmedDelay 
                  /\ isArmed = TRUE
                  /\ passengerAreaState = ClosedAndLocked
                  /\ ~(Car!IsTrunkOpen /\ Car!IsTrunkLocked)
                  

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
\* the car module needs to be initialized
Init == /\ alarmSystemState = Unarmed 
        /\ isArmed = FALSE
        /\ flash = FALSE
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay
        /\ alarmTimer = AlarmDelay
        /\ Car!Init

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

UnlockCarWithoutPin == /\ Car!PassengerArea!Unlock
                       /\ IF Car!IsTrunkLocked
                             THEN /\ Car!Trunk!Unlock
                             ELSE /\ UNCHANGED<<trunkState>>

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* Action that calls the car module's next action if the alarm system is unarmed
\* and there is no pin mismatch
DefaultCarActions == /\ alarmSystemState = Unarmed
                     /\ changeMismatchCounter /= MaxPinMismatch
                     /\ Car!Next
                     /\ armedTimer' = ArmedDelay
                     /\ unlockMismatchCounter' = 0
                     /\ trunkUnlockMismatchCounter' = 0
                     /\ UNCHANGED<<alarm_vars, alarmTimer>>

\* Open the car's trunk
CarOpenTrunk == /\ Car!IsTrunkUnlocked
                /\ Car!OpenTrunk

\* Close the car's trunk
CarCloseTrunk == /\ Car!IsTrunkUnlocked
                 /\ Car!CloseTrunk

\* Lock the car's trunk
CarLockTrunk ==  /\ Car!IsTrunkUnlocked
                 /\ Car!LockTrunk

\* Unlock the car's trunk
CarUnlockTrunk == /\ unlockMismatchCounter /= MaxPinMismatch
                  /\ trunkUnlockMismatchCounter /= MaxPinMismatch
                  /\ Car!UnlockTrunk

\* Action combining the possible actions on the car's trunk
\* when the alarm system is in an armed state
ArmedTrunkActions == /\ alarmSystemState = Armed
                     /\ unlockMismatchCounter /= MaxPinMismatch
                     /\ trunkUnlockMismatchCounter /= MaxPinMismatch
                     /\ \/ CarOpenTrunk
                        \/ CarCloseTrunk
                        \/ /\ Car!IsTrunkClosed
                           /\ CarLockTrunk
                        \/ CarUnlockTrunk
                 /\ UNCHANGED<<alarm_vars, timer_vars>>

\* Action combining the possible car actions
CarActions == \/ DefaultCarActions
              \/ ArmedTrunkActions

(***************************************************************************)
(* Open After Armed Actions                                                *)
(***************************************************************************)

\* car transitioning from closed and unlocked into an armed state
\* the car should also show it is armed, so the flag is set to true to indicate that
\* the armed delay timer reached 0, so the car can be armed and the timer needs to be reset
Arming == /\ Car!IsCarLocked
          /\ Car!IsCarClosed
          /\ armedTimer = 0
          /\ SetArmed
          /\ unlockMismatchCounter' = 0
          /\ trunkUnlockMismatchCounter' = 0
          /\ UNCHANGED<<
            passengerAreaState,
            passengerDoors,
            trunkState,
            flash,
            sound,
            alarmTimer,
            changeMismatchCounter>>

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
                    /\ unlockMismatchCounter' = 0
                    /\ trunkUnlockMismatchCounter' = 0
                    /\ UNCHANGED(timer_vars)
                    /\ UNCHANGED<<changeMismatchCounter>>

\* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
\* this tries to close the doors in the door module and arms the car again if all doors are closed
Close_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                             /\ \/ Car!CloseDoor
                                \/ Car!CloseTrunk
                             /\ IF /\ \A pd \in passengerDoors' : pd[2] = FALSE
                                   /\ trunkState' \in {ClosedAndLocked, ClosedAndUnlocked}
                                    THEN SetArmed
                                    ELSE UNCHANGED<<alarm_vars, armedTimer>>
                             /\ UNCHANGED<<flash, sound, alarmTimer>>
                             /\ UNCHANGED(pin_vars)

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
\* for this action we need to verify the pin when unlocking, which is only possible
\* until the mismatchCounter reaches the MaxPinMismatch number
Unlock_After_Armed == /\ alarmSystemState = Armed
                      /\ unlockMismatchCounter /= MaxPinMismatch
                      /\ trunkUnlockMismatchCounter /= MaxPinMismatch
                      /\ Car!IsTrunkClosed
                      /\ Car!UnlockCar
                      /\ IF passengerAreaState' /= ClosedAndUnlocked
                             THEN /\ UNCHANGED<<alarmSystemState, isArmed>>
                             ELSE /\ alarmSystemState' = Unarmed
                                  /\ isArmed' = FALSE
                      /\ UNCHANGED<<passengerDoors, flash, sound, timer_vars>>

\* Unlock the car after an alarm was triggered (car in alarm state) due to an unauthorized open
\* This ends the path for an illegal action and puts the car in the OpenAndUnlocked state
\* additionally, it deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_OpenAlarm == /\ alarmSystemState = Alarm
                          /\ changeMismatchCounter = 0
                          /\ unlockMismatchCounter = 0
                          /\ trunkUnlockMismatchCounter = 0
                          /\ UnlockCarWithoutPin
                          /\ CarAlarm!Deactivate
                          /\ alarmSystemState' = Unarmed
                          /\ alarmTimer' = AlarmDelay
                          /\ UNCHANGED(pin_vars)
                          /\ UNCHANGED<<isArmed, armedTimer, passengerDoors>>

\* Unlock the car after an alarm was triggered (car in alarm state) by a change pin mismatch
\* This ends the path for an illegal action and puts the car in back in the previous state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_ChangeMismatchAlarm == /\ alarmSystemState  = Alarm
                                    /\ changeMismatchCounter = MaxPinMismatch
                                    /\ unlockMismatchCounter = 0
                                    /\ trunkUnlockMismatchCounter = 0
                                    /\ Car!IsCarUnlocked
                                    /\ CarAlarm!Deactivate
                                    /\ alarmSystemState' = Unarmed
                                    /\ alarmTimer' = AlarmDelay
                                    /\ changeMismatchCounter' = 0
                                    /\ UNCHANGED<<
                                       isArmed, 
                                       car_vars,
                                       armedTimer,
                                       passengerDoors,
                                       unlockMismatchCounter,
                                       trunkUnlockMismatchCounter>>

\* Unlock the car after an alarm was triggered (car in alarm state) after an unlock pin mismatch
\* This ends the path for an illegal action and puts the car in the ClosedAndUnlocked state,
\* resets the mismatch counter and deactivates the alarm and resets the alarm timer
\* we assume that this unlock is done via the physical method (key turned in lock) and we
\* ignore wireless unlocks
Unlock_After_UnlockMismatchAlarm == /\ alarmSystemState  = Alarm
                                    /\ unlockMismatchCounter = MaxPinMismatch
                                    /\ changeMismatchCounter = 0
                                    /\ trunkUnlockMismatchCounter /= MaxPinMismatch
                                    /\ UnlockCarWithoutPin
                                    /\ CarAlarm!Deactivate
                                    /\ alarmSystemState' = Unarmed
                                    /\ alarmTimer' = AlarmDelay
                                    /\ unlockMismatchCounter' = 0
                                    /\ trunkUnlockMismatchCounter' = 0
                                    /\ UNCHANGED<<
                                       isArmed, 
                                       passengerDoors,
                                       armedTimer,
                                       changeMismatchCounter>>

\* TODO
Unlock_After_TrunkUnlockMismatchAlarm == /\ alarmSystemState  = Alarm
                                         /\ trunkUnlockMismatchCounter = MaxPinMismatch
                                         /\ changeMismatchCounter = 0
                                         /\ unlockMismatchCounter /= MaxPinMismatch
                                         /\ UnlockCarWithoutPin
                                         /\ CarAlarm!Deactivate
                                         /\ alarmSystemState' = Unarmed
                                         /\ alarmTimer' = AlarmDelay
                                         /\ unlockMismatchCounter' = 0
                                         /\ trunkUnlockMismatchCounter' = 0
                                         /\ UNCHANGED<<
                                            isArmed, 
                                            passengerDoors,
                                            armedTimer, 
                                            changeMismatchCounter>>

\* Similar to the Unlock_After_Alarm action, but puts the car into a valid
\* state again after the alarm already turned silent, thus, the alarm was already deactivated
\* this is only possible after an unauthorized open alarm was triggered
Unlock_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                              /\ alarmSystemState' = Unarmed
                              /\ UnlockCarWithoutPin
                              /\ UNCHANGED<<timer_vars,
                                            pin_vars,
                                            isArmed,
                                            passengerDoors,
                                            flash,
                                            sound>>



(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* action that triggers the car alarm after there were too many change pin attempts with
\* an invalid pin (changeMismatchCounter reached MaxPinMismatch)
ChangeMismatchAlarm == /\ alarmSystemState = Unarmed
                       /\ changeMismatchCounter = MaxPinMismatch
                       /\ alarmSystemState' = Alarm
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(car_vars)
                       /\ UNCHANGED(pin_vars)
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED<<isArmed>>

\* action that triggers the car alarm after there were too many unlock attempts with
\* an invalid pin (unlockMismatchCounter reached MaxPinMismatch)
UnlockMismatchAlarm == /\ alarmSystemState = Armed
                       /\ unlockMismatchCounter = MaxPinMismatch
                       /\ alarmSystemState' = Alarm
                       /\ isArmed' = FALSE
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(car_vars)
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED(pin_vars)

\* TODO
TrunkUnlockMismatchAlarm == /\ alarmSystemState = Armed
                            /\ trunkUnlockMismatchCounter = MaxPinMismatch
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
                                     /\ changeMismatchCounter = MaxPinMismatch
                                     /\ alarmSystemState' = Unarmed
                                     /\ changeMismatchCounter' = 0
                                     /\ UNCHANGED<<
                                        isArmed,
                                        car_vars,
                                        unlockMismatchCounter, 
                                        trunkUnlockMismatchCounter, 
                                        armedTimer>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go back into an armed state
\* since the alarm was due to too many unlock attempts
AlarmFinished_UnlockMismatch == /\ AlarmFinished
                                /\ unlockMismatchCounter = MaxPinMismatch
                                /\ SetArmed
                                /\ unlockMismatchCounter' = 0
                                /\ UNCHANGED<<
                                   armedTimer,
                                   car_vars,
                                   changeMismatchCounter,
                                   trunkUnlockMismatchCounter>>

\* TODO
AlarmFinished_TrunkUnlockMismatch == /\ AlarmFinished
                                     /\ trunkUnlockMismatchCounter = MaxPinMismatch
                                     /\ SetArmed
                                     /\ trunkUnlockMismatchCounter' = 0
                                     /\ UNCHANGED<<
                                        armedTimer,
                                        car_vars,
                                        changeMismatchCounter,
                                        unlockMismatchCounter>>

\* the car alarm was active (sound for 20 secs, flashing for 300 secs) for 5 mins
\* and not (correctly) unlocked in the meantime, so we go to SilentAndOpen since the
\* alarm was due to an unauthorized open
AlarmFinished_Open == /\ AlarmFinished
                      /\ changeMismatchCounter = 0 
                      /\ unlockMismatchCounter = 0 
                      /\ trunkUnlockMismatchCounter = 0 
                      /\ alarmSystemState' = SilentAndOpen
                      /\ UNCHANGED<<
                         car_vars,
                         isArmed,
                         armedTimer,
                         pin_vars>>

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
                /\ UNCHANGED<<
                   car_vars,
                   alarm_vars,
                   alarmTimer,
                   pin_vars>>

\* count down of the alarm timer from AlarmDelay to 0
\* this is only possible while the car is in the ClosedAndLocked state
\* once the alarm timer leaves the sound range (30 secs, so timer < 270)
\* the sound is deactivated and only the flash continues
AlarmTicker == /\ alarmSystemState = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED<<
                  car_vars,
                  alarmSystemState,
                  isArmed,
                  flash,
                  armedTimer,
                  pin_vars>>

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

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

\* action that defines the state for the higher abstraction depending on the current
\* passenger area and trunk states
CarState == IF Car!IsCarClosed
                THEN IF Car!IsCarLocked
                         THEN ClosedAndLocked
                         ELSE ClosedAndUnlocked
                ELSE IF Car!IsCarLocked
                         THEN OpenAndLocked
                         ELSE OpenAndUnlocked  

\* predicate that is true, if the car reached a mismatch alarm through a trunk unlock mismatch
\* this was added in this refinement and needs to be mapped accordingly to the lower refinement
IsTrunkUnlockMismatchAlarm == trunkUnlockMismatchCounter = MaxPinMismatch /\ alarmSystemState = Alarm

\* action to map the alarm trigger variable value to the higher abstraction one
AlarmTriggerMapping == IF alarmSystemState = Alarm /\ changeMismatchCounter = MaxPinMismatch
                           THEN CarState
                           ELSE -1

\* action to map the state variable value to the higher abstraction one
StateMapping == IF IsTrunkUnlockMismatchAlarm
                    THEN Armed
                    ELSE IF alarmSystemState /= Unarmed
                             THEN alarmSystemState
                             ELSE CarState         

\* action to map the flash variable value to the higher abstraction one
FlashMapping == IF IsTrunkUnlockMismatchAlarm
                    THEN FALSE
                    ELSE flash

\* action to map the sound variable value to the higher abstraction one
SoundMapping == IF IsTrunkUnlockMismatchAlarm
                    THEN FALSE
                    ELSE sound

\* action to map the alarm timer variable value to the higher abstraction one
AlarmTickerMapping == IF IsTrunkUnlockMismatchAlarm
                          THEN AlarmDelay
                          ELSE alarmTimer

\* action to map the is armed flag value to the higher abstraction one
IsArmedMapping == IF IsTrunkUnlockMismatchAlarm
                      THEN TRUE
                      ELSE isArmed

\* instance of the lower refinement
CarAlarmSystem8 == INSTANCE CarAlarmSystem8 
    WITH state <- StateMapping,
         alarmTrigger <- AlarmTriggerMapping,
         flash <- FlashMapping,
         sound <- SoundMapping,
         alarmTimer <- AlarmTickerMapping,
         isArmed <- IsArmedMapping

\* property to check the lower refinement in the TLC
CarAlarmSystem8Spec == /\ CarAlarmSystem8!Spec
                       /\ CarAlarmSystem8!SafetyInvariant
                       /\ CarAlarmSystem8!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

\* check that the car module's invariants also holds in the TLC
CarSpec == /\ Car!SafetyInvariant
           /\ Car!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem8Spec
                /\ CarAlarmSpec
                /\ CarSpec
                /\ []Invariant

=============================================================================
