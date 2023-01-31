-------------------------- MODULE CarAlarmSystem10 --------------------------

(***************************************************************************)
(* Ninth refinement of the car alarm system:                               *)
(*                                                                         *)
(* TODO *)
(*                                                                         *)
(* This refinement targets Requirements 8 and 9.                           *)
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
    DoorCount,                      \* TODO
    MaxPins                         \* TODO

ASSUME ArmedDelay \in Nat           \* ArmedDelay is set in the TLC, 20 sec by requirement
ASSUME AlarmDelay \in Nat           \* AlarmDelay is set in the TLC, 300 sec by requirement (=5 min)
ASSUME MaxPinMismatch \in Nat       \* MaxPinMismatch is set in the TLC, 3 tries by requirement
ASSUME MaxPins \in Nat

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
    isArmed,                        \* flag to indicate if the car is armed
    flash,                          \* flag to indicate if flash is on
    sound,                          \* flag to indicate if sound is on
    armedTimer,                     \* timer that counts from ArmedDelay to 0
    alarmTimer,                     \* timer that counts from AlarmDelay to 0
    changeMismatchCounters,
    unlockMismatchCounters,
    trunkUnlockMismatchCounters

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

alarm_vars == <<alarmSystemState, flash, isArmed, sound>>
car_vars == <<passengerAreaState, passengerDoors, trunkState>>
timer_vars == <<armedTimer, alarmTimer>>
pin_vars   == <<changeMismatchCounters, unlockMismatchCounters, trunkUnlockMismatchCounters>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

Car == INSTANCE Car1                \* Refinement mapping through equal var names
CarAlarm == INSTANCE CarAlarm1      \* Refinement mapping through equal var names
Pins == INSTANCE Pins1      \* Refinement mapping through equal var names

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

\* TODO
AlarmInvariant == /\ flash = TRUE
                  /\ IF Pins!IsAnyMaxMismatch
                         THEN /\ \/ Car!IsCarUnlocked
                                 \/ passengerAreaState = ClosedAndLocked
                         ELSE /\ \/ Car!AreDoorsOpen
                                 \/ /\ Car!IsTrunkOpen 
                                    /\ Car!IsTrunkLocked

\* TODO
ArmedInvariant == /\ armedTimer = ArmedDelay 
                  /\ isArmed = TRUE
                  /\ passengerAreaState = ClosedAndLocked
                  /\ ~(Car!IsTrunkOpen /\ Car!IsTrunkLocked)
                  /\ IF alarmSystemState = Alarm /\ alarmTimer > 269 
                         THEN sound = TRUE
                         ELSE sound = FALSE

\* TODO
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

\* TODO
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

\* TODO
SetArmed == /\ alarmSystemState' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay

\* TODO
AlarmFinished == /\ alarmSystemState = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* TODO
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
                     /\ UNCHANGED<<
                        alarm_vars, 
                        alarmTimer,
                        unlockMismatchCounters,
                        trunkUnlockMismatchCounters>>

\* TODO
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
                              UNCHANGED<<trunkState, passengerAreaState, passengerDoors>>)
                 /\ UNCHANGED<<
                    alarm_vars, 
                    timer_vars, 
                    changeMismatchCounters, 
                    unlockMismatchCounters>>

\* TODO
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
             /\ UNCHANGED<<
                car_vars, 
                alarm_vars,
                timer_vars,
                unlockMismatchCounters,
                trunkUnlockMismatchCounters>>

(***************************************************************************)
(* Open After Armed Actions                                                *)
(***************************************************************************)

\* TODO
Arming == /\ Car!IsCarLocked 
          /\ Car!IsCarClosed
          /\ armedTimer = 0
          /\ SetArmed
          /\ Pins!ResetUnlockCounters
          /\ Pins!ResetTrunkCounters
          /\ UNCHANGED<<
            passengerAreaState, 
            passengerDoors, 
            trunkState,
            flash, 
            sound, 
            alarmTimer,
            changeMismatchCounters>>

\* TODO
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

\* TODO
AlarmFinished_Open == /\ AlarmFinished
                      /\ Pins!IsNoMismatch
                      /\ alarmSystemState' = SilentAndOpen
                      /\ UNCHANGED<<
                         car_vars,
                         isArmed,
                         armedTimer,
                         pin_vars>>

\* TODO
Open_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                            /\ \/ Car!OpenDoor_From_Closed
                               \/ Car!OpenTrunk
                            /\ UNCHANGED<<alarm_vars, pin_vars, timer_vars>>

\* TODO
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

\* TODO
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
                      /\ UNCHANGED<<
                         passengerDoors, 
                         flash, 
                         sound,
                         changeMismatchCounters,
                         timer_vars>>

\* TODO
Unlock_After_OpenAlarm == /\ alarmSystemState = Alarm
                          /\ Pins!IsNoMismatch
                          /\ Car!UnlockCar
                          /\ CarAlarm!Deactivate
                          /\ alarmSystemState' = Unarmed
                          /\ alarmTimer' = AlarmDelay
                          /\ UNCHANGED(pin_vars)
                          /\ UNCHANGED<<isArmed, armedTimer, passengerDoors>>

\* TODO
Unlock_After_ChangeMismatchAlarm == /\ alarmSystemState  = Alarm
                                    /\ Pins!IsChangeMaxMismatch
                                    /\ Pins!IsUnlockNoMismatch
                                    /\ Pins!IsTrunkNoMismatch
                                    /\ Car!IsCarUnlocked
                                    /\ CarAlarm!Deactivate
                                    /\ alarmSystemState' = Unarmed
                                    /\ alarmTimer' = AlarmDelay
                                    /\ Pins!ResetChangeCounters
                                    /\ UNCHANGED<<
                                       isArmed, 
                                       car_vars,
                                       armedTimer,
                                       passengerDoors,
                                       unlockMismatchCounters,
                                       trunkUnlockMismatchCounters>>

\* TODO
Unlock_After_UnlockMismatchAlarm == /\ alarmSystemState  = Alarm
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

\* TODO
Unlock_After_TrunkUnlockMismatchAlarm == /\ alarmSystemState  = Alarm
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

\* TODO
Unlock_After_SilentAndOpen == /\ alarmSystemState  = SilentAndOpen
                              /\ alarmSystemState' = Unarmed
                              /\ Car!UnlockCar
                              /\ UNCHANGED<<timer_vars,
                                            pin_vars,
                                            isArmed,
                                            passengerDoors,
                                            flash,
                                            sound>>



(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* TODO
ChangeMismatchAlarm == /\ alarmSystemState = Unarmed
                       /\ Pins!IsChangeMaxMismatch
                       /\ alarmSystemState' = Alarm
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(car_vars)
                       /\ UNCHANGED(pin_vars)
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED<<isArmed>>

\* TODO
UnlockMismatchAlarm == /\ alarmSystemState = Armed
                       /\ Pins!IsUnlockMaxMismatch
                       /\ alarmSystemState' = Alarm
                       /\ isArmed' = FALSE
                       /\ CarAlarm!Activate
                       /\ UNCHANGED(car_vars)
                       /\ UNCHANGED(timer_vars)
                       /\ UNCHANGED(pin_vars)

\* TODO
TrunkUnlockMismatchAlarm == /\ alarmSystemState = Armed
                            /\ Pins!IsTrunkMaxMismatch
                            /\ alarmSystemState' = Alarm
                            /\ isArmed' = FALSE
                            /\ CarAlarm!Activate
                            /\ UNCHANGED(car_vars)
                            /\ UNCHANGED(timer_vars)
                            /\ UNCHANGED(pin_vars)

\* TODO
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

\* TODO
AlarmFinished_UnlockMismatch == /\ AlarmFinished
                                /\ Pins!IsUnlockMaxMismatch
                                /\ SetArmed
                                /\ Pins!ResetUnlockCounters
                                /\ UNCHANGED<<
                                   armedTimer,
                                   car_vars,
                                   changeMismatchCounters,
                                   trunkUnlockMismatchCounters>>

\* TODO
AlarmFinished_TrunkUnlockMismatch == /\ AlarmFinished
                                     /\ Pins!IsTrunkMaxMismatch
                                     /\ SetArmed
                                     /\ Pins!ResetTrunkCounters
                                     /\ UNCHANGED<<
                                        armedTimer,
                                        car_vars,
                                        changeMismatchCounters,
                                        unlockMismatchCounters>>



(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

\* TODO
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

\* TODO
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
        \/ SetNewPin

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

Max(S) == CHOOSE x \in S : \A y \in S : x[2] >= y[2]

\* TODO refinement mapping + checking
\* instance of the lower refinement
CarAlarmSystem9 == INSTANCE CarAlarmSystem9 
    WITH changeMismatchCounter <- Max(changeMismatchCounters)[2],
         unlockMismatchCounter <- Max(unlockMismatchCounters)[2],
         trunkUnlockMismatchCounter <- Max(trunkUnlockMismatchCounters)[2]

\* property to check the lower refinement in the TLC
CarAlarmSystem9Spec == /\ CarAlarmSystem9!Spec
                       /\ CarAlarmSystem9!SafetyInvariant
                       /\ CarAlarmSystem9!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

\* check that the car module also holds in the TLC
CarSpec == /\ Car!SafetyInvariant
           /\ Car!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem9Spec
                /\ CarAlarmSpec
                /\ CarSpec
                /\ []Invariant

=============================================================================
