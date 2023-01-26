-------------------------- MODULE CarAlarmSystem10 --------------------------

(***************************************************************************)
(* Tenth refinement of the car alarm system:                               *)
(*                                                                         *)
(* TODO *)
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
    DoorCount                       \* TODO
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
    mismatchCounter                 \* tracks how many wrong pins were sent while in an armed state
                                    \* or to change the pin in an unlocked state
    isArmed,                        \* flag to indicate if the car is armed
    flash,                          \* flag to indicate if flash is on
    sound,                          \* flag to indicate if sound is on
    armedTimer,                     \* timer that counts from ArmedDelay to 0
    alarmTimer,                     \* timer that counts from AlarmDelay to 0

vars == 
    <<
        alarmSystemState,
        passengerAreaState, 
        passengerDoors, 
        trunkState,
        mismatchCounter,
        isArmed, 
        flash, 
        sound, 
        armedTimer, 
        alarmTimer
    >>

alarm_vars == <<alarmSystemState, flash, isArmed, sound>>
car_vars == <<passengerAreaState, passengerDoors, trunkState, mismatchCounter>>
timer_vars == <<armedTimer, alarmTimer>>

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

\* TODO
AlarmInvariant == /\ flash = TRUE
                  /\ IF Car!IsMaxPinMismatch
                         THEN /\ \/ Car!IsCarUnlocked
                                 \/ passengerAreaState = ClosedAndLocked
                         ELSE /\ ~Car!IsMaxPinMismatch
                              /\ \/ Car!AreDoorsOpen
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

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* TODO
SetArmed == /\ mismatchCounter' = 0
            /\ alarmSystemState' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay

\* TODO
AlarmFinished == /\ alarmSystemState = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

\* TODO
IncreaseMismatchOnlyInArmed == /\ ~Car!IsMaxPinMismatch
                                /\ IF alarmSystemState = Armed
                                       THEN UNCHANGED<<mismatchCounter>>
                                       ELSE mismatchCounter' = 0

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* Already open door, open another door
\* TODO
DefaultCarActions == /\ alarmSystemState = Unarmed
                     /\ ~Car!IsMaxPinMismatch
                     /\ Car!Next
                     /\ armedTimer' = ArmedDelay
                     /\ mismatchCounter' = 0
                     /\ UNCHANGED<<alarm_vars, alarmTimer>>

\* TODO
CarOpenTrunk == /\ Car!IsTrunkUnlocked
                /\ Car!OpenTrunk

\* TODO
CarCloseTrunk == /\ Car!IsTrunkUnlocked
                 /\ Car!CloseTrunk

\* TODO
CarLockTrunk ==  /\ Car!IsTrunkUnlocked
                 /\ Car!LockTrunk

\* TODO
CarUnlockTrunk == /\ ~Car!IsMaxPinMismatch
                  /\ Car!UnlockTrunk

\* TODO
ArmedTrunkActions == /\ alarmSystemState = Armed
                     /\ \/ CarOpenTrunk
                        \/ CarCloseTrunk
                        \/ /\ Car!IsTrunkClosed
                           /\ CarLockTrunk
                        \/ CarUnlockTrunk
                 /\ UNCHANGED<<alarm_vars, timer_vars>>

\* TODO
CarActions == \/ DefaultCarActions
              \/ ArmedTrunkActions

(***************************************************************************)
(* Open After Armed Actions                                                *)
(***************************************************************************)

\* TODO
Arming == /\ Car!IsCarLocked 
          /\ Car!IsCarClosed
          /\ armedTimer = 0
          /\ SetArmed
          /\ UNCHANGED<<
            passengerAreaState, 
            passengerDoors, 
            trunkState,
            flash, 
            sound, 
            alarmTimer>>

\* TODO
Open_After_Armed == /\ alarmSystemState = Armed
                    /\ passengerAreaState = ClosedAndLocked
                    /\ alarmSystemState' = Alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter = 0
                    /\ \/ Car!OpenDoor_From_Closed
                       \/ /\ Car!IsTrunkLocked 
                          /\ Car!IsTrunkClosed
                          /\ Car!OpenTrunk
                    /\ CarAlarm!Activate
                    /\ UNCHANGED<<timer_vars>>

\* TODO
AlarmFinished_Open == /\ AlarmFinished
                      /\ mismatchCounter = 0 
                      /\ alarmSystemState' = SilentAndOpen
                      /\ UNCHANGED<<car_vars, isArmed,  armedTimer>>

\* TODO
Open_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                            /\ \/ Car!OpenDoor_From_Closed
                               \/ Car!OpenTrunk
                            /\ UNCHANGED<<alarm_vars, timer_vars>>

\* TODO
Close_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                             /\ \/ Car!CloseDoor
                                \/ Car!CloseTrunk
                             /\ IF /\ \A pd \in passengerDoors' : pd[2] = FALSE
                                   /\ trunkState' \in {ClosedAndLocked, ClosedAndUnlocked}
                                    THEN SetArmed
                                    ELSE UNCHANGED<<alarm_vars, armedTimer>>
                             /\ UNCHANGED<<flash, sound, alarmTimer>>

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

\* TODO
Unlock_After_Armed == /\ alarmSystemState = Armed
                      /\ ~Car!IsMaxPinMismatch
                      /\ Car!UnlockCar
                      /\ IF passengerAreaState' /= ClosedAndUnlocked
                             THEN /\ UNCHANGED<<alarmSystemState, isArmed>>
                             ELSE /\ alarmSystemState' = Unarmed
                                  /\ isArmed' = FALSE
                      /\ UNCHANGED<<passengerDoors, flash, sound, timer_vars>>

\* TODO
Unlock_After_Alarm == /\ alarmSystemState = Alarm
                      /\ Car!UnlockCar
                      /\ CarAlarm!Deactivate
                      /\ alarmSystemState' = Unarmed
                      /\ alarmTimer' = AlarmDelay
                      /\ mismatchCounter' = 0
                      /\ UNCHANGED<<passengerDoors, armedTimer, isArmed>>

\* TODO
Unlock_After_SilentAndOpen == /\ alarmSystemState  = SilentAndOpen
                              /\ alarmSystemState' = Unarmed
                              /\ UNCHANGED<<car_vars, 
                                            timer_vars, 
                                            isArmed,
                                            flash,
                                            sound>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* TODO
MismatchAlarm == /\ Car!IsMaxPinMismatch
                 /\ alarmSystemState \in {Armed, Unarmed}
                 /\ alarmSystemState' = Alarm
                 /\ isArmed' = FALSE
                 /\ CarAlarm!Activate
                 /\ UNCHANGED(car_vars)
                 /\ UNCHANGED(timer_vars)

\* TODO
AlarmFinished_Mismatch == /\ AlarmFinished
                          /\ Car!IsMaxPinMismatch
                          /\ mismatchCounter' = 0
                          /\ IF passengerAreaState = ClosedAndLocked
                             THEN SetArmed 
                             ELSE /\ alarmSystemState' = Unarmed 
                                  /\ UNCHANGED<<isArmed, armedTimer>>
                          /\ UNCHANGED<<passengerAreaState, 
                                        passengerDoors, 
                                        trunkState>>

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
                /\ UNCHANGED<< car_vars, alarm_vars, alarmTimer>>

\* TODO
AlarmTicker == /\ alarmSystemState = Alarm
               /\ alarmTimer > 0
               /\ \E d \in { n \in AlarmRange : n < alarmTimer}:
                   /\ alarmTimer' = d
                   /\ IF d < 270
                      THEN CarAlarm!DeactivateSound
                      ELSE UNCHANGED<<sound>>
               /\ UNCHANGED<<car_vars, alarmSystemState, 
                             isArmed, flash, armedTimer>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ CarActions
        \/ Close_After_SilentAndOpen
        \/ Open_After_Armed
        \/ Unlock_After_Armed
        \/ Unlock_After_Alarm
        \/ Unlock_After_SilentAndOpen
        \/ Arming
        \/ AlarmFinished_Mismatch
        \/ AlarmFinished_Open
        \/ ArmingTicker
        \/ AlarmTicker
        \/ MismatchAlarm

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

\* TODO
AlarmTrigger == IF alarmSystemState = Alarm
                    THEN IF passengerAreaState = ClosedAndLocked
                        THEN Armed
                        ELSE passengerAreaState
                    ELSE /\ -1

\* TODO refinement mapping + checking
\* instance of the lower refinement
CarAlarmSystem9 == INSTANCE CarAlarmSystem9 
    WITH state <- passengerAreaState, alarmTrigger <- AlarmTrigger

\* property to check the lower refinement in the TLC
CarAlarmSystem9Spec == /\ CarAlarmSystem9!Spec
                       /\ CarAlarmSystem9!SafetyInvariant
                       /\ CarAlarmSystem9!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

\* check that the car module also holds in the TLC
CarSpec == /\ Car!Spec
           /\ Car!SafetyInvariant
           /\ Car!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem9Spec
                /\ CarAlarmSpec
                /\ CarSpec
                /\ []Invariant

=============================================================================
