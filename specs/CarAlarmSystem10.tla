-------------------------- MODULE CarAlarmSystem10 --------------------------

(***************************************************************************)
(* Tenth refinement of the car alarm system:                               *)
(***************************************************************************)

EXTENDS Integers

CONSTANT ArmedDelay, AlarmDelay, MaxPinMismatch, DoorCount
ASSUME ArmedDelay \in Nat
ASSUME AlarmDelay \in Nat
ASSUME MaxPinMismatch \in Nat

ArmedRange == 0..ArmedDelay
AlarmRange == 0..AlarmDelay

OpenAndUnlocked   == 0
ClosedAndLocked   == 1
OpenAndLocked     == 2
ClosedAndUnlocked == 3

Armed             == 4
Alarm             == 5
SilentAndOpen     == 6
Unarmed           == 7
 
ALARM_SYSTEM_STATES == 
    {
        Armed, 
        Alarm, 
        SilentAndOpen,
        Unarmed
    }
    
VARIABLES
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

Car == INSTANCE Car1
CarAlarm == INSTANCE CarAlarm1

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ alarmSystemState \in ALARM_SYSTEM_STATES
                 /\ isArmed \in BOOLEAN
                 /\ armedTimer \in ArmedRange
                 /\ alarmTimer \in AlarmRange
                 /\ Car!TypeInvariant
                 /\ CarAlarm!TypeInvariant

AlarmInvariant == /\ flash = TRUE
                  /\ IF Car!IsMaxPinMismatch
                     THEN /\ \/ Car!IsCarUnlocked
                             \/ passengerAreaState = ClosedAndLocked
                     ELSE /\ ~Car!IsMaxPinMismatch
                          /\ \/ Car!AreDoorsOpen
                             \/ /\ Car!IsTrunkOpen 
                                /\ Car!IsTrunkLocked

ArmedInvariant == /\ armedTimer = ArmedDelay 
                  /\ isArmed = TRUE
                  /\ passengerAreaState = ClosedAndLocked
                  /\ ~(Car!IsTrunkOpen /\ Car!IsTrunkLocked)
                  /\ IF alarmSystemState = Alarm /\ alarmTimer > 269 
                     THEN sound = TRUE
                     ELSE sound = FALSE


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

SetArmed == /\ mismatchCounter' = 0
            /\ alarmSystemState' = Armed
            /\ isArmed' = TRUE
            /\ armedTimer' = ArmedDelay
            
AlarmFinished == /\ alarmSystemState = Alarm
                 /\ alarmTimer = 0
                 /\ CarAlarm!Deactivate
                 /\ alarmTimer' = AlarmDelay

IncreaseMismatchOnlyInArmed == /\ ~Car!IsMaxPinMismatch
                                /\ IF alarmSystemState = Armed
                                   THEN UNCHANGED<<mismatchCounter>>
                                   ELSE mismatchCounter' = 0

(***************************************************************************)
(* Doors Open Close Actions                                                *)
(***************************************************************************)

\* Already open door, open another door
CarOpenDoor_Another_One == /\ alarmSystemState = Unarmed
                           /\ Car!OpenDoor_Another_One
                           /\ UNCHANGED<<alarm_vars, timer_vars>>

CarOpenDoor_From_Closed == /\ alarmSystemState = Unarmed
                           /\ Car!OpenDoor_From_Closed
                           /\ armedTimer' = ArmedDelay
                           /\ UNCHANGED<<alarm_vars, alarmTimer>>

CarCloseDoor == /\ alarmSystemState = Unarmed
                /\ Car!CloseDoor
                /\ UNCHANGED<<alarm_vars, timer_vars>>

CarOpenTrunk == /\ \/ alarmSystemState = Unarmed
                   \/ Car!IsTrunkUnlocked
                /\ Car!OpenTrunk
                /\ armedTimer' = ArmedDelay
                /\ UNCHANGED<<alarm_vars, alarmTimer>>

CarCloseTrunk == /\ \/ alarmSystemState = Unarmed
                    \/ Car!IsTrunkUnlocked
                 /\ Car!CloseTrunk
                 /\ UNCHANGED<<alarm_vars, timer_vars>>

CarLockTrunk == /\ Car!LockTrunk
                /\ mismatchCounter' = 0              
                /\ UNCHANGED<<alarm_vars, timer_vars>>

CarUnlockTrunk == /\ alarmSystemState = Unarmed
                  /\ ~Car!IsMaxPinMismatch
                  /\ IF alarmSystemState = Armed
                     THEN UNCHANGED<<mismatchCounter>>
                     ELSE mismatchCounter' = 0
                  /\ Car!UnlockTrunk
                  /\ UNCHANGED<<alarm_vars, timer_vars>>

CarLockCar == /\ alarmSystemState = Unarmed
              /\ Car!LockCar
              /\ mismatchCounter' = 0              
              /\ UNCHANGED<<alarm_vars, timer_vars>>

CarUnlockCar == /\ alarmSystemState = Unarmed
                /\ IncreaseMismatchOnlyInArmed
                /\ Car!UnlockCar 
                /\ armedTimer' = ArmedDelay
                /\ UNCHANGED<<alarm_vars, alarmTimer>>

CarSetNewPin == /\ alarmSystemState = Unarmed
                /\ Car!SetNewPin
                /\ UNCHANGED<<alarm_vars, timer_vars>>

CarActions == \/ CarOpenDoor_Another_One
              \/ CarOpenDoor_From_Closed
              \/ CarCloseDoor
              \/ CarOpenTrunk
              \/ CarCloseTrunk
              \/ CarLockTrunk
              \/ CarUnlockTrunk
              \/ CarLockCar
              \/ CarUnlockCar
              \/ CarSetNewPin

(***************************************************************************)
(* Open After Armed Actions                                                *)
(***************************************************************************)

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

Open_After_Armed == /\ alarmSystemState = Armed
                    /\ passengerAreaState = ClosedAndLocked
                    /\ alarmSystemState' = Alarm
                    /\ isArmed' = FALSE
                    /\ mismatchCounter = 0
                    /\ \/ Car!OpenDoor_From_Closed
                       \/ /\ Car!IsTrunkLocked /\ Car!IsTrunkClosed
                          /\ Car!OpenTrunk
                    /\ CarAlarm!Activate
                    /\ UNCHANGED<<timer_vars>>

AlarmFinished_Open == /\ AlarmFinished
                      /\ mismatchCounter = 0 
                      /\ alarmSystemState' = SilentAndOpen
                      /\ UNCHANGED<<car_vars, isArmed,  armedTimer>>

Open_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                            /\ \/ Car!OpenDoor_From_Closed
                               \/ Car!OpenTrunk
                            /\ UNCHANGED<<alarm_vars, timer_vars>>

Close_After_SilentAndOpen == /\ alarmSystemState = SilentAndOpen
                             /\ \/ Car!CloseDoor
                                \/ Car!CloseTrunk
                             /\ IF /\ \A pd \in passengerDoors' : pd[2] = FALSE
                                   /\ trunkState' \in {ClosedAndLocked, ClosedAndUnlocked}
                                THEN SetArmed
                                ELSE UNCHANGED<<alarm_vars>>
                             /\ UNCHANGED<<flash, sound, alarmTimer>>

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

Unlock_After_Armed == /\ alarmSystemState = Armed
                      /\ ~Car!IsMaxPinMismatch
                      /\ Car!UnlockCar
                      /\ IF passengerAreaState' /= ClosedAndUnlocked
                         THEN /\ UNCHANGED<<alarmSystemState, isArmed>>
                         ELSE /\ alarmSystemState' = Unarmed
                              /\ isArmed' = FALSE
                      /\ UNCHANGED<<passengerDoors, flash, sound, timer_vars>>

Unlock_After_Alarm == /\ alarmSystemState = Alarm
                      /\ Car!UnlockCar
                      /\ CarAlarm!Deactivate
                      /\ alarmSystemState' = Unarmed
                      /\ alarmTimer' = AlarmDelay
                      /\ mismatchCounter' = 0
                      /\ UNCHANGED<<passengerDoors, armedTimer, isArmed>>

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

MismatchAlarm == /\ Car!IsMaxPinMismatch
                 /\ alarmSystemState \in {Armed, Unarmed}
                 /\ alarmSystemState' = Alarm
                 /\ isArmed' = FALSE
                 /\ CarAlarm!Activate
                 /\ UNCHANGED(car_vars)
                 /\ UNCHANGED(timer_vars)

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

ArmingTicker == /\ alarmSystemState = Unarmed
                /\ Car!IsCarClosed
                /\ Car!IsCarLocked
                /\ armedTimer > 0
                /\ \E d \in { n \in ArmedRange : n < armedTimer}:
                    armedTimer' = d 
                /\ UNCHANGED<< car_vars, alarm_vars, alarmTimer>>

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

AlarmTrigger == IF alarmSystemState = Alarm
                THEN IF passengerAreaState = ClosedAndLocked
                     THEN Armed
                     ELSE passengerAreaState
                ELSE /\ -1


CarAlarmSystem9 == INSTANCE CarAlarmSystem9 
    WITH state <- passengerAreaState, alarmTrigger <- AlarmTrigger

THEOREM Spec => /\ CarAlarmSystem9!Spec
                /\ Car!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
