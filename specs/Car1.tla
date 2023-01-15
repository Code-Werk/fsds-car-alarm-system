-------------------------- MODULE Car1 --------------------------

(***************************************************************************)
(* First refinement of the car system:                                     *)
(* Module that represent a car with 2 or 4 doors and a trunk.              *)
(* The doors and trunk can be opened and closed separately.                *)
(* The car can also be locked and unlocked, whereby the trunk can be       *)  
(* unlocked and opend even if the car is locked.                           *)
(* Another functionallity of the car is to only unlock the car if the      *)
(* correct pin is provided, otherwise a counter is increased to predefined *)
(* a max.                                                                  *)
(***************************************************************************)

EXTENDS Integers

CONSTANT DoorCount, MaxPinMismatch
ASSUME DoorCount \in {2, 4}
ASSUME MaxPinMismatch \in Nat

OpenAndUnlocked    == 0
ClosedAndLocked    == 1
OpenAndLocked      == 2
ClosedAndUnlocked  == 3

STATES == 
    {
        OpenAndUnlocked, 
        ClosedAndLocked, 
        OpenAndLocked, 
        ClosedAndUnlocked
    }
    
VARIABLES 
    passengerAreaState, 
    passengerDoors, 
    trunkState,
    mismatchCounter

vars_doors == <<passengerAreaState, passengerDoors>>
vars == <<trunkState, passengerAreaState, passengerDoors, mismatchCounter>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

PassengerArea == INSTANCE CarAlarmSystem2 WITH state <- passengerAreaState
Trunk == INSTANCE CarAlarmSystem2 WITH state <- trunkState
Doors == INSTANCE Doors1 WITH passengerDoors <- passengerDoors

(***************************************************************************)
(* Guards                                                                  *)
(***************************************************************************)

IsStateClosed(state) == /\ state \in {ClosedAndLocked, ClosedAndUnlocked}
IsStateLocked(state) == /\ state \in {ClosedAndLocked, OpenAndLocked}
IsStateOpen(state) == /\ state \in {OpenAndLocked, OpenAndUnlocked}
IsStateUnlocked(state) == /\ state \in {ClosedAndUnlocked, OpenAndUnlocked}

AreDoorsClosed == /\ Doors!AreClosed /\ IsStateClosed(passengerAreaState)
AreDoorsLocked == /\ IsStateLocked(passengerAreaState)
AreDoorsOpen == /\ Doors!AreOpen /\ IsStateOpen(passengerAreaState)
AreDoorsUnlocked == /\ IsStateUnlocked(passengerAreaState)

IsTrunkClosed == /\ IsStateClosed(trunkState)
IsTrunkLocked == /\ IsStateLocked(trunkState)
IsTrunkOpen == /\ IsStateOpen(trunkState)
IsTrunkUnlocked == /\ IsStateUnlocked(trunkState)

IsCarClosed == /\ AreDoorsClosed /\ IsTrunkClosed
IsCarLocked == /\ AreDoorsLocked /\ IsTrunkLocked 
IsCarOpen == /\ AreDoorsOpen /\ IsTrunkOpen
IsCarUnlocked == /\ AreDoorsUnlocked /\ IsTrunkUnlocked

IsMaxPinMismatch == mismatchCounter >= MaxPinMismatch

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ passengerAreaState \in STATES
                 /\ trunkState \in STATES
                 /\ mismatchCounter \in 0..MaxPinMismatch
                 /\ Doors!TypeInvariant
                 /\ PassengerArea!TypeInvariant
                 /\ Trunk!TypeInvariant
                 
SafetyInvariant == /\ Doors!SafetyInvariant

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ Doors!Init
        /\ PassengerArea!Init
        /\ Trunk!Init
        /\ mismatchCounter = 0

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

CheckPin(action, unchanged) == /\ \E b \in BOOLEAN:
                                   IF b = TRUE
                                   THEN /\ action
                                        /\ mismatchCounter' = 0
                                   ELSE /\ ~IsMaxPinMismatch 
                                        /\ mismatchCounter' = mismatchCounter + 1
                                        /\ unchanged

(***************************************************************************)
(* Doors Actions                                                           *)
(***************************************************************************)

OpenDoor_From_Closed == /\ AreDoorsClosed
                        /\ PassengerArea!Open
                        /\ Doors!Open
                        /\ UNCHANGED<<trunkState, mismatchCounter>>

OpenDoor_Another_One == /\ AreDoorsOpen
                        /\ Doors!Open
                        /\ UNCHANGED<<passengerAreaState, trunkState, mismatchCounter>>

CloseDoor == /\ AreDoorsOpen
             /\ Doors!Close \*includes open check
             /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                THEN /\ PassengerArea!Close
                ELSE /\ UNCHANGED<<passengerAreaState>>
             /\ UNCHANGED<<trunkState, mismatchCounter>>

DoorActions == \/ OpenDoor_Another_One
               \/ OpenDoor_From_Closed
               \/ CloseDoor

(***************************************************************************)
(* Trunk Actions                                                           *)
(***************************************************************************)

OpenTrunk == /\ Trunk!Open
             /\ UNCHANGED<<vars_doors, mismatchCounter>>

CloseTrunk == /\ Trunk!Close
              /\ UNCHANGED<<vars_doors, mismatchCounter>>

\* Unlock trunk without unlocking doors 
UnlockTrunk == /\ IsCarLocked
               /\ CheckPin(Trunk!Unlock, UNCHANGED<<trunkState>>)
               /\ UNCHANGED<<vars_doors>>

\* Lock trunk again if trunk was unlocked on it's own 
LockTrunk == /\ AreDoorsLocked
             /\ IsTrunkUnlocked
             /\ Trunk!Lock
             /\ UNCHANGED<<vars_doors, mismatchCounter>>

TrunkActions == \/ OpenTrunk
                \/ CloseTrunk
                \/ LockTrunk              
                \/ UnlockTrunk              

(***************************************************************************)
(* Lock Actions                                                            *)
(***************************************************************************)

LockCar == /\ IsCarUnlocked
           /\ PassengerArea!Lock
           /\ Trunk!Lock
           /\ UNCHANGED<<passengerDoors, mismatchCounter>>


UnlockCar == /\ AreDoorsLocked
             /\ CheckPin(
                /\ PassengerArea!Unlock
                /\ IF IsTrunkLocked
                   THEN /\ Trunk!Unlock
                   ELSE /\ UNCHANGED<<trunkState>>,
                /\ UNCHANGED<<passengerAreaState, trunkState>>)
             /\ UNCHANGED<<passengerDoors>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

SetNewPin == /\ IsCarUnlocked
             /\ CheckPin(TRUE, TRUE)
             /\ UNCHANGED<<passengerAreaState, passengerDoors, trunkState>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ DoorActions
        \/ TrunkActions
        \/ LockCar
        \/ UnlockCar
        \/ SetNewPin

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)

THEOREM Spec => /\ PassengerArea!Spec
                /\ Trunk!Spec
                /\ Doors!Spec
                /\ []Invariant

=============================================================================
