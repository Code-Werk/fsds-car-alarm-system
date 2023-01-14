-------------------------- MODULE Car1 --------------------------

(***************************************************************************)
(* Ninth refinement of the car alarm system:                              *)
(*                                                                         *)
(* TODO *)
(***************************************************************************)

EXTENDS Integers

CONSTANT DoorCount, MaxPinMissmatch
ASSUME DoorCount \in {2, 4}
ASSUME MaxPinMissmatch \in Nat

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
    wrongPinCounter

vars_doors == <<passengerAreaState, passengerDoors>>
vars == <<trunkState, passengerAreaState, passengerDoors, wrongPinCounter>>

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

IsTrunkClosed == /\ IsStateClosed(passengerAreaState)
IsTrunkLocked == /\ IsStateLocked(passengerAreaState)
IsTrunkOpen == /\ IsStateOpen(passengerAreaState)
IsTrunkUnlocked == /\ IsStateUnlocked(passengerAreaState)

IsCarClosed == /\ \/ AreDoorsClosed \/ IsTrunkClosed
IsCarLocked == /\ \/ AreDoorsLocked \/ IsTrunkLocked 
IsCarOpen == /\ \/ AreDoorsOpen \/ IsTrunkOpen
IsCarUnlocked == /\ \/ AreDoorsUnlocked \/ IsTrunkUnlocked

IsMaxPinMissmatch == wrongPinCounter >= MaxPinMissmatch

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ passengerAreaState \in STATES
                 /\ trunkState \in STATES
                 /\ wrongPinCounter \in 0..MaxPinMissmatch
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
        /\ wrongPinCounter = 0

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

CheckPin(action, unchanged) == /\ \E b \in BOOLEAN:
                                   IF b = TRUE
                                   THEN /\ action
                                        /\ wrongPinCounter' = 0
                                   ELSE /\ ~IsMaxPinMissmatch 
                                        /\ wrongPinCounter' = wrongPinCounter + 1
                                        /\ unchanged

(***************************************************************************)
(* Doors Actions                                                           *)
(***************************************************************************)

OpenDoor_From_Closed == /\ AreDoorsClosed
                        /\ PassengerArea!Open
                        /\ Doors!Open
                        /\ UNCHANGED<<trunkState, wrongPinCounter>>

OpenDoor_Another_One == /\ AreDoorsOpen
                        /\ Doors!Open
                        /\ UNCHANGED<<passengerAreaState>>
                        /\ UNCHANGED<<trunkState, wrongPinCounter>>

CloseDoor == /\ IsStateOpen(passengerAreaState)
             /\ Doors!Close \*includes open check
             /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                THEN /\ PassengerArea!Close
                ELSE /\ UNCHANGED<<passengerAreaState>>
             /\ UNCHANGED<<trunkState, wrongPinCounter>>

DoorActions == \/ OpenDoor_Another_One
               \/ OpenDoor_From_Closed
               \/ CloseDoor

(***************************************************************************)
(* Trunk Actions                                                           *)
(***************************************************************************)

OpenTrunk == /\ Trunk!Open
             /\ UNCHANGED<<vars_doors, wrongPinCounter>>

CloseTrunk == /\ Trunk!Close
              /\ UNCHANGED<<vars_doors, wrongPinCounter>>

\* Unlock trunk without unlocking doors 
UnlockTrunk == /\ AreDoorsLocked
               /\ CheckPin(Trunk!Unlock, UNCHANGED<<trunkState>>)
               /\ UNCHANGED<<vars_doors>>

\* Lock trunk again if trunk was unlocked on it's own 
LockTrunk == /\ AreDoorsLocked
             /\ Trunk!Lock
             /\ UNCHANGED<<vars_doors, wrongPinCounter>>

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
           /\ UNCHANGED<<passengerDoors, wrongPinCounter>>


UnlockCar == /\ AreDoorsLocked
             /\ CheckPin(
                /\ PassengerArea!Unlock
                /\ Trunk!Unlock,
                UNCHANGED<<passengerAreaState, trunkState>>)
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
(***************************************************************************)


THEOREM Spec => /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:48:38 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
