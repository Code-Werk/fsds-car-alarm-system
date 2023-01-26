-------------------------- MODULE Car1 --------------------------

(***************************************************************************)
(* Module with a single refinement for a car:                              *)
(*                                                                         *)
(* Module that represent a car with 2 or 4 doors and a trunk.              *)
(* The doors and trunk can be opened and closed separately.                *)
(* The car can also be locked and unlocked, whereby the trunk can be       *)  
(* unlocked and opened even if the car is locked.                          *)
(* Another functionality of the car is to only unlock the car if the       *)
(* correct pin is provided, otherwise a counter is increased to predefined *)
(* a max.                                                                  *)
(***************************************************************************)

EXTENDS Integers

CONSTANT
    DoorCount,                      \* Amount of the car's doors
    MaxPinMismatch                  \* Max. count until a pin mismatch alarm is triggered 
                                    \* (here: how often can a key send a wrong pin)
ASSUME DoorCount \in {2,4}          \* DoorCount is set in the TLC
                                    \* has to either be 2 or 4 by requirement
ASSUME MaxPinMismatch \in Nat       \* MaxPinMismatch is set in the TLC, 3 tries by requirement

OpenAndUnlocked   == 0              \* Car is open and unlocked
ClosedAndLocked   == 1              \* Car is closed and locked
OpenAndLocked     == 2              \* Car is still open but already locked
ClosedAndUnlocked == 3              \* Car is not yet closed but already locked

STATES ==                           \* Possible states regarding the entire car
    {
        OpenAndUnlocked,
        ClosedAndLocked,
        OpenAndLocked,
        ClosedAndUnlocked
    }
    
VARIABLES 
    passengerAreaState,             \* variable holding the current state of the passenger area module
                                    \* together with the trunk state this is the car's state
    passengerDoors,                 \* tuple representing the passenger doors
                                    \* consists of an index and a bool flag indicating
                                    \* if the door is open (flag is true), or closed (flag is false)
    trunkState,                     \* variable holding the current state of the trunk module
                                    \* together with the passenger area state this is the car's state
    mismatchCounter                 \* tracks how many wrong pins were sent while in an armed state
                                    \* or to change the pin in an unlocked state

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
(* Accessible outside to ease guard usage for the module if instantiated   *)
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

\* The doors safety variant also holds true for the entire car (either
\* open or closed, never both), so we also check it explicitly
SafetyInvariant == /\ Doors!SafetyInvariant

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* TODO
Init == /\ Doors!Init
        /\ PassengerArea!Init
        /\ Trunk!Init
        /\ mismatchCounter = 0

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* Helper action that is called to non-deterministically check if a sent pin matches
\* and so can unlock the car or change the pin, or if the pin is incorrect
\* It takes the action that should be executed next if the pin matches or the unchanged
\* variables if the pin does not match and the action does not get executed
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

\* TODO
OpenDoor_From_Closed == /\ AreDoorsClosed
                        /\ PassengerArea!Open
                        /\ Doors!Open
                        /\ UNCHANGED<<trunkState, mismatchCounter>>

\* TODO
OpenDoor_Another_One == /\ AreDoorsOpen
                        /\ Doors!Open
                        /\ UNCHANGED<<passengerAreaState, trunkState, mismatchCounter>>

\* TODO
CloseDoor == /\ AreDoorsOpen
             /\ Doors!Close \*includes open check
             /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                    THEN /\ PassengerArea!Close
                    ELSE /\ UNCHANGED<<passengerAreaState>>
             /\ UNCHANGED<<trunkState, mismatchCounter>>

\* TODO
DoorActions == \/ OpenDoor_Another_One
               \/ OpenDoor_From_Closed
               \/ CloseDoor

(***************************************************************************)
(* Trunk Actions                                                           *)
(***************************************************************************)

\* TODO
OpenTrunk == /\ Trunk!Open
             /\ UNCHANGED(vars_doors)
              /\ UNCHANGED<<mismatchCounter>>

\* TODO
CloseTrunk == /\ Trunk!Close
              /\ UNCHANGED(vars_doors)
              /\ UNCHANGED<<mismatchCounter>>

\* Unlock trunk without unlocking doors 
UnlockTrunk == /\ IsCarLocked
               /\ CheckPin(Trunk!Unlock, UNCHANGED<<trunkState>>)
               /\ UNCHANGED(vars_doors)

\* Lock trunk again if trunk was unlocked on its own 
LockTrunk == /\ AreDoorsLocked
             /\ IsTrunkUnlocked
             /\ Trunk!Lock
             /\ UNCHANGED(vars_doors)
             /\ UNCHANGED<<mismatchCounter>>

\* TODO
TrunkActions == \/ OpenTrunk
                \/ CloseTrunk
                \/ LockTrunk              
                \/ UnlockTrunk              

(***************************************************************************)
(* Lock Actions                                                            *)
(***************************************************************************)

\* TODO
LockCar == /\ IsCarUnlocked
           /\ PassengerArea!Lock
           /\ Trunk!Lock
           /\ mismatchCounter' = 0
           /\ UNCHANGED<<passengerDoors>>

\* TODO
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

\* Action that allows changing the wireless key pin
\* This is possible in an unlocked state and requires the old and the new pin
\* to be provided
\* If the old (= current) pin is provided wrongly for three times, a mismatch alarm
\* will be triggered
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

\* check that the passenger area spec also holds in the TLC
PassengerAreaSpec == /\ PassengerArea!Spec
                     /\ PassengerArea!TypeInvariant

\* check that the trunk spec also holds in the TLC
TrunkSpec == /\ Trunk!Spec
             /\ Trunk!TypeInvariant

\* check that the doors module spec also holds in the TLC
DoorsSpec == /\ Doors!Spec
             /\ Doors!SafetyInvariant
             /\ Doors!TypeInvariant

THEOREM Spec => /\ PassengerAreaSpec
                /\ TrunkSpec
                /\ DoorsSpec
                /\ []Invariant

=============================================================================
