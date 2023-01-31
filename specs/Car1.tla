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

CONSTANT DoorCount                  \* Amount of the car's passenger doors
ASSUME DoorCount \in {2,4}          \* DoorCount is set in the TLC
                                    \* has to either be 2 or 4 by requirement

OpenAndUnlocked   == 0              \* Car is open and unlocked
ClosedAndLocked   == 1              \* Car is closed and locked
OpenAndLocked     == 2              \* Car is still open but already locked
ClosedAndUnlocked == 3              \* Car is not yet closed but already locked

STATES ==                           \* Possible car states
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
    trunkState                      \* variable holding the current state of the trunk module
                                    \* together with the passenger area state this is the car's state
  
vars ==
    <<
        trunkState,
        passengerAreaState,
        passengerDoors
    >>

vars_doors == <<passengerAreaState, passengerDoors>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

\* instance of the 2nd car alarm system refinement to represent the open/closed
\* and locked/unlocked states of the doors in the car's passenger area
PassengerArea == INSTANCE CarAlarmSystem2 WITH state <- passengerAreaState
\* instance of the 2nd car alarm system refinement to represent the open/closed
\* and locked/unlocked states of the car's trunk
Trunk == INSTANCE CarAlarmSystem2 WITH state <- trunkState
\* instance of the doors module to represent the car doors
Doors == INSTANCE Doors1 WITH passengerDoors <- passengerDoors

(***************************************************************************)
(* Guards                                                                  *)
(* Accessible outside to ease guard usage for the module if instantiated   *)
(***************************************************************************)

\* Group of guards that allows to check if a given state is a closed, opened
\* locked or unlocked state
IsStateClosed(state) == /\ state \in {ClosedAndLocked, ClosedAndUnlocked}
IsStateLocked(state) == /\ state \in {ClosedAndLocked, OpenAndLocked}
IsStateOpen(state) == /\ state \in {OpenAndLocked, OpenAndUnlocked}
IsStateUnlocked(state) == /\ state \in {ClosedAndUnlocked, OpenAndUnlocked}

\* Group of guards that allows to check if the passenger area doors are in a 
\* closed, opened, locked or unlocked state
AreDoorsClosed == /\ Doors!AreClosed /\ IsStateClosed(passengerAreaState)
AreDoorsLocked == /\ IsStateLocked(passengerAreaState)
AreDoorsOpen == /\ Doors!AreOpen /\ IsStateOpen(passengerAreaState)
AreDoorsUnlocked == /\ IsStateUnlocked(passengerAreaState)

\* Group of guards that allows to check if the trunk is in a 
\* closed, opened, locked or unlocked state
IsTrunkClosed == /\ IsStateClosed(trunkState)
IsTrunkLocked == /\ IsStateLocked(trunkState)
IsTrunkOpen == /\ IsStateOpen(trunkState)
IsTrunkUnlocked == /\ IsStateUnlocked(trunkState)

\* Group of guards that allows to check if the entire car (passenger doors, trunk)
\* is in a closed, opened, locked or unlocked state
IsCarClosed == /\ AreDoorsClosed /\ IsTrunkClosed
IsCarLocked == /\ AreDoorsLocked /\ IsTrunkLocked 
IsCarOpen == /\ AreDoorsOpen /\ IsTrunkOpen
IsCarUnlocked == /\ AreDoorsUnlocked /\ IsTrunkUnlocked

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ passengerAreaState \in STATES
                 /\ trunkState \in STATES
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

\* Initialize the external modules (doors, passenger area and trunk)
Init == /\ Doors!Init
        /\ PassengerArea!Init
        /\ Trunk!Init

(***************************************************************************)
(* Doors Actions                                                           *)
(***************************************************************************)

\* Opens the first passenger door after all of them were closed
OpenDoor_From_Closed == /\ AreDoorsClosed
                        /\ PassengerArea!Open
                        /\ Doors!Open
                        /\ UNCHANGED<<trunkState>>

\* Opens another passenger door (which means at least one has been opened before,
\* but there are still closed ones)
OpenDoor_Another_One == /\ AreDoorsOpen
                        /\ Doors!Open
                        /\ UNCHANGED<<passengerAreaState, trunkState>>

\* Closes a passenger door if there is at least one open door
\* If it was the last open door, the passenger area state changes
CloseDoor == /\ AreDoorsOpen
             /\ Doors!Close \*includes open check
             /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                    THEN /\ PassengerArea!Close
                    ELSE /\ UNCHANGED<<passengerAreaState>>
             /\ UNCHANGED<<trunkState>>

\* Action combining all actions possible in the passenger area (actions on the passenger doors)
DoorActions == \/ OpenDoor_Another_One
               \/ OpenDoor_From_Closed
               \/ CloseDoor

(***************************************************************************)
(* Trunk Actions                                                           *)
(***************************************************************************)

\* Opens the car's trunk
OpenTrunk == /\ Trunk!Open
             /\ UNCHANGED(vars_doors)

\* Closes the car's trunk
CloseTrunk == /\ Trunk!Close
              /\ UNCHANGED(vars_doors)

\* Unlock trunk without unlocking doors
\* this is used to open the trunk even though the car is in an armed state
UnlockTrunk == /\ IsCarLocked
               /\ Trunk!Unlock
               /\ UNCHANGED(vars_doors)

\* Lock trunk again if only the trunk was unlocked before
LockTrunk == /\ AreDoorsLocked
             /\ IsTrunkUnlocked
             /\ Trunk!Lock
             /\ UNCHANGED(vars_doors)

\* Action combining all actions possible for the car's trunk
TrunkActions == \/ OpenTrunk
                \/ CloseTrunk
                \/ LockTrunk              
                \/ UnlockTrunk              

(***************************************************************************)
(* Lock Actions                                                            *)
(***************************************************************************)

\* Locks the entire car (passenger area and trunk)
\* We are resetting the mismatch counts here, since we are moving into a locked state
LockCar == /\ IsCarUnlocked
           /\ PassengerArea!Lock
           /\ Trunk!Lock
           /\ UNCHANGED<<passengerDoors>>

\* Unlocks the entire car (passenger area and trunk)
\* This requires a pin check, since this is only possible from an armed state
\* If the trunk was already unlocked before, ignore it in the state change
UnlockCar == /\ AreDoorsLocked
             /\ PassengerArea!Unlock
             /\ IF IsTrunkLocked
                    THEN /\ Trunk!Unlock
                    ELSE /\ UNCHANGED<<trunkState>>
             /\ UNCHANGED<<passengerDoors>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ DoorActions
        \/ TrunkActions
        \/ LockCar
        \/ UnlockCar

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
