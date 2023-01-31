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
    DoorCount,                      \* Amount of the car's passenger doors
    MaxPinMismatch                  \* Max. count until a pin mismatch alarm is triggered 
                                    \* (here: how often can a key send a wrong pin)
ASSUME DoorCount \in {2,4}          \* DoorCount is set in the TLC
                                    \* has to either be 2 or 4 by requirement
ASSUME MaxPinMismatch \in Nat       \* MaxPinMismatch is set in the TLC, 3 tries by requirement

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
    trunkState,                     \* variable holding the current state of the trunk module
                                    \* together with the passenger area state this is the car's state
    changeMismatchCounter,          \* tracks how many wrong pins were sent to change the pin in an unlocked state
    unlockMismatchCounter,          \* tracks how many wrong pins were sent while in an armed state to unlock the car
    trunkUnlockMismatchCounter      \* tracks how many wrong pins were sent while in an armed state to unlock the trunk alone
  
vars == <<
    trunkState, 
    passengerAreaState,
    passengerDoors,
    changeMismatchCounter,
    unlockMismatchCounter,
    trunkUnlockMismatchCounter>>

vars_doors == <<passengerAreaState, passengerDoors>>
pin_vars == <<changeMismatchCounter, unlockMismatchCounter, trunkUnlockMismatchCounter>>

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
                 /\ changeMismatchCounter \in 0..MaxPinMismatch
                 /\ unlockMismatchCounter \in 0..MaxPinMismatch
                 /\ trunkUnlockMismatchCounter \in 0..MaxPinMismatch
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
\* set mismatch counters to 0
Init == /\ Doors!Init
        /\ PassengerArea!Init
        /\ Trunk!Init
        /\ changeMismatchCounter = 0
        /\ unlockMismatchCounter = 0
        /\ trunkUnlockMismatchCounter = 0

(***************************************************************************)
(* Helper Actions                                                          *)
(* These actions need to be defined before actions that use them           *)
(***************************************************************************)

\* Helper action that is called to non-deterministically check if a sent pin matches,
\* and so can unlock the car or change the pin, or if the pin is incorrect
\* It takes the action that should be executed next if the pin matches or the unchanged
\* variables if the pin does not match and the action does not get executed
CheckPin(action, mismatchVar, unchanged) == 
    /\ \E b \in BOOLEAN:
        IF b = TRUE
            THEN /\ action
                 /\ mismatchVar' = 0
            ELSE /\ mismatchVar < MaxPinMismatch 
                 /\ mismatchVar' = mismatchVar + 1
                 /\ unchanged

(***************************************************************************)
(* Doors Actions                                                           *)
(***************************************************************************)

\* Opens the first passenger door after all of them were closed
OpenDoor_From_Closed == /\ AreDoorsClosed
                        /\ PassengerArea!Open
                        /\ Doors!Open
                        /\ UNCHANGED<<trunkState>>
                        /\ UNCHANGED(pin_vars)

\* Opens another passenger door (which means at least one has been opened before,
\* but there are still closed ones)
OpenDoor_Another_One == /\ AreDoorsOpen
                        /\ Doors!Open
                        /\ UNCHANGED<<passengerAreaState, trunkState>>
                        /\ UNCHANGED(pin_vars)

\* Closes a passenger door if there is at least one open door
\* If it was the last open door, the passenger area state changes
CloseDoor == /\ AreDoorsOpen
             /\ Doors!Close \*includes open check
             /\ IF {pd \in passengerDoors' : pd[2] = TRUE} = {}
                    THEN /\ PassengerArea!Close
                    ELSE /\ UNCHANGED<<passengerAreaState>>
             /\ UNCHANGED<<trunkState>>
             /\ UNCHANGED(pin_vars)

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
             /\ UNCHANGED(pin_vars)

\* Closes the car's trunk
CloseTrunk == /\ Trunk!Close
              /\ UNCHANGED(vars_doors)
              /\ UNCHANGED(pin_vars)

\* Unlock trunk without unlocking doors
\* this is used to open the trunk even though the car is in an armed state
UnlockTrunk == /\ IsCarLocked
               /\ CheckPin(Trunk!Unlock, trunkUnlockMismatchCounter, UNCHANGED<<trunkState>>)
               /\ UNCHANGED(vars_doors)
               /\ UNCHANGED<<changeMismatchCounter, unlockMismatchCounter>>

\* Lock trunk again if only the trunk was unlocked before
LockTrunk == /\ AreDoorsLocked
             /\ IsTrunkUnlocked
             /\ Trunk!Lock
             /\ trunkUnlockMismatchCounter' = 0
             /\ UNCHANGED(vars_doors)
             /\ UNCHANGED<<changeMismatchCounter, unlockMismatchCounter>>

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
           /\ changeMismatchCounter' = 0
           /\ unlockMismatchCounter' = 0
           /\ trunkUnlockMismatchCounter' = 0
           /\ UNCHANGED<<passengerDoors>>

\* Unlocks the entire car (passenger area and trunk)
\* This requires a pin check, since this is only possible from an armed state
\* If the trunk was already unlocked before, ignore it in the state change
UnlockCar == /\ AreDoorsLocked
             /\ CheckPin(
                /\ PassengerArea!Unlock
                /\ IF IsTrunkLocked
                       THEN /\ Trunk!Unlock
                       ELSE /\ UNCHANGED<<trunkState>>
                /\ trunkUnlockMismatchCounter'= 0,
                unlockMismatchCounter,
                /\ UNCHANGED<<passengerAreaState, trunkState, trunkUnlockMismatchCounter>>)
             /\ UNCHANGED<<changeMismatchCounter, passengerDoors>>

(***************************************************************************)
(* Pin Actions                                                             *)
(***************************************************************************)

\* Action that allows changing the wireless key pin
\* This is possible in an unlocked state and requires the old and the new pin
\* to be provided
\* If the old (= current) pin is provided incorrectly for three times, a mismatch alarm
\* will be triggered
SetNewPin == /\ IsCarUnlocked
             /\ CheckPin(TRUE, changeMismatchCounter, TRUE)
             /\ UNCHANGED<<
                passengerAreaState, 
                passengerDoors, 
                trunkState, 
                unlockMismatchCounter,
                trunkUnlockMismatchCounter>>

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
