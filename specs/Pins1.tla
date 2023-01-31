------------------------------- MODULE Pins1 -------------------------------

(***************************************************************************)
(* Module with a single refinement for pins:                               *)
(*                                                                         *)
(* The module represents the set of keys a car has along with their        *)
(* respective mismatch counters for wireless unlocks and pin changes. The  *)
(* maximum number of keys (= length of the key/counter sets) is set in the *)
(* configuration. Each counter consists of the key index and the current   *)
(* count of the specific mismatch type.                                    *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANT
    MaxPins,                        \* Number of currently usable pins; Equivalent to the number of keys
    MaxPinMismatch                  \* Max. count until a pin mismatch alarm is triggered 
                                    \* (here: how often can a key send a wrong pin)

ASSUME MaxPinMismatch \in Nat       \* MaxPinMismatch is set in the TLC, 3 tries by requirement
ASSUME MaxPins \in Nat              \* MaxPins is set in the TLC, requirement does not specify a specific number
    
VARIABLES 
    changeMismatchCounters,         \* tracks how many wrong pins were sent to change the pin in an unlocked state
    unlockMismatchCounters,         \* tracks how many wrong pins were sent while in an armed state to unlock the car
    trunkUnlockMismatchCounters     \* tracks how many wrong pins were sent while in an armed state to unlock the trunk alone

vars ==
    <<
        changeMismatchCounters,
        unlockMismatchCounters,
        trunkUnlockMismatchCounters
    >>

(***************************************************************************)
(* Guards                                                                  *)
(* Accessible outside to ease guard usage for the module if instantiated   *)
(***************************************************************************)

\* Guard that is true if any of the passed counters has reached the max value
IsMaxMismatch(counters) == \E counter \in counters : counter[2] >= MaxPinMismatch

\* Guard that is true if all of the counters have mismatch value 0
IsCountersNoMismatch(counters) == \A counter \in counters : counter[2] = 0

\* Group of guards that allow to check if a given mismatch type has reached
\* the max value
IsChangeMaxMismatch == /\ IsMaxMismatch(changeMismatchCounters)
IsUnlockMaxMismatch == /\ IsMaxMismatch(unlockMismatchCounters)
IsTrunkMaxMismatch == /\ IsMaxMismatch(trunkUnlockMismatchCounters)

\* Guard that is true if any of the mismatch types have reached the max value
IsAnyMaxMismatch == \/ IsChangeMaxMismatch
                    \/ IsUnlockMaxMismatch
                    \/ IsTrunkMaxMismatch

\* Group of guards that allow to check if a given mismatch type has mismatch value 0
IsChangeNoMismatch == /\ IsCountersNoMismatch(changeMismatchCounters)
IsUnlockNoMismatch == /\ IsCountersNoMismatch(unlockMismatchCounters)
IsTrunkNoMismatch == /\ IsCountersNoMismatch(trunkUnlockMismatchCounters)

\* Group of guards that allow to check if all mismatch types have mismatch value 0
IsNoMismatch == /\ IsChangeNoMismatch
                /\ IsUnlockNoMismatch
                /\ IsTrunkNoMismatch

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* check that the number of counters is equivalent to the numbers of keys/pins
\* first value should be the pin, then the mismatch counter
CounterTypeInvariant(set) == 
                 /\ Cardinality(set) = MaxPins
                 /\ \A counter \in set: 
                    /\ counter[1] \in 0..MaxPins
                    /\ counter[2] \in 0..MaxPinMismatch

TypeInvariant == /\ CounterTypeInvariant(changeMismatchCounters)
                 /\ CounterTypeInvariant(unlockMismatchCounters)
                 /\ CounterTypeInvariant(trunkUnlockMismatchCounters)

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* Init a counters set for all mismatch types for each key and init them with count 0
Init == /\ changeMismatchCounters = { <<i,0>> : i \in 1..MaxPins}
        /\ unlockMismatchCounters = { <<i,0>> : i \in 1..MaxPins}
        /\ trunkUnlockMismatchCounters = { <<i,0>> : i \in 1..MaxPins}

\* Resets the counters for a specific mismatch type to 0
ResetCounters(counters) == counters' = { <<i,0>> : i \in 1..MaxPins}

\* Action that is called to non-deterministically check if a sent pin matches
\* and so can unlock the car or change the pin, or if the pin is incorrect
\* It takes the action that should be executed next if the pin matches or the unchanged
\* variables if the pin does not match and the action does not get executed
CheckPin(action, counters, unchanged) == 
    /\ ~ IsMaxMismatch(counters)
    /\ \E b \in BOOLEAN:
        IF b = TRUE
            THEN /\ action
                 /\ ResetCounters(counters)
            ELSE /\ \E counter \in counters:
                    counters' = {x \in counters : x[1] /= counter[1]}
                                \union {<<counter[1], counter[2]+1>>}
                 /\ unchanged

\* Action that calls the CheckPin action for a change pin operation
CheckChangeMismatchCounter(action, unchanged) == 
    /\ CheckPin(action, changeMismatchCounters, unchanged)

\* Action that calls the CheckPin action for an unlock operation
CheckUnlockMismatchCounter(action, unchanged) == 
    /\ CheckPin(action, unlockMismatchCounters, unchanged)

\* Action that calls the CheckPin action for an unlock trunk operation
CheckTrunkUnlockMismatchCounters(action, unchanged) == 
    /\ CheckPin(action, trunkUnlockMismatchCounters, unchanged)

\* Resets the change pin mismatch counters for all keys
ResetChangeCounters == /\ ResetCounters(changeMismatchCounters)

\* Resets the unlock mismatch counters for all keys
ResetUnlockCounters == /\ ResetCounters(unlockMismatchCounters)

\* Resets the unlock trunk mismatch counters for all keys
ResetTrunkCounters == /\ ResetCounters(trunkUnlockMismatchCounters)

\* Action that calls the CheckPin action for a change pin operation
\* used if no variables change
CheckChangeMismatch == 
    /\ CheckChangeMismatchCounter(TRUE, TRUE)
    /\ UNCHANGED<<unlockMismatchCounters, trunkUnlockMismatchCounters>>

\* Action that calls the CheckPin action for an unlock operation
\* used if no variables change
CheckUnlockMismatch == 
    /\ CheckUnlockMismatchCounter(TRUE, TRUE)
    /\ UNCHANGED<<changeMismatchCounters, trunkUnlockMismatchCounters>>

\* Action that calls the CheckPin action for an unlock trunk operation
\* used if no variables change
CheckTrunkUnlockMismatch == 
    /\ CheckTrunkUnlockMismatchCounters(TRUE, TRUE)
    /\ UNCHANGED<<unlockMismatchCounters, changeMismatchCounters>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ CheckChangeMismatch
        \/ CheckUnlockMismatch
        \/ CheckTrunkUnlockMismatch
        \/ /\ IsChangeMaxMismatch
           /\ IsUnlockMaxMismatch
           /\ IsTrunkMaxMismatch
           /\ ResetChangeCounters
           /\ ResetUnlockCounters
           /\ ResetTrunkCounters

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

THEOREM Spec => /\ []TypeInvariant

=============================================================================
