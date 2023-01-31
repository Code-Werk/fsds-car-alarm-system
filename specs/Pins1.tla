------------------------------- MODULE Pins1 -------------------------------

(***************************************************************************)
(* Module with a single refinement for pins:                               *)
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

\* TODO
Init == /\ changeMismatchCounters = { <<i,0>> : i \in 1..MaxPins}
        /\ unlockMismatchCounters = { <<i,0>> : i \in 1..MaxPins}
        /\ trunkUnlockMismatchCounters = { <<i,0>> : i \in 1..MaxPins}

ResetCounters(counters) == counters' = { <<i,0>> : i \in 1..MaxPins}

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

CheckChangeMismatchCounter(action, unchanged) == 
    /\ CheckPin(action, changeMismatchCounters, unchanged)

CheckUnlockMismatchCounter(action, unchanged) == 
    /\ CheckPin(action, unlockMismatchCounters, unchanged)

CheckTrunkUnlockMismatchCounters(action, unchanged) == 
    /\ CheckPin(action, trunkUnlockMismatchCounters, unchanged)

ResetChangeCounters == /\ ResetCounters(changeMismatchCounters)
ResetUnlockCounters == /\ ResetCounters(unlockMismatchCounters)
ResetTrunkCounters == /\ ResetCounters(trunkUnlockMismatchCounters)

CheckChangeMismatch == 
    /\ CheckChangeMismatchCounter(TRUE, TRUE)
    /\ UNCHANGED<<unlockMismatchCounters, trunkUnlockMismatchCounters>>

CheckUnlockMismatch == 
    /\ CheckUnlockMismatchCounter(TRUE, TRUE)
    /\ UNCHANGED<<changeMismatchCounters, trunkUnlockMismatchCounters>>

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
