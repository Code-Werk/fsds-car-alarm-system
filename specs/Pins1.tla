-------------------------- MODULE Pins1 --------------------------

(***************************************************************************)
(* Module with a single refinement for pins:                               *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANT MaxPins,
    MaxPinMismatch                 \* Max. count until a pin mismatch alarm is triggered 
                                    \* (here: how often can a key send a wrong pin)

ASSUME MaxPinMismatch \in Nat       \* MaxPinMismatch is set in the TLC, 3 tries by requirement
ASSUME MaxPins \in Nat
    
VARIABLES 
    changeMismatchCounters,
    unlockMismatchCounters,
    trunkUnlockMismatchCounters

vars == <<
    changeMismatchCounters, 
    unlockMismatchCounters, 
    trunkUnlockMismatchCounters>>


(***************************************************************************)
(* Guards                                                                  *)
(* Accessible outside to ease guard usage for the module if instantiated   *)
(***************************************************************************)


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

CounterTypeInvariant(set) == 
                 /\ Cardinality(set) = MaxPins
                 /\ \A counter \in set: 
                    /\ counter[1] \in 0..MaxPins
                    /\ counter[2] \in 0..MaxPinMismatch

TypeInvariant == /\ CounterTypeInvariant(changeMismatchCounters)
                 /\ CounterTypeInvariant(unlockMismatchCounters)
                 /\ CounterTypeInvariant(trunkUnlockMismatchCounters)


SafetyInvariant == /\ TRUE

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

ResetCounters(counters) == counters' = { <<i,0>> : i \in 1..MaxPins}

IsMaxMismatch(counters) == \E counter \in counters : counter[2] >= MaxPinMismatch

IsCountersNoMismatch(counters) == \A counter \in counters : counter[2] = 0

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
    /\ UNCHANGED<<unlockMismatchCounters, trunkUnlockMismatchCounters>>

CheckUnlockMismatchCounter(action, unchanged) == 
    /\ CheckPin(action, unlockMismatchCounters, unchanged)
    /\ UNCHANGED<<changeMismatchCounters, trunkUnlockMismatchCounters>>

CheckTrunkUnlockMismatchCounters(action, unchanged) == 
    /\ CheckPin(action, trunkUnlockMismatchCounters, unchanged)
    /\ UNCHANGED<<unlockMismatchCounters, changeMismatchCounters>>


IsChangeMaxMismatch == /\ IsMaxMismatch(changeMismatchCounters)
IsUnlockMaxMismatch == /\ IsMaxMismatch(unlockMismatchCounters)
IsTrunkMaxMismatch == /\ IsMaxMismatch(trunkUnlockMismatchCounters)

IsAnyMaxMismatch == \/ IsChangeMaxMismatch
                    \/ IsUnlockMaxMismatch
                    \/ IsTrunkMaxMismatch

IsChangeNoMismatch == /\ IsCountersNoMismatch(changeMismatchCounters)
IsUnlockNoMismatch == /\ IsCountersNoMismatch(unlockMismatchCounters)
IsTrunkNoMismatch == /\ IsCountersNoMismatch(trunkUnlockMismatchCounters)
                     
IsNoMismatch == /\ IsChangeNoMismatch
                /\ IsUnlockNoMismatch
                /\ IsTrunkNoMismatch

ResetChangeCounters == /\ ResetCounters(changeMismatchCounters)
ResetUnlockCounters == /\ ResetCounters(unlockMismatchCounters)
ResetTrunkCounters == /\ ResetCounters(trunkUnlockMismatchCounters)

\* TODO
Init == /\ changeMismatchCounters = { <<i,0>> : i \in 1..MaxPins}
        /\ unlockMismatchCounters = { <<i,0>> : i \in 1..MaxPins}
        /\ trunkUnlockMismatchCounters = { <<i,0>> : i \in 1..MaxPins}

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ CheckChangeMismatchCounter(TRUE, TRUE)
        \/ CheckUnlockMismatchCounter(TRUE, TRUE)
        \/ CheckTrunkUnlockMismatchCounters(TRUE, TRUE)
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

THEOREM Spec => /\ []Invariant

=============================================================================
