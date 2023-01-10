-------------------------- MODULE CarAlarmSystem1 --------------------------

(***************************************************************************)
(* Base refinement for the car alarm system                                *)
(***************************************************************************)

CONSTANT openAndUnlocked, closedAndLocked
ASSUME openAndUnlocked /= closedAndLocked

STATES == {openAndUnlocked, closedAndLocked}

VARIABLES state

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == state \in STATES

SafetyInvariant == \/ state = openAndUnlocked
                   \/ state = closedAndLocked
                 
(***************************************************************************)
(* Actions                                                                  *)
(***************************************************************************)

Init == state = openAndUnlocked

Lock_Close == /\ state = openAndUnlocked
              /\ state' = closedAndLocked  

Unlock_Open == /\ state = closedAndLocked
              /\ state' = openAndUnlocked

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == Lock_Close \/ Unlock_Open

Spec1 == Init /\ [][Next]_state

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

THEOREM Spec1 => [] TypeInvariant

THEOREM Spec1 => [] SafetyInvariant

=============================================================================
\* Modification History
\* Last modified Tue Jan 10 15:38:30 CET 2023 by mitch
\* Last modified Sat Dec 31 09:01:42 CET 2022 by marian
\* Created Sat Dec 31 08:58:24 CET 2022 by marian
