-------------------------- MODULE CarAlarm1 --------------------------

(***************************************************************************)
(* Base refinement for the car alarm                                       *)
(***************************************************************************)

VARIABLES flash, sound

vars == <<flash, sound>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ flash \in BOOLEAN
                 /\ sound \in BOOLEAN
                 
SafetyInvariant == \/ flash = sound
                   \/ /\ flash = TRUE 
                      /\ sound = FALSE    

Invariant == /\ TypeInvariant
             /\ SafetyInvariant 

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ flash = FALSE
        /\ sound = FALSE

Activate == /\ flash' = TRUE
            /\ sound' = TRUE

DeactivateSound == /\ flash  = TRUE
                   /\ sound  = TRUE
                   /\ sound' = FALSE
                   /\ UNCHANGED<<flash>>

Deactivate == /\ flash' = FALSE
              /\ sound' = FALSE
    
(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Activate 
        \/ DeactivateSound
        \/ Deactivate

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification                                                  *)
(***************************************************************************)

THEOREM Spec => []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:39:54 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
