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
                   \/ flash = 1 /\ sound = 0    

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ flash = 0
        /\ sound = 0

Activate == /\ flash' = 1
            /\ sound' = 1

DeactivateSound == /\ flash  = 1
                   /\ sound  = 1
                   /\ sound' = 0
                   /\ UNCHANGED<<flash>>

Deactivate == /\ flash' = 0
              /\ sound' = 0
    
(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Activate 
        \/ DeactivateSound
        \/ Deactivate

SpecAlarm1 == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

THEOREM SpecAlarm1 => /\ TypeInvariant
                      /\ SafetyInvariant

=============================================================================
\* Modification History
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
