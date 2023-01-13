-------------------------- MODULE CarAlarm1 --------------------------

(***************************************************************************)
(* First and base refinement for the alarm sub module of the car alarm     *)
(* system:                                                                 *)
(*                                                                         *)
(* In the initial step of this sub module we check that the internal alarm *)
(* of the car alarm system can be activated, deactivated and reach a state *)
(* where the sound is off and only the flash is still on, but not the other*)
(* way around. We do not care when the sound is turned of yet, but only    *)
(* that it is possible. The alarm can be activated or reactivated at any   *)
(* given point.                                                            *)
(*                                                                         *)
(* This refinement targets Requirements 2.                                 *)
(***************************************************************************)

VARIABLES flash, sound      \* flags to indicate if flash and sound are on

vars == <<flash, sound>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ flash \in BOOLEAN
                 /\ sound \in BOOLEAN
                 
SafetyInvariant == \/ flash = sound             \* sound and flash are either both on or both of
                   \/ /\ flash = TRUE           \* or we are in the alarm state where sound is deactivated
                      /\ sound = FALSE          \* but the alarm is still flashing

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ flash = FALSE                    \* alarm is deactivated in the beginning
        /\ sound = FALSE

Activate == /\ flash' = TRUE                \* activate the alarm by turning on the flash and sound
            /\ sound' = TRUE

DeactivateSound == /\ flash  = TRUE         \* deactivate the alarm sound
                   /\ sound  = TRUE
                   /\ sound' = FALSE
                   /\ UNCHANGED<<flash>>

Deactivate == /\ flash' = FALSE             \* deactivate the alarm by turning off the flash and sound
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
