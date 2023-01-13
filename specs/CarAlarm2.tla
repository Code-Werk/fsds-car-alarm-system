-------------------------- MODULE CarAlarm2 --------------------------

(***************************************************************************)
(* Second refinement for the car alarm                                     *)
(***************************************************************************)

EXTENDS Naturals

DefaultAlarmRange == 1..31

CONSTANT SoundDuration, AlarmRange

VARIABLES flash, sound, now

vars == <<flash, sound, now>>

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

Init == /\ flash = 0
        /\ sound = 0
        /\ now   = 0

Activate == /\ flash = 0
            /\ flash' = 1
            /\ sound' = 1
            /\ now'    = 0

DeactivateSound == /\ now > SoundDuration
                   /\ flash  = 1
                   /\ sound  = 1
                   /\ sound' = 0
                   /\ UNCHANGED<<flash, now>>

Deactivate == /\ flash' = 0
              /\ sound' = 0
              /\ UNCHANGED<<now>>

Tick == /\ sound = 1
        /\ \E d \in { n \in AlarmRange : n > now}:
            now' = d 
        /\ UNCHANGED<<flash, sound>>
    
(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Activate 
        \/ DeactivateSound
        \/ Deactivate
        \/ Tick

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarm1 == INSTANCE CarAlarm1

THEOREM Spec => /\ CarAlarm1!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:39:41 CET 2023 by marian
\* Last modified Tue Jan 10 21:15:14 CET 2023 by mitch
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
