-------------------------- MODULE CarAlarm2 --------------------------

(***************************************************************************)
(* Second refinement for the car alarm                                     *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT SoundDuration

AlarmRange == 0..SoundDuration

VARIABLES flash, sound, soundTimer

vars == <<flash, sound, soundTimer>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ flash \in BOOLEAN
                 /\ sound \in BOOLEAN
                 /\ soundTimer \in SoundDuration
                 
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
        /\ soundTimer = 0

Activate == /\ flash = 0
            /\ flash' = 1
            /\ sound' = 1
            /\ soundTimer' = SoundDuration

DeactivateSound == /\ soundTimer = 0
                   /\ flash  = 1
                   /\ sound  = 1
                   /\ sound' = 0
                   /\ UNCHANGED<<flash, soundTimer>>

Deactivate == /\ flash' = 0
              /\ sound' = 0
              /\ soundTimer' = 0
              /\ UNCHANGED<<soundTimer>>

Tick == /\ sound = 1
        /\ \E d \in { n \in AlarmRange : n < soundTimer}:
            soundTimer' = d 
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
