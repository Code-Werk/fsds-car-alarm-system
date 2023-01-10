-------------------------- MODULE CarAlarm2 --------------------------
EXTENDS Reals

(***************************************************************************)
(* Second refinement for the car alarm                                     *)
(***************************************************************************)


VARIABLES flash, sound, now

vars == <<flash, sound, now>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ flash \in BOOLEAN
                 /\ sound \in BOOLEAN
                 /\ now \in Real
                 
SafetyInvariant == \/ flash = sound
                   \/ flash = 1 /\ sound = 0    

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ flash = 0
        /\ sound = 0
        /\ now   = 0

Activate == /\ flash' = 1
            /\ sound' = 1
            /\ now'    = 0

DeactivateSound == /\ now > 30
                   /\ flash  = 1
                   /\ sound  = 1
                   /\ sound' = 0
                   /\ UNCHANGED<<flash, now>>

Deactivate == /\ flash' = 0
              /\ sound' = 0
              /\ UNCHANGED<<now>>

Tick == /\ sound = 1
        /\ \E r \in Real:
            /\ r > 0
            /\ now' = now + r
            /\ UNCHANGED<<flash, sound>>
    
(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Activate 
        \/ DeactivateSound
        \/ Deactivate
        \/ Tick

SpecAlarm2 == Init /\ [][Next]_vars

FairSpecAlarm2 == /\ SpecAlarm2 
                  /\ \A r \in Real :  WF_now(Tick /\ now' > r)

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

CarAlarm1 == INSTANCE CarAlarm1

THEOREM SpecAlarm2 => /\ CarAlarm1!SpecAlarm1
                 /\ TypeInvariant
                 /\ SafetyInvariant

=============================================================================
\* Modification History
\* Last modified Tue Jan 10 21:15:14 CET 2023 by mitch
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
