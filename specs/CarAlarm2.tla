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
                 /\ now \in AlarmRange
                 
SafetyInvariant == \/ flash = sound
                   \/ flash = 1 /\ sound = 0

RunningAlarmInvariant == \/ flash = 1

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

SpecAlarm2 == Init /\ [][Next]_vars

FairSpecAlarm2 == /\ SpecAlarm2 
                  /\ \A r \in AlarmRange :  WF_now(Tick /\ now' > r)

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
