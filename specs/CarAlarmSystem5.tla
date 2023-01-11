-------------------------- MODULE CarAlarmSystem4 --------------------------

(***************************************************************************)
(* Fourth refinement for the car alarm system                              *)
(***************************************************************************)
\* TODO is old copy of 4 with time: do refinment
EXTENDS Naturals

DefaultAlarmRange == 1..31
DefaultSilentAlarmRange == 1..301

CONSTANT ArmingDelay, AlarmDuration, AlarmRange, SilentAlarmRange, SoundDuration

OpenAndUnlocked   == 0
ClosedAndLocked   == 1
OpenAndLocked     == 2
ClosedAndUnlocked == 3
Armed             == 4
Alarm             == 5
SilentAndOpen     == 6

STATES == 
    {
        OpenAndUnlocked, 
        ClosedAndLocked, 
        OpenAndLocked, 
        ClosedAndUnlocked, 
        Armed, 
        Alarm, 
        SilentAndOpen
    }

VARIABLES state, isArmed, now

vars == <<state, isArmed, now>>

CarAlarm == INSTANCE CarAlarm2 WITH flash <- 0, sound <- 0, now <- 0

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN 
                 /\ now \in Nat
                 
SafetyInvariant == /\ IF state = Armed 
                      THEN isArmed = TRUE
                      ELSE isArmed = FALSE
                \*    /\ state = Alarm => CarAlarm!RunningAlarmInvariant
     
                 
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ state = OpenAndUnlocked
        /\ isArmed = FALSE
        /\ now = 0


Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED<<isArmed,now>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked
                             /\ state' = ClosedAndLocked
                             /\ now' = 0
                             /\ UNCHANGED<<isArmed>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen
                             /\ state' = Armed
                             /\ isArmed' = TRUE
                             /\ UNCHANGED<<now>>

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED<<isArmed, now>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ now'   = 0
                                /\ UNCHANGED<<isArmed>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED<<isArmed, now>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED<<isArmed, now>>

Open_After_Armed == /\ state  = Armed
                    /\ state' = Alarm
                    /\ isArmed' = FALSE
                    /\ now' = 0
                    \* /\ CarAlarm!Activate

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ UNCHANGED<<isArmed, now>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<isArmed, now>>
             
Unlock_After_Armed == /\ state  = Armed
                      /\ state' = ClosedAndUnlocked
                      /\ isArmed' = FALSE
                      /\ UNCHANGED<<now>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ state' = OpenAndUnlocked
                      \* /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed, now>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<isArmed, now>>

Arming == /\ now > ArmingDelay
          /\ state  = ClosedAndLocked
          /\ state' = Armed
          /\ isArmed' = TRUE
          /\ UNCHANGED<<now>>

SilentAlarm == /\ now > AlarmDuration
               /\ state = Alarm
               /\ state' = SilentAndOpen
            \*    /\ CarAlarm!Deactivate
               /\ UNCHANGED<<isArmed, now>>

Tick == /\ state \in { ClosedAndLocked, Alarm }
        /\ \E d \in { n \in SilentAlarmRange : n > now}:
            now' = d 
        /\ UNCHANGED<<state, isArmed>>

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

\* Next == \/ Close 
\*         \/ Lock 
\*         \/ Open 
\*         \/ Unlock
Next == \/ Close_After_OpenAndUnlocked
        \/ Close_After_OpenAndLocked
        \/ Close_After_SilentAndOpen
        \/ Lock_After_OpenAndUnlocked
        \/ Lock_After_ClosedAndUnlocked
        \/ Open_After_ClosedAndUnlocked
        \/ Open_After_ClosedAndLocked
        \/ Open_After_Armed
        \/ Unlock_After_ClosedAndLocked
        \/ Unlock_After_OpenAndLocked
        \/ Unlock_After_Armed
        \/ Unlock_After_Alarm
        \/ Unlock_After_SilentAndOpen
        \/ Arming
        \/ SilentAlarm
        \/ Tick
        \* \/ CarAlarm!Tick
        \* \/ CarAlarm!DeactivateSound

Spec4 == Init /\ [][Next]_vars

\* FairSpec4 == /\ Spec4 
\*              /\ \A r \in SilentAlarmRange : WF_now(Tick /\ now' > r)

(***************************************************************************)
(* Verified Refinement                                                     *)
(***************************************************************************)

CarAlarmSystem3 == INSTANCE CarAlarmSystem3

THEOREM Spec4 => /\ CarAlarmSystem3!Spec3
                 /\ CarAlarm!SpecAlarm2
                 /\ TypeInvariant
                 /\ SafetyInvariant

=============================================================================
\* Modification History
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
