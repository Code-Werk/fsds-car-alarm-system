-------------------------- MODULE CarAlarmSystem4 --------------------------

(***************************************************************************)
(* Fourth refinement of the car alarm system:                              *)
(*                                                                         *)
(* In the fourth refinement we got more detailed with the car alarm        *)
(* system's actions and also added the external car alarm module. The car  *)
(* alarm module is used for the flash and sound functions of the alarm     *)
(* state. To achieve better overview over the car alarm the multipurpose   *)
(* Open, Close, Lock and Unlock were split into respective actions after a *)
(* given state (e.g. Close after one of the two open states).              *)
(* The alarm module is verified by itself and thus we know it works by     *)
(* itself and we can use it in this refinement to verify the entire system.*)
(* Since we do not care about timings yet, we use the first refinement of  *)
(* the alarm. The base function of the lower modules still holds as well.  *)
(*                                                                         *)
(* This refinement targets Requirements 1 - 3.                             *)
(***************************************************************************)

EXTENDS Naturals

OpenAndUnlocked   == 0          \* Car is open and unlocked
ClosedAndLocked   == 1          \* Car is closed and locked
OpenAndLocked     == 2          \* Car is still open but already locked
ClosedAndUnlocked == 3          \* Car is not yet closed but already locked
Armed             == 4          \* Car alarm system is armed (which means it is locked and closed and alarm could be triggered)
Alarm             == 5          \* Car alarm is on (which means an illegal action - car opened without unlocking - occurred in the armed state and the alarm was triggered)
SilentAndOpen     == 6          \* Car has been in alarm (or technically still is, but no flash and sound is on) but is now waiting to return to armed or unlocked (car is closed again or unlocked)

STATES ==                       \* Currently possible states
    {
        OpenAndUnlocked,
        ClosedAndLocked,
        OpenAndLocked,
        ClosedAndUnlocked,
        Armed,
        Alarm,
        SilentAndOpen
    }

VARIABLES
    state,                      \* the current state in the state diagram
    isArmed,                    \* flag to indicate if the car is armed
    flash,                      \* flag to indicate if flash is on
    sound                       \* flag to indicate if sound is on

vars == <<state, isArmed, flash, sound>>
alarm_vars == <<flash, sound>>

(***************************************************************************)
(* External Modules                                                        *)
(***************************************************************************)

CarAlarm == INSTANCE CarAlarm1      \* Refinement mapping through equal var names

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ state \in STATES
                 /\ isArmed \in BOOLEAN
                 
SafetyInvariant == /\ IF state = Armed                  \* if the car is in an armed state
                        THEN isArmed = TRUE             \* indicate  that in some way
                        ELSE isArmed = FALSE            \* here: by simply setting a flag
                   /\ state = Alarm => flash = TRUE     \* if car is in an alarm state (not silent!), the flash is on

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ state = OpenAndUnlocked                                      \* state diagram starts in the OpenAndUnlocked state
        /\ isArmed = FALSE                                              \* the car is unarmed
        /\ flash = FALSE                                                \* alarm indicators are off (alarm is deactivated)
        /\ sound = FALSE

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked               \* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED(alarm_vars)
                               /\ UNCHANGED<<isArmed>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked                  \* Close the car from the OpenAndLocked state to get to ClosedAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED<<isArmed>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen                  \* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
                             /\ state' = Armed                          \* This arms the car again
                             /\ isArmed' = TRUE
                             /\ UNCHANGED(alarm_vars)

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked               \* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked           \* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked           \* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked               \* Open the car from the ClosedAndLocked state to get to OpenAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>

Open_After_Armed == /\ state  = Armed                                   \* Open the car from an armed state
                    /\ state' = Alarm                                   \* this is an illegal action -> trigger alarm
                    /\ isArmed' = FALSE
                    /\ CarAlarm!Activate

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked             \* Unlock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
                                /\ state' = ClosedAndUnlocked
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked                 \* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>
             
Unlock_After_Armed == /\ state  = Armed                                 \* Unlock the car from an armed state to get into an unarmed state
                      /\ state' = ClosedAndUnlocked                     \* so the car can be arbitrarily unlocked/locked and opened/closed
                      /\ isArmed' = FALSE
                      /\ UNCHANGED(alarm_vars)

Unlock_After_Alarm == /\ state  = Alarm                                 \* Unlock the car after an alarm was triggered (car in alarm state)
                      /\ state' = OpenAndUnlocked                       \* this ends the path for an illegal action and puts the car in the OpenAndUnlocked state
                      /\ CarAlarm!Deactivate                            \* and deactivates the alarm
                      /\ UNCHANGED<<isArmed>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen                 \* Similar to the Unlock_After_Alarm action, but puts the car into a valid
                              /\ state' = OpenAndUnlocked               \* state again after the alarm already turned silent, thus, the alarm was already deactivated
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>

Arming == /\ state  = ClosedAndLocked                                   \* car transitioning from closed and unlocked into an armed state
          /\ state' = Armed                                             \* the car should also show it is armed, so the flag is set to true to indicate that
          /\ isArmed' = TRUE
          /\ UNCHANGED(alarm_vars)

SilentAlarm == /\ state = Alarm                                         \* car switches to silent alarm (no sound and flash) and is waiting to return to armed or unlocked
               /\ state' = SilentAndOpen
               /\ CarAlarm!Deactivate
               /\ UNCHANGED<<isArmed>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

DeactivateSound == /\ CarAlarm!DeactivateSound                          \* Turns off the sound of the car alarm module
                   /\ UNCHANGED<<state, isArmed>>   

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

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
        \/ DeactivateSound

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem3 == INSTANCE CarAlarmSystem3

THEOREM Spec => /\ CarAlarmSystem3!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:46:44 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
