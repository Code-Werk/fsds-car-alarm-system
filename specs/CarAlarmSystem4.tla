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
Armed             == 4          \* Car alarm system is armed (which means it is locked and
                                \* closed and alarm could be triggered)
Alarm             == 5          \* Car alarm is on (which means an illegal action
                                \* - car opened without unlocking -
                                \* occurred in the armed state and the alarm was triggered)
SilentAndOpen     == 6          \* Car has been in alarm (or technically still is, but no
                                \* flash and sound is on) but is now waiting to return to
                                \* armed or unlocked (car is closed again or unlocked)

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

\* If the car is in an armed state indicate that in some way.
\* Here: by simply setting a flag.
\* If car is in an alarm state (not silent!), the flash is on.
SafetyInvariant == /\ IF state = Armed
                        THEN isArmed = TRUE
                        ELSE isArmed = FALSE
                   /\ state = Alarm => flash = TRUE

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

\* State diagram starts in the OpenAndUnlocked state.
\* The car is unarmed.
\* Alarm indicators are off (alarm is deactivated).
Init == /\ state = OpenAndUnlocked                                      
        /\ isArmed = FALSE                                              
        /\ flash = FALSE                                                
        /\ sound = FALSE

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

\* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked               
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED(alarm_vars)
                               /\ UNCHANGED<<isArmed>>

\* Close the car from the OpenAndLocked state to get to ClosedAndLocked
Close_After_OpenAndLocked == /\ state = OpenAndLocked 
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED(alarm_vars)
                             /\ UNCHANGED<<isArmed>>

\* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
\* This arms the car again
Close_After_SilentAndOpen == /\ state = SilentAndOpen
                             /\ state' = Armed                          
                             /\ isArmed' = TRUE
                             /\ UNCHANGED(alarm_vars)

\* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
Lock_After_OpenAndUnlocked == /\ state = OpenAndUnlocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>

\* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
Lock_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed>>

\* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
Open_After_ClosedAndUnlocked == /\ state = ClosedAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed>>

\* Open the car from the ClosedAndLocked state to get to OpenAndLocked
Open_After_ClosedAndLocked == /\ state = ClosedAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>

\* Open the car from an armed state
\* this is an illegal action -> trigger alarm
Open_After_Armed == /\ state = Armed                                   
                    /\ state' = Alarm                                   
                    /\ isArmed' = FALSE
                    /\ CarAlarm!Activate

\* Unlock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
Unlock_After_ClosedAndLocked == /\ state = ClosedAndLocked
                                /\ state' = ClosedAndUnlocked
                                /\ UNCHANGED(alarm_vars)
                                /\ UNCHANGED<<isArmed>>

\* Unlock the car from the OpenAndLocked state to get to OpenAndUnlocked
Unlock_After_OpenAndLocked == /\ state = OpenAndLocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>
             
\* Unlock the car from an armed state to get into an unarmed state
\* so the car can be arbitrarily unlocked/locked and opened/closed
Unlock_After_Armed == /\ state = Armed
                      /\ state' = ClosedAndUnlocked
                      /\ isArmed' = FALSE
                      /\ UNCHANGED(alarm_vars)

\* Unlock the car after an alarm was triggered (car in alarm state)
\* this ends the path for an illegal action and puts the car in the OpenAndUnlocked state
\* and deactivates the alarm
Unlock_After_Alarm == /\ state = Alarm
                      /\ state' = OpenAndUnlocked
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed>>

\* Similar to the Unlock_After_Alarm action, but puts the car into a valid
\* state again after the alarm already turned silent, thus, the alarm was already deactivated
Unlock_After_SilentAndOpen == /\ state = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED(alarm_vars)
                              /\ UNCHANGED<<isArmed>>

\* car transitioning from closed and unlocked into an armed state
\* the car should also show it is armed, so the flag is set to true to indicate that
Arming == /\ state = ClosedAndLocked
          /\ state' = Armed
          /\ isArmed' = TRUE
          /\ UNCHANGED(alarm_vars)

\* car switches to silent alarm (no sound and flash) and is waiting to return to armed or unlocked
SilentAlarm == /\ state = Alarm
               /\ state' = SilentAndOpen
               /\ CarAlarm!Deactivate
               /\ UNCHANGED<<isArmed>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

\* Turns off the sound of the car alarm module
DeactivateSound == /\ CarAlarm!DeactivateSound
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

\* instance of the lower refinement
\* the states are now similar, so no mapping is needed
CarAlarmSystem3 == INSTANCE CarAlarmSystem3

\* property to check the lower refinement in the TLC
CarAlarmSystem3Spec == /\ CarAlarmSystem3!Spec
                       /\ CarAlarmSystem3!TypeInvariant

\* check that the car alarm also holds in the TLC
CarAlarmSpec == /\ CarAlarm!Spec
                /\ CarAlarm!SafetyInvariant
                /\ CarAlarm!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem3Spec
                /\ CarAlarmSpec
                /\ []Invariant

=============================================================================
