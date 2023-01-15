-------------------------- MODULE CarAlarmSystem5 --------------------------

(***************************************************************************)
(* Fifth refinement of the car alarm system:                               *)
(*                                                                         *)
(* In this refinement we finally added one of the required timings for the car alarm system, the timeout between locking the car and it switching into an armed state. We did not add all the timings at once, so we can work out how to implement it properly.  TODO *)
(*                                                                         *)
(* This refinement targets Requirements 1 - 3.                             *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT ArmedDelay             \* Time the car takes to switch into an armed state after it was locked (here: time to change the state from ClosedAndLocked to Armed)
ASSUME ArmedDelay \in Nat       \* ArmedDelay is set in the TLC, 20 by requirement

ArmedRange == 0..ArmedDelay     \* Range for the timer, it counts down from the max value (= ArmedDelay) to 0

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
    sound,                      \* flag to indicate if sound is on
    armedTimer                  \* timer that counts from ArmedDelay to 0

vars == <<state, isArmed, flash, sound, armedTimer>>
vars_without_state == <<isArmed, flash, sound, armedTimer>>
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
                 /\ armedTimer \in ArmedRange
                 
SafetyInvariant == /\ state = Alarm => flash = TRUE                         \* if car is in an alarm state (not silent!), the flash is on
                   /\ state = Armed                                         \* if the car is in an armed state indicate that by setting the isArmed flag
                        => armedTimer = ArmedDelay /\ isArmed = TRUE        \* the armed timer should be reset to the ArmedDelay when reaching this state
                   /\ state /= ClosedAndLocked => armedTimer = ArmedDelay   \* the only state where the armed timer should change is ClosedAndLocked, otherwise it's set to ArmedDelay

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ state = OpenAndUnlocked                                      \* state diagram starts in the OpenAndUnlocked state
        /\ isArmed = FALSE                                              \* the car is unarmed, timer is set to ArmedDelay
        /\ flash = FALSE                                                \* alarm indicators are off (alarm is deactivated)
        /\ sound = FALSE
        /\ armedTimer = ArmedDelay

(***************************************************************************)
(* State Actions                                                           *)
(***************************************************************************)

Close_After_OpenAndUnlocked == /\ state = OpenAndUnlocked               \* Close the car from the OpenAndUnlocked state to get to ClosedAndUnlocked
                               /\ state' = ClosedAndUnlocked
                               /\ UNCHANGED<<isArmed, flash, sound, armedTimer>>

Close_After_OpenAndLocked == /\ state  = OpenAndLocked                  \* Close the car from the OpenAndLocked state to get to ClosedAndLocked
                             /\ state' = ClosedAndLocked
                             /\ UNCHANGED<<isArmed, flash, sound, armedTimer>>

Close_After_SilentAndOpen == /\ state  = SilentAndOpen                  \* Close the car from the SilentAndOpen state (after an alarm was triggered but was already deactivated)
                             /\ state' = Armed                          \* This arms the car again
                             /\ isArmed' = TRUE
                             /\ UNCHANGED<<flash, sound, armedTimer>>

Lock_After_OpenAndUnlocked == /\ state  = OpenAndUnlocked               \* Lock the car from the OpenAndUnlocked state to get to OpenAndLocked
                              /\ state' = OpenAndLocked
                              /\ UNCHANGED<<vars_without_state>>

Lock_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked           \* Lock the car from the OpenAndLocked state to get to ClosedAndLocked
                                /\ state' = ClosedAndLocked
                                /\ UNCHANGED<<vars_without_state>>

Open_After_ClosedAndUnlocked == /\ state  = ClosedAndUnlocked           \* Open the car from the ClosedAndUnlocked state to get to OpenAndUnlocked
                                /\ state' = OpenAndUnlocked
                                /\ UNCHANGED<<vars_without_state>>

Open_After_ClosedAndLocked == /\ state  = ClosedAndLocked               \* Open the car from the ClosedAndLocked state to get to OpenAndLocked
                              /\ state' = OpenAndLocked
                              /\ armedTimer' = ArmedDelay
                              /\ UNCHANGED<<flash, sound, isArmed>>

Open_After_Armed == /\ state  = Armed                                   \* Open the car from an armed state
                    /\ state' = Alarm                                   \* this is an illegal action -> trigger alarm
                    /\ isArmed' = FALSE
                    /\ CarAlarm!Activate
                    /\ UNCHANGED<<armedTimer>>

Unlock_After_ClosedAndLocked == /\ state  = ClosedAndLocked             \* Lock the car from the ClosedAndLocked state to get to ClosedAndUnlocked
                                /\ state' = ClosedAndUnlocked
                                /\ armedTimer' = ArmedDelay
                                /\ UNCHANGED<<flash, sound, isArmed>>

Unlock_After_OpenAndLocked == /\ state  = OpenAndLocked                 \* Lock the car from the OpenAndLocked state to get to OpenAndUnlocked
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>
             
Unlock_After_Armed == /\ state  = Armed
                      /\ state' = ClosedAndUnlocked
                      /\ isArmed' = FALSE
                      /\ UNCHANGED<<flash, sound, armedTimer>>

Unlock_After_Alarm == /\ state  = Alarm
                      /\ state' = OpenAndUnlocked
                      /\ CarAlarm!Deactivate
                      /\ UNCHANGED<<isArmed, armedTimer>>

Unlock_After_SilentAndOpen == /\ state  = SilentAndOpen
                              /\ state' = OpenAndUnlocked
                              /\ UNCHANGED<<vars_without_state>>

Arming == /\ state  = ClosedAndLocked
          /\ armedTimer = 0
          /\ state' = Armed
          /\ isArmed' = TRUE
          /\ armedTimer' = ArmedDelay
          /\ UNCHANGED<<flash, sound>>

SilentAlarm == /\ state = Alarm
               /\ state' = SilentAndOpen
               /\ CarAlarm!Deactivate
               /\ UNCHANGED<<isArmed, armedTimer>>

(***************************************************************************)
(* Alarm Actions                                                           *)
(***************************************************************************)

DeactivateSound == /\ CarAlarm!DeactivateSound
                   /\ UNCHANGED<<state, isArmed, armedTimer>>   

(***************************************************************************)
(* Timer Actions                                                           *)
(***************************************************************************)

Tick == /\ state = ClosedAndLocked
        /\ armedTimer > 0
        /\ \E d \in { n \in ArmedRange : n < armedTimer}:
            armedTimer' = d 
        /\ UNCHANGED<<state, isArmed, sound, flash>>

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
        \/ Tick

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

CarAlarmSystem4 == INSTANCE CarAlarmSystem4

THEOREM Spec => /\ CarAlarmSystem4!Spec
                /\ CarAlarm!Spec
                /\ []Invariant

=============================================================================
\* Modification History
\* Last modified Fri Jan 13 09:48:38 CET 2023 by marian
\* Created Tue Jan 10 16:19:21 CET 2023 by mitch
