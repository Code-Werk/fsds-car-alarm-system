-------------------------- MODULE CarAlarm2 --------------------------

(***************************************************************************)
(* Second refinement for the alarm sub module of the car alarm system:     *)
(*                                                                         *)
(* In the second refinement we added a timer that terminates the sound     *)
(* after a given time in the alarm state and just continues flashing.      *)
(* According to the requirements the sound is on for 30 seconds, where both*)
(* flash and sound are on. After that, only the flash is on. The sound can *)
(* be activated again while the alarm is still in an alarm or not at all,  *)
(* but not while it is currently going off.                                *)
(*                                                                         *)
(* For the timer implementation we simply chose to count down in integer   *)
(* steps from the sound duration to 0. If 0 is reached, the guard to the   *)
(* DeactivateSound passes and the sound will turn off.                     *)
(*                                                                         *)
(* This refinement targets Requirements 2.                                 *)
(***************************************************************************)

EXTENDS Naturals

CONSTANT SoundDuration                      \* SoundDuration set in the TLC, 30 sec by requirement
ASSUME SoundDuration \in Nat

SoundRange == 0..SoundDuration

VARIABLES
    flash,              \* flag to indicate if flash is on
    sound,              \* flag to indicate if sound is on
    soundTimer          \* timer that counts from SoundDuration to 0

vars == <<flash, sound, soundTimer>>

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == /\ flash \in BOOLEAN
                 /\ sound \in BOOLEAN
                 /\ soundTimer \in SoundRange
                 
SafetyInvariant == \/ flash = sound             \* sound and flash are either both on or both of
                   \/ /\ flash = TRUE           \* or we are in the alarm state where sound is deactivated
                      /\ sound = FALSE          \* but the alarm is still flashing

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ flash = FALSE                            \* alarm is deactivated in the beginning
        /\ sound = FALSE
        /\ soundTimer = 0

Activate == /\ flash  = FALSE                       \* activate the alarm by turning on the flash and sound
            /\ flash' = TRUE
            /\ sound' = TRUE
            /\ soundTimer' = SoundDuration

DeactivateSound == /\ soundTimer = 0                \* deactivate the alarm sound
                   /\ flash  = TRUE                 \* once the sound timer reaches 0
                   /\ sound  = TRUE
                   /\ sound' = FALSE
                   /\ UNCHANGED<<flash, soundTimer>>

Deactivate == /\ flash' = FALSE                     \* deactivate the alarm by turning off the flash and sound
              /\ sound' = FALSE
              /\ soundTimer' = 0
              /\ UNCHANGED<<soundTimer>>

Tick == /\ sound = TRUE                             \* count down of the sound timer from SoundDuration to 0
        /\ \E d \in { n \in SoundRange : n < soundTimer}:
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

\* instance of the lower refinement
\* the variables are similar, so no mapping is needed
CarAlarm1 == INSTANCE CarAlarm1

\* property to check the lower refinement in the TLC
CarAlarm1Spec == /\ CarAlarm1!Spec
                 /\ CarAlarm1!SafetyInvariant
                 /\ CarAlarm1!TypeInvariant

THEOREM Spec => /\ CarAlarm1Spec
                /\ []Invariant

=============================================================================
