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

AlarmRange == 0..SoundDuration

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
                 /\ soundTimer \in SoundDuration
                 
SafetyInvariant == \/ flash = sound             \* sound and flash are either both on or both of
                   \/ /\ flash = TRUE           \* or we are in the alarm state where sound is deactivated
                      /\ sound = FALSE          \* but the alarm is still flashing

Invariant == /\ TypeInvariant
             /\ SafetyInvariant

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == /\ flash = 0                           \* alarm is deactivated in the beginning
        /\ sound = 0
        /\ soundTimer = 0

Activate == /\ flash = 0                        \* activate the alarm by turning on the flash and sound
            /\ flash' = 1
            /\ sound' = 1
            /\ soundTimer' = SoundDuration

DeactivateSound == /\ soundTimer = 0            \* deactivate the alarm sound
                   /\ flash  = 1                \* once the sound timer reaches 0
                   /\ sound  = 1
                   /\ sound' = 0
                   /\ UNCHANGED<<flash, soundTimer>>

Deactivate == /\ flash' = 0                     \* deactivate the alarm by turning off the flash and sound
              /\ sound' = 0
              /\ soundTimer' = 0
              /\ UNCHANGED<<soundTimer>>

Tick == /\ sound = 1                            \* count down of the sound timer from SoundDuration to 0
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
