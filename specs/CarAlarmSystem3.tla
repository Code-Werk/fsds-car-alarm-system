-------------------------- MODULE CarAlarmSystem3 --------------------------

(***************************************************************************)
(* Third refinement of the car alarm system:                               *)
(*                                                                         *)
(* In the third refinement we add the last states on the state diagram:    *)
(* Armed and Alarm. New actions are added with guards according to the     *)
(* state diagram. The basic lock and unlock features holds, but we are     *)
(* getting closer to the actual required design and now can handle all     *)
(* states of the state diagram.                                            *)
(*                                                                         *)
(* This refinement targets Requirements 1 - 3.                             *)
(***************************************************************************)

OpenAndUnlocked   == 0          \* Car is open and unlocked
ClosedAndLocked   == 1          \* Car is closed and locked
OpenAndLocked     == 2          \* Car is still open but already locked
ClosedAndUnlocked == 3          \* Car is not yet closed but already locked
Armed             == 4          \* Car alarm system is armed (which means it is locked and
                                \*  closed and alarm could be triggered)
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

VARIABLES state                 \* the current state in the state diagram

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeInvariant == state \in STATES
                 
(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

Init == state = OpenAndUnlocked                     \* state diagram starts in the 
                                                    \* OpenAndUnlocked state

Close == /\ \/ /\ state  = OpenAndUnlocked          \* close the car
               /\ state' = ClosedAndUnlocked
            \/ /\ state  = OpenAndLocked
               /\ state' = ClosedAndLocked
            \/ /\ state  = SilentAndOpen
               /\ state' = Armed

Lock == /\ \/ /\ state  = OpenAndUnlocked           \* lock the car
              /\ state' = OpenAndLocked
           \/ /\ state  = ClosedAndUnlocked
              /\ state' = ClosedAndLocked

Open == /\ \/ /\ state  = ClosedAndUnlocked         \* open the car
              /\ state' = OpenAndUnlocked
           \/ /\ state  = ClosedAndLocked
              /\ state' = OpenAndLocked
           \/ /\ state  = Armed                     \* car is opened in an 
              /\ state' = Alarm                     \* armed state => alarm!
           
Unlock == /\ \/ /\ state  = ClosedAndLocked         \* unlock the car
                /\ state' = ClosedAndUnlocked
             \/ /\ state  = OpenAndLocked
                /\ state' = OpenAndUnlocked
             \/ /\ state  = Armed
                /\ state' = ClosedAndUnlocked
             \/ /\ state  = Alarm
                /\ state' = OpenAndUnlocked
             \/ /\ state  = SilentAndOpen
                /\ state' = OpenAndUnlocked

Arming == /\ state  = ClosedAndLocked               \* car transitioning from closed and 
          /\ state' = Armed                         \* unlocked into an armed state

SilentAlarm == /\ state = Alarm                     \* car switches to silent alarm 
               /\ state' = SilentAndOpen            \* (no sound and flash) and is waiting
                                                    \* to return to armed or unlocked

(***************************************************************************)
(* Top-level Specification                                                 *)
(***************************************************************************)

Next == \/ Close
        \/ Lock
        \/ Open
        \/ Unlock
        \/ Arming
        \/ SilentAlarm

Spec == Init /\ [][Next]_state

(***************************************************************************)
(* Verified Specification and Verified Refinement                          *)
(***************************************************************************)

\* action to map the new states to the corresponding states of CarAlarmSystem2
StateMapping == IF state \in { Armed, Alarm, SilentAndOpen }
                    THEN IF state = Armed
                        THEN ClosedAndLocked
                        ELSE OpenAndLocked
                    ELSE state

\* instance of the lower refinement
CarAlarmSystem2 == INSTANCE CarAlarmSystem2 WITH state <- StateMapping

\* property to check the lower refinement in the TLC
CarAlarmSystem2Spec == /\ CarAlarmSystem2!Spec
                       /\ CarAlarmSystem2!TypeInvariant

THEOREM Spec => /\ CarAlarmSystem2Spec
                /\ []TypeInvariant
                
=============================================================================
