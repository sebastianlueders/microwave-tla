\*34567890123456789012345678901234567890123456789012

-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS 
  OFF, ON, CLOSED, OPEN

VARIABLES 
  door, radiation, timeRemaining

vars == << door, radiation, timeRemaining >>

RequireSafety == TRUE
RequireLiveness == FALSE

ImplementStartSafety == TRUE
ImplementOpenDoorSafety == TRUE
ImplementProgress == FALSE

TypeOK == 
  /\ door \in { CLOSED, OPEN }
  /\ radiation \in { OFF, ON }
  /\ timeRemaining \in Nat

MaxTime == 60

Init ==
  /\ door \in { OPEN, CLOSED }
  /\ radiation = OFF
  /\ timeRemaining = 0

IncTime ==
  /\ radiation = OFF
  /\ timeRemaining' = timeRemaining + 1
  /\ timeRemaining' <= MaxTime
  /\ UNCHANGED << door, radiation >>

Start ==
  /\ radiation = OFF
  /\ ImplementStartSafety => door = CLOSED
  /\ timeRemaining > 0
  /\ radiation' = ON
  /\ UNCHANGED << door, timeRemaining >>

Cancel ==
  /\ radiation' = OFF
  /\ timeRemaining' = 0
  /\ UNCHANGED << door >>

Tick ==
  /\ radiation = ON
  /\ timeRemaining' = timeRemaining - 1
  /\ timeRemaining' >= 0
  /\ IF timeRemaining' = 0 
     THEN radiation' = OFF 
     ELSE UNCHANGED << radiation >>
  /\ UNCHANGED << door >>

OpenDoor ==
  /\ door' = OPEN
  /\ IF ImplementOpenDoorSafety 
     THEN radiation' = OFF 
     ELSE UNCHANGED << radiation >>
  /\ UNCHANGED << timeRemaining >>

CloseDoor ==
  /\ door' = CLOSED
  /\ UNCHANGED << radiation, timeRemaining >>

Next ==
  \/ IncTime
  \/ Start
  \/ Cancel
  \/ OpenDoor
  \/ CloseDoor
  \/ Tick

TickProgress == ImplementProgress => WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ TickProgress

DoorSafety == RequireSafety => 
  ( door = OPEN => radiation = OFF )

HeatLiveness == ( radiation = ON ) ~> 
  ( RequireLiveness => radiation = OFF )

RunsUntilDoneOrInterrupted == TRUE

\* RunsUntilDoneOrInterrupted == 
\*   [][radiation = ON => radiation' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(* other possible events
    action := "10min"
    action := "1min"
    action := "10sec"
    action := "power"
    action := "timer"
*)

\* DoorSafety == RequireSafety => radiation = ON => door = CLOSED
