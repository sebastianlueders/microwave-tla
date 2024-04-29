\*34567890123456789012345678901234567890123456789012

-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS 
  OFF, ON, CLOSED, OPEN

VARIABLES 
  door, running, timeRemaining

vars == << door, running, timeRemaining >>

RequireSafety == FALSE
RequireLiveness == FALSE

ImplementStartSafety == FALSE
ImplementOpenDoorSafety == FALSE
ImplementProgress == FALSE

TypeOK == 
  /\ door \in { CLOSED, OPEN }
  /\ running \in { OFF, ON }
  /\ timeRemaining \in Nat

MaxTime == 60

Init ==
  /\ door \in { OPEN, CLOSED }
  /\ running = OFF
  /\ timeRemaining = 0

IncTime ==
  /\ running = OFF
  /\ timeRemaining' = timeRemaining + 1
  /\ timeRemaining' <= MaxTime
  /\ UNCHANGED << door, running >>

Start ==
  /\ running = OFF
  /\ ImplementStartSafety => door = CLOSED
  /\ timeRemaining > 0
  /\ running' = ON
  /\ UNCHANGED << door, timeRemaining >>

Cancel ==
  /\ running' = OFF
  /\ timeRemaining' = 0
  /\ UNCHANGED << door >>

Tick ==
  /\ running = ON
  /\ timeRemaining' = timeRemaining - 1
  /\ timeRemaining' >= 0
  /\ IF timeRemaining' = 0 
     THEN running' = OFF 
     ELSE UNCHANGED << running >>
  /\ UNCHANGED << door >>

OpenDoor ==
  /\ door' = OPEN
  /\ IF ImplementOpenDoorSafety 
     THEN running' = OFF 
     ELSE UNCHANGED << running >>
  /\ UNCHANGED << timeRemaining >>

CloseDoor ==
  /\ door' = CLOSED
  /\ UNCHANGED << running, timeRemaining >>

Next ==
  \/ IncTime
  \/ Start
  \/ Cancel
  \/ OpenDoor
  \/ CloseDoor
  \/ Tick

TickProgress == ImplementProgress => WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ TickProgress

DoorSafety == RequireSafety => 
  ( door = OPEN => running = OFF )

HeatLiveness == ( running = ON ) ~> 
  ( RequireLiveness => running = OFF )

RunsUntilDoneOrInterrupted == TRUE

\* RunsUntilDoneOrInterrupted == 
\*   [][running = ON => running' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(* other possible events
    action := "10min"
    action := "1min"
    action := "10sec"
    action := "power"
    action := "timer"
*)

\* DoorSafety == RequireSafety => running = ON => door = CLOSED
