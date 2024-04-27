-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS 
    OFF, ON, CLOSED, OPEN

VARIABLES 
    door,
    running,
    timeRemaining

RequireSafety == FALSE
RequireLiveness == FALSE

ImplementStartSafety == FALSE
ImplementOpenDoorSafety == FALSE
ImplementProgress == FALSE

vars == << door, running, timeRemaining >>

TypeOK == door \in { CLOSED, OPEN } /\ running \in { OFF, ON } /\ timeRemaining \in Nat

MaxTime == 5
MaxCycles == 3

Init ==
    /\ door \in { OPEN, CLOSED }
    /\ running = OFF
    /\ timeRemaining = 0

\* increment remaining time by one second
IncTime ==
    /\ running = OFF
    /\ timeRemaining' = timeRemaining + 1
    /\ timeRemaining' <= MaxTime
    /\ UNCHANGED << door, running >>

Start ==
    /\ running = OFF
    /\ ImplementStartSafety => door = CLOSED \* additional precondition
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
    /\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    /\ UNCHANGED << door >>

OpenDoor ==
    /\ door' = OPEN
    /\ IF ImplementOpenDoorSafety THEN running' = OFF ELSE UNCHANGED << running >> \* additional effect
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

DoorSafety == RequireSafety => ( door = OPEN => running = OFF )

\* DoorSafety == RequireSafety => running = ON => door = CLOSED

HeatLiveness == ( running = ON ) ~> ( RequireLiveness => running = OFF )

RunsUntilDoneOrInterrupted == TRUE

\* RunsUntilDoneOrInterrupted == 
\*     [][running = ON => running' = ON \/ timeRemaining' = 0 \/ door' = OPEN]_vars

====

(* other possible events
      action := "10min"
      action := "1min"
      action := "10sec"
      action := "power"
      action := "timer"
*)
