-------------------------- MODULE Microwave  --------------------------

EXTENDS TLC, Integers

CONSTANTS 
    OFF, ON, CLOSED, OPEN

VARIABLES 
    door,
    running,
    timeRemaining,
    cycles

vars == << door, running, timeRemaining, cycles >>

TypeOK == door \in { CLOSED, OPEN } /\ running \in { OFF, ON } /\ timeRemaining \in Nat

MaxTime == 5
MaxCycles == 3

Init ==
    /\ door = CLOSED
    /\ running = OFF
    /\ timeRemaining = 0
    /\ cycles = 0

\* increment remaining time by one second
IncTime ==
    /\ running = OFF
    /\ timeRemaining' = timeRemaining + 1
    /\ timeRemaining' <= MaxTime
    /\ UNCHANGED << door, running, cycles >>

Start ==
    /\ cycles < MaxCycles
    /\ timeRemaining > 0
    /\ running' = ON
    /\ cycles' = cycles + 1
    /\ UNCHANGED << door, timeRemaining >>

Cancel ==
    /\ running' = OFF
    /\ timeRemaining' = 0
    /\ UNCHANGED << door, cycles >>

Tick ==
    /\ running = ON
    /\ timeRemaining' = timeRemaining - 1
    /\ timeRemaining' >= 0
    /\ IF timeRemaining' = 0 THEN running' = OFF ELSE UNCHANGED << running >>
    /\ UNCHANGED << door, cycles >>

OpenDoor ==
    /\ door' = OPEN
    /\ UNCHANGED << running, timeRemaining, cycles >>

CloseDoor ==
    /\ door' = CLOSED
    /\ UNCHANGED << running, timeRemaining, cycles >>

TickProgress == TRUE

\* TickProgress == WF_timeRemaining(Tick)

Next ==
    \/ IncTime
    \/ Start
    \/ Cancel
    \/ OpenDoor
    \/ CloseDoor
    \/ Tick

Spec == Init /\ [][Next]_vars /\ TickProgress

DoorSafety == TRUE

\* DoorSafety == door = OPEN => running = OFF

\* DoorSafety == running = ON => door = CLOSED

HeatLiveness == TRUE

\* HeatLiveness == running = ON ~> running = OFF

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
