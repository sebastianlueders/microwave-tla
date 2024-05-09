# TLA+ Microwave Model

This example models a very basic microwave oven with very simple state:

- door open or closed
- radiation on or off
- time remaining in seconds between zero and some maximum

The model has various actions:

- opening/closing the door
- starting/canceling the heater (magnetron)
- incrementing/counting down time

These typically correspond to buttons and other affordances in the appliance's user interface or internal events.

## Typing

TLA+ does not support static typing, but we can define a (dynamic) invariant `TypeOK` that constrains which variable can take on which values.

## Safety

Checking the intial model succeeds, but...

*What does it actually mean for the microwave to be safe?*

Typically, we wouldn't want it to be heating when the door is open. 
So let's define a `DoorSafety` invariant accordingly.

Now the initial model fails, and we need to fix it so it satisfies the invariant!

- stage 1: turn off when opening door
- stage 2: don't allow turning on when door is open

## Liveness

Is this notion of safety enough? 

*How do we know it won't accidentally keep running, overheat, and catch on fire?*

We need some kind of `HeatLiveness` property.
This reveals that the model could go into stuttering, i.e., staying in the same state without getting closer to finishing.

We need to enable weak fairness (WF) to break this stutter-invariance! 
(See also [www.hillelwayne.com/post/fairness](https://www.hillelwayne.com/post/fairness).)

## Other properties

We can add other interesting properties, e.g., `RunsUntilDoneOrInterrupted`.
