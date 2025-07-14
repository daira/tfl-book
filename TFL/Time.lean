import Mathlib.Logic.Basic

/--
Making `Time` an abbrev for `ℕ` simplifies things by allowing us to assume that
state can be reconstructed by running the sequence of updates for each time step.

Recall that [[Clinger 1981]](https://dspace.mit.edu/handle/1721.1/6935) proves that
the history of any actor system can be realized (non-uniquely) in global time with
countably many events, and so this choice is without loss of practical generality.
-/
public abbrev Time := ℕ
