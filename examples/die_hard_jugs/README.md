# Die Hard Jug Problem

Two jugs with a capacity of 3 and 5. We need an amount of exactly 4 (search on
youtube for the film scene).

Problem is modelled as a series of state transitions. Once TLC finds a path that
violates the invariant `big_jug /= 4` we have a solution (not necessarily the
only one).
