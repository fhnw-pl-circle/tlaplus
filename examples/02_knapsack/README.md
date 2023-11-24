# Knapsack

Constants need to be set in the model and can be typechecked with `ASSUME` in
the spec.

## set of model values

These are sets where it is not important what exactly the values are, merely
that they are distinct (as in all sets of course).

For example, instead of the set `{"a", "b", "c"}` it is possible to use
`{m1, m2, m3}` if the actual value is of no matter. The values are only tokens
in that case.

As a special case, model values can be declared as _symmetric_, if their order
does not matter for the purpose of model checking. This means that any two
states that are identical except for a permutation of the elements in the
symmetry set should be considered equivalent.

With this information, the model checker can optimize more efficiently and cut
down the time it takes to run.

## CHOOSE

`CHOOSE x \in S : P(x)`: "select an x such that P(x) is true".

For example an indexOf operator for a sequence:

```
IndexOf(seq, elem) ==
  CHOOSE i \in 1..Len(seq): seq[i] = elem
```
