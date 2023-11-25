# Resources

A set of actors concurrently access a finite amount of resources.

## label

Everything within a label is executed as part of the same atomic step.
Afterwards all invariants are checked and the next label chosen to execute.

A label _must_ be placed in the following locations:

- beginning of a process
- before a while
- after every goto

An implicit label `Done` is added to the end of every process.

## await

Wait until the following expression becomes true. Other processes run
simultaneously.
