# Simple Wire Transfer

## Operators

- `<>[]`: eventually true (in the end, can flip back and forth until then)

## Invariants

- NoOverdrafts

## Temporal Properties

- EventuallyConsistent

## fair process

The `fair` specifies that the process does not stop until it gets to the end. If
it is removed it leads to `stuttering`.

## Stuttering

A process might just stop (simulating timeouts, network errors, ...).

The way this example is specified, it is unavoidable without using `fair`.
