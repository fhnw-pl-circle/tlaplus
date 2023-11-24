# Simple Wire Transfer

## Operators

- `<>[]`: eventually true (in the end, can flip back and forth until then)

## Invariants

- NoOverdrafts

## Temporal Properties

- EventuallyConsistent

## Stuttering

A process might just stop (simulating timeouts, network errors, ...).

The way this example is specified, it is unavoidable. To fix it we would have to
change the spec.
