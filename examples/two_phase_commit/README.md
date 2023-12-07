# Two-Phase Commit

Model a
[two-phase commit protocol](https://en.wikipedia.org/wiki/Two-phase_commit_protocol).

## INSTANCE

```
INSTANCE transaction_commit
```

«Import» module `transaction_commit` and allow to parameterize it.

## THEOREM

```
THEOREM TPSpec => TCSpec
```

Every behaviour satisfying TPSpec also satisfies TCSpec.
