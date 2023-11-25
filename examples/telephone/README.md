# Telephone

No invariants here, only the assertion that the end result is the sequence of
`<<1,2,3>>`.

The endresult is a deadlock.

## either

```
either
  \* branch 1
or
  \* branch 2
  \* ...
or
  \* branch n
end either;
```

One of several possibilites happens (all with the same chance). TLC checks all
possibilities in all states.
