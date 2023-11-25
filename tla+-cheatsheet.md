TLA+ cheatsheet, taken from
[here](https://mbt.informal.systems/docs/tla_basics_tutorials/tla+cheatsheet.html)
and extended with temporal operators.

For a more thorough summary take a look at the
[official cheatsheet](https://lamport.azurewebsites.net/tla/summary-standalone.pdf).

```
(* Comments *)

(* This is a
   multiline comment *)
\* This is a single line comment

(* Module structure *)

---- MODULE <module> ----   \* Starts TLA+ module (should be in file <module>.tla)
====                        \* Ends TLA+ module (everything after that is ignored)

EXTENDS <module>            \* EXTEND (import) another TLA+ module
VARIABLES x, y, ...         \* declares variables x, y, ...
CONSTANTS x, y, ...         \* declares constants x, y, ... (should be defined in configuration)

Name == e                   \* defines operator Name without parameters, and with expression e as a body
Name(x, y, ...) == e        \* defines operator Name with parameters x, y, ..., and body e (may refer to x, y, ...)

(* Boolean logic *)

BOOLEAN                     \* the set of all booleans (same as {TRUE, FALSE})
TRUE                        \* Boolean true
FALSE                       \* Boolean false
~x                          \* not x; negation
x /\ y                      \* x and y; conjunction (can be also put at line start, in multi-line conjunctions)
x \/ y                      \* x or y; disjunction (can be also put at line start, in multi-line disjunctions)
x = y                       \* x equals y
x /= y                      \* x not equals y
x => y                      \* implication: y is true whenever x is true
x <=> y                     \* equivalence: x is true if and only if y is true

(* Integers *)              \* EXTENDS Integers (should extend standard module Integers)

Int                         \* the set of all integers (an infinite set)
1, -2, 1234567890           \* integer literals; integers are unbounded
a..b                        \* integer range: all integers between a and b inclusive
x + y, x - y, x * y         \* integer addition, subtraction, multiplication
x < y, x <= y               \* less than, less than or equal
x > y, x >= y               \* greater than, greater than or equal

(* Strings *)

STRING                      \* the set of all finite strings (an infinite set)
"", "a", "hello, world"     \* string literals (can be compared for equality; otherwise uninterpreted)

(* Finite sets *)           \* EXTENDS FiniteSets (should extend standard module FiniteSets)

{a, b, c}                   \* set constructor: the set containing a, b, c
Cardinality(S)              \* number of elements in set S
x \in S                     \* x belongs to set S
x \notin S                  \* x does not belong to set S
S \subseteq T               \* is set S a subset of set T? true of all elements of S belong to T
S \union T                  \* union of sets S and T: all x belonging to S or T
S \intersect T              \* intersection of sets S and T: all x belonging to S and T
S \ T                       \* set difference, S less T: all x belonging to S but not T
{x \in S: P(x)}             \* set filter: selects all elements x in S such that P(x) is true
{e: x \in S}                \* set map: maps all elements x in set S to expression e (which may contain x)

(* Functions *)

[x \in S |-> e]             \* function constructor: maps all keys x from set S to expression e (may refer to x)
f[x]                        \* function application: the value of function f at key x
DOMAIN f                    \* function domain: the set of keys of function f
[f EXCEPT ![x] = e]         \* function f with key x remapped to expression e (may reference @, the original f[x])
[f EXCEPT ![x] = e1,        \* function f with multiple keys remapped:
          ![y] = e2, ...]   \*   x to e1 (@ in e1 will be equal to f[x]), y to e2 (@ in e2 will be equal to f[y])
[S -> T]                    \* function set constructor: set of all functions with keys from S and values from T

(* Records *)

[x |-> e1, y |-> e2, ...]   \* record constructor: a record which field x equals to e1, field y equals to e2, ...
r.x                         \* record field access: the value of field x of record r
[r EXCEPT !.x = e]          \* record r with field x remapped to expression e (may reference @, the original r.x)
[r EXCEPT !.x = e1,         \* record r with multiple fields remapped:
          !.y = e2, ...]    \*   x to e1 (@ in e1 is equal to r.x), y to e2 (@ in e2 is equal to r.y)
[x: S, y: T, ...]           \* record set constructor: set of all records with field x from S, field y from T, ...

(* Sequences *)             \* EXTENDS Sequences (should extend standard module Sequences)

<<a, b, c>>                 \* sequence constructor: a sequence containing elements a, b, c
s[i]                        \* the ith element of the sequence s (1-indexed!)
s \o t                      \* the sequences s and t concatenated
Len(s)                      \* the length of sequence s
Append(s, x)                \* the sequence s with x added to the end
Head(s)                     \* the first element of sequence s

(* Tuples *)

<<a, b, c>>                 \* tuple constructor: a tuple of a,b,c (yes! the <<>> constructor is overloaded)
                            \* - sequence elements should be same type; tuple elements may have different types
t[i]                        \* the ith element of the tuple t (1-indexed!)
S \X T                      \* Cartesian product: set of all tuples <<x, y>>, where x is from S, y is from T

(* Quantifiers *)

\A x \in S: e               \* for all elements x in set S it holds that expression e is true
\E x \in S: e               \* there exists an element x in set S such that expression e is true

(* State changes *)

x', y'                      \* a primed variable (suffixed with ') denotes variable value in the next state
UNCHANGED <<x,y>>           \* variables x, y are unchanged in the next state (same as x'=x /\ y'=y)

(* Control structures *)

LET x == e1 IN e2           \* introduces a local definition: every occurrence of x in e2 is replaced with e1
IF P THEN e1 ELSE e2        \* if P is true, then e1 should be true; otherwise e2 should be true

(* Temporal operators *)

[]                          \* always: []P means that P is true for all states in all behaviors.
<>                          \* eventually: <>P means that for every behavior, there is at least one state where P is true.
~>                          \* leads-to: P ~> Q means that for any state in which P is true, Q must be true in that state or in some later state.
[]<>                        \* always-eventually-true: []<>P means that if P ever becomes false, it will eventually become true again.
<>[]                        \* eventually-always-true: <>[]P means that once P is true, it stays true forever.

[A]_v                       \* always action operator: at every step either A happens or v stays the same.
WF_v(A)                     \* weak fairness action operator: once A's preconditions are satisfied and stay true, its action will eventually occur, affecting variable v
SF_v(A)                     \* strong fairness action operator: action A is taken eventually even if it is not continously enabled
```
