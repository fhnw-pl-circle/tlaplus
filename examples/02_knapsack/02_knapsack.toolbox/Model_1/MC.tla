---- MODULE MC ----
EXTENDS 02_knapsack, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
i1, i2, i3
----

\* MV CONSTANT definitions Items
const_1700851032186152000 == 
{i1, i2, i3}
----

\* SYMMETRY definition
symm_1700851032186153000 == 
Permutations(const_1700851032186152000)
----

\* CONSTANT definitions @modelParameterConstants:1ValueRange
const_1700851032186154000 == 
0..5
----

\* CONSTANT definitions @modelParameterConstants:2SizeRange
const_1700851032186155000 == 
2..4
----

\* CONSTANT definitions @modelParameterConstants:3Capacity
const_1700851032186156000 == 
4
----

=============================================================================
\* Modification History
\* Created Fri Nov 24 19:37:12 CET 2023 by shu
