---- MODULE MC ----
EXTENDS 03_resources, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Actors
const_170090677580372000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_170090677580373000 == 
Permutations(const_170090677580372000)
----

\* CONSTANT definitions @modelParameterConstants:0ResourceCap
const_170090677580374000 == 
6
----

\* CONSTANT definitions @modelParameterConstants:1MaxConsumerReq
const_170090677580375000 == 
2
----

=============================================================================
\* Modification History
\* Created Sat Nov 25 11:06:15 CET 2023 by shu
