---- MODULE MC ----
EXTENDS 01_telephone, TLC

\* INIT definition @modelBehaviorNoSpec:0
init_170081303455811000 ==
FALSE/\in_transit = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_170081303455812000 ==
FALSE/\in_transit' = in_transit
----
=============================================================================
\* Modification History
\* Created Fri Nov 24 09:03:54 CET 2023 by shu
