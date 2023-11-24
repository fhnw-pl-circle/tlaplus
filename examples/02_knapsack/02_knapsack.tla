---------------------------- MODULE 02_knapsack ----------------------------
EXTENDS TLC, Integers, Sequences
PT == INSTANCE PT

CONSTANTS Capacity, Items, SizeRange, ValueRange
ASSUME Capacity \in Nat \ {0}
\*ASSUME Capacity > 0
ASSUME SizeRange \subseteq 1..Capacity
ASSUME ValueRange \subseteq Nat
\*ASSUME \A v \in ValueRange: v >= 0


ItemParams == [size: SizeRange, value: ValueRange]
ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) == 
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)
    
ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..5]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)
    
BestKnapsacks(itemset) ==
    LET 
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
            \A worse \in all \ {best}: 
                value(best) >= value(worse)
        value_of_best == value(best)
    IN
        {k \in all: value_of_best = value(k)}
        
(*--algorithm debug
variables itemset \in ItemSets
begin
    assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset);
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ad9806a8" /\ chksum(tla) = "61575d18")
VARIABLES itemset, pc

vars == << itemset, pc >>

Init == (* Global variables *)
        /\ itemset \in ItemSets
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset), 
                   "Failure of assertion at line 41, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED itemset

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
\* Modification History
\* Last modified Fri Nov 24 19:37:10 CET 2023 by shu
\* Created Fri Nov 24 19:30:54 CET 2023 by shu
