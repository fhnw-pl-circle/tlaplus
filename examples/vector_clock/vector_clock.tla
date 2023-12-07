---------------------------- MODULE vector_clock ----------------------------
EXTENDS Integers, Sequences

CONSTANT Nodes

VARIABLES vcState, messages, systemActive

VCInit == /\ vcState = [n \in Nodes |-> [on \in Nodes |-> 0]]
          /\ messages = [n \in Nodes |-> {}]
          /\ systemActive = FALSE

VCInternalEvent(n) == 
    LET newVcState == vcState[n][n] + 1
        newAllVcState == [vcState EXCEPT ![n][n] = newVcState]
        newMessage == [sender |-> n, vc |-> newAllVcState[n]]
        newMessages == 
            [m \in Nodes |-> 
                IF m = n 
                THEN messages[m] 
                ELSE messages[m] \cup {newMessage}]
    IN /\ vcState' = newAllVcState
       /\ messages' = newMessages
       /\ systemActive' = TRUE

VCExternalEvent(n, msg) == 
    /\ msg \in messages[n]
    /\ vcState' = [vcState EXCEPT ![n] =
        [nd \in Nodes |-> 
            IF vcState[n][nd] > msg.vc[nd]
            THEN vcState[n][nd] 
            ELSE msg.vc[nd]]]
    /\ messages' = [messages EXCEPT ![n] = messages[n] \ {msg}]
    /\ UNCHANGED systemActive

VCNext == 
    \/ \E n \in Nodes : VCInternalEvent(n)
    \/ \E n \in Nodes: \E m \in messages[n] : VCExternalEvent(n, m)

VCNoMessagesLeft == \A n \in Nodes : messages[n] = {}
VCMonotonicity == \A n1 \in Nodes, n2 \in Nodes : vcState[n1][n2] <= vcState'[n1][n2]
VCSpec == 
    /\ VCInit 
    (***********************************************************************)
    (*figure out why this stutters after VCInit                            *)
    (***********************************************************************)
    \* /\ WF_<<vcState, messages>>(VCNext) 
    /\ [][VCNext]_<<vcState, messages>>
    /\ [][VCMonotonicity]_<<vcState, messages>>
    /\ <>[](systemActive => <>VCNoMessagesLeft)

=============================================================================
\* Modification History
\* Last modified Thu Dec 07 21:20:08 CET 2023 by shu
\* Created Thu Dec 07 14:23:41 CET 2023 by shu