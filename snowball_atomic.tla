-------------------------- MODULE snowball_atomic --------------------------
EXTENDS Sequences, Integers, Naturals, TLC, FiniteSets

CONSTANTS K, M, Alpha, N, Beta
(* K is the sample size, M is rounds, N is nodes, Alpha is threshold per the paper*)
Nodes == 1..N
Colors == {0, 1}

(*
--algorithm atomic{
    variable colors = <<1, 1, 0, 2, 2>>, counter = {}, query = {}, zeroConfidence = 0, oneConfidence = 0;
    define{
        RoundMsg(round) == {resp \in counter: resp.myrounds = round}
        ColorCounter(c) == {resp \in counter: resp.color = c}
    }
    
    macro Respond(n, c){
        counter := counter \union {[node |-> n, color |-> c]}
    }
    
    fair process (n \in Nodes)
    variables count = 1, decided = 2, decision = FALSE, majority = FALSE, conviction = 0, lastcol = 0  ;{
    LOOOP: while(decision # TRUE){
            if(colors[self] # 2){
                \* if it has color than respond
                Respond(self, colors[self]);
                if(self # 1){
                    decision := TRUE;
                };
            }  
            else {
                \* set color from the node 1
                \* Here we assume that uncolored node got a query from a querying node with color of colors[1] 
                colors[self] := colors[1];
                Respond(self, colors[self]);
                decision := TRUE;
            };
     WAIT:  if(self = 1){
    CONV0:      with(c \in {0}){
                    if(Cardinality(ColorCounter(c)) \geq Alpha){
                        majority := TRUE;
                        zeroConfidence := zeroConfidence + 1;
                        if(zeroConfidence > oneConfidence){
                            colors[self] := 0;
                        };
                        if(colors[self] # lastcol){
                            lastcol := 0;
                            conviction := 1
                        }
                        else{
                            conviction := conviction + 1;
                            if(conviction \geq Beta){
                                decided := 0;
                                decision := TRUE;
                            }
                        };
                    }
                };
    CONV1:      with(c \in {1}){
                    if(Cardinality(ColorCounter(c)) \geq Alpha){
                        oneConfidence := oneConfidence + 1;
                        if(oneConfidence > zeroConfidence){
                            colors[self] := 1;
                        };
                        if(colors[self] # lastcol){
                            lastcol := 1;
                            conviction := 1
                        }
                        else{
                            conviction := conviction + 1;
                            if(conviction \geq Beta){
                                decided := 1;
                                decision := TRUE;
                            }
                        };
                    }
                };
            };
           };  
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES colors, counter, query, zeroConfidence, oneConfidence, pc

(* define statement *)
RoundMsg(round) == {resp \in counter: resp.myrounds = round}
ColorCounter(c) == {resp \in counter: resp.color = c}

VARIABLES count, decided, decision, majority, conviction, lastcol

vars == << colors, counter, query, zeroConfidence, oneConfidence, pc, count, 
           decided, decision, majority, conviction, lastcol >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ colors = <<1, 1, 0, 2, 2>>
        /\ counter = {}
        /\ query = {}
        /\ zeroConfidence = 0
        /\ oneConfidence = 0
        (* Process n *)
        /\ count = [self \in Nodes |-> 1]
        /\ decided = [self \in Nodes |-> 2]
        /\ decision = [self \in Nodes |-> FALSE]
        /\ majority = [self \in Nodes |-> FALSE]
        /\ conviction = [self \in Nodes |-> 0]
        /\ lastcol = [self \in Nodes |-> 0]
        /\ pc = [self \in ProcSet |-> "LOOOP"]

LOOOP(self) == /\ pc[self] = "LOOOP"
               /\ IF decision[self] # TRUE
                     THEN /\ IF colors[self] # 2
                                THEN /\ counter' = (counter \union {[node |-> self, color |-> (colors[self])]})
                                     /\ IF self # 1
                                           THEN /\ decision' = [decision EXCEPT ![self] = TRUE]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED decision
                                     /\ UNCHANGED colors
                                ELSE /\ colors' = [colors EXCEPT ![self] = colors[1]]
                                     /\ counter' = (counter \union {[node |-> self, color |-> (colors'[self])]})
                                     /\ decision' = [decision EXCEPT ![self] = TRUE]
                          /\ pc' = [pc EXCEPT ![self] = "WAIT"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << colors, counter, decision >>
               /\ UNCHANGED << query, zeroConfidence, oneConfidence, count, 
                               decided, majority, conviction, lastcol >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ IF self = 1
                    THEN /\ pc' = [pc EXCEPT ![self] = "CONV0"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "LOOOP"]
              /\ UNCHANGED << colors, counter, query, zeroConfidence, 
                              oneConfidence, count, decided, decision, 
                              majority, conviction, lastcol >>

CONV0(self) == /\ pc[self] = "CONV0"
               /\ \E c \in {0}:
                    IF Cardinality(ColorCounter(c)) \geq Alpha
                       THEN /\ majority' = [majority EXCEPT ![self] = TRUE]
                            /\ zeroConfidence' = zeroConfidence + 1
                            /\ IF zeroConfidence' > oneConfidence
                                  THEN /\ colors' = [colors EXCEPT ![self] = 0]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED colors
                            /\ IF colors'[self] # lastcol[self]
                                  THEN /\ lastcol' = [lastcol EXCEPT ![self] = 0]
                                       /\ conviction' = [conviction EXCEPT ![self] = 1]
                                       /\ UNCHANGED << decided, decision >>
                                  ELSE /\ conviction' = [conviction EXCEPT ![self] = conviction[self] + 1]
                                       /\ IF conviction'[self] \geq Beta
                                             THEN /\ decided' = [decided EXCEPT ![self] = 0]
                                                  /\ decision' = [decision EXCEPT ![self] = TRUE]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << decided, 
                                                                  decision >>
                                       /\ UNCHANGED lastcol
                       ELSE /\ TRUE
                            /\ UNCHANGED << colors, zeroConfidence, decided, 
                                            decision, majority, conviction, 
                                            lastcol >>
               /\ pc' = [pc EXCEPT ![self] = "CONV1"]
               /\ UNCHANGED << counter, query, oneConfidence, count >>

CONV1(self) == /\ pc[self] = "CONV1"
               /\ \E c \in {1}:
                    IF Cardinality(ColorCounter(c)) \geq Alpha
                       THEN /\ oneConfidence' = oneConfidence + 1
                            /\ IF oneConfidence' > zeroConfidence
                                  THEN /\ colors' = [colors EXCEPT ![self] = 1]
                                  ELSE /\ TRUE
                                       /\ UNCHANGED colors
                            /\ IF colors'[self] # lastcol[self]
                                  THEN /\ lastcol' = [lastcol EXCEPT ![self] = 1]
                                       /\ conviction' = [conviction EXCEPT ![self] = 1]
                                       /\ UNCHANGED << decided, decision >>
                                  ELSE /\ conviction' = [conviction EXCEPT ![self] = conviction[self] + 1]
                                       /\ IF conviction'[self] \geq Beta
                                             THEN /\ decided' = [decided EXCEPT ![self] = 1]
                                                  /\ decision' = [decision EXCEPT ![self] = TRUE]
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED << decided, 
                                                                  decision >>
                                       /\ UNCHANGED lastcol
                       ELSE /\ TRUE
                            /\ UNCHANGED << colors, oneConfidence, decided, 
                                            decision, conviction, lastcol >>
               /\ pc' = [pc EXCEPT ![self] = "LOOOP"]
               /\ UNCHANGED << counter, query, zeroConfidence, count, majority >>

n(self) == LOOOP(self) \/ WAIT(self) \/ CONV0(self) \/ CONV1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: n(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Progress == <>(decided[1] # 2)
=============================================================================
\* Modification History
\* Last modified Fri May 22 02:15:33 EDT 2020 by yashf
\* Created Fri May 22 01:08:07 EDT 2020 by yashf
