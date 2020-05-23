------------------------------- MODULE atomic -------------------------------
EXTENDS Sequences, Integers, Naturals, TLC, FiniteSets

CONSTANTS K, M, Alpha, N
(* K is the sample size, M is rounds, N is nodes, Alpha is threshold per the paper*)
Nodes == 1..N
Colors == {0, 1}

(*
--algorithm atomic{
    variable colors = <<1, 1, 0, 0, 2>>, counter = {}, query = {};
    
    define{
        RoundMsg(round) == {resp \in counter: resp.myrounds = round}
        ColorCounter(c, round) == {resp \in counter: resp.color = c /\ resp.myrounds = round}
    }
    
    macro Respond(n, c, rounds){
        counter := counter \union {[node |-> n, color |-> c, myrounds |-> rounds]}
    }
    
    fair process (n \in Nodes)
    variables rounds = 1, count = 1, decided = 2 ;{
    
    LOOOP: while(rounds <= M){
            if(colors[self] # 2){
                \* if it has color than respond
                Respond(self, colors[self], rounds);
            };  
            else {
                \* set color from the node 1
                \* Here we assume that uncolored node got a query from a querying node with color of colors[1] 
                colors[self] := colors[1];
                Respond(self, colors[self], rounds);
            };
    WAIT:   await(Cardinality(RoundMsg(rounds)) > K + 1);
            if(Cardinality(ColorCounter(0, rounds)) \geq Alpha){
                colors[self] := 0;
            };
            if(Cardinality(ColorCounter(1, rounds)) \geq Alpha){
    COLOR:      colors[self] := 1;
            };
            
    INCRE:  rounds := rounds + 1;
          };
          
          decided := colors[self];
          
    }
}
*)
\* BEGIN TRANSLATION
VARIABLES colors, counter, query, pc

(* define statement *)
RoundMsg(round) == {resp \in counter: resp.myrounds = round}
ColorCounter(c, round) == {resp \in counter: resp.color = c /\ resp.myrounds = round}

VARIABLES rounds, count, decided

vars == << colors, counter, query, pc, rounds, count, decided >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ colors = <<1, 1, 0, 0, 2>>
        /\ counter = {}
        /\ query = {}
        (* Process n *)
        /\ rounds = [self \in Nodes |-> 1]
        /\ count = [self \in Nodes |-> 1]
        /\ decided = [self \in Nodes |-> 2]
        /\ pc = [self \in ProcSet |-> "LOOOP"]

LOOOP(self) == /\ pc[self] = "LOOOP"
               /\ IF rounds[self] <= M
                     THEN /\ IF colors[self] # 2
                                THEN /\ counter' = (counter \union {[node |-> self, color |-> (colors[self]), myrounds |-> rounds[self]]})
                                     /\ UNCHANGED colors
                                ELSE /\ colors' = [colors EXCEPT ![self] = colors[1]]
                                     /\ counter' = (counter \union {[node |-> self, color |-> (colors'[self]), myrounds |-> rounds[self]]})
                          /\ pc' = [pc EXCEPT ![self] = "WAIT"]
                          /\ UNCHANGED decided
                     ELSE /\ decided' = [decided EXCEPT ![self] = colors[self]]
                          /\ pc' = [pc EXCEPT ![self] = "Done"]
                          /\ UNCHANGED << colors, counter >>
               /\ UNCHANGED << query, rounds, count >>

WAIT(self) == /\ pc[self] = "WAIT"
              /\ (Cardinality(RoundMsg(rounds[self])) > K + 1)
              /\ IF Cardinality(ColorCounter(0, rounds[self])) \geq Alpha
                    THEN /\ colors' = [colors EXCEPT ![self] = 0]
                    ELSE /\ TRUE
                         /\ UNCHANGED colors
              /\ IF Cardinality(ColorCounter(1, rounds[self])) \geq Alpha
                    THEN /\ pc' = [pc EXCEPT ![self] = "COLOR"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "INCRE"]
              /\ UNCHANGED << counter, query, rounds, count, decided >>

COLOR(self) == /\ pc[self] = "COLOR"
               /\ colors' = [colors EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "INCRE"]
               /\ UNCHANGED << counter, query, rounds, count, decided >>

INCRE(self) == /\ pc[self] = "INCRE"
               /\ rounds' = [rounds EXCEPT ![self] = rounds[self] + 1]
               /\ pc' = [pc EXCEPT ![self] = "LOOOP"]
               /\ UNCHANGED << colors, counter, query, count, decided >>

n(self) == LOOOP(self) \/ WAIT(self) \/ COLOR(self) \/ INCRE(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Nodes: n(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(n(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
Agreement == (\A i,j \in Nodes: decided[i] # 2 /\ decided[j] # 2 => decided[i] = decided[j])
Progress == <>(\A i \in Nodes: decided[i] # 2)

=============================================================================
\* Modification History
\* Last modified Fri May 22 22:25:00 EDT 2020 by yashf
\* Created Mon May 18 18:09:14 EDT 2020 by yashf
