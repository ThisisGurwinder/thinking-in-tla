------------------------------- MODULE Graphs -------------------------------
(***************************************************************************)
(* Another module that defines operators on graphs, almost exactly         *)
(* following the design principle introduced in The TLA+ Book, "Specifying *)
(* Systems", page 172.  A directed graph is represented as a record whose  *)
(* node field is the set of nodes and whose edge field is the set of       *)
(* edges, where an edge is an ordered pair of nodes.  Note that the node   *)
(* field is not used for now.                                              *)
(*                                                                         *)
(* A copy of the module introduced in The TLA+ Book is available at:       *)
(* https://github.com/tlaplus/Examples/blob/master/specifications/SpecifyingSystems/AdvancedExamples/Graphs.tla *)
(***************************************************************************)
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

(***************************************************************************)
(* Path enumerates all paths in G whose length, in terms of the number of  *)
(* edges in a path, is up to LEN.                                          *)
(***************************************************************************)
Path(G, LEN) ==
  {p \in UNION {[1..n -> G.edge] : n \in 1..LEN}
   : \A i \in 1..(Len(p)-1) : p[i][2] = p[i+1][1]}

(***************************************************************************)
(* IsCycle asserts that G is a cycle graph.                                *)
(***************************************************************************)
IsCycle(G) ==
  \E p \in Path(G, Cardinality(G.edge))
   : \E i, j \in 1..Len(p) : i # j /\ p[i][1] = p[j][2]

(***************************************************************************)
(* AreConnectedIn asserts that node m and n are connected in G.            *)
(***************************************************************************)
AreConnectedIn(m, n, G) ==
  \E p \in Path(G, Cardinality(G.edge))
   : (p[1][1] = m) /\ (p[Len(p)][2] = n)

(***************************************************************************)
(* IsInCycle asserts that node m is in a cycle.                            *)
(***************************************************************************)
IsInCycle(m, G) == AreConnectedIn(m, m, G)

=============================================================================
\* Modification History
\* Last modified Wed Mar 14 11:15:36 JST 2018 by takayuki
\* Created Tue Mar 13 15:43:02 JST 2018 by takayuki
