-------------------------- MODULE TwoPhaseLocking --------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANT Proc, Object

VARIABLE
  transact,
  history,
  state,
  store,
  READ,        (* read lock  *)
  WRITE        (* write lock *)

vars == <<
  transact,
  history,
  state,
  store,
  READ,
  WRITE
>>

(***************************************************************************)
(* Transaction is a set of all possible transactions                       *)
(***************************************************************************)
Transaction ==
  LET Op == [f : {"Read", "Write"}, obj : Object]
      seq(S) == UNION {[1..n -> S] : n \in Nat}
  IN  {Append(op, [f |-> "Commit"]) : op \in seq(Op)}

Init ==
  /\ \E tx \in [Proc -> Transaction] : transact = tx
  /\ history = <<>>
  /\ state = [proc \in Proc |-> "Init"]
  /\ store = [obj \in Object |-> 0]
  /\ READ = [obj \in Object |-> {}]
  /\ WRITE = [obj \in Object |-> {}]

updateHistory(self, hd, tl, val) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd, val |-> val])
  /\ transact' = [transact EXCEPT ![self] = tl]

ReadLongDurationLock(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ READ' = [READ EXCEPT ![hd.obj] = READ[hd.obj] \cup {self}]
  /\ updateHistory(self, hd, tl, store[hd.obj])
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, WRITE>>
     ELSE UNCHANGED <<state, store, WRITE>>

ReadShortDurationLock(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ updateHistory(self, hd, tl, store[hd.obj])
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, READ, WRITE>>
     ELSE UNCHANGED <<state, store, READ, WRITE>>

Read(self, hd, tl) == ReadLongDurationLock(self, hd, tl)

Write(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Write"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ WRITE' = [WRITE EXCEPT ![hd.obj] = WRITE[hd.obj] \cup {self}]
  /\ READ[hd.obj] \in SUBSET WRITE'[hd.obj]
  /\ store' = [store EXCEPT ![hd.obj] = store[hd.obj]+1]
  /\ updateHistory(self, hd, tl, store[hd.obj]+1)
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<READ>>
     ELSE UNCHANGED <<state, READ>>

Commit(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Commit"
  /\ updateHistory(self, hd, tl, 0)
  /\ state' = [state EXCEPT ![self] = "Commit"]
  /\ READ' = [obj \in Object |-> READ[obj] \ {self}]
  /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
  /\ UNCHANGED <<store>>

Next == \E self \in Proc
  : /\ transact[self] # <<>>
    /\ LET hd == Head(transact[self])
           tl == Tail(transact[self])
       IN  \/ Read(self, hd, tl)
           \/ Write(self, hd, tl)
           \/ Commit(self, hd, tl)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Invariants ==
  /\ \A proc \in Proc
     : state[proc] \in {"Init", "Running", "Commit"}
  /\ \A obj \in Object
     : Cardinality(WRITE[obj]) \in {0,1}
  /\ \A obj \in Object
     : Cardinality(WRITE[obj]) # 0 =>  READ[obj] \in SUBSET WRITE[obj]

(***************************************************************************)
(* Serializable tests if a history is serializable                         *)
(***************************************************************************)
RECURSIVE consistent(_, _)
consistent(s, hist) ==
  IF hist = <<>>
  THEN TRUE
  ELSE LET hd == Head(hist)
        IN CASE hd.op.f = "Read"
                -> s[hd.op.obj] = hd.val /\ consistent(s, Tail(hist))
             [] hd.op.f = "Write"
                -> consistent([s EXCEPT ![hd.op.obj] = hd.val], Tail(hist))
             [] OTHER
                -> consistent(s, Tail(hist))

Serializable ==
  LET Tx == {SelectSeq(history, LAMBDA x: x.proc = proc) : proc
             \in {proc \in Proc : state[proc] = "Commit"}}
      perms == {f \in [1..Cardinality(Tx) -> Tx]
                    : \A tx \in Tx
                      : \E proc \in 1..Cardinality(Tx) : f[proc] = tx}
   IN LET RECURSIVE concat(_, _, _, _)
          concat(f, n, size, acc) ==
            IF n > size THEN acc ELSE concat(f, n+1, size, acc \o f[n])
       IN \E perm \in perms
          : consistent([obj \in Object |-> 0],
                       concat(perm, 1, Cardinality(Tx), <<>>))
\*            /\ \/ Cardinality(Tx) < 2
\*               \/ PrintT(<<history, concat(perm, 1, Cardinality(Tx), <<>>)>>)

(****************************************************************************
Properties assert that if some of transactions successfully commit then
the history of the committed transactions is serializable
****************************************************************************)
Properties == []Serializable

(***************************************************************************)
(* EventuallyAllCommit is used to detect a deadlock                        *)
(***************************************************************************)
EventuallyAllCommit == <>[](\E proc \in Proc : state[proc] = "Commit")

THEOREM Spec => []Invariants /\ Properties
=============================================================================
\* Modification History
\* Last modified Sat Feb 17 13:58:11 JST 2018 by takayuki
\* Created Sat Feb 17 10:34:44 JST 2018 by takayuki
