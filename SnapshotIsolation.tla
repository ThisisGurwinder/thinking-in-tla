------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANT Proc, Object

VARIABLE
  transact,
  history,
  state,
  store,
  ts,
  writeSet, (* writes of uncommitted transaction *)
  startTS,
  commitTS,
  WRITE     (* write lock *)

vars == <<
  transact,
  history,
  state,
  store,
  ts,
  writeSet,
  startTS,
  commitTS,
  WRITE
>>

(***************************************************************************)
(* Transaction is a set of all possible transactions                       *)
(***************************************************************************)
Transact ==
  LET Op == [f : {"Read", "Write"}, obj : Object]
      seq(S) == UNION {[1..n -> S] : n \in Nat}
  IN  {Append(op, [f |-> "Commit"]) : op \in seq(Op)}

Init ==
  /\ \E tx \in [Proc -> Transact] : transact = tx
  /\ history = <<>>
  /\ state = [proc \in Proc |-> "Init"]
  /\ store = [obj \in Object |-> {[ver |-> 0, val |-> 0]}]
  /\ ts = 0
  /\ writeSet = [proc \in Proc |-> [obj \in Object |-> {}]]
  /\ startTS = [proc \in Proc |-> 0]
  /\ commitTS = [proc \in Proc |-> 0]
  /\ WRITE = [obj \in Object |-> {}]

(***************************************************************************)
(* snapshotWrite records writes of running, uncommitted transactions       *)
(***************************************************************************)
snapshotWrite(self, obj, val) ==
  writeSet' = [writeSet EXCEPT ![self][obj] = {val}]

(***************************************************************************)
(* snapshotRead reads an object in writeSet if exists, then the latest     *)
(* version in store among ones visible to the transaction                  *)
(***************************************************************************)
snapshotRead(self, obj, ver) ==
  IF writeSet[self][obj] # {}
  THEN CHOOSE v \in writeSet[self][obj] : TRUE
  ELSE LET h == {i \in store[obj] : i.ver <= ver}
           s == CHOOSE i \in h : \A j \in h: i.ver >= j.ver
        IN s.val

(***************************************************************************)
(* snapshotCommit reflects writeSet into store                             *)
(***************************************************************************)
snapshotCommit(self, ver) ==
  store' = [obj \in Object |->
    IF writeSet[self][obj] # {}
    THEN store[obj] \cup
         {[ver |-> commitTS'[self],
           val |-> CHOOSE v \in writeSet[self][obj] : TRUE]}
    ELSE store[obj]]

updateHistory(self, hd, tl, val) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd, val |-> val])
  /\ transact' = [transact EXCEPT ![self] = tl]

Read(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ IF state[self] = "Init"
     THEN /\ startTS' = [startTS EXCEPT ![self] = ts]
          /\ state' = [state EXCEPT ![self] = "Running"]
     ELSE UNCHANGED <<state, startTS>>
  /\ LET val == snapshotRead(self, hd.obj, startTS'[self])
     IN  updateHistory(self, hd, tl, val)
  /\ UNCHANGED <<store, ts, writeSet, commitTS, WRITE>>

Write(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Write"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ WRITE' = [WRITE EXCEPT ![hd.obj] = WRITE[hd.obj] \cup {self}]
  /\ IF state[self] = "Init"
     THEN startTS' = [startTS EXCEPT ![self] = ts]
     ELSE UNCHANGED <<startTS>>
  (* Detect Write-Write conflict *)
  /\ IF {i \in store[hd.obj] : i.ver > startTS'[self]} # {}
     THEN state' = [state EXCEPT ![self] = "Abort"]
     ELSE IF state[self] = "Init"
          THEN state' = [state EXCEPT ![self] = "Running"]
          ELSE UNCHANGED  <<state>>
  /\ IF state'[self] = "Running"
     THEN LET val == snapshotRead(self, hd.obj, startTS'[self])
          IN  /\ snapshotWrite(self, hd.obj, val+1)
              /\ updateHistory(self, hd, tl, val+1)
     ELSE UNCHANGED <<transact, history, writeSet>>
  /\ UNCHANGED <<store, ts, commitTS>>

Commit(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Commit"
  /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
  /\ ts' = ts + 1
  /\ commitTS' = [commitTS EXCEPT ![self] = ts']
  /\ state' = [state EXCEPT ![self] = "Commit"]
  /\ snapshotCommit(self, commitTS'[self])
  /\ updateHistory(self, hd, tl, commitTS'[self])
  /\ UNCHANGED <<writeSet, startTS>>

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
     : state[proc] \in {"Init", "Running", "Commit", "Abort"}
  /\ \A proc \in Proc
     : \A obj \in Object
       : Cardinality(writeSet[proc][obj]) \in {0, 1}
  /\ \A obj \in Object
     : Cardinality(WRITE[obj]) \in {0,1}

(***************************************************************************)
(* Serializable asserts that, if some of transactions successfully commit, *)
(* the history of the committed transactions is serializable.              *)
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

(***************************************************************************)
(* Deadlock asserts that a process is stopping in a deadlock               *)
(***************************************************************************)
Waiting[self \in Proc, blocking \in SUBSET Proc] ==
  IF self \in blocking \/ state[self] # "Running"
  THEN {}
  ELSE LET grandChildren(proc) == Waiting[proc, blocking \cup {self}]
       IN LET dependsOn(children) ==
                children \cup UNION {grandChildren(proc) : proc \in children}
              hd == Head(transact[self])
          IN  CASE hd.f = "Write"
                   -> dependsOn(WRITE[hd.obj] \ {self})
                [] OTHER -> {}

Deadlock[self \in Proc] == self \in Waiting[self, {}]

(***************************************************************************)
(* Properties assert that all transactions eventually commit, abort or     *)
(* stop in a deadlock.                                                     *)
(***************************************************************************)
Properties == <>[](\A proc \in Proc
                   : state[proc] \in {"Commit", "Abort"} \/ Deadlock[proc])

THEOREM Spec => []Invariants /\ Properties
=============================================================================
\* Modification History
\* Last modified Sat Feb 17 21:16:52 JST 2018 by takayuki
\* Created Mon Feb 12 21:27:20 JST 2018 by takayuki
