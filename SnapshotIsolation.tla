------------------------- MODULE SnapshotIsolation -------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC, Graphs

CONSTANT Proc, Object, MAXTXOPS

(***************************************************************************)
(* Proc is a set of non-zero process IDs, i.e.  TXIDs.  Note that TXID #0  *)
(* is a hypothetical transaction that wrote all initial values in store.   *)
(* Object represents a set of objects in database.  MAXTXOPS is the max    *)
(* number of read and write operations in a transaction.                   *)
(***************************************************************************)
ASSUME
  /\ Proc \subseteq Nat \ {0}
  /\ Proc \cap Object = {}
  /\ MAXTXOPS \in Nat \ {0}

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

ANY(S) == CHOOSE s \in S : TRUE

(***************************************************************************)
(* Transaction is a set of all possible transactions                       *)
(***************************************************************************)
Transact ==
  LET Op == [f : {"Read", "Write"}, obj : Object]
      seq(S) == UNION {[1..n -> S] : n \in 1..MAXTXOPS}
  IN  {Append(op, [f |-> "Commit"]) : op \in seq(Op)}

State == {"Init", "Running", "Commit", "Abort"}
Value == [proc : {0} \cup Proc]
Version == [ver : Nat, val : Value]
InitValues == [obj \in Object |-> {[ver |-> 0, val |-> [proc |-> 0]]}]

Init ==
  /\ \E tx \in [Proc -> Transact] : transact = tx
  /\ history = <<>>
  /\ state = [proc \in Proc |-> "Init"]
  /\ store = InitValues
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
  THEN ANY(writeSet[self][obj])
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
           val |-> ANY(writeSet[self][obj])]}
    ELSE store[obj]]


recordHistoryValue(self, hd, tl, val) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd, val |-> val])
  /\ transact' = [transact EXCEPT ![self] = tl]

recordHistory(self, hd, tl) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd])
  /\ transact' = [transact EXCEPT ![self] = tl]

appendHistory(self, op) ==
  /\ history' = Append(history, [proc |-> self, op |-> op])

Read(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ IF state[self] = "Init"
     THEN /\ startTS' = [startTS EXCEPT ![self] = ts]
          /\ state' = [state EXCEPT ![self] = "Running"]
     ELSE UNCHANGED <<state, startTS>>
  /\ LET val == snapshotRead(self, hd.obj, startTS'[self])
     IN  recordHistoryValue(self, hd, tl, val)
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
     THEN LET val == [proc |-> self]
          IN  /\ snapshotWrite(self, hd.obj, val)
              /\ recordHistoryValue(self, hd, tl, val)
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
  /\ recordHistory(self, hd, tl)
  /\ UNCHANGED <<writeSet, startTS>>

Abort(victim, reason) ==
  /\ state[victim] \in {"Init", "Running"}
  /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {victim}]
  /\ state' = [state EXCEPT ![victim] = "Abort"]
  /\ appendHistory(victim, [f |-> "Abort", reason|-> reason])
  /\ UNCHANGED <<transact, store, ts, writeSet, startTS, commitTS>>

TypeOK ==
  /\ \A idx \in DOMAIN history
     : LET e == history[idx]
       IN  /\ e.proc \in Proc
           /\ \/ /\ e.op.f \in {"Read", "Write"}
                 /\ e.op.obj \in Object
                 /\ e.val \in Value
              \/ e.op.f \in {"Commit", "Abort"}
  /\ \A proc \in Proc
     : state[proc] \in State
  /\ \A obj \in Object
     : \A t \in store[obj] : t \in Version
  /\ \A proc \in Proc
     : \A obj \in Object
       : Cardinality(writeSet[proc][obj]) \in {0, 1}

LockOK ==
  /\ \A obj \in Object
     : Cardinality(WRITE[obj]) \in {0,1}

Invariants ==
  /\ TypeOK
  /\ LockOK

(***************************************************************************)
(* ViewSerializable asserts that, if some of transactions successfully     *)
(* commit, the history of the committed transactions is view-serializable. *)
(***************************************************************************)
RECURSIVE viewEq(_, _)
viewEq(s, hist) ==
  IF hist = <<>>
  THEN (********************************************************************)
       (* transaction updates store on commit, so store has only writes    *)
       (* successfully committed.                                          *)
       (********************************************************************)
       \A obj \in Object
       : \E i \in store[obj]
         : \A j \in store[obj]
           : i.ver >= j.ver /\ s[obj].proc = i.val.proc
  ELSE LET hd == Head(hist)
        IN CASE hd.op.f = "Read"
                -> s[hd.op.obj] = hd.val /\ viewEq(s, Tail(hist))
             [] hd.op.f = "Write"
                -> viewEq([s EXCEPT ![hd.op.obj] = hd.val], Tail(hist))
             [] OTHER
                -> viewEq(s, Tail(hist))

RECURSIVE concat(_, _, _, _)
concat(f, n, size, acc) ==
  IF n > size THEN acc ELSE concat(f, n+1, size, acc \o f[n])

ViewSerializable ==
  LET commit == SelectSeq(history, LAMBDA x: x.op.f = "Commit")
      Tx == {SelectSeq(history, LAMBDA x: x.proc = proc)
             : proc \in {commit[i].proc : i \in 1..Len(commit)}}
      perms == {f \in [1..Cardinality(Tx) -> Tx]
                : \A tx \in Tx
                  : \E i \in 1..Cardinality(Tx) : f[i] = tx}
  IN  \E perm \in perms
      : LET serialHistory == concat(perm, 1, Cardinality(Tx), <<>>)
        IN  viewEq([obj \in Object |-> [proc |-> 0]], serialHistory)
\*      /\ \/ Cardinality(Tx) < 2
\*         \/ PrintT(<<history, serialHistory>>)

(***************************************************************************)
(* WaitingFor builds a set of edges of dependency graph in which a cycle   *)
(* occurs when deadlock has happened.                                      *)
(***************************************************************************)
WaitingFor[proc \in Proc] ==
  IF state[proc] # "Running"
  THEN {}
  ELSE LET from == proc
           hd == Head(transact[from])
           edges(TO) == {<<from, to>> : to \in TO}
       IN  CASE hd.f = "Write"
                  -> edges(WRITE[hd.obj] \ {from})
             [] OTHER -> {}

(***************************************************************************)
(* Resolve aborts a transaction involved in deadlock and try to resolve.   *)
(***************************************************************************)
Resolve(self) ==
  LET edge == UNION {WaitingFor[proc] : proc \in Proc}
      node == UNION {{from, to} : <<from, to>> \in edge}
      dependency == [edge |-> edge, node |-> node]
   IN  \E victim \in {t \in node : IsInCycle(t, dependency)}
        : Abort(victim, "deadlock")

Next ==
  \/ \E self \in Proc
     : \/ /\ transact[self] # <<>>
          /\ \/ LET hd == Head(transact[self])
                    tl == Tail(transact[self])
                IN  \/ Read(self, hd, tl)
                    \/ Write(self, hd, tl)
                    \/ Commit(self, hd, tl)
                    \/ Resolve(self)
       \/ Abort(self, "voluntary")
  \/ /\ \A proc \in Proc : state[proc] \in {"Commit", "Abort"}
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* A temporal property asserts that all transactions eventually commit or  *)
(* abort without deadlock.                                                 *)
(***************************************************************************)
EventuallyAllCommitOrAbort ==
   <>[](\A proc \in Proc : state[proc] \in {"Commit", "Abort"})

(***************************************************************************)
(* A temporal property asserts that some transactions eventually commit.   *)
(***************************************************************************)
EventuallySomeCommit ==
   <>[](\E proc \in Proc : state[proc] = "Commit")

Properties ==
  /\ EventuallyAllCommitOrAbort

THEOREM Spec => []Invariants /\ Properties
=============================================================================
\* Modification History
\* Last modified Sat Mar 17 15:37:46 JST 2018 by takayuki
\* Created Mon Feb 12 21:27:20 JST 2018 by takayuki
