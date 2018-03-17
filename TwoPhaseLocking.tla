-------------------------- MODULE TwoPhaseLocking --------------------------
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
  writeSet,
  READ,        (* read lock  *)
  WRITE        (* write lock *)

vars == <<
  transact,
  history,
  state,
  store,
  writeSet,
  READ,
  WRITE
>>

(***************************************************************************)
(* Transaction is a set of all possible transactions                       *)
(***************************************************************************)
Transaction ==
  LET Op == [f : {"Read", "Write"}, obj : Object]
      seq(S) == UNION {[1..n -> S] : n \in 1..MAXTXOPS}
  IN  {Append(op, [f |-> "Commit"]) : op \in seq(Op)}

State == {"Init", "Running", "Commit", "Abort"}
Value == [proc : {0} \cup Proc]
InitValues == [obj \in Object |-> [proc |-> 0]]

Init ==
  /\ \E tx \in [Proc -> Transaction] : transact = tx
  /\ history = <<>>
  /\ state = [proc \in Proc |-> "Init"]
  /\ store = InitValues
  /\ writeSet = [proc \in Proc |-> [obj \in Object |-> {}]]
  /\ READ = [obj \in Object |-> {}]
  /\ WRITE = [obj \in Object |-> {}]

bufferWrite(self, obj, val) ==
  writeSet' = [writeSet EXCEPT ![self][obj] = {val}]

ANY(S) == CHOOSE s \in S : TRUE

bufferRead(self, obj) ==
  IF writeSet[self][obj] # {} THEN ANY(writeSet[self][obj]) ELSE store[obj]

bufferFlush(self) ==
  store' = [obj \in Object |-> bufferRead(self, obj)]

recordHistoryValue(self, hd, tl, val) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd, val |-> val])
  /\ transact' = [transact EXCEPT ![self] = tl]

recordHistory(self, hd, tl) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd])
  /\ transact' = [transact EXCEPT ![self] = tl]

appendHistory(self, op) ==
  /\ history' = Append(history, [proc |-> self, op |-> op])

ReadLongDurationLock(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ READ' = [READ EXCEPT ![hd.obj] = READ[hd.obj] \cup {self}]
  /\ recordHistoryValue(self, hd, tl, bufferRead(self, hd.obj))
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, writeSet, WRITE>>
     ELSE UNCHANGED <<state, store, writeSet, WRITE>>

ReadShortDurationLock(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ recordHistoryValue(self, hd, tl, bufferRead(self, hd.obj))
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, writeSet, READ, WRITE>>
     ELSE UNCHANGED <<state, store, writeSet, READ, WRITE>>

Read(self, hd, tl) == ReadLongDurationLock(self, hd, tl)

Write(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Write"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ WRITE' = [WRITE EXCEPT ![hd.obj] = WRITE[hd.obj] \cup {self}]
  /\ READ[hd.obj] \in SUBSET WRITE'[hd.obj]
  /\ bufferWrite(self, hd.obj, [proc |-> self])
  /\ recordHistoryValue(self, hd, tl, [proc |-> self])
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, READ>>
     ELSE UNCHANGED <<state, store, READ>>

Commit(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Commit"
  /\ recordHistory(self, hd, tl)
  /\ bufferFlush(self)
  /\ state' = [state EXCEPT ![self] = "Commit"]
  /\ READ' = [obj \in Object |-> READ[obj] \ {self}]
  /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
  /\ UNCHANGED <<writeSet>>

Abort(victim, reason) ==
  /\ state[victim] \in {"Init", "Running"}
  /\ appendHistory(victim, [f |-> "Abort", reason|-> reason])
  /\ state' = [state EXCEPT ![victim] = "Abort"]
  /\ READ' = [obj \in Object |-> READ[obj] \ {victim}]
  /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {victim}]
  /\ UNCHANGED <<transact, store, writeSet>>

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
       \A obj \in Object : s[obj].proc = store[obj].proc
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
      Tx == {SelectSeq(history, LAMBDA x: x.proc = proc) : proc
             \in {commit[i].proc : i \in 1..Len(commit)}}
      perms == {f \in [1..Cardinality(Tx) -> Tx]
                    : \A tx \in Tx
                      : \E i \in 1..Cardinality(Tx) : f[i] = tx}
  IN  \E perm \in perms
      : viewEq(InitValues, concat(perm, 1, Cardinality(Tx), <<>>))
\*      /\ \/ Cardinality(Tx) < 2
\*         \/ PrintT(<<history, concat(perm, 1, Cardinality(Tx), <<>>)>>)

(***************************************************************************)
(* ViewSerializableInCommitOrder is stronger than ViewSerializable in that *)
(* serialization order is restricted to commit order.                      *)
(***************************************************************************)
ViewSerializableInCommitOrder ==
  LET commit == SelectSeq(history, LAMBDA x: x.op.f = "Commit")
      tx == [i \in 1..Len(commit)
             |-> SelectSeq(history, LAMBDA x: x.proc = commit[i].proc)]
      serialHistory == concat(tx, 1, Len(tx), <<>>)
  IN viewEq(InitValues, serialHistory)
\*     /\ \/ Len(tx) < 2
\*        \/ PrintT(<<history, serialHistory>>)

(***************************************************************************)
(* Invariants are a set of state predicates to assert that all states and  *)
(* locks are consistent, and if some of transactions successfully commit,  *)
(* the history of the committed transactions is serializable.              *)
(***************************************************************************)
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
     : store[obj] \in Value
  /\ \A proc \in Proc
     : \A obj \in Object
       : Cardinality(writeSet[proc][obj]) \in {0, 1}

LockOK ==
  /\ \A obj \in Object
     : Cardinality(WRITE[obj]) \in {0,1}
  /\ \A obj \in Object
     : Cardinality(WRITE[obj]) # 0 =>  READ[obj] \in SUBSET WRITE[obj]

Invariants ==
  /\ TypeOK
  /\ LockOK
  /\ ViewSerializableInCommitOrder

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
       IN  CASE hd.f = "Read"
                  -> edges(WRITE[hd.obj] \ {from})
             [] hd.f = "Write"
                  -> edges((READ[hd.obj] \cup WRITE[hd.obj]) \ {from})
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
          /\ LET hd == Head(transact[self])
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
(* abort.                                                                  *)
(***************************************************************************)
EventuallyAllCommitOrAbort ==
  <>[](\A proc \in Proc : state[proc] \in {"Commit", "Abort"})

Properties == EventuallyAllCommitOrAbort

THEOREM Spec => []Invariants /\ Properties
=============================================================================
\* Modification History
\* Last modified Sat Mar 17 14:37:51 JST 2018 by takayuki
\* Created Sat Feb 17 10:34:44 JST 2018 by takayuki
