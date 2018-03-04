-------------------------- MODULE TwoPhaseLocking --------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

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

insertHistory(self, op) ==
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

Abort(self, victim, reason) ==
  /\ state[victim] \in {"Init", "Running"}
  /\ insertHistory(victim, [f |-> "Abort"])
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

ViewSerializable ==
  LET Tx == {SelectSeq(history, LAMBDA x: x.proc = proc) : proc
             \in {proc \in Proc : state[proc] = "Commit"}}
      perms == {f \in [1..Cardinality(Tx) -> Tx]
                    : \A tx \in Tx
                      : \E proc \in 1..Cardinality(Tx) : f[proc] = tx}
   IN LET RECURSIVE concat(_, _, _, _)
          concat(f, n, size, acc) ==
            IF n > size THEN acc ELSE concat(f, n+1, size, acc \o f[n])
       IN \E perm \in perms
          : viewEq(InitValues, concat(perm, 1, Cardinality(Tx), <<>>))
\*            /\ \/ Cardinality(Tx) < 2
\*               \/ PrintT(<<history, concat(perm, 1, Cardinality(Tx), <<>>)>>)

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
     : state[proc] \in {"Init", "Running", "Commit", "Abort"}
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
  /\ ViewSerializable

(***************************************************************************)
(* Deadlock asserts that a process is stopping in a deadlock               *)
(***************************************************************************)
WaitingFor[self \in Proc, blocking \in SUBSET Proc] ==
  IF self \in blocking \/ state[self] # "Running"
  THEN {}
  ELSE LET grandChildren(proc) == WaitingFor[proc, blocking \cup {self}]
       IN LET dependsOn(children) ==
                children \cup UNION {grandChildren(proc) : proc \in children}
              hd == Head(transact[self])
          IN  CASE hd.f = "Read"
                   -> dependsOn(WRITE[hd.obj] \ {self})
                [] hd.f = "Write"
                   -> dependsOn((READ[hd.obj] \cup WRITE[hd.obj]) \ {self})
                [] OTHER -> {}

Deadlock[self \in Proc] == self \in WaitingFor[self, {}]

Resolve(self) ==
  LET waitingFor == WaitingFor[self, {}]
   IN  /\ (* <=> Deadlock[self] *)
           self \in waitingFor
       /\ (* abort a single transaction in deadlock randomly *)
          \E victim \in waitingFor : Abort(self, victim, "deadlock")

Next ==
  \/ \E self \in Proc
     : \/ /\ transact[self] # <<>>
          /\ LET hd == Head(transact[self])
                 tl == Tail(transact[self])
             IN  \/ Read(self, hd, tl)
                 \/ Write(self, hd, tl)
                 \/ Commit(self, hd, tl)
                 \/ Resolve(self)
       \/ Abort(self, self, "voluntary")
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
\* Last modified Sun Mar 04 11:45:11 JST 2018 by takayuki
\* Created Sat Feb 17 10:34:44 JST 2018 by takayuki
