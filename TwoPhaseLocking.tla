-------------------------- MODULE TwoPhaseLocking --------------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

CONSTANT Proc, Object

(***************************************************************************)
(* Proc is a set of transaction IDs.  Note that transaction #0 is a        *)
(* hypothetical transaction that wrote all initial values in store.        *)
(***************************************************************************)
ASSUME
  /\ Proc \subseteq Nat \ {0}
  /\ Proc \cap Object = {}

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
      seq(S) == UNION {[1..n -> S] : n \in Nat}
  IN  {Append(op, [f |-> "Commit"]) : op \in seq(Op)}

initValues == [obj \in Object |-> [proc |-> 0]]

Init ==
  /\ \E tx \in [Proc -> Transaction] : transact = tx
  /\ history = <<>>
  /\ state = [proc \in Proc |-> "Init"]
  /\ store = initValues
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

updateHistory(self, hd, tl, val) ==
  /\ history' = Append(history, [proc |-> self, op |-> hd, val |-> val])
  /\ transact' = [transact EXCEPT ![self] = tl]

ReadLongDurationLock(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ READ' = [READ EXCEPT ![hd.obj] = READ[hd.obj] \cup {self}]
  /\ updateHistory(self, hd, tl, bufferRead(self, hd.obj))
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, writeSet, WRITE>>
     ELSE UNCHANGED <<state, store, writeSet, WRITE>>

ReadShortDurationLock(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Read"
  /\ WRITE[hd.obj] \in {{}, {self}}
  /\ updateHistory(self, hd, tl, bufferRead(self, hd.obj))
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
  /\ updateHistory(self, hd, tl, [proc |-> self])
  /\ IF state[self] = "Init"
     THEN /\ state' = [state EXCEPT ![self] = "Running"]
          /\ UNCHANGED <<store, READ>>
     ELSE UNCHANGED <<state, store, READ>>

Commit(self, hd, tl) ==
  /\ state[self] \in {"Init", "Running"}
  /\ hd.f = "Commit"
  /\ updateHistory(self, hd, tl, [proc |-> self])
  /\ bufferFlush(self)
  /\ state' = [state EXCEPT ![self] = "Commit"]
  /\ READ' = [obj \in Object |-> READ[obj] \ {self}]
  /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
  /\ UNCHANGED <<writeSet>>

Abort(self, victim) ==
  /\ state[victim] \in {"Init", "Running"}
  /\ history' = Append(history, [proc |-> victim, op |-> [f |-> "Abort"]])
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
          : viewEq(initValues, concat(perm, 1, Cardinality(Tx), <<>>))
\*            /\ \/ Cardinality(Tx) < 2
\*               \/ PrintT(<<history, concat(perm, 1, Cardinality(Tx), <<>>)>>)

(***************************************************************************)
(* Invariants are a set of state predicates to assert that all states and  *)
(* locks are consistent, and if some of transactions successfully commit,  *)
(* the history of the committed transactions is serializable.              *)
(***************************************************************************)
TypeOK ==
  /\ \A proc \in Proc
     : state[proc] \in {"Init", "Running", "Commit", "Abort"}

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
          \E victim \in waitingFor : Abort(self, victim)

Next ==
  \/ \E self \in Proc
     : /\ transact[self] # <<>>
       /\ LET hd == Head(transact[self])
              tl == Tail(transact[self])
          IN  \/ Read(self, hd, tl)
              \/ Write(self, hd, tl)
              \/ Commit(self, hd, tl)
              \/ Resolve(self)
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
\* Last modified Sat Mar 03 14:33:25 JST 2018 by takayuki
\* Created Sat Feb 17 10:34:44 JST 2018 by takayuki
