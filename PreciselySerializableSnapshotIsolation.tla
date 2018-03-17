--------------- MODULE PreciselySerializableSnapshotIsolation ---------------
EXTENDS FiniteSets, Naturals, Sequences, TLC, Graphs

(***************************************************************************)
(* This module specifies Serializable Snapshot Isolation (SSI) as well as  *)
(* Snapshot Isolation (SI).  You can use a boolean constant SERIALIZE to   *)
(* enable and disable the extention SSI introduces over SI.                *)
(***************************************************************************)
CONSTANTS Proc, Object, MAXTXOPS, SERIALIZE

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

ANY(S) == CHOOSE s \in S : TRUE

Starting == "Starting"
Running == "Running"
Commit == "Commit"
Abort == "Abort"
State == {Starting, Running, Commit, Abort}

(***************************************************************************)
(* Transaction is a set of all possible transactions                       *)
(***************************************************************************)
Read == "Read"
Write == "Write"
Transact ==
  LET Op == [f : {Read, Write}, obj : Object]
      seq(S) == UNION {[1..n -> S] : n \in 1..MAXTXOPS}
  IN  {Append(op, [f |-> Commit]) : op \in seq(Op)}


Value == [proc : {0} \cup Proc]
Version == [ver : Nat, val : Value]
InitValues == [obj \in Object |-> {[ver |-> 0, val |-> [proc |-> 0]]}]

(***************************************************************************
--fair algorithm PreciselySerializableSnapshotIsolation {
  variable
    transact \in [Proc -> Transact];
    state = [proc \in Proc |-> Starting];
    history = <<>>;
    store = InitValues;
    ts = 0;
    writeSet = [proc \in Proc |-> [obj \in Object |-> {}]];
    startTS = [proc \in Proc |-> 0];
    commitTS = [proc \in Proc |-> 0];
    SIREAD = [obj \in Object |-> {}];
    WRITE = [obj \in Object |-> {}]
  define {
    Hd[proc \in Proc] == Head(transact[proc])
    Tl[proc \in Proc] == Tail(transact[proc])

    TypeOK ==
      /\ \A idx \in DOMAIN history
         : LET e == history[idx]
           IN  /\ e.proc \in Proc
               /\ \/ /\ e.op.f \in {Read, Write}
                     /\ e.op.obj \in Object
                     /\ e.val \in Value
                  \/ e.op.f \in {Commit, Abort}
      /\ \A proc \in Proc
         : state[proc] \in State
      /\ \A obj \in Object
         : \A t \in store[obj] : t \in Version
      /\ \A proc \in Proc
         : \A obj \in Object
           : Cardinality(writeSet[proc][obj]) \in {0, 1}

    LockOK ==
      /\ \A obj \in Object
         : LET active == {proc \in WRITE[obj] : state[proc] = Running}
           IN  Cardinality(active) \in {0,1}

    (***********************************************************************)
    (* ConflictSerializable tests if a multiversion serialization graph    *)
    (* has no cycle, and asserts that the history of the committed         *)
    (* transactions is conflict-serializable.  DependsOn is also used to   *)
    (* implement a Cycle Testing Graph for PSSI.                           *)
    (***********************************************************************)
    DependsOn[__state    \in [Proc -> State],
              __commitTS \in [Proc -> Nat],
              proc \in Proc] ==
      IF __state[proc] # Commit
      THEN {}
      ELSE LET from == proc
               conflict(X, Y) == UNION {Y[obj] : obj \in {obj \in Object : proc \in X[obj]}}
           IN LET wr == {r \in conflict(WRITE, SIREAD) : __commitTS[from] <= startTS[r] /\ __state[r] = Commit}
                  ww == {w \in conflict(WRITE, WRITE)  : __commitTS[from] <= startTS[w] /\ __state[w] = Commit}
                  rw == {w \in conflict(SIREAD, WRITE) : startTS[from] < __commitTS[w]  /\ __state[w] = Commit}
              IN  UNION {{<<from, to>> : to \in (wr \ {from})},
                         {<<from, to>> : to \in (ww \ {from})},
                         {<<from, to>> : to \in (rw \ {from})}}

    __ConflictSerializable[__state    \in [Proc -> State],
                           __commitTS \in [Proc -> Nat]] ==
      LET edge == UNION {DependsOn[__state, __commitTS, proc] : proc \in Proc}
          node == UNION {{from, to} : <<from, to>> \in edge}
      IN ~IsCycle([edge |-> edge, node |-> node])

    ConflictSerializable == __ConflictSerializable[state, commitTS]

    (***********************************************************************)
    (* ViewSerializable asserts that, if some of transactions successfully *)
    (* commit, the history of the committed transactions is                *)
    (* view-serializable.                                                  *)
    (***********************************************************************)
    RECURSIVE viewEq(_, _)
    viewEq(s, hist) ==
      IF hist = <<>>
      THEN  \A obj \in Object
            : \E i \in store[obj]
              : \A j \in store[obj]
                : i.ver >= j.ver /\ s[obj].proc = i.val.proc
      ELSE LET hd == Head(hist)
           IN  CASE hd.op.f = Read
                    -> s[hd.op.obj] = hd.val /\ viewEq(s, Tail(hist))
                 [] hd.op.f = Write
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
\*                /\ \/ Cardinality(Tx) < 2
\*                   \/ PrintT(<<history, serialHistory>>)

    Invariants ==
      /\ TypeOK
      /\ LockOK
      /\ ConflictSerializable
      /\ ViewSerializable

    (***********************************************************************)
    (* WaitingFor builds a set of edges of dependency graph in which a     *)
    (* cycle occurs when deadlock has happened.                            *)
    (***********************************************************************)
    WaitingFor[proc \in Proc] ==
      IF state[proc] # "Running"
      THEN {}
      ELSE LET from == proc
               hd == Head(transact[from])
               edges(TO) == {<<from, to>> : to \in TO}
           IN  CASE hd.f = "Write"
                      -> edges(WRITE[hd.obj] \ {from})
                 [] OTHER -> {}

    Dependency ==
      LET edge == UNION {WaitingFor[proc] : proc \in Proc}
          node == UNION {{from, to} : <<from, to>> \in edge}
      IN  [edge |-> edge, node |-> node]

    Deadlock == IsCycle(Dependency)

    (***********************************************************************)
    (* A temporal property asserts that all transactions eventually commit *)
    (* or abort without deadlock.                                          *)
    (***********************************************************************)
    EventuallyAllCommitOrAbort ==
      <>[](\A proc \in Proc : state[proc] \in {Commit, Abort})

    (***********************************************************************)
    (* A temporal property asserts that some transactions eventually       *)
    (* commit.                                                             *)
    (***********************************************************************)
    EventuallySomeCommit ==
      <>[](\E proc \in Proc : state[proc] = Commit)

    Properties ==
      /\ EventuallyAllCommitOrAbort
  }
  macro recordHistoryValue(val) {
    history := Append(history, [proc |-> self, op |-> Hd[self], val |-> val]);
    transact[self] := Tl[self];
  }
  macro recordHistory() {
    history := Append(history, [proc |-> self, op |-> Hd[self]]);
    transact[self] := Tl[self];
  }
  macro appendHistory(proc, op) {
    history := Append(history, [proc |-> proc, op |-> op]);
  }
  macro Lock(lock, obj) {
    lock[obj] := lock[obj] \cup {self}
  }
  macro Abort(proc, reason) {
    state[proc] := Abort;
    appendHistory(proc, [f |-> Abort]);
  }
  process (proc \in Proc)
    variables
      temp = [proc |-> 0];
    {L10:
     startTS[self] := ts;
     state[self] := Running;
     L20:
      while (state[self] = Running)
       { either
         { await Hd[self].f = Read;
           if (SERIALIZE)
           { Lock(SIREAD, Hd[self].obj);
           }
           else
           { (* Get SIREAD for conflict-serializability test *)
             Lock(SIREAD, Hd[self].obj);
           };
         L30:
           (****************************************************************)
           (* Read in SI                                                   *)
           (****************************************************************)
           temp :=
             IF writeSet[self][Hd[self].obj] # {}
             THEN ANY(writeSet[self][Hd[self].obj])
             ELSE LET h == {i \in store[Hd[self].obj]
                            : i.ver <= startTS[self]}
                      s == CHOOSE i \in h : \A j \in h : i.ver >= j.ver
                  IN  s.val;
           recordHistoryValue(temp);
         }
         or
         { await /\ Hd[self].f = Write
                 /\ LET active == {proc \in WRITE[Hd[self].obj]
                                   : state[proc] = Running}
                    IN  active \in {{}, {self}};
           Lock(WRITE, Hd[self].obj);
          L40:
           (****************************************************************)
           (* Detect Write-Write conflict in SI                            *)
           (****************************************************************)
           if ({i \in store[Hd[self].obj] : i.ver > startTS[self]} # {})
           { Abort(self, "First-Updater-Wins");
             goto L20;
           };
          L43:
           writeSet[self][Hd[self].obj] := {[proc |-> self]};
           recordHistoryValue([proc |-> self]);
         }
         or
         { await Hd[self].f = Commit;
           if (/\ SERIALIZE
               /\ LET __state    == [state    EXCEPT ![self] = Commit]
                      __commitTS == [commitTS EXCEPT ![self] = ts + 1]
                  IN  ~__ConflictSerializable[__state, __commitTS])
           { Abort(self, "Cycle-Testing-Graph");
           }
           else
           { ts := ts + 1;
             commitTS[self] := ts;
             store := [obj \in Object |->
               IF writeSet[self][obj] # {}
               THEN store[obj] \cup {[ver |-> commitTS[self],
                                      val |-> ANY(writeSet[self][obj])]}
               ELSE store[obj]];
             state[self] := Commit;
             recordHistory();
           }
         }
         or
         { await Deadlock;
           (****************************************************************)
           (* Aborts a transaction involved in deadlock                    *)
           (****************************************************************)
           with (victim \in {proc \in Proc : IsInCycle(proc, Dependency)}) {
             Abort(victim, "deadlock");
           };
         }
         or
         { Abort(self, "voluntary")
         }
       }
    }
  }
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES transact, state, history, store, ts, writeSet, startTS, commitTS, 
          SIREAD, WRITE, pc

(* define statement *)
Hd[proc \in Proc] == Head(transact[proc])
Tl[proc \in Proc] == Tail(transact[proc])

TypeOK ==
  /\ \A idx \in DOMAIN history
     : LET e == history[idx]
       IN  /\ e.proc \in Proc
           /\ \/ /\ e.op.f \in {Read, Write}
                 /\ e.op.obj \in Object
                 /\ e.val \in Value
              \/ e.op.f \in {Commit, Abort}
  /\ \A proc \in Proc
     : state[proc] \in State
  /\ \A obj \in Object
     : \A t \in store[obj] : t \in Version
  /\ \A proc \in Proc
     : \A obj \in Object
       : Cardinality(writeSet[proc][obj]) \in {0, 1}

LockOK ==
  /\ \A obj \in Object
     : LET active == {proc \in WRITE[obj] : state[proc] = Running}
       IN  Cardinality(active) \in {0,1}







DependsOn[__state    \in [Proc -> State],
          __commitTS \in [Proc -> Nat],
          proc \in Proc] ==
  IF __state[proc] # Commit
  THEN {}
  ELSE LET from == proc
           conflict(X, Y) == UNION {Y[obj] : obj \in {obj \in Object : proc \in X[obj]}}
       IN LET wr == {r \in conflict(WRITE, SIREAD) : __commitTS[from] <= startTS[r] /\ __state[r] = Commit}
              ww == {w \in conflict(WRITE, WRITE)  : __commitTS[from] <= startTS[w] /\ __state[w] = Commit}
              rw == {w \in conflict(SIREAD, WRITE) : startTS[from] < __commitTS[w]  /\ __state[w] = Commit}
          IN  UNION {{<<from, to>> : to \in (wr \ {from})},
                     {<<from, to>> : to \in (ww \ {from})},
                     {<<from, to>> : to \in (rw \ {from})}}

__ConflictSerializable[__state    \in [Proc -> State],
                       __commitTS \in [Proc -> Nat]] ==
  LET edge == UNION {DependsOn[__state, __commitTS, proc] : proc \in Proc}
      node == UNION {{from, to} : <<from, to>> \in edge}
  IN ~IsCycle([edge |-> edge, node |-> node])

ConflictSerializable == __ConflictSerializable[state, commitTS]






RECURSIVE viewEq(_, _)
viewEq(s, hist) ==
  IF hist = <<>>
  THEN  \A obj \in Object
        : \E i \in store[obj]
          : \A j \in store[obj]
            : i.ver >= j.ver /\ s[obj].proc = i.val.proc
  ELSE LET hd == Head(hist)
       IN  CASE hd.op.f = Read
                -> s[hd.op.obj] = hd.val /\ viewEq(s, Tail(hist))
             [] hd.op.f = Write
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



Invariants ==
  /\ TypeOK
  /\ LockOK
  /\ ConflictSerializable
  /\ ViewSerializable





WaitingFor[proc \in Proc] ==
  IF state[proc] # "Running"
  THEN {}
  ELSE LET from == proc
           hd == Head(transact[from])
           edges(TO) == {<<from, to>> : to \in TO}
       IN  CASE hd.f = "Write"
                  -> edges(WRITE[hd.obj] \ {from})
             [] OTHER -> {}

Dependency ==
  LET edge == UNION {WaitingFor[proc] : proc \in Proc}
      node == UNION {{from, to} : <<from, to>> \in edge}
  IN  [edge |-> edge, node |-> node]

Deadlock == IsCycle(Dependency)





EventuallyAllCommitOrAbort ==
  <>[](\A proc \in Proc : state[proc] \in {Commit, Abort})





EventuallySomeCommit ==
  <>[](\E proc \in Proc : state[proc] = Commit)

Properties ==
  /\ EventuallyAllCommitOrAbort

VARIABLE temp

vars == << transact, state, history, store, ts, writeSet, startTS, commitTS, 
           SIREAD, WRITE, pc, temp >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ transact \in [Proc -> Transact]
        /\ state = [proc \in Proc |-> Starting]
        /\ history = <<>>
        /\ store = InitValues
        /\ ts = 0
        /\ writeSet = [proc \in Proc |-> [obj \in Object |-> {}]]
        /\ startTS = [proc \in Proc |-> 0]
        /\ commitTS = [proc \in Proc |-> 0]
        /\ SIREAD = [obj \in Object |-> {}]
        /\ WRITE = [obj \in Object |-> {}]
        (* Process proc *)
        /\ temp = [self \in Proc |-> [proc |-> 0]]
        /\ pc = [self \in ProcSet |-> "L10"]

L10(self) == /\ pc[self] = "L10"
             /\ startTS' = [startTS EXCEPT ![self] = ts]
             /\ state' = [state EXCEPT ![self] = Running]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << transact, history, store, ts, writeSet, commitTS, 
                             SIREAD, WRITE, temp >>

L20(self) == /\ pc[self] = "L20"
             /\ IF state[self] = Running
                   THEN /\ \/ /\ Hd[self].f = Read
                              /\ IF SERIALIZE
                                    THEN /\ SIREAD' = [SIREAD EXCEPT ![(Hd[self].obj)] = SIREAD[(Hd[self].obj)] \cup {self}]
                                    ELSE /\ SIREAD' = [SIREAD EXCEPT ![(Hd[self].obj)] = SIREAD[(Hd[self].obj)] \cup {self}]
                              /\ pc' = [pc EXCEPT ![self] = "L30"]
                              /\ UNCHANGED <<transact, state, history, store, ts, commitTS, WRITE>>
                           \/ /\ /\ Hd[self].f = Write
                                 /\ LET active == {proc \in WRITE[Hd[self].obj]
                                                   : state[proc] = Running}
                                    IN  active \in {{}, {self}}
                              /\ WRITE' = [WRITE EXCEPT ![(Hd[self].obj)] = WRITE[(Hd[self].obj)] \cup {self}]
                              /\ pc' = [pc EXCEPT ![self] = "L40"]
                              /\ UNCHANGED <<transact, state, history, store, ts, commitTS, SIREAD>>
                           \/ /\ Hd[self].f = Commit
                              /\ IF /\ SERIALIZE
                                    /\ LET __state    == [state    EXCEPT ![self] = Commit]
                                           __commitTS == [commitTS EXCEPT ![self] = ts + 1]
                                       IN  ~__ConflictSerializable[__state, __commitTS]
                                    THEN /\ state' = [state EXCEPT ![self] = Abort]
                                         /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort])])
                                         /\ UNCHANGED << transact, store, ts, 
                                                         commitTS >>
                                    ELSE /\ ts' = ts + 1
                                         /\ commitTS' = [commitTS EXCEPT ![self] = ts']
                                         /\ store' =        [obj \in Object |->
                                                     IF writeSet[self][obj] # {}
                                                     THEN store[obj] \cup {[ver |-> commitTS'[self],
                                                                            val |-> ANY(writeSet[self][obj])]}
                                                     ELSE store[obj]]
                                         /\ state' = [state EXCEPT ![self] = Commit]
                                         /\ history' = Append(history, [proc |-> self, op |-> Hd[self]])
                                         /\ transact' = [transact EXCEPT ![self] = Tl[self]]
                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                              /\ UNCHANGED <<SIREAD, WRITE>>
                           \/ /\ Deadlock
                              /\ \E victim \in {proc \in Proc : IsInCycle(proc, Dependency)}:
                                   /\ state' = [state EXCEPT ![victim] = Abort]
                                   /\ history' = Append(history, [proc |-> victim, op |-> ([f |-> Abort])])
                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                              /\ UNCHANGED <<transact, store, ts, commitTS, SIREAD, WRITE>>
                           \/ /\ state' = [state EXCEPT ![self] = Abort]
                              /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort])])
                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                              /\ UNCHANGED <<transact, store, ts, commitTS, SIREAD, WRITE>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << transact, state, history, store, ts, 
                                        commitTS, SIREAD, WRITE >>
             /\ UNCHANGED << writeSet, startTS, temp >>

L30(self) == /\ pc[self] = "L30"
             /\ temp' = [temp EXCEPT ![self] = IF writeSet[self][Hd[self].obj] # {}
                                               THEN ANY(writeSet[self][Hd[self].obj])
                                               ELSE LET h == {i \in store[Hd[self].obj]
                                                              : i.ver <= startTS[self]}
                                                        s == CHOOSE i \in h : \A j \in h : i.ver >= j.ver
                                                    IN  s.val]
             /\ history' = Append(history, [proc |-> self, op |-> Hd[self], val |-> temp'[self]])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << state, store, ts, writeSet, startTS, commitTS, 
                             SIREAD, WRITE >>

L40(self) == /\ pc[self] = "L40"
             /\ IF {i \in store[Hd[self].obj] : i.ver > startTS[self]} # {}
                   THEN /\ state' = [state EXCEPT ![self] = Abort]
                        /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort])])
                        /\ pc' = [pc EXCEPT ![self] = "L20"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L43"]
                        /\ UNCHANGED << state, history >>
             /\ UNCHANGED << transact, store, ts, writeSet, startTS, commitTS, 
                             SIREAD, WRITE, temp >>

L43(self) == /\ pc[self] = "L43"
             /\ writeSet' = [writeSet EXCEPT ![self][Hd[self].obj] = {[proc |-> self]}]
             /\ history' = Append(history, [proc |-> self, op |-> Hd[self], val |-> ([proc |-> self])])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << state, store, ts, startTS, commitTS, SIREAD, 
                             WRITE, temp >>

proc(self) == L10(self) \/ L20(self) \/ L30(self) \/ L40(self) \/ L43(self)

Next == (\E self \in Proc: proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sat Mar 17 18:54:52 JST 2018 by takayuki
\* Created Wed Mar 07 16:46:38 JST 2018 by takayuki
