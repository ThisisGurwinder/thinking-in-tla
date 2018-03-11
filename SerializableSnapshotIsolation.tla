------------------- MODULE SerializableSnapshotIsolation -------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

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
RANGE(f) == {f[x] : x \in DOMAIN f}

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
--fair algorithm SerializableSnapshotIsolation {
  variable
    transact \in [Proc -> Transact];
    state = [proc \in Proc |-> Starting];
    history = <<>>;
    store = InitValues;
    ts = 0;
    writeSet = [proc \in Proc |-> [obj \in Object |-> {}]];
    startTS = [proc \in Proc |-> 0];
    commitTS = [proc \in Proc |-> 0];
    inConflict = [proc \in Proc |-> FALSE];
    outConflict = [proc \in Proc |-> FALSE];
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
         : Cardinality(WRITE[obj]) \in {0,1}

    (***********************************************************************)
    (* ConflictSerializable tests if a multiversion serialization graph    *)
    (* has no cycle, and asserts that the history of the committed         *)
    (* transactions is conflict-serializable.                              *)
    (***********************************************************************)
    DependsOn[visiting \in Proc, visited \in SUBSET Proc] ==
      IF visiting \in visited
      THEN {}
      ELSE LET dependsOn(children) ==
                 children \cup UNION {DependsOn[proc, visited \cup {visiting}] : proc \in children}
               conflict(X, Y) ==
                 LET C  == RANGE(SelectSeq(history, LAMBDA x: state[x.proc] = Commit))
                     CX == {c \in C : c.proc = visiting /\ c.op.f = X}
                     CXOBJ == {cx.op.obj : cx \in CX}
                     CY == {c \in C : c.op.f = Y /\ c.op.obj \in CXOBJ}
                 IN  {cy.proc : cy \in CY}
           IN LET wr == {r \in conflict(Write, Read) : commitTS[visiting] <= startTS[r] /\ state[r] = Commit}
                  ww == {w \in conflict(Write, Write): commitTS[visiting] <= startTS[w] /\ state[w] = Commit}
                  rw == {w \in conflict(Read,  Write): startTS[visiting]  < commitTS[w] /\ state[w] = Commit}
              IN  UNION {
                    dependsOn(wr \ {visiting}),
                    dependsOn(ww \ {visiting}),
                    dependsOn(rw \ {visiting})}

    ConflictSerializable ==
      \A proc \in {proc \in Proc : state[proc] = Commit}
      : proc \notin DependsOn[proc, {}]

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

    ViewSerializable ==
      LET Tx == {SelectSeq(history, LAMBDA x: x.proc = proc) : proc
                 \in {proc \in Proc : state[proc] = Commit}}
          perms == {f \in [1..Cardinality(Tx) -> Tx]
                    : \A tx \in Tx
                      : \E idx \in 1..Cardinality(Tx) : f[idx] = tx}
       IN LET RECURSIVE concat(_, _, _, _)
              concat(f, n, size, acc) ==
                IF n > size THEN acc ELSE concat(f, n+1, size, acc \o f[n])
          IN  \E perm \in perms
              : viewEq([obj \in Object |-> [proc |-> 0]],
                       concat(perm, 1, Cardinality(Tx), <<>>))
\*            /\ \/ Cardinality(Tx) < 2
\*               \/ PrintT(<<history, concat(perm, 1, Cardinality(Tx), <<>>)>>)

    Invariants ==
      /\ TypeOK
      /\ LockOK
      /\ ConflictSerializable
      /\ ViewSerializable

    (***********************************************************************)
    (* Deadlock asserts that a process is stopping in a deadlock           *)
    (***********************************************************************)
    WaitingFor[visiting \in Proc, visited \in SUBSET Proc] ==
      IF visiting \in visited \/ state[visiting] # Running
      THEN {}
      ELSE LET dependsOn(children) ==
                 children \cup UNION {WaitingFor[proc, visited \cup {visiting}]
                                      : proc \in children}
               hd == Head(transact[visiting])
           IN CASE hd.f = Write
                     -> dependsOn(WRITE[hd.obj] \ {visiting})
                [] OTHER -> {}

    Deadlock[self \in Proc] == self \in WaitingFor[self, {}]

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
  macro Unlock(lock, proc) {
    lock := [obj \in Object |-> lock[obj] \ {proc}]
  }
  macro Abort(proc, reason) {
    state[proc] := Abort;
    appendHistory(proc, [f |-> Abort, reason |-> reason]);
    Unlock(WRITE, proc);
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
           { SIREAD[Hd[self].obj] := SIREAD[Hd[self].obj] \cup {self};
             inConflict := [proc \in Proc
                            |-> \/ proc \in WRITE[Hd[self].obj]
                                \/ inConflict[proc]];
             outConflict[self] := TRUE;
           };
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
         L30:
           if (SERIALIZE)
           { if ({v \in store[Hd[self].obj]
                  : v.ver > startTS[self]} # {})
             { if ({v \in store[Hd[self].obj]
                    : /\ v.ver > startTS[self]
                      /\ state[v.val.proc] = Commit
                      /\ outConflict[v.val.proc]} # {})
               { Abort(self, "dangerous structure");
                 goto L20;
               };
              L31:
               inConflict := [proc \in Proc |->
                   \/ \E v \in {v \in store[Hd[self].obj]
                                : /\ v.ver > startTS[self]
                                  /\ state[v.val.proc] = Commit
                                  /\ outConflict[v.val.proc]}
                      : proc = v.val.proc
                   \/ inConflict[proc]];
               outConflict[self] := TRUE;
             }
           };
         L32:
           recordHistoryValue(temp);
         }
         or
         { await /\ Hd[self].f = Write
                 /\ WRITE[Hd[self].obj] \in {{}, {self}};
           Lock(WRITE, Hd[self].obj);
          L40:
           if (SERIALIZE)
           { if ({owner \in SIREAD[Hd[self].obj]
                  : \/ state[owner] = Running
                    \/ /\ state[owner] = Commit
                       /\ commitTS[owner] > startTS[self]} # {})
             { if ({owner \in SIREAD[Hd[self].obj]
                  : /\ state[owner] = Commit
                    /\ inConflict[owner]} # {})
               { Abort(self, "dangerous structure");
                 goto L20;
               };
              L41:
               outConflict := [proc \in Proc
                 |-> \/ proc \in {owner \in SIREAD[Hd[self].obj]
                                  : \/ state[owner] = Running
                                    \/ /\ state[owner] = Commit
                                       /\ commitTS[owner] > startTS[self]}
                     \/ outConflict[proc]];
               inConflict[self] := TRUE;
             }
           };
          L42:
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
           if (SERIALIZE)
           { if (inConflict[self] /\ outConflict[self])
              { Abort(self, "dangerous structure");
                goto L20;
              }
           };
          L50:
           ts := ts + 1;
           commitTS[self] := ts;
           store := [obj \in Object |->
             IF writeSet[self][obj] # {}
             THEN store[obj] \cup {[ver |-> commitTS[self],
                                    val |-> ANY(writeSet[self][obj])]}
             ELSE store[obj]];
           state[self] := Commit;
           recordHistory();
           Unlock(WRITE, self);
         }
         or
         { await Deadlock[self];
           (* abort a single transaction in deadlock randomly *)
           with (victim \in WaitingFor[self, {}]) {
             Abort(victim, "deadlock");
           };
           goto L20;
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
          inConflict, outConflict, SIREAD, WRITE, pc

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
     : Cardinality(WRITE[obj]) \in {0,1}






DependsOn[visiting \in Proc, visited \in SUBSET Proc] ==
  IF visiting \in visited
  THEN {}
  ELSE LET dependsOn(children) ==
             children \cup UNION {DependsOn[proc, visited \cup {visiting}] : proc \in children}
           conflict(X, Y) ==
             LET C  == RANGE(SelectSeq(history, LAMBDA x: state[x.proc] = Commit))
                 CX == {c \in C : c.proc = visiting /\ c.op.f = X}
                 CXOBJ == {cx.op.obj : cx \in CX}
                 CY == {c \in C : c.op.f = Y /\ c.op.obj \in CXOBJ}
             IN  {cy.proc : cy \in CY}
       IN LET wr == {r \in conflict(Write, Read) : commitTS[visiting] <= startTS[r] /\ state[r] = Commit}
              ww == {w \in conflict(Write, Write): commitTS[visiting] <= startTS[w] /\ state[w] = Commit}
              rw == {w \in conflict(Read,  Write): startTS[visiting]  < commitTS[w] /\ state[w] = Commit}
          IN  UNION {
                dependsOn(wr \ {visiting}),
                dependsOn(ww \ {visiting}),
                dependsOn(rw \ {visiting})}

ConflictSerializable ==
  \A proc \in {proc \in Proc : state[proc] = Commit}
  : proc \notin DependsOn[proc, {}]






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

ViewSerializable ==
  LET Tx == {SelectSeq(history, LAMBDA x: x.proc = proc) : proc
             \in {proc \in Proc : state[proc] = Commit}}
      perms == {f \in [1..Cardinality(Tx) -> Tx]
                : \A tx \in Tx
                  : \E idx \in 1..Cardinality(Tx) : f[idx] = tx}
   IN LET RECURSIVE concat(_, _, _, _)
          concat(f, n, size, acc) ==
            IF n > size THEN acc ELSE concat(f, n+1, size, acc \o f[n])
      IN  \E perm \in perms
          : viewEq([obj \in Object |-> [proc |-> 0]],
                   concat(perm, 1, Cardinality(Tx), <<>>))



Invariants ==
  /\ TypeOK
  /\ LockOK
  /\ ConflictSerializable
  /\ ViewSerializable




WaitingFor[visiting \in Proc, visited \in SUBSET Proc] ==
  IF visiting \in visited \/ state[visiting] # Running
  THEN {}
  ELSE LET dependsOn(children) ==
             children \cup UNION {WaitingFor[proc, visited \cup {visiting}]
                                  : proc \in children}
           hd == Head(transact[visiting])
       IN CASE hd.f = Write
                 -> dependsOn(WRITE[hd.obj] \ {visiting})
            [] OTHER -> {}

Deadlock[self \in Proc] == self \in WaitingFor[self, {}]





EventuallyAllCommitOrAbort ==
  <>[](\A proc \in Proc : state[proc] \in {Commit, Abort})





EventuallySomeCommit ==
  <>[](\E proc \in Proc : state[proc] = Commit)

Properties ==
  /\ EventuallyAllCommitOrAbort

VARIABLE temp

vars == << transact, state, history, store, ts, writeSet, startTS, commitTS, 
           inConflict, outConflict, SIREAD, WRITE, pc, temp >>

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
        /\ inConflict = [proc \in Proc |-> FALSE]
        /\ outConflict = [proc \in Proc |-> FALSE]
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
                             inConflict, outConflict, SIREAD, WRITE, temp >>

L20(self) == /\ pc[self] = "L20"
             /\ IF state[self] = Running
                   THEN /\ \/ /\ Hd[self].f = Read
                              /\ IF SERIALIZE
                                    THEN /\ SIREAD' = [SIREAD EXCEPT ![Hd[self].obj] = SIREAD[Hd[self].obj] \cup {self}]
                                         /\ inConflict' = [proc \in Proc
                                                           |-> \/ proc \in WRITE[Hd[self].obj]
                                                               \/ inConflict[proc]]
                                         /\ outConflict' = [outConflict EXCEPT ![self] = TRUE]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << inConflict, 
                                                         outConflict, SIREAD >>
                              /\ temp' = [temp EXCEPT ![self] = IF writeSet[self][Hd[self].obj] # {}
                                                                THEN ANY(writeSet[self][Hd[self].obj])
                                                                ELSE LET h == {i \in store[Hd[self].obj]
                                                                               : i.ver <= startTS[self]}
                                                                         s == CHOOSE i \in h : \A j \in h : i.ver >= j.ver
                                                                     IN  s.val]
                              /\ pc' = [pc EXCEPT ![self] = "L30"]
                              /\ UNCHANGED <<state, history, WRITE>>
                           \/ /\ /\ Hd[self].f = Write
                                 /\ WRITE[Hd[self].obj] \in {{}, {self}}
                              /\ WRITE' = [WRITE EXCEPT ![(Hd[self].obj)] = WRITE[(Hd[self].obj)] \cup {self}]
                              /\ pc' = [pc EXCEPT ![self] = "L40"]
                              /\ UNCHANGED <<state, history, inConflict, outConflict, SIREAD, temp>>
                           \/ /\ Hd[self].f = Commit
                              /\ IF SERIALIZE
                                    THEN /\ IF inConflict[self] /\ outConflict[self]
                                               THEN /\ state' = [state EXCEPT ![self] = Abort]
                                                    /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort, reason |-> "dangerous structure"])])
                                                    /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                                                    /\ pc' = [pc EXCEPT ![self] = "L20"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "L50"]
                                                    /\ UNCHANGED << state, 
                                                                    history, 
                                                                    WRITE >>
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "L50"]
                                         /\ UNCHANGED << state, history, WRITE >>
                              /\ UNCHANGED <<inConflict, outConflict, SIREAD, temp>>
                           \/ /\ Deadlock[self]
                              /\ \E victim \in WaitingFor[self, {}]:
                                   /\ state' = [state EXCEPT ![victim] = Abort]
                                   /\ history' = Append(history, [proc |-> victim, op |-> ([f |-> Abort, reason |-> "deadlock"])])
                                   /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {victim}]
                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                              /\ UNCHANGED <<inConflict, outConflict, SIREAD, temp>>
                           \/ /\ state' = [state EXCEPT ![self] = Abort]
                              /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort, reason |-> "voluntary"])])
                              /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                              /\ UNCHANGED <<inConflict, outConflict, SIREAD, temp>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << state, history, inConflict, 
                                        outConflict, SIREAD, WRITE, temp >>
             /\ UNCHANGED << transact, store, ts, writeSet, startTS, commitTS >>

L30(self) == /\ pc[self] = "L30"
             /\ IF SERIALIZE
                   THEN /\ IF {v \in store[Hd[self].obj]
                               : v.ver > startTS[self]} # {}
                              THEN /\ IF {v \in store[Hd[self].obj]
                                          : /\ v.ver > startTS[self]
                                            /\ state[v.val.proc] = Commit
                                            /\ outConflict[v.val.proc]} # {}
                                         THEN /\ state' = [state EXCEPT ![self] = Abort]
                                              /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort, reason |-> "dangerous structure"])])
                                              /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "L31"]
                                              /\ UNCHANGED << state, history, 
                                                              WRITE >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "L32"]
                                   /\ UNCHANGED << state, history, WRITE >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L32"]
                        /\ UNCHANGED << state, history, WRITE >>
             /\ UNCHANGED << transact, store, ts, writeSet, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, temp >>

L31(self) == /\ pc[self] = "L31"
             /\ inConflict' =           [proc \in Proc |->
                              \/ \E v \in {v \in store[Hd[self].obj]
                                           : /\ v.ver > startTS[self]
                                             /\ state[v.val.proc] = Commit
                                             /\ outConflict[v.val.proc]}
                                 : proc = v.val.proc
                              \/ inConflict[proc]]
             /\ outConflict' = [outConflict EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "L32"]
             /\ UNCHANGED << transact, state, history, store, ts, writeSet, 
                             startTS, commitTS, SIREAD, WRITE, temp >>

L32(self) == /\ pc[self] = "L32"
             /\ history' = Append(history, [proc |-> self, op |-> Hd[self], val |-> temp[self]])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << state, store, ts, writeSet, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, WRITE, temp >>

L40(self) == /\ pc[self] = "L40"
             /\ IF SERIALIZE
                   THEN /\ IF {owner \in SIREAD[Hd[self].obj]
                               : \/ state[owner] = Running
                                 \/ /\ state[owner] = Commit
                                    /\ commitTS[owner] > startTS[self]} # {}
                              THEN /\ IF  {owner \in SIREAD[Hd[self].obj]
                                         : /\ state[owner] = Commit
                                           /\ inConflict[owner]} # {}
                                         THEN /\ state' = [state EXCEPT ![self] = Abort]
                                              /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort, reason |-> "dangerous structure"])])
                                              /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "L41"]
                                              /\ UNCHANGED << state, history, 
                                                              WRITE >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "L42"]
                                   /\ UNCHANGED << state, history, WRITE >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L42"]
                        /\ UNCHANGED << state, history, WRITE >>
             /\ UNCHANGED << transact, store, ts, writeSet, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, temp >>

L41(self) == /\ pc[self] = "L41"
             /\ outConflict' =              [proc \in Proc
                               |-> \/ proc \in {owner \in SIREAD[Hd[self].obj]
                                                : \/ state[owner] = Running
                                                  \/ /\ state[owner] = Commit
                                                     /\ commitTS[owner] > startTS[self]}
                                   \/ outConflict[proc]]
             /\ inConflict' = [inConflict EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "L42"]
             /\ UNCHANGED << transact, state, history, store, ts, writeSet, 
                             startTS, commitTS, SIREAD, WRITE, temp >>

L42(self) == /\ pc[self] = "L42"
             /\ IF {i \in store[Hd[self].obj] : i.ver > startTS[self]} # {}
                   THEN /\ state' = [state EXCEPT ![self] = Abort]
                        /\ history' = Append(history, [proc |-> self, op |-> ([f |-> Abort, reason |-> "First-Updater-Wins"])])
                        /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                        /\ pc' = [pc EXCEPT ![self] = "L20"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L43"]
                        /\ UNCHANGED << state, history, WRITE >>
             /\ UNCHANGED << transact, store, ts, writeSet, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, temp >>

L43(self) == /\ pc[self] = "L43"
             /\ writeSet' = [writeSet EXCEPT ![self][Hd[self].obj] = {[proc |-> self]}]
             /\ history' = Append(history, [proc |-> self, op |-> Hd[self], val |-> ([proc |-> self])])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << state, store, ts, startTS, commitTS, inConflict, 
                             outConflict, SIREAD, WRITE, temp >>

L50(self) == /\ pc[self] = "L50"
             /\ ts' = ts + 1
             /\ commitTS' = [commitTS EXCEPT ![self] = ts']
             /\ store' =        [obj \in Object |->
                         IF writeSet[self][obj] # {}
                         THEN store[obj] \cup {[ver |-> commitTS'[self],
                                                val |-> ANY(writeSet[self][obj])]}
                         ELSE store[obj]]
             /\ state' = [state EXCEPT ![self] = Commit]
             /\ history' = Append(history, [proc |-> self, op |-> Hd[self]])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << writeSet, startTS, inConflict, outConflict, 
                             SIREAD, temp >>

proc(self) == L10(self) \/ L20(self) \/ L30(self) \/ L31(self) \/ L32(self)
                 \/ L40(self) \/ L41(self) \/ L42(self) \/ L43(self)
                 \/ L50(self)

Next == (\E self \in Proc: proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Mar 11 16:17:47 JST 2018 by takayuki
\* Created Wed Feb 21 14:32:17 JST 2018 by takayuki
