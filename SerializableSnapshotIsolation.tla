------------------- MODULE SerializableSnapshotIsolation -------------------
EXTENDS FiniteSets, Naturals, Sequences, TLC

(***************************************************************************)
(* This module specifies Serializable Snapshot Isolation (SSI) as well as  *)
(* Snapshot Isolation (SI).  You can use a boolean constant SERIALIZE to   *)
(* enable and disable the extention to SI so as to accept only             *)
(* serializable history.                                                   *)
(***************************************************************************)
CONSTANTS Proc, Object, SERIALIZE

(***************************************************************************)
(* Transaction is a set of all possible transactions                       *)
(***************************************************************************)
Transact ==
  LET Op == [f : {"Read", "Write"}, obj : Object]
      seq(S) == UNION {[1..n -> S] : n \in Nat}
  IN  {Append(op, [f |-> "Commit"]) : op \in seq(Op)}

ANY(S) == CHOOSE s \in S : TRUE

(***************************************************************************
--fair algorithm SerializableSnapshotIsolation {
  variable
    transact \in [Proc -> Transact];
    state = [proc \in Proc |-> "Init"];
    history = <<>>;
    store = [obj \in Object |-> {[ver |-> 0, val |-> 0]}];
    ts = 0;
    startTS = [proc \in Proc |-> 0];
    commitTS = [proc \in Proc |-> 0];
    inConflict = [proc \in Proc |-> FALSE];
    outConflict = [proc \in Proc |-> FALSE];
    SIREAD = [obj \in Object |-> {}];
    WRITE = [obj \in Object |-> {}]
  define {
    Hd[proc \in Proc] == Head(transact[proc])
    Tl[proc \in Proc] == Tail(transact[proc])

    (***********************************************************************)
    (* Serializable asserts that, if some of transactions successfully     *)
    (* commit, the history of the committed transactions is serializable.  *)
    (***********************************************************************)
    RECURSIVE consistent(_, _)
    consistent(s, hist) ==
      IF hist = <<>>
      THEN TRUE
      ELSE LET hd == Head(hist)
               tl == Tail(hist)
           IN  CASE hd.op.f = "Read"
                    -> s[hd.op.obj] = hd.val /\ consistent(s, tl)
                 [] hd.op.f = "Write"
                    -> consistent([s EXCEPT ![hd.op.obj] = hd.val], tl)
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
              : LET serial == concat(perm, 1, Cardinality(Tx), <<>>)
                IN  consistent([obj \in Object |-> 0], serial)
\*                    /\ \/ Cardinality(Tx) < 2
\*                       \/ PrintT(<<history, serial>>)

    (***********************************************************************)
    (* Deadlock asserts that a process is stopping in a deadlock           *)
    (***********************************************************************)
    Waiting[self \in Proc, blocking \in SUBSET Proc] ==
      IF self \in blocking \/ state[self] # "Running"
      THEN {}
      ELSE LET grandChildren(p) == Waiting[p, blocking \cup {self}]
           IN LET dependsOn(children) ==
                    children \cup UNION {grandChildren(p) : p \in children}
                  hd == Head(transact[self])
              IN  CASE hd.f = "Write"
                       -> dependsOn(WRITE[hd.obj] \ {self})
                    [] OTHER -> {}
    Blocking[self \in Proc] == Waiting[self, {}]
    Deadlock[self \in Proc] == self \in Blocking[self]

    (***********************************************************************)
    (* A temporal property asserts that all transactions eventually commit *)
    (* or abort without deadlock.                                          *)
    (***********************************************************************)
    EventuallyAllCommitOrAbort ==
      <>[](\A proc \in Proc : state[proc] \in {"Commit", "Abort"})

    (***********************************************************************)
    (* A temporal property asserts that some transactions eventually       *)
    (* commit.                                                             *)
    (***********************************************************************)
    EventuallySomeCommit ==
      <>[](\E proc \in Proc : state[proc] = "Commit")

    Properties ==
      /\ EventuallyAllCommitOrAbort
      /\ EventuallySomeCommit
  }
  macro AppendHistory(val) {
    history := Append(history,
      [proc |-> self, op |-> Hd[self], val |-> val]);
    transact[self] := Tl[self];
  }
  macro Lock(lock, obj) {
    lock[obj] := lock[obj] \cup {self}
  }
  macro Unlock(lock, proc) {
    lock := [obj \in Object |-> lock[obj] \ {proc}]
  }
  macro Abort(proc) {
    state[proc] := "Abort";
    Unlock(WRITE, proc);
  }
  process (proc \in Proc)
    variables
      writeSet = [obj \in Object |-> {}];
      reg = 0;
    {L10:
     startTS[self] := ts;
     state[self] := "Running";
     L20:
      while (state[self] = "Running")
       { either
         { await Hd[self].f = "Read";
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
           reg :=
             IF writeSet[Hd[self].obj] # {}
             THEN ANY(writeSet[Hd[self].obj])
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
                      /\ state[v.proc] = "Commit"
                      /\ outConflict[v.proc]} # {})
               { Abort(self);
                 goto L20;
               };
              L31:
               inConflict := [proc \in Proc |->
                   \/ \E v \in {v \in store[Hd[self].obj]
                                : /\ v.ver > startTS[self]
                                  /\ state[v.proc] = "Commit"
                                  /\ outConflict[v.proc]}
                      : proc = v.proc
                   \/ inConflict[proc]];
               outConflict[self] := TRUE;
             }
           };
         L32:
           AppendHistory(reg);
         }
         or
         { await /\ Hd[self].f = "Write"
                 /\ WRITE[Hd[self].obj] \in {{}, {self}};
           Lock(WRITE, Hd[self].obj);
          L40:
           if (SERIALIZE)
           { if ({owner \in SIREAD[Hd[self].obj]
                  : \/ state[owner] = "Running"
                    \/ /\ state[owner] = "Commit"
                       /\ commitTS[owner] > startTS[self]} # {})
             { if ({owner \in SIREAD[Hd[self].obj]
                  : /\ state[owner] = "Commit"
                    /\ inConflict[owner]} # {})
               { Abort(self);
                 goto L20;
               };
              L41:
               outConflict := [proc \in Proc
                 |-> \/ proc \in {owner \in SIREAD[Hd[self].obj]
                                  : \/ state[owner] = "Running"
                                    \/ /\ state[owner] = "Commit"
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
           { Abort(self);
             goto L20;
           };
          L43:
           (****************************************************************)
           (* Write has to write a unique value for serializability tests  *)
           (* to identify each committed write.                            *)
           (****************************************************************)
           writeSet[Hd[self].obj] := {Len(history) + 1};
           AppendHistory(ANY(writeSet[Hd[self].obj]));
         }
         or
         { await Hd[self].f = "Commit";
           if (SERIALIZE)
           { if (inConflict[self] /\ outConflict[self])
              { Abort(self);
                goto L20;
              }
           };
          L50:
           ts := ts + 1;
           commitTS[self] := ts;
           store := [obj \in Object |->
             IF writeSet[obj] # {}
             THEN store[obj] \cup {[ver |-> commitTS[self],
                                    val |-> ANY(writeSet[obj]),
                                    proc |-> self]}
             ELSE store[obj]];
           state[self] := "Commit";
           AppendHistory(commitTS[self]);
           Unlock(WRITE, self);
         }
         or
         { await Deadlock[self];
           (* abort a single transaction in deadlock randomly *)
           with (victim \in Blocking[self]) {
             Abort(victim);
           };
           goto L20;
         }
       }
    }
  }
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES transact, state, history, store, ts, startTS, commitTS, inConflict, 
          outConflict, SIREAD, WRITE, pc

(* define statement *)
Hd[proc \in Proc] == Head(transact[proc])
Tl[proc \in Proc] == Tail(transact[proc])





RECURSIVE consistent(_, _)
consistent(s, hist) ==
  IF hist = <<>>
  THEN TRUE
  ELSE LET hd == Head(hist)
           tl == Tail(hist)
       IN  CASE hd.op.f = "Read"
                -> s[hd.op.obj] = hd.val /\ consistent(s, tl)
             [] hd.op.f = "Write"
                -> consistent([s EXCEPT ![hd.op.obj] = hd.val], tl)
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
          : LET serial == concat(perm, 1, Cardinality(Tx), <<>>)
            IN  consistent([obj \in Object |-> 0], serial)






Waiting[self \in Proc, blocking \in SUBSET Proc] ==
  IF self \in blocking \/ state[self] # "Running"
  THEN {}
  ELSE LET grandChildren(p) == Waiting[p, blocking \cup {self}]
       IN LET dependsOn(children) ==
                children \cup UNION {grandChildren(p) : p \in children}
              hd == Head(transact[self])
          IN  CASE hd.f = "Write"
                   -> dependsOn(WRITE[hd.obj] \ {self})
                [] OTHER -> {}
Blocking[self \in Proc] == Waiting[self, {}]
Deadlock[self \in Proc] == self \in Blocking[self]





EventuallyAllCommitOrAbort ==
  <>[](\A proc \in Proc : state[proc] \in {"Commit", "Abort"})





EventuallySomeCommit ==
  <>[](\E proc \in Proc : state[proc] = "Commit")

Properties ==
  /\ EventuallyAllCommitOrAbort
  /\ EventuallySomeCommit

VARIABLES writeSet, reg

vars == << transact, state, history, store, ts, startTS, commitTS, inConflict, 
           outConflict, SIREAD, WRITE, pc, writeSet, reg >>

ProcSet == (Proc)

Init == (* Global variables *)
        /\ transact \in [Proc -> Transact]
        /\ state = [proc \in Proc |-> "Init"]
        /\ history = <<>>
        /\ store = [obj \in Object |-> {[ver |-> 0, val |-> 0]}]
        /\ ts = 0
        /\ startTS = [proc \in Proc |-> 0]
        /\ commitTS = [proc \in Proc |-> 0]
        /\ inConflict = [proc \in Proc |-> FALSE]
        /\ outConflict = [proc \in Proc |-> FALSE]
        /\ SIREAD = [obj \in Object |-> {}]
        /\ WRITE = [obj \in Object |-> {}]
        (* Process proc *)
        /\ writeSet = [self \in Proc |-> [obj \in Object |-> {}]]
        /\ reg = [self \in Proc |-> 0]
        /\ pc = [self \in ProcSet |-> "L10"]

L10(self) == /\ pc[self] = "L10"
             /\ startTS' = [startTS EXCEPT ![self] = ts]
             /\ state' = [state EXCEPT ![self] = "Running"]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << transact, history, store, ts, commitTS, 
                             inConflict, outConflict, SIREAD, WRITE, writeSet, 
                             reg >>

L20(self) == /\ pc[self] = "L20"
             /\ IF state[self] = "Running"
                   THEN /\ \/ /\ Hd[self].f = "Read"
                              /\ IF SERIALIZE
                                    THEN /\ SIREAD' = [SIREAD EXCEPT ![Hd[self].obj] = SIREAD[Hd[self].obj] \cup {self}]
                                         /\ inConflict' = [proc \in Proc
                                                           |-> \/ proc \in WRITE[Hd[self].obj]
                                                               \/ inConflict[proc]]
                                         /\ outConflict' = [outConflict EXCEPT ![self] = TRUE]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << inConflict, 
                                                         outConflict, SIREAD >>
                              /\ reg' = [reg EXCEPT ![self] = IF writeSet[self][Hd[self].obj] # {}
                                                              THEN ANY(writeSet[self][Hd[self].obj])
                                                              ELSE LET h == {i \in store[Hd[self].obj]
                                                                             : i.ver <= startTS[self]}
                                                                       s == CHOOSE i \in h : \A j \in h : i.ver >= j.ver
                                                                   IN  s.val]
                              /\ pc' = [pc EXCEPT ![self] = "L30"]
                              /\ UNCHANGED <<state, WRITE>>
                           \/ /\ /\ Hd[self].f = "Write"
                                 /\ WRITE[Hd[self].obj] \in {{}, {self}}
                              /\ WRITE' = [WRITE EXCEPT ![(Hd[self].obj)] = WRITE[(Hd[self].obj)] \cup {self}]
                              /\ pc' = [pc EXCEPT ![self] = "L40"]
                              /\ UNCHANGED <<state, inConflict, outConflict, SIREAD, reg>>
                           \/ /\ Hd[self].f = "Commit"
                              /\ IF SERIALIZE
                                    THEN /\ IF inConflict[self] /\ outConflict[self]
                                               THEN /\ state' = [state EXCEPT ![self] = "Abort"]
                                                    /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                                                    /\ pc' = [pc EXCEPT ![self] = "L20"]
                                               ELSE /\ pc' = [pc EXCEPT ![self] = "L50"]
                                                    /\ UNCHANGED << state, 
                                                                    WRITE >>
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "L50"]
                                         /\ UNCHANGED << state, WRITE >>
                              /\ UNCHANGED <<inConflict, outConflict, SIREAD, reg>>
                           \/ /\ Deadlock[self]
                              /\ \E victim \in Blocking[self]:
                                   /\ state' = [state EXCEPT ![victim] = "Abort"]
                                   /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {victim}]
                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                              /\ UNCHANGED <<inConflict, outConflict, SIREAD, reg>>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << state, inConflict, outConflict, SIREAD, 
                                        WRITE, reg >>
             /\ UNCHANGED << transact, history, store, ts, startTS, commitTS, 
                             writeSet >>

L30(self) == /\ pc[self] = "L30"
             /\ IF SERIALIZE
                   THEN /\ IF {v \in store[Hd[self].obj]
                               : v.ver > startTS[self]} # {}
                              THEN /\ IF {v \in store[Hd[self].obj]
                                          : /\ v.ver > startTS[self]
                                            /\ state[v.proc] = "Commit"
                                            /\ outConflict[v.proc]} # {}
                                         THEN /\ state' = [state EXCEPT ![self] = "Abort"]
                                              /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "L31"]
                                              /\ UNCHANGED << state, WRITE >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "L32"]
                                   /\ UNCHANGED << state, WRITE >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L32"]
                        /\ UNCHANGED << state, WRITE >>
             /\ UNCHANGED << transact, history, store, ts, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, writeSet, reg >>

L31(self) == /\ pc[self] = "L31"
             /\ inConflict' =           [proc \in Proc |->
                              \/ \E v \in {v \in store[Hd[self].obj]
                                           : /\ v.ver > startTS[self]
                                             /\ state[v.proc] = "Commit"
                                             /\ outConflict[v.proc]}
                                 : proc = v.proc
                              \/ inConflict[proc]]
             /\ outConflict' = [outConflict EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "L32"]
             /\ UNCHANGED << transact, state, history, store, ts, startTS, 
                             commitTS, SIREAD, WRITE, writeSet, reg >>

L32(self) == /\ pc[self] = "L32"
             /\ history' =          Append(history,
                           [proc |-> self, op |-> Hd[self], val |-> reg[self]])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << state, store, ts, startTS, commitTS, inConflict, 
                             outConflict, SIREAD, WRITE, writeSet, reg >>

L40(self) == /\ pc[self] = "L40"
             /\ IF SERIALIZE
                   THEN /\ IF {owner \in SIREAD[Hd[self].obj]
                               : \/ state[owner] = "Running"
                                 \/ /\ state[owner] = "Commit"
                                    /\ commitTS[owner] > startTS[self]} # {}
                              THEN /\ IF  {owner \in SIREAD[Hd[self].obj]
                                         : /\ state[owner] = "Commit"
                                           /\ inConflict[owner]} # {}
                                         THEN /\ state' = [state EXCEPT ![self] = "Abort"]
                                              /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                                              /\ pc' = [pc EXCEPT ![self] = "L20"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "L41"]
                                              /\ UNCHANGED << state, WRITE >>
                              ELSE /\ pc' = [pc EXCEPT ![self] = "L42"]
                                   /\ UNCHANGED << state, WRITE >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L42"]
                        /\ UNCHANGED << state, WRITE >>
             /\ UNCHANGED << transact, history, store, ts, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, writeSet, reg >>

L41(self) == /\ pc[self] = "L41"
             /\ outConflict' =              [proc \in Proc
                               |-> \/ proc \in {owner \in SIREAD[Hd[self].obj]
                                                : \/ state[owner] = "Running"
                                                  \/ /\ state[owner] = "Commit"
                                                     /\ commitTS[owner] > startTS[self]}
                                   \/ outConflict[proc]]
             /\ inConflict' = [inConflict EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "L42"]
             /\ UNCHANGED << transact, state, history, store, ts, startTS, 
                             commitTS, SIREAD, WRITE, writeSet, reg >>

L42(self) == /\ pc[self] = "L42"
             /\ IF {i \in store[Hd[self].obj] : i.ver > startTS[self]} # {}
                   THEN /\ state' = [state EXCEPT ![self] = "Abort"]
                        /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
                        /\ pc' = [pc EXCEPT ![self] = "L20"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "L43"]
                        /\ UNCHANGED << state, WRITE >>
             /\ UNCHANGED << transact, history, store, ts, startTS, commitTS, 
                             inConflict, outConflict, SIREAD, writeSet, reg >>

L43(self) == /\ pc[self] = "L43"
             /\ writeSet' = [writeSet EXCEPT ![self][Hd[self].obj] = {Len(history) + 1}]
             /\ history' =          Append(history,
                           [proc |-> self, op |-> Hd[self], val |-> (ANY(writeSet'[self][Hd[self].obj]))])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << state, store, ts, startTS, commitTS, inConflict, 
                             outConflict, SIREAD, WRITE, reg >>

L50(self) == /\ pc[self] = "L50"
             /\ ts' = ts + 1
             /\ commitTS' = [commitTS EXCEPT ![self] = ts']
             /\ store' =        [obj \in Object |->
                         IF writeSet[self][obj] # {}
                         THEN store[obj] \cup {[ver |-> commitTS'[self],
                                                val |-> ANY(writeSet[self][obj]),
                                                proc |-> self]}
                         ELSE store[obj]]
             /\ state' = [state EXCEPT ![self] = "Commit"]
             /\ history' =          Append(history,
                           [proc |-> self, op |-> Hd[self], val |-> (commitTS'[self])])
             /\ transact' = [transact EXCEPT ![self] = Tl[self]]
             /\ WRITE' = [obj \in Object |-> WRITE[obj] \ {self}]
             /\ pc' = [pc EXCEPT ![self] = "L20"]
             /\ UNCHANGED << startTS, inConflict, outConflict, SIREAD, 
                             writeSet, reg >>

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
\* Last modified Sat Feb 24 12:55:13 JST 2018 by takayuki
\* Created Wed Feb 21 14:32:17 JST 2018 by takayuki
