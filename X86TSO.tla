------------------------------- MODULE X86TSO -------------------------------
(***************************************************************************)
(* An attempt that specifies the x86-TSO abstract memory model, which is   *)
(* an intuitive programmer's model to define Intel and AMD x86             *)
(* architecture.                                                           *)
(*                                                                         *)
(* x86-TSO: A Rigorous and Usable Programmer’s Model for x86               *)
(* Multiprocessors                                                         *)
(* https://www.cl.cam.ac.uk/~pes20/weakmemory/cacm.pdf                     *)
(*                                                                         *)
(* A Better x86 Memory Model: x86-TSO                                      *)
(* https://www.cl.cam.ac.uk/~pes20/weakmemory/x86tso-paper.tphols.pdf      *)
(*                                                                         *)
(***************************************************************************)
EXTENDS FiniteSets, Integers, Sequences, TLC

CONSTANTS Proc, Code, Reg, Addr, Value, InitReg, InitMem

First(s) == s[1]
Last(s) == s[Len(s)]

Map(Op(_), s) ==
  LET F[i \in 0..Len(s)] == IF i = 0 THEN <<>> ELSE Append(F[i-1], Op(s[i]))
  IN  F[Len(s)]

RANGE(f) == {f[x] : x \in DOMAIN f}
MAX(S) == CHOOSE s \in S : \A t \in S : s >= t

(***************************************************************************)
(* CTRL is an internal process to represent memory controller.             *)
(***************************************************************************)
CTRL == "ctrl"

(***************************************************************************)
(* Instr is a set of instructions visible to user.  Note that "0" and "1"  *)
(* are virtual registers that represent immediate values.                  *)
(***************************************************************************)
LOAD   == "LOAD"
STORE  == "STORE"

SFENCE == "SFENCE"
LFENCE == "LFENCE"
MFENCE == "MFENCE"

MOV    == "MOV"
CMP    == "CMP"
SUB    == "SUB"
JNZ    == "JNZ"
JNS    == "JNS"
JLE    == "JLE"
JMP    == "JMP"
NOP    == "NOP"

XCHG   == "XCHG"
DEC    == "DEC"
CMPXCHG == "CMPXCHG"

IP == 1..(MAX({Len(t) : t \in RANGE(Code)}) + 1)

Instr == UNION {
  [op : {LOAD, XCHG}, reg : Reg, addr : Addr],
  [op : {STORE}, addr : Addr, reg : ({"0", "1"} \cup Reg)],
  [op : {SFENCE, LFENCE, MFENCE, NOP}],
  [op : {MOV, CMP, SUB}, dst : Reg, src : ({"0", "1"} \cup Reg)],
  [op : {JNZ, JNS, JLE, JMP}, label: IP],
  [op : {DEC}, addr : Addr, reg : Reg],
  [op : {CMPXCHG}, addr : Addr, dst : Reg, src : ({"0", "1"} \cup Reg)]
}

(***************************************************************************)
(* LOCK and UNLOCK are internal events under x86-TSO.                      *)
(***************************************************************************)
LOCK   == "LOCK"
UNLOCK == "UNLOCK"

(***************************************************************************)
(* The following stack-based events are introduced to implement XCHG and   *)
(* CMPXCHG.                                                                *)
(***************************************************************************)
PUSH   == "push"
POP    == "pop"
EXCH   == "exch"
SC     == "store-conditional"

(***************************************************************************)
(* Event is a set of events executed under x86-TSO.                        *)
(***************************************************************************)
Event == UNION {
  [ip : IP, op : {LOAD}, reg : Reg, addr : Addr],
  [ip : IP, op : {STORE}, addr : Addr, reg : ({"0", "1"} \cup Reg)],
  [ip : IP, op : {SFENCE, LFENCE, MFENCE, NOP}],
  [ip : IP, op : {MOV, CMP, SUB}, dst : Reg, src :({"0", "1"} \cup Reg)],
  [ip : IP, op : {JNZ, JNS, JLE, JMP}, label: IP],
  [ip : IP, op : {LOCK, UNLOCK}],
  [ip : IP, op : {PUSH, POP}, reg : Reg],
  [ip : IP, op : {EXCH}],
  [ip : IP, op : {SC}, addr : Addr, src : Reg, dst : Reg]
}

Decode[ip \in IP, code \in Seq(Instr)] ==
  IF code = <<>>
  THEN <<>>
  ELSE LET hd == Head(code)
           tl == Tail(code)
    IN CASE hd.op = XCHG
         -> Map(LAMBDA x : [ip |-> ip] @@ x,
                <<[op |-> LOCK],
                  [op |-> PUSH, reg |-> hd.reg],
                  [op |-> LOAD, reg |-> hd.reg, addr |-> hd.addr],
                  [op |-> PUSH, reg |-> hd.reg],
                  [op |-> EXCH],
                  [op |-> POP, reg |-> hd.reg],
                  [op |-> STORE, addr |-> hd.addr, reg |-> hd.reg],
                  [op |-> POP, reg |-> hd.reg],
                  [op |-> UNLOCK]>>)
            \o Decode[ip + 1, tl]
       [] Head(code).op = DEC
         -> Map(LAMBDA x : [ip |-> ip] @@ x,
                <<[op |-> LOCK],
                  [op |-> LOAD, reg |-> hd.reg, addr |-> hd.addr],
                  [op |-> SUB, dst |-> hd.reg, src |-> "1"],
                  [op |-> STORE, addr |-> hd.addr, reg |-> hd.reg],
                  [op |-> UNLOCK]>>)
            \o Decode[ip + 1, tl]
       [] Head(code).op = CMPXCHG
         -> Map(LAMBDA x : [ip |-> ip] @@ x,
                <<[op |-> LOCK],
                  [op |-> PUSH, reg |-> hd.dst],
                  [op |-> LOAD, reg |-> hd.dst, addr |-> hd.addr],
                  [op |-> SC, addr |-> hd.addr, dst |-> hd.dst, src |-> hd.src],
                  [op |-> UNLOCK]>>)
            \o Decode[ip + 1, tl]
       [] OTHER
         -> <<[ip |-> ip] @@ hd>> \o Decode[ip + 1, tl]

ASSUME
  /\ ({CTRL} \cap Proc) = {}
  /\ Code \in [Proc -> Seq(Instr)]
  /\ Reg \subseteq {"r1", "r2", "r3", "r4", "r5", "r6"}
  /\ Addr \subseteq {"x", "y"}
  /\ Value \subseteq Int
  /\ InitReg \in [Reg -> Value]
  /\ InitMem \in [Addr -> Value]

(***************************************************************************
--algorithm X86TSO {
  variables
    reg = [proc \in Proc |-> InitReg];
    mem = InitMem;
    lock = {};
    writeBuffer = [proc \in Proc |-> <<>>]
  define {
    Blocked(p) == lock # {} /\ p \notin lock

    Pending(p, a) ==
      SelectSeq(writeBuffer[p], LAMBDA w: w.addr = a) # <<>>

    ReadFromWriteBuffer(p, r) ==
      Last(SelectSeq(writeBuffer[p], LAMBDA w: w.addr = r.addr)).value

    ReadFromRegister(p, r) ==
      CASE r = "0" -> 0
        [] r = "1" -> 1
        [] OTHER   -> reg[p][r]

    TypeOK ==
      /\ \A proc \in Proc :
           /\ reg[proc] \in [Reg -> Value]
           /\ writeBuffer[proc]
              \in Seq([addr : Addr, value : Value])
      /\  mem \in [Addr -> Value]

    LockOK ==
      /\ lock \in SUBSET Proc
      /\ Cardinality(lock) \in {0, 1}
  }
  macro WriteToWriteBuffer(p, a, v) {
    writeBuffer[p] := Append(writeBuffer[p], [addr |-> a, value |-> v]);
  }
  macro WriteToRegister(p, r, value) {
    reg := [reg EXCEPT ![p][r] = value];
  }
  macro Commit(proc, w) {
    mem := [mem EXCEPT ![w.addr] = w.value];
  }
  macro Step(proc) {
    code := Tail(code);
  }
  macro Jump(proc, j) {
    code := Decode[j.label, SubSeq(Code[proc], j.label, Len(Code[proc]))]; 
  }
  (*************************************************************************)
  (* Weak fairness is required to flush write buffers eventually.          *)
  (*************************************************************************)
  fair process (Controller = CTRL) {
   C10:
    while (TRUE) {
      with (proc \in {proc \in Proc : writeBuffer[proc] # <<>> /\ ~Blocked(proc)}) {
        Commit(proc, Head(writeBuffer[proc]));
        writeBuffer[proc] := Tail(writeBuffer[proc]);
      }
    }
  }
  (*************************************************************************)
  (* Strong fairness is required among processors.  Assume that two        *)
  (* processors, proc0 and proc1, are repeatedly trying acquiring a lock,  *)
  (* proc0 repeatedly acquires the lock successfully and releases it,      *)
  (* meanwhile proc1 keeps trying acquiring the lock but in vain.  This    *)
  (* livelock behavior is accepted in weak fairness, but not in strong     *)
  (* fairness.                                                             *)
  (*************************************************************************)
  fair+ process (Processor \in Proc)
    variable
      code = Decode[1, Code[self]];
      cf = FALSE;
      sf = FALSE;
      zf = FALSE;
      stack = <<>>;
  {P10:
    while (code # <<>>) {
      either {
        await /\ Head(code).op = STORE
              /\ ~Blocked(self);
        WriteToWriteBuffer(self, Head(code).addr, ReadFromRegister(self, Head(code).reg));
        Step(self);
      }
      or {
        await /\ Head(code).op = LOAD
              /\ ~Blocked(self)
              /\ Pending(self, Head(code).addr);
        WriteToRegister(self, Head(code).reg, ReadFromWriteBuffer(self, Head(code)));
        Step(self);
      }
      or {
        await /\ Head(code).op = LOAD
              /\ ~Blocked(self)
              /\ ~Pending(self, Head(code).addr);
        WriteToRegister(self, Head(code).reg, mem[Head(code).addr]);
        Step(self);
      }
      or {
        await /\ Head(code).op = LOCK
              /\ lock = {}
              /\ writeBuffer[self] = <<>>;
        lock := {self};
        Step(self);
      }
      or {
        await /\ Head(code).op = UNLOCK
              /\ lock = {self}
              /\ writeBuffer[self] = <<>>;
        lock := {};
        Step(self);
      }
      or {
        (*******************************************************************)
        (* x86-TSO treats SFENCE as no-op, although SDM Vol.  3A, 11.10    *)
        (* states, "(The processor) insures that the contents of the store *)
        (* buffer are always drained to memory in the following            *)
        (* situations: (Pentium III, and more recent processor families    *)
        (* only) When using an SFENCE instruction to order stores."        *)
        (*******************************************************************)
        await Head(code).op = LFENCE;
        Step(self);
      }
      or {
        (*******************************************************************)
        (* x86-TSO treats LFENCE as no-op.                                 *)
        (*******************************************************************)
        await Head(code).op = LFENCE;
        code := Tail(code);
      }
      or {
        await /\ Head(code).op = MFENCE
              /\ writeBuffer[self] = <<>>;
        Step(self);
      }
      (*********************************************************************

       *********************************************************************)
      or {
        await Head(code).op = MOV;
        WriteToRegister(self, Head(code).dst, ReadFromRegister(self, Head(code).src));
        Step(self);
      }
      or {
        await Head(code).op = CMP;
        cf := ReadFromRegister(self, Head(code).dst) < ReadFromRegister(self, Head(code).src);
        sf := ReadFromRegister(self, Head(code).dst) < ReadFromRegister(self, Head(code).src);
        zf := ReadFromRegister(self, Head(code).dst) = ReadFromRegister(self, Head(code).src);
        Step(self);
      }
      or {
        await Head(code).op = SUB;
        WriteToRegister(self, Head(code).dst, ReadFromRegister(self, Head(code).dst) - ReadFromRegister(self, Head(code).src));
        cf := ReadFromRegister(self, Head(code).dst) < ReadFromRegister(self, Head(code).src);
        sf := ReadFromRegister(self, Head(code).dst) < ReadFromRegister(self, Head(code).src);
        zf := ReadFromRegister(self, Head(code).dst) = ReadFromRegister(self, Head(code).src);
        Step(self);
      }
      or {
        await Head(code).op = SC;
        if (ReadFromRegister(self, Head(code).dst) = Head(stack)) {
          WriteToWriteBuffer(self, Head(code).addr, ReadFromRegister(self, Head(code).src));
        };
        zf := ReadFromRegister(self, Head(code).dst) = Head(stack);
        stack := Tail(stack);
        Step(self);
      }
      (*********************************************************************

       *********************************************************************)
      or {
        await Head(code).op = JNZ;
        if (~zf) {
          Jump(self, Head(code));
        } else {
          Step(self);
        }
      }
      or {
        await Head(code).op = JNS;
        if (~sf) {
          Jump(self, Head(code));
        } else {
          Step(self);
        }
      }
      or {
        await Head(code).op = JLE;
        if (cf \/ zf) {
          Jump(self, Head(code));
        } else {
          Step(self);
        }
      }
      or {
        await Head(code).op = JMP;
        Jump(self, Head(code));
      }
      or {
        await Head(code).op = NOP;
        Step(self);
      }
      (*********************************************************************)
      (* The following stack-based events are introduced to implement XCHG *)
      (* and is semantically equivalent to registers under x86-TSO.        *)
      (*********************************************************************)
      or {
        await Head(code).op = PUSH;
        stack := <<ReadFromRegister(self, Head(code).reg)>> \o stack;
        Step(self);
      }
      or {
        await Head(code).op = POP;
        reg[self][Head(code).reg] := Head(stack);
        stack := Tail(stack);
        Step(self);
      }
      or {
        await Head(code).op = EXCH;
        stack := <<Head(Tail(stack)), Head(stack)>> \o Tail(Tail(stack));
        Step(self);
      };
    }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES reg, mem, lock, writeBuffer, pc

(* define statement *)
Blocked(p) == lock # {} /\ p \notin lock

Pending(p, a) ==
  SelectSeq(writeBuffer[p], LAMBDA w: w.addr = a) # <<>>

ReadFromWriteBuffer(p, r) ==
  Last(SelectSeq(writeBuffer[p], LAMBDA w: w.addr = r.addr)).value

ReadFromRegister(p, r) ==
  CASE r = "0" -> 0
    [] r = "1" -> 1
    [] OTHER   -> reg[p][r]

TypeOK ==
  /\ \A proc \in Proc :
       /\ reg[proc] \in [Reg -> Value]
       /\ writeBuffer[proc]
          \in Seq([addr : Addr, value : Value])
  /\  mem \in [Addr -> Value]

LockOK ==
  /\ lock \in SUBSET Proc
  /\ Cardinality(lock) \in {0, 1}

VARIABLES code, cf, sf, zf, stack

vars == << reg, mem, lock, writeBuffer, pc, code, cf, sf, zf, stack >>

ProcSet == {CTRL} \cup (Proc)

Init == (* Global variables *)
        /\ reg = [proc \in Proc |-> InitReg]
        /\ mem = InitMem
        /\ lock = {}
        /\ writeBuffer = [proc \in Proc |-> <<>>]
        (* Process Processor *)
        /\ code = [self \in Proc |-> Decode[1, Code[self]]]
        /\ cf = [self \in Proc |-> FALSE]
        /\ sf = [self \in Proc |-> FALSE]
        /\ zf = [self \in Proc |-> FALSE]
        /\ stack = [self \in Proc |-> <<>>]
        /\ pc = [self \in ProcSet |-> CASE self = CTRL -> "C10"
                                        [] self \in Proc -> "P10"]

C10 == /\ pc[CTRL] = "C10"
       /\ \E proc \in {proc \in Proc : writeBuffer[proc] # <<>> /\ ~Blocked(proc)}:
            /\ mem' = [mem EXCEPT ![(Head(writeBuffer[proc])).addr] = (Head(writeBuffer[proc])).value]
            /\ writeBuffer' = [writeBuffer EXCEPT ![proc] = Tail(writeBuffer[proc])]
       /\ pc' = [pc EXCEPT ![CTRL] = "C10"]
       /\ UNCHANGED << reg, lock, code, cf, sf, zf, stack >>

Controller == C10

P10(self) == /\ pc[self] = "P10"
             /\ IF code[self] # <<>>
                   THEN /\ \/ /\ /\ Head(code[self]).op = STORE
                                 /\ ~Blocked(self)
                              /\ writeBuffer' = [writeBuffer EXCEPT ![self] = Append(writeBuffer[self], [addr |-> (Head(code[self]).addr), value |-> (ReadFromRegister(self, Head(code[self]).reg))])]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, cf, sf, zf, stack>>
                           \/ /\ /\ Head(code[self]).op = LOAD
                                 /\ ~Blocked(self)
                                 /\ Pending(self, Head(code[self]).addr)
                              /\ reg' = [reg EXCEPT ![self][(Head(code[self]).reg)] = (ReadFromWriteBuffer(self, Head(code[self])))]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ /\ Head(code[self]).op = LOAD
                                 /\ ~Blocked(self)
                                 /\ ~Pending(self, Head(code[self]).addr)
                              /\ reg' = [reg EXCEPT ![self][(Head(code[self]).reg)] = (mem[Head(code[self]).addr])]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ /\ Head(code[self]).op = LOCK
                                 /\ lock = {}
                                 /\ writeBuffer[self] = <<>>
                              /\ lock' = {self}
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ /\ Head(code[self]).op = UNLOCK
                                 /\ lock = {self}
                                 /\ writeBuffer[self] = <<>>
                              /\ lock' = {}
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = LFENCE
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = LFENCE
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ /\ Head(code[self]).op = MFENCE
                                 /\ writeBuffer[self] = <<>>
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = MOV
                              /\ reg' = [reg EXCEPT ![self][(Head(code[self]).dst)] = (ReadFromRegister(self, Head(code[self]).src))]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = CMP
                              /\ cf' = [cf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) < ReadFromRegister(self, Head(code[self]).src)]
                              /\ sf' = [sf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) < ReadFromRegister(self, Head(code[self]).src)]
                              /\ zf' = [zf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) = ReadFromRegister(self, Head(code[self]).src)]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, stack>>
                           \/ /\ Head(code[self]).op = SUB
                              /\ reg' = [reg EXCEPT ![self][(Head(code[self]).dst)] = (ReadFromRegister(self, Head(code[self]).dst) - ReadFromRegister(self, Head(code[self]).src))]
                              /\ cf' = [cf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) < ReadFromRegister(self, Head(code[self]).src)]
                              /\ sf' = [sf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) < ReadFromRegister(self, Head(code[self]).src)]
                              /\ zf' = [zf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) = ReadFromRegister(self, Head(code[self]).src)]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<lock, writeBuffer, stack>>
                           \/ /\ Head(code[self]).op = SC
                              /\ IF ReadFromRegister(self, Head(code[self]).dst) = Head(stack[self])
                                    THEN /\ writeBuffer' = [writeBuffer EXCEPT ![self] = Append(writeBuffer[self], [addr |-> (Head(code[self]).addr), value |-> (ReadFromRegister(self, Head(code[self]).src))])]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED writeBuffer
                              /\ zf' = [zf EXCEPT ![self] = ReadFromRegister(self, Head(code[self]).dst) = Head(stack[self])]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, cf, sf>>
                           \/ /\ Head(code[self]).op = JNZ
                              /\ IF ~zf[self]
                                    THEN /\ code' = [code EXCEPT ![self] = Decode[(Head(code[self])).label, SubSeq(Code[self], (Head(code[self])).label, Len(Code[self]))]]
                                    ELSE /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = JNS
                              /\ IF ~sf[self]
                                    THEN /\ code' = [code EXCEPT ![self] = Decode[(Head(code[self])).label, SubSeq(Code[self], (Head(code[self])).label, Len(Code[self]))]]
                                    ELSE /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = JLE
                              /\ IF cf[self] \/ zf[self]
                                    THEN /\ code' = [code EXCEPT ![self] = Decode[(Head(code[self])).label, SubSeq(Code[self], (Head(code[self])).label, Len(Code[self]))]]
                                    ELSE /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = JMP
                              /\ code' = [code EXCEPT ![self] = Decode[(Head(code[self])).label, SubSeq(Code[self], (Head(code[self])).label, Len(Code[self]))]]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = NOP
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf, stack>>
                           \/ /\ Head(code[self]).op = PUSH
                              /\ stack' = [stack EXCEPT ![self] = <<ReadFromRegister(self, Head(code[self]).reg)>> \o stack[self]]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf>>
                           \/ /\ Head(code[self]).op = POP
                              /\ reg' = [reg EXCEPT ![self][Head(code[self]).reg] = Head(stack[self])]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<lock, writeBuffer, cf, sf, zf>>
                           \/ /\ Head(code[self]).op = EXCH
                              /\ stack' = [stack EXCEPT ![self] = <<Head(Tail(stack[self])), Head(stack[self])>> \o Tail(Tail(stack[self]))]
                              /\ code' = [code EXCEPT ![self] = Tail(code[self])]
                              /\ UNCHANGED <<reg, lock, writeBuffer, cf, sf, zf>>
                        /\ pc' = [pc EXCEPT ![self] = "P10"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << reg, lock, writeBuffer, code, cf, sf, 
                                        zf, stack >>
             /\ mem' = mem

Processor(self) == P10(self)

Next == Controller
           \/ (\E self \in Proc: Processor(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Controller)
        /\ \A self \in Proc : SF_vars(Processor(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun Apr 29 10:32:31 JST 2018 by takayuki
\* Created Sun Apr 15 22:38:22 JST 2018 by takayuki
