---- MODULE IPC_Liveness ----
EXTENDS Integers, Sequences, TLC, TLAPS, FiniteSets

CONSTANTS Clients, MaxBufferSize

ASSUME ClientsAssumption == Clients # {} /\ IsFiniteSet(Clients)
ASSUME MaxBufferSizeAssumption == MaxBufferSize \in Nat /\ MaxBufferSize > 0

VARIABLES
  channels,
  capabilities,
  waiting,
  active

vars == <<channels, capabilities, waiting, active>>

TypeOK ==
  /\ channels \in [Clients \times Clients -> Seq(Nat)]
  /\ capabilities \in [Clients -> SUBSET {"send", "receive", "grant"}]
  /\ waiting \subseteq Clients
  /\ active \subseteq Clients

Init ==
  /\ channels = [c \in Clients \times Clients |-> <<>>]
  /\ capabilities = [c \in Clients |-> {"send", "receive"}]
  /\ waiting = {}
  /\ active = Clients

Send(sender, receiver, msg) ==
  /\ sender \in active
  /\ "send" \in capabilities[sender]
  /\ Len(channels[<<sender, receiver>>]) < MaxBufferSize
  /\ channels' = [channels EXCEPT ![<<sender, receiver>>] = Append(@, msg)]
  /\ waiting' = waiting \ {receiver}
  /\ UNCHANGED <<capabilities, active>>

Receive(client) ==
  /\ client \in active
  /\ "receive" \in capabilities[client]
  /\ \E sender \in Clients :
       /\ Len(channels[<<sender, client>>]) > 0
       /\ channels' = [channels EXCEPT ![<<sender, client>>] = Tail(@)]
       /\ UNCHANGED <<capabilities, waiting, active>>

Wait(client) ==
  /\ client \in active
  /\ \A sender \in Clients : Len(channels[<<sender, client>>]) = 0
  /\ waiting' = waiting \union {client}
  /\ UNCHANGED <<channels, capabilities, active>>

Grant(granter, grantee, cap) ==
  /\ granter \in active
  /\ "grant" \in capabilities[granter]
  /\ cap \in capabilities[granter]
  /\ capabilities' = [capabilities EXCEPT ![grantee] = @ \union {cap}]
  /\ UNCHANGED <<channels, waiting, active>>

Next ==
  \/ \E s, r \in Clients, m \in Nat : Send(s, r, m)
  \/ \E c \in Clients : Receive(c)
  \/ \E c \in Clients : Wait(c)
  \/ \E g, e \in Clients, cap \in {"send", "receive", "grant"} : Grant(g, e, cap)

Fairness ==
  /\ \A c \in Clients : WF_vars(Receive(c))
  /\ \A s, r \in Clients, m \in Nat : WF_vars(Send(s, r, m))

Spec == Init /\ [][Next]_vars /\ Fairness

TypeInvariant == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, Next
               PROVE TypeOK'
    BY DEF vars
  <2>1. CASE \E s, r \in Clients, m \in Nat : Send(s, r, m)
    BY <2>1 DEF TypeOK, Send
  <2>2. CASE \E c \in Clients : Receive(c)
    BY <2>2 DEF TypeOK, Receive
  <2>3. CASE \E c \in Clients : Wait(c)
    BY <2>3 DEF TypeOK, Wait
  <2>4. CASE \E g, e \in Clients, cap \in {"send", "receive", "grant"} : Grant(g, e, cap)
    BY <2>4 DEF TypeOK, Grant
  <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1> QED BY <1>1, <1>2, PTL DEF Spec

NoMessageLoss ==
  \A s, r \in Clients : 
    [](Len(channels[<<s, r>>]) > 0 => 
       <>(Len(channels[<<s, r>>]) = 0))

THEOREM MessageLossProperty == Spec => NoMessageLoss
<1>1. SUFFICES ASSUME Spec
               PROVE NoMessageLoss
  OBVIOUS
<1>2. ASSUME NEW s \in Clients, NEW r \in Clients,
             [](Len(channels[<<s, r>>]) > 0)
      PROVE FALSE
  <2>1. ASSUME Len(channels[<<s, r>>]) > 0
        PROVE ENABLED Receive(r)
    BY <2>1 DEF Receive
  <2>2. []ENABLED Receive(r)
    BY <1>2, <2>1
  <2>3. <>Receive(r)
    BY <2>2, PTL DEF Spec, Fairness
  <2>4. Receive(r) => Len(channels'[<<s, r>>]) < Len(channels[<<s, r>>])
    BY DEF Receive
  <2>5. <>(Len(channels[<<s, r>>]) = 0)
    BY <2>3, <2>4, PTL
  <2> QED BY <1>2, <2>5
<1> QED BY <1>1, <1>2, PTL DEF NoMessageLoss

CapabilityMonotonicity ==
  [][\A c \in Clients : capabilities'[c] \supseteq capabilities[c]]_vars

THEOREM CapabilityMonotonicityProperty == Spec => CapabilityMonotonicity
<1>1. Init => \A c \in Clients : capabilities[c] # {}
  BY DEF Init
<1>2. ASSUME TypeOK, Next, NEW c \in Clients
      PROVE capabilities'[c] \supseteq capabilities[c]
  <2>1. CASE \E s, r \in Clients, m \in Nat : Send(s, r, m)
    BY <2>1 DEF Send
  <2>2. CASE \E cl \in Clients : Receive(cl)
    BY <2>2 DEF Receive
  <2>3. CASE \E cl \in Clients : Wait(cl)
    BY <2>3 DEF Wait
  <2>4. CASE \E g, e \in Clients, cap \in {"send", "receive", "grant"} : Grant(g, e, cap)
    <3>1. PICK g, e \in Clients, cap \in {"send", "receive", "grant"} : Grant(g, e, cap)
      BY <2>4
    <3>2. CASE c = e
      BY <3>1, <3>2 DEF Grant
    <3>3. CASE c # e
      BY <3>1, <3>3 DEF Grant
    <3> QED BY <3>2, <3>3
  <2> QED BY <2>1, <2>2, <2>3, <2>4 DEF Next
<1> QED BY <1>1, <1>2, PTL DEF Spec, CapabilityMonotonicity

NoBufferOverflow ==
  \A s, r \in Clients : 
    [](Len(channels[<<s, r>>]) <= MaxBufferSize)

THEOREM BufferOverflowProperty == Spec => NoBufferOverflow
<1>1. Init => \A s, r \in Clients : Len(channels[<<s, r>>]) = 0
  BY DEF Init
<1>2. ASSUME TypeOK, Next, 
             NEW s \in Clients, NEW r \in Clients,
             Len(channels[<<s, r>>]) <= MaxBufferSize
      PROVE Len(channels'[<<s, r>>]) <= MaxBufferSize
  <2>1. CASE Send(s, r, _)
    BY <2>1, <1>2, MaxBufferSizeAssumption DEF Send
  <2>2. CASE Receive(r)
    BY <2>2, <1>2 DEF Receive
  <2>3. CASE ~(Send(s, r, _) \/ Receive(r))
    BY <2>3, <1>2 DEF Next, Wait, Grant
  <2> QED BY <2>1, <2>2, <2>3
<1> QED BY <1>1, <1>2, MaxBufferSizeAssumption, PTL DEF Spec, NoBufferOverflow

NoDeadlock ==
  \A c \in Clients :
    c \in active => (c \in waiting => <>~(c \in waiting))

THEOREM NoDeadlockProperty == Spec => NoDeadlock
<1>1. ASSUME NEW c \in Clients, c \in active, c \in waiting
      PROVE <>~(c \in waiting)
  <2>1. c \in waiting => \A s \in Clients : Len(channels[<<s, c>>]) = 0
    BY DEF Wait
  <2>2. \E s \in Clients : <>(Len(channels[<<s, c>>]) > 0)
    BY WF_vars(Send(s, c, _)) DEF Spec, Fairness
  <2>3. ASSUME NEW s \in Clients, Len(channels[<<s, c>>]) > 0
        PROVE ENABLED Receive(c)
    BY <2>3 DEF Receive
  <2>4. <>(Len(channels[<<s, c>>]) > 0) => <>ENABLED Receive(c)
    BY <2>3
  <2>5. <>ENABLED Receive(c) => <>Receive(c)
    BY PTL, WF_vars(Receive(c)) DEF Spec, Fairness
  <2>6. Receive(c) => ~(c \in waiting')
    BY DEF Receive
  <2> QED BY <2>1, <2>2, <2>4, <2>5, <2>6, PTL
<1> QED BY <1>1, PTL DEF NoDeadlock, Spec

MessageEventuallyReceived ==
  \A s, r \in Clients, m \in Nat :
    (Len(channels[<<s, r>>]) > 0) ~> (Len(channels[<<s, r>>]) = 0)

THEOREM MessageEventuallyReceivedProperty == Spec => MessageEventuallyReceived
<1>1. ASSUME NEW s \in Clients, NEW r \in Clients,
             Len(channels[<<s, r>>]) > 0
      PROVE <>(Len(channels[<<s, r>>]) = 0)
  <2>1. Len(channels[<<s, r>>]) > 0 => ENABLED Receive(r)
    BY DEF Receive
  <2>2. <>ENABLED Receive(r) => <>Receive(r)
    BY PTL, WF_vars(Receive(r)) DEF Spec, Fairness
  <2>3. []ENABLED Receive(r) \/ <>(Len(channels[<<s, r>>]) = 0)
    BY <2>1, <2>2
  <2>4. Receive(r) => 
        Len(channels'[<<s, r>>]) < Len(channels[<<s, r>>]) \/
        Len(channels'[<<s, r>>]) = 0
    BY DEF Receive
  <2>5. \A n \in Nat : 
        (Len(channels[<<s, r>>]) = n /\ n > 0 /\ Receive(r)) =>
        <>(Len(channels[<<s, r>>]) = 0)
    <3>1. Base case n = 1
      BY <2>4 DEF Receive
    <3>2. Inductive case
      BY <2>4, <3>1, PTL
    <3> QED BY <3>1, <3>2, NatInduction
  <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, PTL
<1> QED BY <1>1, PTL DEF MessageEventuallyReceived, Spec

NoStarvation ==
  \A c \in Clients :
    c \in active => []<>(~(c \in waiting))

THEOREM NoStarvationProperty == Spec => NoStarvation
<1>1. ASSUME NEW c \in Clients, c \in active
      PROVE []<>(~(c \in waiting))
  <2>1. c \in waiting => <>(~(c \in waiting))
    BY NoDeadlockProperty, PTL DEF NoDeadlock, Spec
  <2>2. ~(c \in waiting) => []<>(~(c \in waiting))
    BY <2>1, PTL
  <2> QED BY <2>1, <2>2, PTL
<1> QED BY <1>1, PTL DEF NoStarvation, Spec

FairSend ==
  \A s, r \in Clients, m \in Nat :
    WF_vars(Send(s, r, m))

FairReceive ==
  \A c \in Clients :
    WF_vars(Receive(c))

THEOREM FairnessProperty == Spec => (FairSend /\ FairReceive)
  BY DEF Spec, Fairness, FairSend, FairReceive

CapabilityIntegrity ==
  \A c \in Clients : 
    "send" \in capabilities[c] /\ "receive" \in capabilities[c]

THEOREM CapabilityIntegrityProperty == Spec => []CapabilityIntegrity
<1>1. Init => CapabilityIntegrity
  BY DEF Init, CapabilityIntegrity
<1>2. ASSUME CapabilityIntegrity, [Next]_vars, NEW c \in Clients
      PROVE "send" \in capabilities'[c] /\ "receive" \in capabilities'[c]
  <2>1. "send" \in capabilities[c] /\ "receive" \in capabilities[c]
    BY <1>2 DEF CapabilityIntegrity
  <2>2. capabilities'[c] \supseteq capabilities[c]
    BY CapabilityMonotonicityProperty, <1>2 DEF CapabilityMonotonicity
  <2> QED BY <2>1, <2>2
<1> QED BY <1>1, <1>2, PTL DEF Spec, CapabilityIntegrity

ActiveStable ==
  \A c \in Clients : c \in active => [](c \in active)

THEOREM ActiveStableProperty == Spec => ActiveStable
<1>1. Init => active = Clients
  BY DEF Init
<1>2. [Next]_vars => UNCHANGED active
  BY DEF Next, Send, Receive, Wait, Grant
<1> QED BY <1>1, <1>2, PTL DEF Spec, ActiveStable

MCClients == {c1, c2, c3}
MCMaxBufferSize == 5

Alias == 
  [channels |-> channels,
   capabilities |-> capabilities,
   waiting |-> waiting,
   active |-> active,
   buffer_sizes |-> [s \in Clients, r \in Clients |-> Len(channels[<<s, r>>])]]

StateConstraint ==
  /\ \A s, r \in Clients : Len(channels[<<s, r>>]) <= MaxBufferSize
  /\ \A c \in Clients : capabilities[c] \subseteq {"send", "receive", "grant"}

ActionConstraint ==
  \A s, r \in Clients : 
    Len(channels'[<<s, r>>]) - Len(channels[<<s, r>>]) \in {-1, 0, 1}

====
