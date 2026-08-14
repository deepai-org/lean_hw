-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compose
import Loom.Hw.Semantics
import Loom.Hw.Trees
import Mathlib.Data.Nat.ModEq

/-!
# Typed elastic channels

`Chan w` is the ordinary-user handle for a width-`w` FIFO connection.  This
file contains both its small executable specification and the stock
single-clock endpoint/adapter implementation used by `System` assembly.

The endpoint protocol is generated: users enqueue, inspect `canEnq`, inspect
`canDeq`/`deq`, and pop.  They never spell valid/ready or payload wires.  The
adapter uses ordinary Loom registers, memory, actions, `par`, and `connect`;
there is no second synchronous semantics.
-/

namespace Loom.Hw

/-- Behavior of a full FIFO when producer and consumer accept on one aligned
event.  It is declaration data, never evaluator-order accident. -/
inductive FullCoTickPolicy where
  | refusePush
  | exchange
  deriving DecidableEq, Repr

/-- A width-typed bounded FIFO handle.  This is a logical queue declaration,
not a choice of CDC circuit.  Positive depth is a fail-closed assembly check
because names and depths are ordinary generator data.  A physical multiclock
emitter separately binds each crossing to a certified realization. -/
structure Chan (width : Nat) where
  name : String
  depth : Nat := 1
  policy : FullCoTickPolicy := .exchange
  deriving Repr

namespace Chan

variable {w : Nat}

/-! ## Executable abstract queue -/

/-- Abstract state is deliberately executable and finite-prefix friendly. -/
abbrev State (width : Nat) := List (BitVec width)

structure EventData (width : Nat) where
  push : Option (BitVec width) := none
  pop : Bool := false
  deriving DecidableEq, Repr

abbrev Event := EventData

structure Result (width : Nat) where
  state : State width
  accepted : Bool
  delivered : Option (BitVec width)
  deriving DecidableEq, Repr

/-- Atomic channel event. Reads use the pre-event queue. On a full queue,
`refusePush` rejects a simultaneous push/pop; `exchange` accepts it. -/
def step (c : Chan w) (q : State w) (event : Event w) : Result w :=
  let popAccepted := event.pop && !q.isEmpty
  let delivered := if popAccepted then q.head? else none
  let afterPop := if popAccepted then q.drop 1 else q
  let hasSpace := q.length < c.depth
  let exchange := c.policy == .exchange && popAccepted
  let pushAccepted := event.push.isSome && (hasSpace || exchange)
  let next := match event.push with
    | some value => if pushAccepted then afterPop ++ [value] else afterPop
    | none => afterPop
  { state := next, accepted := pushAccepted, delivered }

/-- Retain only transfers that the abstract queue actually performed.  This
is the event observed by a conservative physical implementation that may
stall a request because a synchronized full/empty view is stale. -/
def successfulEvent (c : Chan w) (q : State w) (event : Event w) : Event w :=
  let result := c.step q event
  { push := if result.accepted then event.push else none
    pop := result.delivered.isSome }

/-- Replaying only the successful transfers is observationally and
state-wise identical to the original request.  This normalization is the
bridge used by concrete implementations whose public trace records accepted
traffic rather than attempted traffic. -/
theorem step_successfulEvent (c : Chan w) (q : State w) (event : Event w) :
    c.step q (c.successfulEvent q event) = c.step q event := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases q with
  | nil =>
      cases push <;> cases pop <;> cases policy <;>
        simp [successfulEvent, step]
      all_goals split <;> simp_all
  | cons head tail =>
      cases push <;> cases pop <;> cases policy <;>
        simp [successfulEvent, step]
      all_goals split <;> simp_all

@[simp] theorem step_no_push_accepted (c : Chan w) (q : State w) (pop : Bool) :
    (c.step q { push := none, pop }).accepted = false := by
  simp [step]

theorem step_delivered_eq_head (c : Chan w) (q : State w) (event : Event w) :
    (c.step q event).delivered = if event.pop && !q.isEmpty then q.head? else none := by
  rfl

/-- A delivered value is always the pre-event head: the one-step FIFO-order
fact used by larger trace theorems. -/
theorem fifoOrder (c : Chan w) (q : State w) (event : Event w) (value : BitVec w)
    (delivered : (c.step q event).delivered = some value) :
    q.head? = some value := by
  rw [step_delivered_eq_head] at delivered
  split at delivered
  · exact delivered
  · simp at delivered

/-- An accepted payload occurs exactly once at the new queue tail. -/
theorem accepted_state (c : Chan w) (q : State w) (value : BitVec w) (pop : Bool)
    (accepted : (c.step q { push := some value, pop }).accepted = true) :
    (c.step q { push := some value, pop }).state =
      (if pop && !q.isEmpty then q.drop 1 else q) ++ [value] := by
  simp only [step, Option.isSome_some] at accepted ⊢
  simp [accepted]

/-- No event overflows a queue that was within its declared capacity. -/
theorem noOverflow (c : Chan w) (q : State w) (event : Event w)
    (bounded : q.length ≤ c.depth) : (c.step q event).state.length ≤ c.depth := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases q with
  | nil =>
      cases push <;> cases pop <;> cases policy <;>
        simp [step] at bounded ⊢ <;> try split <;> simp_all
      all_goals omega
  | cons head tail =>
      cases push <;> cases pop <;> cases policy <;>
        simp [step] at bounded ⊢ <;> try split <;> simp_all
      all_goals omega

/-- Queue occupancy changes only by the accepted and delivered decisions.  The
subtraction is first because a simultaneous exchange removes the old head
before appending the accepted payload. -/
theorem step_length (c : Chan w) (q : State w) (event : Event w) :
    (c.step q event).state.length =
      q.length - (if (c.step q event).delivered.isSome then 1 else 0) +
        (if (c.step q event).accepted then 1 else 0) := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases q with
  | nil =>
      cases push <;> cases pop <;> cases policy <;>
        simp [step]
      all_goals split <;> simp_all
  | cons head tail =>
      cases push <;> cases pop <;> cases policy <;>
        simp [step]
      all_goals split <;> simp_all

/-- Decision-normal form of the next queue: remove the delivered head first,
then append exactly the accepted payload. -/
theorem step_state (c : Chan w) (q : State w) (event : Event w) :
    (c.step q event).state =
      (if (c.step q event).delivered.isSome then q.drop 1 else q) ++
        (if (c.step q event).accepted then [event.push.getD 0] else []) := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases q with
  | nil =>
      cases push <;> cases pop <;> cases policy <;>
        simp [step]
  | cons head tail =>
      cases push <;> cases pop <;> cases policy <;>
        simp [step]
      all_goals split <;> simp_all

/-- A successful delivery witnesses a nonempty pre-event queue. -/
theorem nonempty_of_delivered (c : Chan w) (q : State w) (event : Event w)
    (delivered : (c.step q event).delivered.isSome = true) :
    0 < q.length := by
  rcases event with ⟨push, pop⟩
  cases q <;> simp [step] at delivered ⊢

/-! ## Finite-trace safety ledger -/

def acceptedValues (c : Chan w) (q : State w) (event : Event w) : List (BitVec w) :=
  if (c.step q event).accepted then event.push.toList else []

def deliveredValues (c : Chan w) (q : State w) (event : Event w) : List (BitVec w) :=
  (c.step q event).delivered.toList

/-- One event neither invents nor loses a payload.  The equation also fixes
FIFO order: old queue followed by newly accepted input equals delivered output
followed by the new queue. -/
theorem step_conservation (c : Chan w) (q : State w) (event : Event w) :
    q ++ c.acceptedValues q event =
      c.deliveredValues q event ++ (c.step q event).state := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases q with
  | nil =>
      cases push <;> cases pop <;> cases policy <;>
        simp [acceptedValues, deliveredValues, step]
  | cons head tail =>
      cases push <;> cases pop <;> cases policy <;>
        simp [acceptedValues, deliveredValues, step, List.cons_append]
      all_goals split <;> simp_all

structure TraceResult (width : Nat) where
  state : State width
  accepted : List (BitVec width)
  delivered : List (BitVec width)

/-- Execute a finite event trace while recording exactly the accepted and
delivered payload sequences. -/
def runTrace (c : Chan w) : State w → List (Event w) → TraceResult w
  | q, [] => ⟨q, [], []⟩
  | q, event :: rest =>
      let one := c.step q event
      let later := c.runTrace one.state rest
      ⟨later.state, c.acceptedValues q event ++ later.accepted,
        c.deliveredValues q event ++ later.delivered⟩

/-- Trace-level losslessness, non-duplication, non-corruption, and FIFO order
in one reusable equation. -/
theorem runTrace_conservation (c : Chan w) (initial : State w)
    (events : List (Event w)) :
    initial ++ (c.runTrace initial events).accepted =
      (c.runTrace initial events).delivered ++ (c.runTrace initial events).state := by
  induction events generalizing initial with
  | nil => simp [runTrace]
  | cons event rest ih =>
      simp only [runTrace]
      rw [← List.append_assoc, c.step_conservation initial event]
      simpa only [List.append_assoc] using
        congrArg (fun values => c.deliveredValues initial event ++ values)
          (ih (c.step initial event).state)

/-! ## Registered source endpoint ledger -/

/-- Semantic contents of the stock one-entry source register. -/
def sourcePending (valid : Bool) (payload : BitVec w) : List (BitVec w) :=
  if valid then [payload] else []

/-- Result of one stock source-endpoint edge.  A replacement written by the
application wins over acknowledgement cleanup, matching `withSource` rule
order and Loom's last-write-wins cycle semantics. -/
structure SourceStep (width : Nat) where
  valid : Bool
  payload : BitVec width
  deriving DecidableEq, Repr

def sourceStep (valid : Bool) (payload : BitVec w) (accepted : Bool)
    (replacement : Option (BitVec w)) : SourceStep w :=
  match replacement with
  | some value => ⟨true, value⟩
  | none => ⟨valid && !accepted, payload⟩

/-- A stock registered source neither loses, duplicates, reorders, nor
corrupts values in one edge.  The premises are the endpoint protocol facts:
the FIFO only acknowledges a valid offer, and an application only replaces a
busy slot when that offer is acknowledged. -/
theorem sourceStep_conservation (valid : Bool) (payload : BitVec w)
    (accepted : Bool) (replacement : Option (BitVec w))
    (acceptedLegal : accepted = true → valid = true)
    (replacementLegal : replacement.isSome = true →
      valid = false ∨ accepted = true) :
    sourcePending valid payload ++ replacement.toList =
      (if accepted then sourcePending valid payload else []) ++
        sourcePending (sourceStep valid payload accepted replacement).valid
          (sourceStep valid payload accepted replacement).payload := by
  cases valid <;> cases accepted <;> cases replacement with
  | none => simp [sourcePending, sourceStep] at acceptedLegal ⊢
  | some value =>
      simp [sourcePending, sourceStep] at acceptedLegal replacementLegal ⊢

/-! ### Registered sink endpoint conservation -/

/-- A sink pop already issued by the application but not yet observed by the
channel event.  The payload is retained because the FIFO head remains stable
until that event performs the pop. -/
def sinkPending (pop : Bool) (payload : BitVec w) : List (BitVec w) :=
  if pop then [payload] else []

/-- The application-side half of one registered sink step.  A fresh consume
captures the currently presented FIFO head and raises the pop request; the
request reaches the abstract queue in the following atomic sink event. -/
def sinkStep (queue : State w) (consume : Bool) : Bool × BitVec w :=
  (consume, queue.head?.getD 0)

/-- Conservation and head coherence for a registered sink endpoint sharing a
clock event with an arbitrary source push.  `consumeLegal` is precisely the
generated `canDeq` contract: a visible head and no older outstanding pop. -/
theorem sinkStep_conservation (c : Chan w) (queue : State w)
    (push : Option (BitVec w)) (pop : Bool) (payload : BitVec w)
    (consume : Bool)
    (coherent : pop = true → queue.head? = some payload)
    (consumeLegal : consume = true → pop = false ∧ queue.isEmpty = false) :
    sinkPending pop payload ++
        (if consume then [queue.head?.getD 0] else []) =
      c.deliveredValues queue { push, pop } ++
        sinkPending (sinkStep queue consume).1 (sinkStep queue consume).2 ∧
      (consume = true →
        (c.step queue { push, pop }).state.head? =
          some (sinkStep queue consume).2) := by
  rcases c with ⟨name, depth, policy⟩
  cases queue with
  | nil =>
      cases push <;> cases pop <;> cases consume <;>
        simp [sinkPending, sinkStep, deliveredValues, step] at coherent consumeLegal ⊢
  | cons head tail =>
      cases push <;> cases pop <;> cases consume <;> cases policy <;>
        simp [sinkPending, sinkStep, deliveredValues, step] at coherent consumeLegal ⊢
      all_goals try split <;> simp_all
      all_goals exact coherent.symm

/-- Without a sink pop, an existing FIFO head is stable even if the source
simultaneously appends a value. -/
theorem step_head_of_no_pop (c : Chan w) (queue : State w)
    (push : Option (BitVec w)) (payload : BitVec w)
    (head : queue.head? = some payload) :
    (c.step queue { push, pop := false }).state.head? = some payload := by
  rcases c with ⟨name, depth, policy⟩
  cases queue with
  | nil => simp at head
  | cons first rest =>
      cases push <;> cases policy <;>
        simp [step] at head ⊢
      all_goals try split <;> simp_all
      all_goals exact head

/-- Channel names are expanded in one place; callers never hand-spell the
generated handshake coordinates. Public so endpoint proofs and structural
release checks can normalize names produced by the channel API. -/
def stem (c : Chan w) := "__loom_chan_" ++ c.name ++ "_"
def sourceValidName (c : Chan w) := c.stem ++ "src_valid"
def sourcePayloadName (c : Chan w) := c.stem ++ "src_payload"
def sourceReadyName (c : Chan w) := c.stem ++ "src_ready"
def sourceAcceptedName (c : Chan w) := c.stem ++ "src_accepted"
def sinkValidName (c : Chan w) := c.stem ++ "dst_valid"
def sinkPayloadName (c : Chan w) := c.stem ++ "dst_payload"
def sinkPopName (c : Chan w) := c.stem ++ "dst_pop"
/-- Destination-local coordinates used only by the opt-in buffered sink. -/
def sinkBufferCountName (c : Chan w) := c.stem ++ "dst_buffer_count"
def sinkBufferHeadName (c : Chan w) := c.stem ++ "dst_buffer_head"
def sinkBufferTailName (c : Chan w) := c.stem ++ "dst_buffer_tail"

/-- Maximum writes to one register coordinate along any executable action
path. Sequential actions add; mutually exclusive branches take the maximum.
This is deliberately more precise than counting syntax occurrences. -/
def _root_.Loom.Hw.Act.maxWritesTo (target : String) (targetWidth : Nat) :
    Act → Nat
  | .skip => 0
  | .seq left right =>
      left.maxWritesTo target targetWidth + right.maxWritesTo target targetWidth
  | .ite _ thenAction elseAction =>
      max (thenAction.maxWritesTo target targetWidth)
        (elseAction.maxWritesTo target targetWidth)
  | .write width name _ =>
      if name = target && width = targetWidth then 1 else 0
  | .writeSlice width name _ _ _ _ =>
      if name = target && width = targetWidth then 1 else 0
  | .memWrite .. => 0

def _root_.Loom.Hw.Design.maxWritesTo (design : Design)
    (target : String) (targetWidth : Nat) : Nat :=
  design.rules.foldl
    (fun count rule => count + rule.body.maxWritesTo target targetWidth) 0

def countName (c : Chan w) := c.stem ++ "count"
def headName (c : Chan w) := c.stem ++ "head"
def tailName (c : Chan w) := c.stem ++ "tail"
def memoryName (c : Chan w) := c.stem ++ "storage"
def acceptedName (c : Chan w) := c.stem ++ "accepted"
def deliveredName (c : Chan w) := c.stem ++ "delivered"
/-- Generated adapter input names. Public realization code consumes these;
application authors continue to use the directional endpoint operations. -/
def pushName (c : Chan w) := c.stem ++ "push"
def pushPayloadName (c : Chan w) := c.stem ++ "push_payload"
def popName (c : Chan w) := c.stem ++ "pop"

def countWidth (c : Chan w) : Nat := Nat.log2 c.depth + 1
def indexWidth (c : Chan w) : Nat := Nat.log2 (c.depth - 1) + 1

def sourceValid (c : Chan w) : Expr 1 := .reg 1 c.sourceValidName
def sourceAccepted (c : Chan w) : Expr 1 := .reg 1 c.sourceAcceptedName
def sourceReady (c : Chan w) : Expr 1 := .reg 1 c.sourceReadyName
def sourcePayload (c : Chan w) : Expr w := .reg w c.sourcePayloadName

/-- Whether the generated source endpoint can accept a new message. -/
def canEnq (c : Chan w) : Expr 1 :=
  .and (.or (.not c.sourceValid) c.sourceAccepted) c.sourceReady

/-- Guarded enqueue action. Endpoint declaration/plumbing comes from
`withSource`; no valid/ready signal is exposed at this call site. -/
def enq (c : Chan w) (value : Expr w) : Act :=
  .ite c.canEnq
    (.seq (.write w c.sourcePayloadName value)
      (.write 1 c.sourceValidName (.lit 1)))
    .skip

/-- A head is available and there is no registered pop still awaiting the
next channel event.  Masking the outstanding request is essential in the
named-clock semantics: without it an island can consume the same pre-event
head again on the event that commits its previous pop. -/
def canDeq (c : Chan w) : Expr 1 :=
  .and (.reg 1 c.sinkValidName) (.not (.reg 1 c.sinkPopName))
def deq (c : Chan w) : Expr w := .reg w c.sinkPayloadName

/-- The current registered sink protocol has an explicit bubble after every
consume: while the previous pop request is pending, application code cannot
observe another consumable item. Timing reports cite this theorem when they
state the stock endpoint's two-destination-tick issue interval. -/
theorem canDeq_zero_of_pending (c : Chan w) (state : St)
    (pending : state.regs c.sinkPopName 1 = 1#1) :
    c.canDeq.eval state = 0#1 := by
  simp [canDeq, Expr.eval, pending]

/-- An accepted source offer may be replaced on the same source edge whenever
the FIFO remains ready. This is the local fact behind the stock source
endpoint's one-source-tick issue interval. -/
theorem canEnq_one_of_accepted_ready (c : Chan w) (state : St)
    (accepted : state.regs c.sourceAcceptedName 1 = 1#1)
  (ready : state.regs c.sourceReadyName 1 = 1#1) :
    c.canEnq.eval state = 1#1 := by
  simp only [canEnq, sourceValid, sourceAccepted, sourceReady, Expr.eval]
  rw [accepted, ready]
  bv_decide

/-- A source replacement without acknowledgement is legal only when the
registered source slot was empty. -/
theorem sourceValid_zero_of_canEnq_notAccepted (c : Chan w) (state : St)
    (ready : c.canEnq.eval state = 1#1)
    (notAccepted : state.regs c.sourceAcceptedName 1 = 0#1) :
    state.regs c.sourceValidName 1 = 0#1 := by
  simp only [canEnq, sourceValid, sourceAccepted, sourceReady, Expr.eval]
    at ready
  rw [notAccepted] at ready
  have validCases : state.regs c.sourceValidName 1 = 0#1 ∨
      state.regs c.sourceValidName 1 = 1#1 := by bv_omega
  rcases validCases with valid | valid
  · exact valid
  · rw [valid] at ready
    simp at ready

/-- Consume the currently visible head when one exists. -/
def pop (c : Chan w) : Act :=
  .ite c.canDeq (.write 1 c.sinkPopName (.lit 1)) .skip

/-- Add the stock source endpoint to an island. Its maintenance rule precedes
the island rules, so a user enqueue in the same cycle wins over acknowledgement
cleanup under Loom's existing last-write-wins semantics. -/
def withSource (c : Chan w) (d : Design) : Design where
  name := d.name
  regs :=
    ⟨c.sourceValidName, 1, 0⟩ :: ⟨c.sourcePayloadName, w, 0⟩ :: d.regs
  mems := d.mems
  inputs := ⟨c.sourceReadyName, 1⟩ :: ⟨c.sourceAcceptedName, 1⟩ :: d.inputs
  rules := ⟨c.stem ++ "source_maintenance",
    .ite c.sourceAccepted (.write 1 c.sourceValidName (.lit 0)) .skip⟩ :: d.rules
  ackMemInit := d.ackMemInit
  syncReadMems := d.syncReadMems
  -- Endpoint state is part of the generated physical module interface. Users
  -- still manipulate only the typed `Chan`; System assembly consumes these
  -- ports and rejects raw cross-clock references.
  outputs := [c.sourceValidName, c.sourcePayloadName] ++ d.outputs
  combOutputs := d.combOutputs

/-- Add the stock sink endpoint. `pop` is a generated one-cycle request. -/
def withSink (c : Chan w) (d : Design) : Design where
  name := d.name
  regs := ⟨c.sinkPopName, 1, 0⟩ :: d.regs
  mems := d.mems
  inputs := ⟨c.sinkValidName, 1⟩ :: ⟨c.sinkPayloadName, w⟩ :: d.inputs
  rules := ⟨c.stem ++ "sink_maintenance",
    .write 1 c.sinkPopName (.lit 0)⟩ :: d.rules
  ackMemInit := d.ackMemInit
  syncReadMems := d.syncReadMems
  outputs := [c.sinkPopName] ++ d.outputs
  combOutputs := d.combOutputs

/-! ### Full-rate registered sink

The ordinary endpoint deliberately inserts a bubble after a consume.  This
alternative remains entirely in the destination clock domain and uses two
presentation registers to cover the one outstanding FIFO pop.  It therefore
has no combinational CDC path and can sustain one accepted consume per
destination tick while input remains available.
-/

/-- Values retained by the full-rate endpoint.  The list representation is
the specification; the generated hardware below uses a two-entry register
bank. -/
def FullRateBuffer (w : Nat) := List (BitVec w)

/-- One abstract full-rate presentation step.  Consumption observes the
pre-event head; an item arriving on the same edge is appended afterwards. -/
def fullRateBufferStep (buffer : FullRateBuffer w) (incoming : Option (BitVec w))
    (consume : Bool) : FullRateBuffer w :=
  (if consume then buffer.drop 1 else buffer) ++ incoming.toList

def fullRateDelivered (buffer : FullRateBuffer w) (consume : Bool) : List (BitVec w) :=
  if consume then buffer.take 1 else []

/-- The presentation buffer neither loses nor duplicates values. -/
theorem fullRateBuffer_conservation (buffer : FullRateBuffer w)
    (incoming : Option (BitVec w)) (consume : Bool) :
    List.append (fullRateDelivered buffer consume)
        (fullRateBufferStep buffer incoming consume) =
      List.append buffer incoming.toList := by
  cases consume <;> cases buffer <;> simp [fullRateDelivered, fullRateBufferStep]

/-- In the steady state, a simultaneous consume and arrival delivers the old
head and leaves the new value immediately available for the next tick. -/
theorem fullRateBuffer_onePerTick (head next : BitVec w) :
    fullRateDelivered [head] true = [head] ∧
      fullRateBufferStep [head] (some next) true = [next] := by
  simp [fullRateDelivered, fullRateBufferStep]

def fullRateCount (c : Chan w) : Expr 2 := .reg 2 c.sinkBufferCountName
def fullRateHasData (c : Chan w) : Expr 1 :=
  .not (.eq c.fullRateCount (.lit 0))
def fullRateData (c : Chan w) : Expr w := .reg w c.sinkBufferHeadName
private def fullRateIncoming (c : Chan w) : Expr 1 :=
  .and (.reg 1 c.sinkValidName) (.reg 1 c.sinkPopName)
private def fullRateCountEq (c : Chan w) (n : Nat) : Expr 1 :=
  .eq c.fullRateCount (.lit (BitVec.ofNat 2 n))

/-- Destination-local maintenance runs before application rules.  A later
`fullRateConsume` overrides these writes using the same pre-cycle state,
which implements an atomic consume-plus-arrival without exposing a
combinational ready path. -/
private def fullRateMaintenance (c : Chan w) : Act :=
  .ite c.fullRateIncoming
    (.ite (c.fullRateCountEq 0)
      (.seq (.write w c.sinkBufferHeadName (.reg w c.sinkPayloadName))
        (.seq (.write 2 c.sinkBufferCountName (.lit 1))
          (.write 1 c.sinkPopName (.lit 1))))
      (.ite (c.fullRateCountEq 1)
        (.seq (.write w c.sinkBufferTailName (.reg w c.sinkPayloadName))
          (.seq (.write 2 c.sinkBufferCountName (.lit 2))
            (.write 1 c.sinkPopName (.lit 0))))
        (.write 1 c.sinkPopName (.lit 0))))
    (.ite (c.fullRateCountEq 2)
      (.write 1 c.sinkPopName (.lit 0))
      (.write 1 c.sinkPopName (.lit 1)))

/-- Consume one presented item.  If the FIFO's previously requested item
arrives on this edge, it is folded into the post-cycle buffer in the same
destination transition. -/
def fullRateConsume (c : Chan w) : Act :=
  .ite c.fullRateHasData
    (.ite c.fullRateIncoming
      (.ite (c.fullRateCountEq 1)
        (.seq (.write w c.sinkBufferHeadName (.reg w c.sinkPayloadName))
          (.seq (.write 2 c.sinkBufferCountName (.lit 1))
            (.write 1 c.sinkPopName (.lit 1))))
        (.seq (.write w c.sinkBufferHeadName (.reg w c.sinkBufferTailName))
          (.seq (.write w c.sinkBufferTailName (.reg w c.sinkPayloadName))
            (.seq (.write 2 c.sinkBufferCountName (.lit 2))
              (.write 1 c.sinkPopName (.lit 0))))))
      (.ite (c.fullRateCountEq 1)
        (.seq (.write 2 c.sinkBufferCountName (.lit 0))
          (.write 1 c.sinkPopName (.lit 1)))
        (.seq (.write w c.sinkBufferHeadName (.reg w c.sinkBufferTailName))
          (.seq (.write 2 c.sinkBufferCountName (.lit 1))
            (.write 1 c.sinkPopName (.lit 1))))))
    .skip

/-- Add the proved, destination-local two-entry presentation endpoint.  Its
pop request starts asserted so the FIFO may present the first item without an
extra application round trip. -/
def withFullRateSink (c : Chan w) (d : Design) : Design where
  name := d.name
  regs :=
    ⟨c.sinkPopName, 1, 1⟩ ::
    ⟨c.sinkBufferCountName, 2, 0⟩ ::
    ⟨c.sinkBufferHeadName, w, 0⟩ ::
    ⟨c.sinkBufferTailName, w, 0⟩ :: d.regs
  mems := d.mems
  inputs := ⟨c.sinkValidName, 1⟩ :: ⟨c.sinkPayloadName, w⟩ :: d.inputs
  rules := ⟨c.stem ++ "full_rate_sink_maintenance", c.fullRateMaintenance⟩ :: d.rules
  ackMemInit := d.ackMemInit
  syncReadMems := d.syncReadMems
  outputs := [c.sinkPopName] ++ d.outputs
  combOutputs := d.combOutputs

/-- Fail-closed structural identity for the generated full-rate presentation
endpoint.  Timing metadata uses this complete shape rather than inferring a
one-tick contract from one reserved register name.  The ordinary constructor
above supplies the shape; expert assembly must supply it exactly. -/
def hasFullRateSinkShape (c : Chan w) (d : Design) : Bool :=
  let hasReg (name : String) (width init : Nat) := d.regs.any fun reg =>
    reg.name == name && reg.width == width && reg.init.toNat == init
  hasReg c.sinkPopName 1 1 &&
    hasReg c.sinkBufferCountName 2 0 &&
    hasReg c.sinkBufferHeadName w 0 &&
    hasReg c.sinkBufferTailName w 0 &&
    (d.rules.filter fun rule =>
      rule.name == c.stem ++ "full_rate_sink_maintenance").length == 1

/-- The generated maintenance-plus-consume actions implement the abstract
steady-state exchange for arbitrary payloads: the old head is replaced by the
new FIFO value, occupancy remains one, and the next pop stays issued.  This is
the action-level bridge from `fullRateBuffer_onePerTick` to actual `Design`
semantics; compiler correctness then carries the same transition to emitted
RTL semantics. -/
theorem fullRateActions_onePerTick (c : Chan w) (head next : BitVec w)
    (state : St)
    (count : state.regs c.sinkBufferCountName 2 = 1#2)
    (oldHead : state.regs c.sinkBufferHeadName w = head)
    (pending : state.regs c.sinkPopName 1 = 1#1)
    (valid : state.regs c.sinkValidName 1 = 1#1)
    (payload : state.regs c.sinkPayloadName w = next) :
    let afterMaintenance := c.fullRateMaintenance.run state state
    let afterConsume := c.fullRateConsume.run state afterMaintenance
    c.fullRateData.eval state = head ∧
      afterConsume.regs c.sinkBufferCountName 2 = 1#2 ∧
      afterConsume.regs c.sinkBufferHeadName w = next ∧
      afterConsume.regs c.sinkPopName 1 = 1#1 := by
  have head_ne_pop : c.sinkBufferHeadName ≠ c.sinkPopName := by
    intro equal
    have chars := congrArg String.toList equal
    simp [sinkBufferHeadName, sinkPopName, stem] at chars
    have different : "dst_buffer_head".toList ≠ "dst_pop".toList := by decide
    exact different chars
  have head_ne_count : c.sinkBufferHeadName ≠ c.sinkBufferCountName := by
    intro equal
    have chars := congrArg String.toList equal
    simp [sinkBufferHeadName, sinkBufferCountName, stem] at chars
    have different : "dst_buffer_head".toList ≠ "dst_buffer_count".toList := by decide
    exact different chars
  simp [fullRateMaintenance, fullRateConsume, fullRateHasData, fullRateIncoming,
    fullRateCountEq, fullRateCount, fullRateData, Expr.eval, Act.run, count,
    oldHead, pending, valid, payload]
  simp [RegEnv.set, head_ne_pop, head_ne_count]

def count (c : Chan w) : Expr c.countWidth :=
  .reg c.countWidth c.countName
def head (c : Chan w) : Expr c.indexWidth :=
  .reg c.indexWidth c.headName
def tail (c : Chan w) : Expr c.indexWidth :=
  .reg c.indexWidth c.tailName
def nonempty (c : Chan w) : Expr 1 := .not (.eq c.count (.lit 0))
def hasSpace (c : Chan w) : Expr 1 :=
  .ult c.count (.lit (BitVec.ofNat c.countWidth c.depth))
private def inputPush (c : Chan w) : Expr 1 := .reg 1 c.pushName
private def inputPayload (c : Chan w) : Expr w := .reg w c.pushPayloadName
private def inputPop (c : Chan w) : Expr 1 := .reg 1 c.popName
private def popAccepted (c : Chan w) : Expr 1 := .and c.inputPop c.nonempty
private def pushAccepted (c : Chan w) : Expr 1 :=
  let exchange : Expr 1 := match c.policy with
    | .refusePush => .lit 0
    | .exchange => c.popAccepted
  .and c.inputPush (.or c.hasSpace exchange)

private def advanceIndex (c : Chan w) (value : Expr c.indexWidth) : Expr c.indexWidth :=
  .urem (.add value (.lit 1)) (.lit (BitVec.ofNat c.indexWidth c.depth))

/-- Stock bounded synchronous FIFO, expressed entirely as an ordinary Design.
It is the Phase-1 implementation and the aligned-clock reference refined by
later CDC realizations. -/
def adapter (c : Chan w) : Design where
  name := c.stem ++ "adapter"
  regs := [⟨c.countName, c.countWidth, 0⟩,
    ⟨c.headName, c.indexWidth, 0⟩,
    ⟨c.tailName, c.indexWidth, 0⟩,
    ⟨c.acceptedName, 1, 0⟩,
    ⟨c.deliveredName, 1, 0⟩]
  mems := [⟨c.memoryName, c.indexWidth, w, fun _ => 0⟩]
  inputs := [⟨c.pushName, 1⟩, ⟨c.pushPayloadName, w⟩, ⟨c.popName, 1⟩]
  rules := [⟨c.stem ++ "fifo_step",
    .seq (.write 1 c.acceptedName (.lit 0)) <|
    .seq (.write 1 c.deliveredName (.lit 0)) <|
    .seq (.ite c.popAccepted
      (.seq (.write 1 c.deliveredName (.lit 1))
        (.write c.indexWidth c.headName (c.advanceIndex c.head))) .skip) <|
    .seq (.ite c.pushAccepted
      (.seq (.memWrite c.indexWidth w c.memoryName 0 c.tail c.inputPayload)
        (.seq (.write c.indexWidth c.tailName (c.advanceIndex c.tail))
          (.write 1 c.acceptedName (.lit 1)))) .skip) <|
    .ite c.pushAccepted
      (.ite c.popAccepted .skip
        (.write c.countWidth c.countName (.add c.count (.lit 1))))
      (.ite c.popAccepted
        (.write c.countWidth c.countName (.sub c.count (.lit 1))) .skip)⟩]
  syncReadMems := []
  outputs := []

def adapterPayload (c : Chan w) : Expr w :=
  .memRead w c.memoryName c.head
def adapterValid (c : Chan w) : Expr 1 := c.nonempty
def adapterReady (c : Chan w) (sinkPop : Expr 1) : Expr 1 :=
  match c.policy with
  | .refusePush => c.hasSpace
  | .exchange => .or c.hasSpace (.and sinkPop c.nonempty)

/-- Compiler-facing same-clock realization. It is the proved `adapter` with
three combinational observations added; `combOutputs` do not alter cycle
semantics. This keeps the synchronous physical binding on the ordinary
proved compiler path instead of introducing handwritten FIFO RTL. -/
def physicalAdapter (c : Chan w) : Design :=
  { c.adapter with
    name := c.stem ++ "sync_adapter"
    combOutputs :=
      [ ⟨"source_ready", 1, c.adapterReady (.reg 1 c.popName)⟩,
        ⟨"sink_valid", 1, c.adapterValid⟩,
        ⟨"sink_payload", w, c.adapterPayload⟩ ] }

@[simp] theorem physicalAdapter_cycleOpen (c : Chan w) (inputs : InEnv)
    (state : St) :
    c.physicalAdapter.cycleOpen inputs state = c.adapter.cycleOpen inputs state :=
  rfl

@[simp] theorem physicalAdapter_reset (c : Chan w) :
    c.physicalAdapter.reset = c.adapter.reset := rfl

/-- Expert/runner input for the stock adapter. Ordinary users enqueue/pop
through endpoints; tests and schedule replay drive the same concrete Design. -/
def drive (c : Chan w) (push : Option (BitVec w)) (pop : Bool) : InEnv :=
  fun name width =>
    if name = c.pushName then
      if h : width = 1 then h.symm ▸ (if push.isSome then 1#1 else 0#1)
      else 0
    else if name = c.pushPayloadName then
      if h : width = w then h.symm ▸ push.getD 0 else 0
    else if name = c.popName then
      if h : width = 1 then h.symm ▸ (if pop then 1#1 else 0#1)
      else 0
    else 0

/-! ## Generated synchronous-adapter refinement -/

/-- State presented to the generated adapter at an edge, after its declared
inputs have been driven from one abstract event. -/
def drivenState (c : Chan w) (state : St) (event : Event w) : St :=
  state.setInputs c.adapter.inputs (c.drive event.push event.pop)

@[simp] theorem mems_drivenState (c : Chan w) (state : St) (event : Event w) :
    (c.drivenState state event).mems = state.mems := rfl

private theorem append_ne_of_length_ne (base left right : String)
    (different : left.length ≠ right.length) :
    base ++ left ≠ base ++ right := by
  intro equal
  have lengths := congrArg String.length equal
  simp only [String.length_append] at lengths
  omega

private theorem append_ne_of_ne (base left right : String)
    (different : left ≠ right) : base ++ left ≠ base ++ right := by
  intro equal
  have lists := congrArg String.toList equal
  simp only [String.toList_append] at lists
  exact different (String.toList_inj.mp ((List.append_right_inj base.toList).mp lists))

@[simp] theorem pushName_ne_payloadName (c : Chan w) :
    c.pushName ≠ c.pushPayloadName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem pushName_ne_popName (c : Chan w) :
    c.pushName ≠ c.popName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem payloadName_ne_popName (c : Chan w) :
    c.pushPayloadName ≠ c.popName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem payloadName_ne_pushName (c : Chan w) :
    c.pushPayloadName ≠ c.pushName := (c.pushName_ne_payloadName).symm

@[simp] theorem popName_ne_pushName (c : Chan w) :
    c.popName ≠ c.pushName := (c.pushName_ne_popName).symm

@[simp] theorem popName_ne_payloadName (c : Chan w) :
    c.popName ≠ c.pushPayloadName := (c.payloadName_ne_popName).symm

@[simp] theorem acceptedName_ne_deliveredName (c : Chan w) :
    c.acceptedName ≠ c.deliveredName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem acceptedName_ne_countName (c : Chan w) :
    c.acceptedName ≠ c.countName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem acceptedName_ne_headName (c : Chan w) :
    c.acceptedName ≠ c.headName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem acceptedName_ne_tailName (c : Chan w) :
    c.acceptedName ≠ c.tailName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem deliveredName_ne_countName (c : Chan w) :
    c.deliveredName ≠ c.countName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem deliveredName_ne_headName (c : Chan w) :
    c.deliveredName ≠ c.headName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem deliveredName_ne_tailName (c : Chan w) :
    c.deliveredName ≠ c.tailName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem deliveredName_ne_acceptedName (c : Chan w) :
    c.deliveredName ≠ c.acceptedName := (c.acceptedName_ne_deliveredName).symm

@[simp] theorem countName_ne_acceptedName (c : Chan w) :
    c.countName ≠ c.acceptedName := (c.acceptedName_ne_countName).symm

@[simp] theorem headName_ne_acceptedName (c : Chan w) :
    c.headName ≠ c.acceptedName := (c.acceptedName_ne_headName).symm

@[simp] theorem tailName_ne_acceptedName (c : Chan w) :
    c.tailName ≠ c.acceptedName := (c.acceptedName_ne_tailName).symm

@[simp] theorem countName_ne_deliveredName (c : Chan w) :
    c.countName ≠ c.deliveredName := (c.deliveredName_ne_countName).symm

@[simp] theorem headName_ne_deliveredName (c : Chan w) :
    c.headName ≠ c.deliveredName := (c.deliveredName_ne_headName).symm

@[simp] theorem tailName_ne_deliveredName (c : Chan w) :
    c.tailName ≠ c.deliveredName := (c.deliveredName_ne_tailName).symm

@[simp] theorem countName_ne_headName (c : Chan w) :
    c.countName ≠ c.headName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem countName_ne_tailName (c : Chan w) :
    c.countName ≠ c.tailName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem headName_ne_countName (c : Chan w) :
    c.headName ≠ c.countName := (c.countName_ne_headName).symm

@[simp] theorem tailName_ne_countName (c : Chan w) :
    c.tailName ≠ c.countName := (c.countName_ne_tailName).symm

@[simp] theorem countName_ne_pushName (c : Chan w) :
    c.countName ≠ c.pushName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem countName_ne_payloadName (c : Chan w) :
    c.countName ≠ c.pushPayloadName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem countName_ne_popName (c : Chan w) :
    c.countName ≠ c.popName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem headName_ne_pushName (c : Chan w) :
    c.headName ≠ c.pushName := by
  apply append_ne_of_ne c.stem
  decide

@[simp] theorem headName_ne_payloadName (c : Chan w) :
    c.headName ≠ c.pushPayloadName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem headName_ne_popName (c : Chan w) :
    c.headName ≠ c.popName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem tailName_ne_pushName (c : Chan w) :
    c.tailName ≠ c.pushName := by
  apply append_ne_of_ne c.stem
  decide

@[simp] theorem tailName_ne_payloadName (c : Chan w) :
    c.tailName ≠ c.pushPayloadName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem tailName_ne_popName (c : Chan w) :
    c.tailName ≠ c.popName := by
  apply append_ne_of_length_ne c.stem
  decide

@[simp] theorem headName_ne_tailName (c : Chan w) :
    c.headName ≠ c.tailName := by
  apply append_ne_of_ne c.stem
  decide

@[simp] theorem tailName_ne_headName (c : Chan w) :
    c.tailName ≠ c.headName := (c.headName_ne_tailName).symm

@[simp] theorem inputPush_drivenState (c : Chan w) (state : St) (event : Event w) :
    c.inputPush.eval (c.drivenState state event) =
      (if event.push.isSome then 1#1 else 0#1) := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases push <;> cases pop <;>
    simp [drivenState, adapter, drive, inputPush, Expr.eval, St.setInputs,
      RegEnv.set]

@[simp] theorem inputPayload_drivenState (c : Chan w) (state : St)
    (event : Event w) :
    c.inputPayload.eval (c.drivenState state event) = event.push.getD 0 := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases push <;> cases pop <;>
    simp [drivenState, adapter, drive, inputPayload, Expr.eval, St.setInputs,
      RegEnv.set]

@[simp] theorem inputPop_drivenState (c : Chan w) (state : St) (event : Event w) :
    c.inputPop.eval (c.drivenState state event) =
      (if event.pop then 1#1 else 0#1) := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases push <;> cases pop <;>
    simp [drivenState, adapter, drive, inputPop, Expr.eval, St.setInputs,
      RegEnv.set]

@[simp] theorem count_drivenState (c : Chan w) (state : St) (event : Event w) :
    c.count.eval (c.drivenState state event) = c.count.eval state := by
  simp [drivenState, adapter, count, Expr.eval, St.setInputs, RegEnv.set]

@[simp] theorem head_drivenState (c : Chan w) (state : St) (event : Event w) :
    c.head.eval (c.drivenState state event) = c.head.eval state := by
  simp [drivenState, adapter, head, Expr.eval, St.setInputs, RegEnv.set]

@[simp] theorem tail_drivenState (c : Chan w) (state : St) (event : Event w) :
    c.tail.eval (c.drivenState state event) = c.tail.eval state := by
  simp [drivenState, adapter, tail, Expr.eval, St.setInputs, RegEnv.set]

def boolBit (value : Bool) : BitVec 1 := if value then 1#1 else 0#1

def ringSlot (c : Chan w) (state : St) (offset : Nat) : BitVec w :=
  state.mems c.memoryName
    (((c.head.eval state).toNat + offset) % c.depth) w

private theorem mod_add_mod_left (a b modulus : Nat) :
    (a % modulus + b) % modulus = (a + b) % modulus := by
  simp only [Nat.add_mod, Nat.mod_mod]

/-- Circular-buffer offsets smaller than the depth name distinct slots even
after adding and reducing the same head pointer. -/
private theorem ringOffset_injective {head left right depth : Nat}
    (leftBound : left < depth) (rightBound : right < depth)
    (equal : (head + left) % depth = (head + right) % depth) :
    left = right := by
  have shifted : head + left ≡ head + right [MOD depth] := equal
  have offsets : left ≡ right [MOD depth] :=
    Nat.ModEq.add_left_cancel' head shifted
  exact offsets.eq_of_lt_of_lt leftBound rightBound

/-- A positive live offset before the tail cannot alias the tail slot, even
when a full ring represents its tail at offset zero. -/
private theorem ringOffset_ne_tail {head offset length depth : Nat}
    (offsetPositive : 0 < offset) (offsetBeforeTail : offset < length)
    (lengthBound : length ≤ depth) :
    (head + offset) % depth ≠ (head + length) % depth := by
  intro equal
  have shifted : head + offset ≡ head + length [MOD depth] := equal
  have offsets : offset ≡ length [MOD depth] :=
    Nat.ModEq.add_left_cancel' head shifted
  by_cases short : length < depth
  · have := offsets.eq_of_lt_of_lt (by omega) short
    omega
  · have fills : length = depth := by omega
    unfold Nat.ModEq at offsets
    rw [Nat.mod_eq_of_lt (by omega), fills, Nat.mod_self] at offsets
    omega

@[simp] theorem ringSlot_drivenState (c : Chan w) (state : St)
    (event : Event w) (offset : Nat) :
    c.ringSlot (c.drivenState state event) offset = c.ringSlot state offset := by
  unfold ringSlot
  change state.mems c.memoryName
      (((c.head.eval (c.drivenState state event)).toNat + offset) % c.depth) _ = _
  rw [head_drivenState]

/-- Full circular-buffer representation used by the state-preservation proof.
It relates every live memory slot, not only the currently visible payload. -/
structure AdapterRep (c : Chan w) (queue : State w) (state : St) : Prop where
  positiveDepth : 0 < c.depth
  bounded : queue.length ≤ c.depth
  countEq : (c.count.eval state).toNat = queue.length
  headBound : (c.head.eval state).toNat < c.depth
  tailEq : (c.tail.eval state).toNat =
    ((c.head.eval state).toNat + queue.length) % c.depth
  storage : ∀ (offset : Nat) (present : offset < queue.length),
    c.ringSlot state offset = queue[offset]

/-- Driving declared inputs does not disturb the ring-buffer representation. -/
theorem AdapterRep.driven {c : Chan w} {queue : State w} {state : St}
    (rep : AdapterRep c queue state) (event : Event w) :
    AdapterRep c queue (c.drivenState state event) where
  positiveDepth := rep.positiveDepth
  bounded := rep.bounded
  countEq := by simpa using rep.countEq
  headBound := by simpa using rep.headBound
  tailEq := by simpa using rep.tailEq
  storage := by
    intro offset present
    simpa using rep.storage offset present

/-- Reset establishes the full empty-ring representation. -/
theorem adapterRep_reset (c : Chan w) (positiveDepth : 0 < c.depth) :
    AdapterRep c [] c.adapter.reset where
  positiveDepth := positiveDepth
  bounded := by simp
  countEq := by
    simp [count, adapter, Design.reset, Expr.eval, RegEnv.set]
  headBound := by
    simp [head, adapter, Design.reset, Expr.eval, RegEnv.set, positiveDepth]
  tailEq := by
    simp [tail, head, adapter, Design.reset, Expr.eval, RegEnv.set,
      Nat.zero_mod]
  storage := by simp

/-- The observable portion of the ring-buffer representation needed to prove
the concrete adapter's transfer decisions.  The later storage invariant adds
head/tail/memory correspondence without changing these fields. -/
structure AdapterView (c : Chan w) (queue : State w) (state : St) : Prop where
  nonempty : c.nonempty.eval state = boolBit (!queue.isEmpty)
  hasSpace : c.hasSpace.eval state = boolBit (queue.length < c.depth)
  payload : !queue.isEmpty → c.adapterPayload.eval state = queue.head?.getD 0

/-- The full ring representation entails the observable decision view. -/
theorem AdapterRep.toView {c : Chan w} {queue : State w} {state : St}
    (rep : AdapterRep c queue state) :
    AdapterView c queue state := by
  have depthFits : c.depth < 2 ^ c.countWidth := Nat.lt_log2_self
  constructor
  · cases queue with
    | nil =>
        have countZero : c.count.eval state = 0 := by
          apply BitVec.toNat_inj.mp
          simpa using rep.countEq
        simp [nonempty, Expr.eval, countZero, boolBit]
    | cons head tail =>
        have countNonzero : c.count.eval state ≠ 0 := by
          intro countZero
          have := rep.countEq
          simp [countZero] at this
        simp only [nonempty, Expr.eval]
        rw [if_neg countNonzero]
        change (~~~0#1) = 1#1
        decide
  · simp [hasSpace, Expr.eval, BitVec.ult, rep.countEq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt depthFits, boolBit]
  · intro nonemptyQueue
    have queuePositive : 0 < queue.length := by
      apply List.length_pos_iff.mpr
      intro empty
      subst queue
      simp at nonemptyQueue
    have slot := rep.storage 0 queuePositive
    simp [ringSlot, Nat.mod_eq_of_lt rep.headBound] at slot
    change state.mems c.memoryName (c.head.eval state).toNat _ =
      queue.head?.getD 0
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem queuePositive]
    simpa using slot

/-- The actual expressions executed by the generated adapter make exactly the
same push/pop decisions as `Chan.step`, assuming its observable ring-buffer
view represents the abstract queue. -/
theorem adapter_decisions_refine (c : Chan w) (queue : State w)
    (event : Event w) (state : St)
    (rep : AdapterView c queue (c.drivenState state event)) :
    c.pushAccepted.eval (c.drivenState state event) =
        boolBit (c.step queue event).accepted ∧
      c.popAccepted.eval (c.drivenState state event) =
        boolBit ((c.step queue event).delivered.isSome) := by
  rcases c with ⟨name, depth, policy⟩
  rcases event with ⟨push, pop⟩
  cases queue with
  | nil =>
      cases push <;> cases pop <;> cases policy <;>
        simp [pushAccepted, popAccepted, step, boolBit,
          Expr.eval, rep.nonempty, rep.hasSpace]
      all_goals split <;> decide
  | cons head tail =>
      cases push <;> cases pop <;> cases policy <;>
        simp [pushAccepted, popAccepted, step, boolBit,
          Expr.eval, rep.nonempty, rep.hasSpace]
      all_goals split <;> decide

/-- The generated Design records the concrete accept decision computed from
the pre-edge state.  This is a theorem about `Design.cycleOpen`, not a second
adapter model. -/
theorem adapter_cycle_accepted (c : Chan w) (state : St) (event : Event w) :
    (Expr.reg 1 c.acceptedName).eval
        (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
      c.pushAccepted.eval (c.drivenState state event) := by
  change (Expr.reg 1 c.acceptedName).eval
      (c.adapter.cycle (c.drivenState state event)) = _
  by_cases push : c.pushAccepted.eval (c.drivenState state event) = 1#1 <;>
    by_cases pop : c.popAccepted.eval (c.drivenState state event) = 1#1 <;>
      simp [Design.cycle, adapter, Act.run, push, pop, count, Expr.eval, RegEnv.set]
  all_goals exact ((bv1_cases _).resolve_right push).symm

/-- The generated Design likewise records exactly whether the old head was
delivered on this edge. -/
theorem adapter_cycle_delivered (c : Chan w) (state : St) (event : Event w) :
    (Expr.reg 1 c.deliveredName).eval
        (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
      c.popAccepted.eval (c.drivenState state event) := by
  change (Expr.reg 1 c.deliveredName).eval
      (c.adapter.cycle (c.drivenState state event)) = _
  by_cases push : c.pushAccepted.eval (c.drivenState state event) = 1#1 <;>
    by_cases pop : c.popAccepted.eval (c.drivenState state event) = 1#1 <;>
      simp [Design.cycle, adapter, Act.run, push, pop, head, Expr.eval, RegEnv.set]
  all_goals exact ((bv1_cases _).resolve_right pop).symm

theorem adapter_cycle_count (c : Chan w) (state : St) (event : Event w) :
    c.count.eval (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
      let pre := c.drivenState state event
      if c.pushAccepted.eval pre = 1#1 then
        if c.popAccepted.eval pre = 1#1 then c.count.eval pre
        else c.count.eval pre + 1
      else if c.popAccepted.eval pre = 1#1 then c.count.eval pre - 1
      else c.count.eval pre := by
  change c.count.eval (c.adapter.cycle (c.drivenState state event)) = _
  by_cases push : c.pushAccepted.eval (c.drivenState state event) = 1#1 <;>
    by_cases pop : c.popAccepted.eval (c.drivenState state event) = 1#1 <;>
      simp [Design.cycle, adapter, Act.run, push, pop, count, Expr.eval, RegEnv.set]

/-- Concrete occupancy after one generated adapter edge is exactly abstract
queue occupancy after the corresponding channel event. -/
theorem adapter_cycle_count_refines (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    (c.count.eval
      (c.adapter.cycleOpen (c.drive event.push event.pop) state)).toNat =
        (c.step queue event).state.length := by
  have decisions := c.adapter_decisions_refine queue event state (rep.driven event).toView
  have lengthEq := c.step_length queue event
  have nextBound := c.noOverflow queue event rep.bounded
  have depthFits : c.depth < 2 ^ c.countWidth := Nat.lt_log2_self
  rw [c.adapter_cycle_count state event]
  dsimp only
  rw [decisions.1, decisions.2]
  cases accepted : (c.step queue event).accepted <;>
    cases delivered : (c.step queue event).delivered.isSome
  · simp [accepted, delivered, boolBit] at lengthEq ⊢
    exact rep.countEq.trans lengthEq.symm
  · have queuePositive := c.nonempty_of_delivered queue event delivered
    simp [accepted, delivered, boolBit] at lengthEq ⊢
    have oneLt : 1 < 2 ^ c.countWidth := by
      have positive := Nat.two_pow_pos (Nat.log2 c.depth)
      change 1 < 2 ^ (Nat.log2 c.depth + 1)
      rw [Nat.pow_succ]
      omega
    rw [Nat.mod_eq_of_lt oneLt, rep.countEq]
    have rearrange :
        2 ^ c.countWidth - 1 + queue.length =
          2 ^ c.countWidth + (queue.length - 1) := by omega
    rw [rearrange, Nat.add_mod]
    simp only [Nat.mod_self, Nat.zero_add]
    have remainLt : queue.length - 1 < 2 ^ c.countWidth := by omega
    simpa [Nat.mod_eq_of_lt remainLt] using lengthEq.symm
  · simp [accepted, delivered, boolBit] at lengthEq ⊢
    rw [rep.countEq]
    rw [Nat.mod_eq_of_lt]
    · omega
    · omega
  · have queuePositive := c.nonempty_of_delivered queue event delivered
    simp [accepted, delivered, boolBit] at lengthEq ⊢
    rw [rep.countEq]
    omega

theorem advanceIndex_toNat (c : Chan w) (state : St) (value : Expr c.indexWidth)
    (positiveDepth : 0 < c.depth)
    (bounded : (value.eval state).toNat < c.depth) :
    ((c.advanceIndex value).eval state).toNat =
      ((value.eval state).toNat + 1) % c.depth := by
  have depthLe : c.depth ≤ 2 ^ c.indexWidth := by
    unfold indexWidth
    have logarithm := Nat.lt_log2_self (n := c.depth - 1)
    omega
  simp only [advanceIndex, Expr.eval, BitVec.toNat_umod, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  have oneNat : (1#c.indexWidth).toNat = 1 :=
    BitVec.toNat_one (by unfold indexWidth; omega)
  change (((value.eval state).toNat + (1#c.indexWidth).toNat) %
      2 ^ c.indexWidth) % (c.depth % 2 ^ c.indexWidth) = _
  rw [oneNat]
  by_cases fills : c.depth = 2 ^ c.indexWidth
  · simp [fills]
  · have depthLt : c.depth < 2 ^ c.indexWidth := by omega
    rw [Nat.mod_eq_of_lt depthLt]
    rw [Nat.mod_eq_of_lt (show (value.eval state).toNat + 1 <
      2 ^ c.indexWidth by omega)]

theorem adapter_cycle_head (c : Chan w) (state : St) (event : Event w) :
    c.head.eval (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
      let pre := c.drivenState state event
      if c.popAccepted.eval pre = 1#1 then c.advanceIndex c.head |>.eval pre
      else c.head.eval pre := by
  change c.head.eval (c.adapter.cycle (c.drivenState state event)) = _
  by_cases push : c.pushAccepted.eval (c.drivenState state event) = 1#1 <;>
    by_cases pop : c.popAccepted.eval (c.drivenState state event) = 1#1 <;>
      simp [Design.cycle, adapter, Act.run, push, pop, head, Expr.eval, RegEnv.set]

/-- The concrete read pointer advances exactly when the abstract event
delivers the old queue head. -/
theorem adapter_cycle_head_refines (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    (c.head.eval
      (c.adapter.cycleOpen (c.drive event.push event.pop) state)).toNat =
        if (c.step queue event).delivered.isSome then
          ((c.head.eval state).toNat + 1) % c.depth
        else (c.head.eval state).toNat := by
  have decisions := c.adapter_decisions_refine queue event state (rep.driven event).toView
  rw [c.adapter_cycle_head state event]
  dsimp only
  rw [decisions.2]
  cases delivered : (c.step queue event).delivered.isSome
  · simp [boolBit]
  · simpa [boolBit] using
      c.advanceIndex_toNat (c.drivenState state event) c.head
        rep.positiveDepth (by simpa using rep.headBound)

theorem adapter_cycle_tail (c : Chan w) (state : St) (event : Event w) :
    c.tail.eval (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
      let pre := c.drivenState state event
      if c.pushAccepted.eval pre = 1#1 then c.advanceIndex c.tail |>.eval pre
      else c.tail.eval pre := by
  change c.tail.eval (c.adapter.cycle (c.drivenState state event)) = _
  by_cases push : c.pushAccepted.eval (c.drivenState state event) = 1#1 <;>
    by_cases pop : c.popAccepted.eval (c.drivenState state event) = 1#1 <;>
      simp [Design.cycle, adapter, Act.run, push, pop, tail, Expr.eval, RegEnv.set]

/-- The concrete write pointer advances exactly when the abstract channel
accepts a payload. -/
theorem adapter_cycle_tail_refines (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    (c.tail.eval
      (c.adapter.cycleOpen (c.drive event.push event.pop) state)).toNat =
        if (c.step queue event).accepted then
          ((c.tail.eval state).toNat + 1) % c.depth
        else (c.tail.eval state).toNat := by
  have decisions := c.adapter_decisions_refine queue event state (rep.driven event).toView
  rw [c.adapter_cycle_tail state event]
  dsimp only
  rw [decisions.1]
  cases accepted : (c.step queue event).accepted
  · simp [boolBit]
  · simpa [boolBit] using
      c.advanceIndex_toNat (c.drivenState state event) c.tail
        rep.positiveDepth (by
          simpa using show (c.tail.eval state).toNat < c.depth from by
            rw [rep.tailEq]
            exact Nat.mod_lt _ rep.positiveDepth)

/-- Concrete head/tail coordinates continue to delimit exactly the abstract
next queue. -/
theorem adapter_cycle_tail_relation (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    (c.tail.eval
      (c.adapter.cycleOpen (c.drive event.push event.pop) state)).toNat =
      ((c.head.eval
          (c.adapter.cycleOpen (c.drive event.push event.pop) state)).toNat +
        (c.step queue event).state.length) % c.depth := by
  rw [c.adapter_cycle_tail_refines queue event state rep]
  rw [c.adapter_cycle_head_refines queue event state rep]
  have lengthEq := c.step_length queue event
  cases accepted : (c.step queue event).accepted <;>
    cases delivered : (c.step queue event).delivered.isSome
  · simp [accepted, delivered] at lengthEq ⊢
    simpa [lengthEq] using rep.tailEq
  · have queuePositive := c.nonempty_of_delivered queue event delivered
    simp [accepted, delivered] at lengthEq ⊢
    rw [lengthEq, rep.tailEq]
    congr 1
    omega
  · simp [accepted, delivered] at lengthEq ⊢
    rw [lengthEq, rep.tailEq, mod_add_mod_left]
    exact congrArg (fun value => value % c.depth) (by omega)
  · have queuePositive := c.nonempty_of_delivered queue event delivered
    simp [accepted, delivered] at lengthEq ⊢
    rw [lengthEq, rep.tailEq, mod_add_mod_left]
    congr 1
    omega

theorem adapter_cycle_storage (c : Chan w) (state : St) (event : Event w)
    (address : Nat) :
    (c.adapter.cycleOpen (c.drive event.push event.pop) state).mems
        c.memoryName address w =
      let pre := c.drivenState state event
      if c.pushAccepted.eval pre = 1#1 ∧ address = (c.tail.eval pre).toNat then
        c.inputPayload.eval pre
      else pre.mems c.memoryName address w := by
  change (c.adapter.cycle (c.drivenState state event)).mems
      c.memoryName address w = _
  by_cases push : c.pushAccepted.eval (c.drivenState state event) = 1#1 <;>
    by_cases pop : c.popAccepted.eval (c.drivenState state event) = 1#1 <;>
      by_cases atTail : address =
        (c.tail.eval (c.drivenState state event)).toNat <;>
        simp [Design.cycle, adapter, Act.run, push, pop, atTail, MemEnv.set]

/-- Slot-level form of the concrete memory update, expressed solely in terms
of the abstract accept/deliver decisions and the pre-edge ring coordinates. -/
theorem adapter_cycle_ringSlot (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state)
    (offset : Nat) :
    let nextHead := if (c.step queue event).delivered.isSome then
      ((c.head.eval state).toNat + 1) % c.depth
    else (c.head.eval state).toNat
    c.ringSlot
        (c.adapter.cycleOpen (c.drive event.push event.pop) state) offset =
      if (c.step queue event).accepted ∧
          (nextHead + offset) % c.depth = (c.tail.eval state).toNat then
        event.push.getD 0
      else state.mems c.memoryName ((nextHead + offset) % c.depth) w := by
  dsimp only
  unfold ringSlot
  rw [c.adapter_cycle_head_refines queue event state rep]
  rw [c.adapter_cycle_storage state event]
  dsimp only
  have decisions := c.adapter_decisions_refine queue event state (rep.driven event).toView
  rw [decisions.1]
  rw [c.tail_drivenState state event, c.inputPayload_drivenState state event]
  simp [boolBit]

/-- Every live concrete circular-buffer slot represents the corresponding
element of the abstract next queue after one generated adapter edge. -/
theorem adapter_cycle_storage_refines (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    ∀ (offset : Nat) (present : offset < (c.step queue event).state.length),
      c.ringSlot
          (c.adapter.cycleOpen (c.drive event.push event.pop) state) offset =
        (c.step queue event).state[offset] := by
  intro offset present
  have stateEq := c.step_state queue event
  have nextBound := c.noOverflow queue event rep.bounded
  rw [c.adapter_cycle_ringSlot queue event state rep offset]
  cases accepted : (c.step queue event).accepted <;>
    cases delivered : (c.step queue event).delivered.isSome
  · simp [stateEq, accepted, delivered] at present ⊢
    exact rep.storage offset present
  · have queuePositive := c.nonempty_of_delivered queue event delivered
    cases queue with
    | nil => simp at queuePositive
    | cons first rest =>
        simp [stateEq, accepted, delivered] at present ⊢
        have oldPresent : offset + 1 < (first :: rest).length := by simp; omega
        have addressEq :
            ((c.head.eval state).toNat + 1 + offset) % c.depth =
              ((c.head.eval state).toNat + (offset + 1)) % c.depth := by
          exact congrArg (fun value => value % c.depth) (by omega)
        rw [addressEq]
        simpa [ringSlot] using rep.storage (offset + 1) oldPresent
  · simp [stateEq, accepted, delivered] at present nextBound ⊢
    have room : queue.length < c.depth := by omega
    by_cases old : offset < queue.length
    · have noOverwrite :
          ((c.head.eval state).toNat + offset) % c.depth ≠
            (c.tail.eval state).toNat := by
        rw [rep.tailEq]
        intro equal
        have same := ringOffset_injective
          (head := (c.head.eval state).toNat) (left := offset)
          (right := queue.length) (depth := c.depth) (by omega) room equal
        omega
      rw [if_neg (by simpa using noOverwrite)]
      simpa [List.getElem_append_left old, ringSlot] using rep.storage offset old
    · have last : offset = queue.length := by omega
      subst offset
      simp [rep.tailEq]
  · have queuePositive := c.nonempty_of_delivered queue event delivered
    simp [stateEq, accepted, delivered] at present nextBound ⊢
    by_cases old : offset < queue.length - 1
    · have originalPresent : offset + 1 < queue.length := by omega
      have addressEq :
          ((c.head.eval state).toNat + 1 + offset) % c.depth =
            ((c.head.eval state).toNat + (offset + 1)) % c.depth := by
        exact congrArg (fun value => value % c.depth) (by omega)
      have noOverwrite :
          ((c.head.eval state).toNat + (offset + 1)) % c.depth ≠
            (c.tail.eval state).toNat := by
        rw [rep.tailEq]
        exact ringOffset_ne_tail (by omega) originalPresent rep.bounded
      rw [addressEq, if_neg (by simpa using noOverwrite)]
      cases queue with
      | nil => simp at queuePositive
      | cons first rest =>
          simpa [List.getElem_append_left old, ringSlot] using
            rep.storage (offset + 1) originalPresent
    · have last : offset = queue.length - 1 := by omega
      subst offset
      have addressEq :
          ((c.head.eval state).toNat + 1 +
              (queue.length - 1)) % c.depth =
            ((c.head.eval state).toNat + queue.length) % c.depth := by
        exact congrArg (fun value => value % c.depth) (by omega)
      rw [addressEq]
      simp [rep.tailEq]

/-- The full circular-buffer representation is a forward simulation: one
actual generated `Design` edge preserves it against one abstract `Chan.step`.
-/
theorem AdapterRep.step {c : Chan w} {queue : State w} {state : St}
    (rep : AdapterRep c queue state) (event : Event w) :
    AdapterRep c (c.step queue event).state
      (c.adapter.cycleOpen (c.drive event.push event.pop) state) where
  positiveDepth := rep.positiveDepth
  bounded := c.noOverflow queue event rep.bounded
  countEq := c.adapter_cycle_count_refines queue event state rep
  headBound := by
    rw [c.adapter_cycle_head_refines queue event state rep]
    split
    · exact Nat.mod_lt _ rep.positiveDepth
    · exact rep.headBound
  tailEq := c.adapter_cycle_tail_relation queue event state rep
  storage := c.adapter_cycle_storage_refines queue event state rep

/-- One generated adapter edge and one abstract queue event have identical
accept/deliver observations. -/
theorem adapter_transfer_refines (c : Chan w) (queue : State w)
    (event : Event w) (state : St)
    (rep : AdapterView c queue (c.drivenState state event)) :
    (Expr.reg 1 c.acceptedName).eval
          (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
        boolBit (c.step queue event).accepted ∧
      (Expr.reg 1 c.deliveredName).eval
          (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
        boolBit ((c.step queue event).delivered.isSome) := by
  rw [c.adapter_cycle_accepted state event, c.adapter_cycle_delivered state event]
  exact c.adapter_decisions_refine queue event state rep

theorem adapter_transfer_refines_of_rep (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    (Expr.reg 1 c.acceptedName).eval
          (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
        boolBit (c.step queue event).accepted ∧
      (Expr.reg 1 c.deliveredName).eval
          (c.adapter.cycleOpen (c.drive event.push event.pop) state) =
        boolBit ((c.step queue event).delivered.isSome) :=
      c.adapter_transfer_refines queue event state (rep.driven event).toView

def adapterAcceptedValues (c : Chan w) (state : St) (event : Event w) :
    List (BitVec w) :=
  let next := c.adapter.cycleOpen (c.drive event.push event.pop) state
  if (Expr.reg 1 c.acceptedName).eval next = 1#1 then event.push.toList else []

def adapterDeliveredValues (c : Chan w) (state : St) (event : Event w) :
    List (BitVec w) :=
  let next := c.adapter.cycleOpen (c.drive event.push event.pop) state
  if (Expr.reg 1 c.deliveredName).eval next = 1#1 then
    [c.adapterPayload.eval state]
  else []

theorem adapterAcceptedValues_refine (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    c.adapterAcceptedValues state event = c.acceptedValues queue event := by
  have transfer := c.adapter_transfer_refines_of_rep queue event state rep
  unfold adapterAcceptedValues acceptedValues
  dsimp only
  rw [transfer.1]
  cases accepted : (c.step queue event).accepted <;> simp [boolBit]

theorem adapterDeliveredValues_refine (c : Chan w) (queue : State w)
    (event : Event w) (state : St) (rep : AdapterRep c queue state) :
    c.adapterDeliveredValues state event = c.deliveredValues queue event := by
  have transfer := c.adapter_transfer_refines_of_rep queue event state rep
  unfold adapterDeliveredValues deliveredValues
  dsimp only
  rw [transfer.2]
  cases delivered : (c.step queue event).delivered with
  | none => simp [boolBit]
  | some value =>
      have deliveredSome : (c.step queue event).delivered = some value := delivered
      have headEq := c.fifoOrder queue event value deliveredSome
      have nonempty : !queue.isEmpty := by
        cases queue with
        | nil => simp [step] at delivered
        | cons head tail => simp
      have payload := rep.toView.payload nonempty
      simp [boolBit, payload, headEq]

structure AdapterTraceResult (width : Nat) where
  state : St
  accepted : List (BitVec width)
  delivered : List (BitVec width)

/-- Execute the actual generated synchronous adapter while recording its
observable transfer trace. -/
def runAdapter (c : Chan w) : St → List (Event w) → AdapterTraceResult w
  | state, [] => ⟨state, [], []⟩
  | state, event :: rest =>
      let next := c.adapter.cycleOpen (c.drive event.push event.pop) state
      let later := c.runAdapter next rest
      ⟨later.state, c.adapterAcceptedValues state event ++ later.accepted,
        c.adapterDeliveredValues state event ++ later.delivered⟩

/-- Finite-trace equivalence of the executable abstract queue and the actual
generated synchronous `Design`, from any pair of related starting states. -/
theorem runAdapter_refines (c : Chan w) (queue : State w) (state : St)
    (events : List (Event w)) (rep : AdapterRep c queue state) :
    let abstract := c.runTrace queue events
    let concrete := c.runAdapter state events
    AdapterRep c abstract.state concrete.state ∧
      concrete.accepted = abstract.accepted ∧
      concrete.delivered = abstract.delivered := by
  induction events generalizing queue state with
  | nil => simpa [runTrace, runAdapter] using rep
  | cons event rest ih =>
      simp only [runTrace, runAdapter]
      have nextRep := rep.step event
      have later := ih (c.step queue event).state
        (c.adapter.cycleOpen (c.drive event.push event.pop) state) nextRep
      exact ⟨later.1,
        by rw [c.adapterAcceptedValues_refine queue event state rep, later.2.1],
        by rw [c.adapterDeliveredValues_refine queue event state rep, later.2.2]⟩

/-- Reset-to-trace equivalence: for every finite event sequence, the adapter
that Loom actually lowers/emits has the same accepted and delivered FIFO trace
as `Chan.runTrace`, and its final concrete state represents the final abstract
queue. -/
theorem adapter_equivalent (c : Chan w) (positiveDepth : 0 < c.depth)
    (events : List (Event w)) :
    let abstract := c.runTrace [] events
    let concrete := c.runAdapter c.adapter.reset events
    AdapterRep c abstract.state concrete.state ∧
      concrete.accepted = abstract.accepted ∧
      concrete.delivered = abstract.delivered :=
  c.runAdapter_refines [] c.adapter.reset events (c.adapterRep_reset positiveDepth)

/-- The generated adapter reset represents the empty abstract queue. -/
theorem adapterView_reset (c : Chan w) (positiveDepth : 0 < c.depth) :
    AdapterView c [] c.adapter.reset := by
  have depthFits : c.depth < 2 ^ c.countWidth := by
    exact Nat.lt_log2_self
  constructor
  · simp [nonempty, count, adapter, Design.reset, Expr.eval, RegEnv.set, boolBit]
  · simp [hasSpace, count, adapter, Design.reset, Expr.eval, RegEnv.set, boolBit,
      positiveDepth, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt depthFits]
  · simp

def occupancy (c : Chan w) (state : St) : Nat := (c.count.eval state).toNat
def headValue (c : Chan w) (state : St) : BitVec w := c.adapterPayload.eval state

/-- The complete generated wiring for one synchronous connection. Prefixes
are the namespaces assigned by `System.island` and the adapter instance. -/
def connectionWire (c : Chan w) (sourcePrefix sinkPrefix adapterPrefix : String)
    (name : String) (width : Nat) : Option (Expr width) :=
  let atAdapter {n : Nat} (e : Expr n) := e.mapSignals (adapterPrefix ++ ·)
  let sourceValid : Expr 1 := .reg 1 (sourcePrefix ++ c.sourceValidName)
  let sourcePayload : Expr w := .reg w (sourcePrefix ++ c.sourcePayloadName)
  let sinkPop : Expr 1 := .reg 1 (sinkPrefix ++ c.sinkPopName)
  let ready : Expr 1 := match c.policy with
    | .refusePush => atAdapter c.hasSpace
    | .exchange => .or (atAdapter c.hasSpace) (.and sinkPop (atAdapter c.nonempty))
  let valid : Expr 1 := atAdapter c.adapterValid
  let payload : Expr w := atAdapter c.adapterPayload
  let push : Expr 1 := sourceValid
  let accepted : Expr 1 := .and push ready
  if name = sourcePrefix ++ c.sourceReadyName then
    if h : width = 1 then some (h.symm ▸ ready) else none
  else if name = sourcePrefix ++ c.sourceAcceptedName then
    if h : width = 1 then some (h.symm ▸ accepted) else none
  else if name = sinkPrefix ++ c.sinkValidName then
    if h : width = 1 then some (h.symm ▸ valid) else none
  else if name = sinkPrefix ++ c.sinkPayloadName then
    if h : width = w then some (h.symm ▸ payload) else none
  else if name = adapterPrefix ++ c.pushName then
    if h : width = 1 then some (h.symm ▸ push) else none
  else if name = adapterPrefix ++ c.pushPayloadName then
    if h : width = w then some (h.symm ▸ sourcePayload) else none
  else if name = adapterPrefix ++ c.popName then
    if h : width = 1 then some (h.symm ▸ sinkPop) else none
  else none

end Chan
end Loom.Hw
