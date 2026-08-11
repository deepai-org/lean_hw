-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Compose
import Loom.Hw.Semantics

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

/-- Concrete implementation class selected for a channel crossing.  Only
`synchronous` is lowered in this file; asynchronous realizations are accepted
only by backends carrying their refinement certificate. -/
inductive ChanRealization where
  | synchronous
  | toggle
  | asyncFifo
  deriving DecidableEq, Repr

/-- A width-typed bounded FIFO handle.  Positive depth and realization/clock
compatibility are fail-closed assembly checks because names and depths are
ordinary generator data. -/
structure Chan (width : Nat) where
  name : String
  depth : Nat := 1
  policy : FullCoTickPolicy := .exchange
  realization : ChanRealization := .synchronous
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
  rcases c with ⟨name, depth, policy, realization⟩
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

/-- Channel names are expanded in one place; callers never hand-spell the
generated handshake coordinates. -/
private def stem (c : Chan w) := "__loom_chan_" ++ c.name ++ "_"
def sourceValidName (c : Chan w) := c.stem ++ "src_valid"
def sourcePayloadName (c : Chan w) := c.stem ++ "src_payload"
def sourceReadyName (c : Chan w) := c.stem ++ "src_ready"
def sourceAcceptedName (c : Chan w) := c.stem ++ "src_accepted"
def sinkValidName (c : Chan w) := c.stem ++ "dst_valid"
def sinkPayloadName (c : Chan w) := c.stem ++ "dst_payload"
def sinkPopName (c : Chan w) := c.stem ++ "dst_pop"

private def countName (c : Chan w) := c.stem ++ "count"
private def headName (c : Chan w) := c.stem ++ "head"
private def tailName (c : Chan w) := c.stem ++ "tail"
private def memoryName (c : Chan w) := c.stem ++ "storage"
def acceptedName (c : Chan w) := c.stem ++ "accepted"
def deliveredName (c : Chan w) := c.stem ++ "delivered"
private def pushName (c : Chan w) := c.stem ++ "push"
private def pushPayloadName (c : Chan w) := c.stem ++ "push_payload"
private def popName (c : Chan w) := c.stem ++ "pop"

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

def canDeq (c : Chan w) : Expr 1 := .reg 1 c.sinkValidName
def deq (c : Chan w) : Expr w := .reg w c.sinkPayloadName

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
  outputs := d.outputs

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
  outputs := d.outputs

private def count (c : Chan w) : Expr c.countWidth :=
  .reg c.countWidth c.countName
private def head (c : Chan w) : Expr c.indexWidth :=
  .reg c.indexWidth c.headName
private def tail (c : Chan w) : Expr c.indexWidth :=
  .reg c.indexWidth c.tailName
private def nonempty (c : Chan w) : Expr 1 := .not (.eq c.count (.lit 0))
private def hasSpace (c : Chan w) : Expr 1 :=
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
