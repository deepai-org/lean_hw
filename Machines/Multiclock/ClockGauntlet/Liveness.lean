-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Machines.Multiclock.ClockGauntlet.Execution

/-! Compact finite certificate for arbitrary-order bounded-tick progress. -/

namespace Machines.Multiclock.ClockGauntlet.Execution

open Loom.Hw
open Machines.Multiclock.ClockGauntlet

/-- Representative protocol state indexed by seven-or-fewer remaining source
packets and the 144 finite control/occupancy encodings. States farther from the
source boundary are normalized to seven remaining packets; the semantic bridge
below accounts for that translation. -/
def rankRepresentative (code : Nat) : ProtocolState :=
  let remaining := code % 8
  let controls := code / 8
  let sourceValid := controls % 2 != 0
  let transformPending := (controls / 2) % 2 != 0
  let transformValid := (controls / 4) % 2 != 0
  let checkerPop := (controls / 8) % 2 != 0
  let firstLength := (controls / 16) % 3
  let secondLength := controls / 48
  let nextPacket := packetCount - remaining
  let outstanding := boolNat sourceValid + firstLength + secondLength +
    boolNat (transformValid && !transformPending)
  { sourceValid, nextPacket, transformPending, transformValid, checkerPop
    expectedSequence := nextPacket + boolNat checkerPop - outstanding
    firstLength, secondLength }

/-- Search node retaining exactly the two masks required by the sliding
three-event tick premise. -/
structure RankNode where
  state : ProtocolState
  older : Nat
  newer : Nat
  deriving BEq, ReflBEq, Hashable, LawfulBEq

def rankSuccessors (depth : Nat) (node : RankNode) : List RankNode :=
  (List.range 8).filterMap fun mask =>
    if depth < 2 || node.older ||| node.newer ||| mask == 7 then
      some ⟨protocolAdvance (event mask) node.state, node.newer, mask⟩
    else none

def insertRankNodes (frontier : Std.HashSet RankNode) (nodes : List RankNode) :
    Std.HashSet RankNode :=
  nodes.foldl (fun current node => current.insert node) frontier

def rankFrontierStep (depth : Nat) (frontier : Std.HashSet RankNode) :
    Std.HashSet RankNode :=
  frontier.toList.foldl
    (fun current node => insertRankNodes current (rankSuccessors depth node)) {}

def rankFrontier (state : ProtocolState) : Nat → Std.HashSet RankNode
  | 0 => { ⟨state, 0, 0⟩ }
  | depth + 1 => rankFrontierStep depth (rankFrontier state depth)

def rankBlockResult (start finish : ProtocolState) : Bool :=
  protocolComplete finish || protocolPhaseRank finish < protocolPhaseRank start

/-- All invariant, incomplete representatives either complete or strictly
decrease the phase-aware rank after every legal six-event block. -/
def rankBlockCertificate : Bool :=
  (List.range 1152).all fun code =>
    let state := rankRepresentative code
    !protocolInvariantB state || protocolComplete state ||
      (rankFrontier state 6).toList.all fun node =>
        rankBlockResult state node.state

theorem rankBlockCertificate_true : rankBlockCertificate = true := by
  native_decide

def FollowsRankGap : Nat → Nat → Nat → List Nat → Prop
  | _, _, _, [] => True
  | depth, older, newer, mask :: rest =>
      mask < 8 ∧ (depth < 2 ∨ older ||| newer ||| mask = 7) ∧
        FollowsRankGap (depth + 1) newer mask rest

def runRankNode : RankNode → List Nat → RankNode
  | node, [] => node
  | node, mask :: rest =>
      runRankNode
        ⟨protocolAdvance (event mask) node.state, node.newer, mask⟩ rest

private theorem mem_insertRankNodes_of_mem {frontier : Std.HashSet RankNode}
    {node : RankNode} (member : node ∈ frontier) (nodes : List RankNode) :
    node ∈ insertRankNodes frontier nodes := by
  induction nodes generalizing frontier with
  | nil => exact member
  | cons next rest ih =>
      apply ih
      exact Std.HashSet.mem_insert.mpr (Or.inr member)

private theorem mem_insertRankNodes_of_list_mem
    {frontier : Std.HashSet RankNode} {node : RankNode} {nodes : List RankNode}
    (member : node ∈ nodes) : node ∈ insertRankNodes frontier nodes := by
  induction nodes generalizing frontier with
  | nil => contradiction
  | cons next rest ih =>
      cases member with
      | head =>
          exact mem_insertRankNodes_of_mem
            (Std.HashSet.mem_insert_self (m := frontier)) rest
      | tail _ member =>
          exact ih (frontier := frontier.insert next) member

private theorem mem_rankFold_of_mem {frontier : Std.HashSet RankNode}
    {node : RankNode} (member : node ∈ frontier) (nodes : List RankNode)
    (depth : Nat) :
    node ∈ nodes.foldl
      (fun current next => insertRankNodes current (rankSuccessors depth next))
      frontier := by
  induction nodes generalizing frontier with
  | nil => exact member
  | cons next rest ih =>
      apply ih
      exact mem_insertRankNodes_of_mem member _

private theorem mem_rankFold_of_successor {frontier : Std.HashSet RankNode}
    {source target : RankNode} {nodes : List RankNode} {depth : Nat}
    (sourceMember : source ∈ nodes)
    (targetMember : target ∈ rankSuccessors depth source) :
    target ∈ nodes.foldl
      (fun current next => insertRankNodes current (rankSuccessors depth next))
      frontier := by
  induction nodes generalizing frontier with
  | nil => contradiction
  | cons next rest ih =>
      cases sourceMember with
      | head =>
          exact mem_rankFold_of_mem
            (mem_insertRankNodes_of_list_mem targetMember) rest depth
      | tail _ sourceMember =>
          exact ih (frontier := insertRankNodes frontier
            (rankSuccessors depth next)) sourceMember

private theorem rankSuccessor_mem {frontier : Std.HashSet RankNode}
    {node : RankNode} (member : node ∈ frontier) {depth mask : Nat}
    (maskBound : mask < 8)
    (window : depth < 2 ∨ node.older ||| node.newer ||| mask = 7) :
    ⟨protocolAdvance (event mask) node.state, node.newer, mask⟩ ∈
      rankFrontierStep depth frontier := by
  apply mem_rankFold_of_successor (frontier := {})
    (Std.HashSet.mem_toList.mpr member)
  simp only [rankSuccessors, List.mem_filterMap]
  exact ⟨mask, List.mem_range.mpr maskBound, by simp [window]⟩

theorem runRankNode_mem {start : ProtocolState} {depth : Nat}
    {node : RankNode} (member : node ∈ rankFrontier start depth)
    {masks : List Nat} (follows : FollowsRankGap depth node.older node.newer masks) :
    runRankNode node masks ∈ rankFrontier start (depth + masks.length) := by
  induction masks generalizing depth node with
  | nil => simpa [runRankNode] using member
  | cons mask rest ih =>
      rcases follows with ⟨maskBound, window, follows⟩
      let next : RankNode :=
        ⟨protocolAdvance (event mask) node.state, node.newer, mask⟩
      have nextMember : next ∈ rankFrontier start (depth + 1) := by
        simpa [rankFrontier, Nat.add_assoc, next] using
          rankSuccessor_mem member maskBound window
      convert ih nextMember follows using 1 <;>
        simp [runRankNode, next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem runRankNode_state (node : RankNode) (masks : List Nat) :
    (runRankNode node masks).state =
      runProtocol node.state (masks.map event) := by
  induction masks generalizing node with
  | nil => rfl
  | cons mask rest ih =>
      simpa [runRankNode, runProtocol] using
        ih ⟨protocolAdvance (event mask) node.state, node.newer, mask⟩

/-- Checked local progress result for each normalized representative. -/
theorem rankRepresentative_block_progress {code : Nat} (codeBound : code < 1152)
    (invariant : ProtocolInvariant (rankRepresentative code))
    (incomplete : protocolComplete (rankRepresentative code) = false)
    {masks : List Nat} (length : masks.length = 6)
    (follows : FollowsRankGap 0 0 0 masks) :
    protocolComplete
        (runProtocol (rankRepresentative code) (masks.map event)) = true ∨
      protocolPhaseRank
          (runProtocol (rankRepresentative code) (masks.map event)) <
        protocolPhaseRank (rankRepresentative code) := by
  have rows := List.all_eq_true.mp rankBlockCertificate_true code
    (List.mem_range.mpr codeBound)
  have invariantB := (protocolInvariantB_iff (rankRepresentative code)).mpr invariant
  have frontierRows : (rankFrontier (rankRepresentative code) 6).toList.all
      (fun node => rankBlockResult (rankRepresentative code) node.state) = true := by
    simpa [rankBlockCertificate, invariantB, incomplete] using rows
  let initial : RankNode := ⟨rankRepresentative code, 0, 0⟩
  have initialMember : initial ∈ rankFrontier (rankRepresentative code) 0 := by
    simp [rankFrontier, initial]
  have finalMember : runRankNode initial masks ∈
      rankFrontier (rankRepresentative code) 6 := by
    simpa [length] using runRankNode_mem initialMember follows
  have result := List.all_eq_true.mp frontierRows (runRankNode initial masks)
    (Std.HashSet.mem_toList.mpr finalMember)
  rw [rankBlockResult] at result
  simp only [Bool.or_eq_true, decide_eq_true_eq] at result
  simpa [runRankNode_state, initial] using result

end Machines.Multiclock.ClockGauntlet.Execution
