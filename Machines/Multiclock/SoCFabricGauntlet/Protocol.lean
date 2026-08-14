-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.Packed

/-!
# SoC Fabric Gauntlet protocol

The transaction records are semantic Lean structures with one canonical,
padding-free hardware representation.  Declaration order is MSB first.
-/

namespace Machines.Multiclock.SoCFabricGauntlet

open Loom.Hw

structure Request where
  client : BitVec 1
  tag : BitVec 4
  write : BitVec 1
  addr : BitVec 8
  data : BitVec 32
  mask : BitVec 4
  deriving DecidableEq, Repr

structure Response where
  client : BitVec 1
  tag : BitVec 4
  data : BitVec 32
  error : BitVec 1
  deriving DecidableEq, Repr

structure CommitRecord where
  client : BitVec 1
  tag : BitVec 4
  addr : BitVec 8
  write : BitVec 1
  result : BitVec 32
  deriving DecidableEq, Repr

instance : HwPacked Request where
  width := 1 + (4 + (1 + (8 + (32 + 4))))
  pack := fun value =>
    value.client ++ (value.tag ++ (value.write ++
      (value.addr ++ (value.data ++ value.mask))))
  unpack := fun bits =>
    let afterClient := bits.extractLsb' 0 49
    let afterTag := afterClient.extractLsb' 0 45
    let afterWrite := afterTag.extractLsb' 0 44
    let afterAddr := afterWrite.extractLsb' 0 36
    { client := bits.extractLsb' 49 1
      tag := afterClient.extractLsb' 45 4
      write := afterTag.extractLsb' 44 1
      addr := afterWrite.extractLsb' 36 8
      data := afterAddr.extractLsb' 4 32
      mask := afterAddr.extractLsb' 0 4 }
  unpack_pack := by
    intro value
    cases value
    simp only [BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right]
  pack_unpack := by
    intro bits
    let afterClient := bits.extractLsb' 0 49
    let afterTag := afterClient.extractLsb' 0 45
    let afterWrite := afterTag.extractLsb' 0 44
    let afterAddr := afterWrite.extractLsb' 0 36
    change bits.extractLsb' 49 1 ++
      (afterClient.extractLsb' 45 4 ++
        (afterTag.extractLsb' 44 1 ++
          (afterWrite.extractLsb' 36 8 ++
            (afterAddr.extractLsb' 4 32 ++ afterAddr.extractLsb' 0 4)))) = bits
    rw [show afterAddr.extractLsb' 4 32 ++ afterAddr.extractLsb' 0 4 =
        afterAddr from BitVec.extractLsb'_append_extractLsb']
    rw [show afterWrite.extractLsb' 36 8 ++ afterAddr = afterWrite from
      BitVec.extractLsb'_append_extractLsb']
    rw [show afterTag.extractLsb' 44 1 ++ afterWrite = afterTag from
      BitVec.extractLsb'_append_extractLsb']
    rw [show afterClient.extractLsb' 45 4 ++ afterTag = afterClient from
      BitVec.extractLsb'_append_extractLsb']
    exact BitVec.extractLsb'_append_extractLsb'

instance : HwPacked Response where
  width := 1 + (4 + (32 + 1))
  pack := fun value => value.client ++ (value.tag ++ (value.data ++ value.error))
  unpack := fun bits =>
    let afterClient := bits.extractLsb' 0 37
    let afterTag := afterClient.extractLsb' 0 33
    { client := bits.extractLsb' 37 1
      tag := afterClient.extractLsb' 33 4
      data := afterTag.extractLsb' 1 32
      error := afterTag.extractLsb' 0 1 }
  unpack_pack := by
    intro value
    cases value
    simp only [BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right]
  pack_unpack := by
    intro bits
    let afterClient := bits.extractLsb' 0 37
    let afterTag := afterClient.extractLsb' 0 33
    change bits.extractLsb' 37 1 ++
      (afterClient.extractLsb' 33 4 ++
        (afterTag.extractLsb' 1 32 ++ afterTag.extractLsb' 0 1)) = bits
    rw [show afterTag.extractLsb' 1 32 ++ afterTag.extractLsb' 0 1 =
      afterTag from BitVec.extractLsb'_append_extractLsb']
    rw [show afterClient.extractLsb' 33 4 ++ afterTag = afterClient from
      BitVec.extractLsb'_append_extractLsb']
    exact BitVec.extractLsb'_append_extractLsb'

instance : HwPacked CommitRecord where
  width := 1 + (4 + (8 + (1 + 32)))
  pack := fun value =>
    value.client ++ (value.tag ++ (value.addr ++ (value.write ++ value.result)))
  unpack := fun bits =>
    let afterClient := bits.extractLsb' 0 45
    let afterTag := afterClient.extractLsb' 0 41
    let afterAddr := afterTag.extractLsb' 0 33
    { client := bits.extractLsb' 45 1
      tag := afterClient.extractLsb' 41 4
      addr := afterTag.extractLsb' 33 8
      write := afterAddr.extractLsb' 32 1
      result := afterAddr.extractLsb' 0 32 }
  unpack_pack := by
    intro value
    cases value
    simp only [BitVec.extractLsb'_append_eq_left,
      BitVec.extractLsb'_append_eq_right]
  pack_unpack := by
    intro bits
    let afterClient := bits.extractLsb' 0 45
    let afterTag := afterClient.extractLsb' 0 41
    let afterAddr := afterTag.extractLsb' 0 33
    change bits.extractLsb' 45 1 ++
      (afterClient.extractLsb' 41 4 ++
        (afterTag.extractLsb' 33 8 ++
          (afterAddr.extractLsb' 32 1 ++ afterAddr.extractLsb' 0 32))) = bits
    rw [show afterAddr.extractLsb' 32 1 ++ afterAddr.extractLsb' 0 32 =
      afterAddr from BitVec.extractLsb'_append_extractLsb']
    rw [show afterTag.extractLsb' 33 8 ++ afterAddr = afterTag from
      BitVec.extractLsb'_append_extractLsb']
    rw [show afterClient.extractLsb' 41 4 ++ afterTag = afterClient from
      BitVec.extractLsb'_append_extractLsb']
    exact BitVec.extractLsb'_append_extractLsb'

def requestLayout : PackedLayout Request where
  fields :=
    [ ⟨"client", 1, 49⟩, ⟨"tag", 4, 45⟩, ⟨"write", 1, 44⟩
    , ⟨"addr", 8, 36⟩, ⟨"data", 32, 4⟩, ⟨"mask", 4, 0⟩ ]
  namesUnique := by decide
  inBounds := by
    intro field member
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  disjoint := by decide
  complete := by decide
  msbFirst := by
    intro index inRange
    simp at inRange
    have : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

def responseLayout : PackedLayout Response where
  fields :=
    [ ⟨"client", 1, 37⟩, ⟨"tag", 4, 33⟩
    , ⟨"data", 32, 1⟩, ⟨"error", 1, 0⟩ ]
  namesUnique := by decide
  inBounds := by
    intro field member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  disjoint := by decide
  complete := by decide
  msbFirst := by
    intro index inRange
    simp at inRange
    have : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp

def commitLayout : PackedLayout CommitRecord where
  fields :=
    [ ⟨"client", 1, 45⟩, ⟨"tag", 4, 41⟩, ⟨"addr", 8, 33⟩
    , ⟨"write", 1, 32⟩, ⟨"result", 32, 0⟩ ]
  namesUnique := by decide
  inBounds := by
    intro field member
    simp at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  disjoint := by decide
  complete := by decide
  msbFirst := by
    intro index inRange
    simp at inRange
    have : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> simp

instance : HwPackedLayout Request := ⟨requestLayout⟩
instance : HwPackedLayout Response := ⟨responseLayout⟩
instance : HwPackedLayout CommitRecord := ⟨commitLayout⟩

namespace Request

def clientField : PackedField Request 1 :=
  HwPackedLayout.fieldAt (α := Request) ⟨0, by decide⟩
def tagField : PackedField Request 4 :=
  HwPackedLayout.fieldAt (α := Request) ⟨1, by decide⟩
def writeField : PackedField Request 1 :=
  HwPackedLayout.fieldAt (α := Request) ⟨2, by decide⟩
def addrField : PackedField Request 8 :=
  HwPackedLayout.fieldAt (α := Request) ⟨3, by decide⟩
def dataField : PackedField Request 32 :=
  HwPackedLayout.fieldAt (α := Request) ⟨4, by decide⟩
def maskField : PackedField Request 4 :=
  HwPackedLayout.fieldAt (α := Request) ⟨5, by decide⟩

end Request

namespace Response

def clientField : PackedField Response 1 :=
  HwPackedLayout.fieldAt (α := Response) ⟨0, by decide⟩
def tagField : PackedField Response 4 :=
  HwPackedLayout.fieldAt (α := Response) ⟨1, by decide⟩
def dataField : PackedField Response 32 :=
  HwPackedLayout.fieldAt (α := Response) ⟨2, by decide⟩
def errorField : PackedField Response 1 :=
  HwPackedLayout.fieldAt (α := Response) ⟨3, by decide⟩

end Response

namespace CommitRecord

def clientField : PackedField CommitRecord 1 :=
  HwPackedLayout.fieldAt (α := CommitRecord) ⟨0, by decide⟩
def tagField : PackedField CommitRecord 4 :=
  HwPackedLayout.fieldAt (α := CommitRecord) ⟨1, by decide⟩
def addrField : PackedField CommitRecord 8 :=
  HwPackedLayout.fieldAt (α := CommitRecord) ⟨2, by decide⟩
def writeField : PackedField CommitRecord 1 :=
  HwPackedLayout.fieldAt (α := CommitRecord) ⟨3, by decide⟩
def resultField : PackedField CommitRecord 32 :=
  HwPackedLayout.fieldAt (α := CommitRecord) ⟨4, by decide⟩

end CommitRecord

def cpuRequest : PackedChan Request := .named "cpu_request" 2
def cpuResponse : PackedChan Response := .named "cpu_response" 2
def dmaRequest : PackedChan Request := .named "dma_request" 4
def dmaResponse : PackedChan Response := .named "dma_response" 4
def targetRequest : PackedChan Request := .named "target_request" 4
def targetResponse : PackedChan Response := .named "target_response" 4
def audit : PackedChan CommitRecord := .named "audit" 4

theorem packedWidths :
    HwPacked.width Request = 50 ∧ HwPacked.width Response = 38 ∧
      HwPacked.width CommitRecord = 46 := by
  decide

end Machines.Multiclock.SoCFabricGauntlet
