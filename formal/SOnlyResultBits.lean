import SOnlyResult

/-!
# Structural bitword recovery at the ordinary CTS event

Decode only fixed 19-bit one-hot blocks, restoring the known symbol-18 head
from its remaining `10` suffix. Fuel is the supplied bit length, not a bound
on any source execution. Results use published one-based labels.
-/
namespace SOnlyResultBits

open PureSFormal
open SOnlySource

set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

def decodeBlock (bits : List Bool) : Option Nat :=
  if bits.length = 19 ∧ bits.count true = 1 then some (bits.idxOf true + 1) else none

def decodeBlocks : Nat → List Bool → Option (List Nat)
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bits =>
      if bits = [] then some [] else do
        let symbol ← decodeBlock (bits.take 19)
        let rest ← decodeBlocks fuel (bits.drop 19)
        some (symbol :: rest)

def published (word : List Symbol) : List Nat := word.map (fun s => s.val + 1)

def decodeEventWord : List Bool → Option (List Nat)
  | true :: false :: rest => (decodeBlocks rest.length rest).map (18 :: ·)
  | _ => none

def readMachineBits (bits : List Bool) : Option Nat :=
  (decodeEventWord bits).bind SOnlyResult.readMachineValue

theorem decodeBlock_code : ∀ symbol : Symbol, decodeBlock (code symbol) = some (symbol.val + 1) := by
  decide +kernel

theorem encodeWord_length (word : List Symbol) : (encodeWord word).length = 19 * word.length := by
  induction word with
  | nil => rfl
  | cons symbol tail ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem decodeBlocks_encode (word : List Symbol) (fuel : Nat) (enough : word.length ≤ fuel) :
    decodeBlocks fuel (encodeWord word) = some (published word) := by
  induction word generalizing fuel with
  | nil => cases fuel <;> simp [decodeBlocks, published]
  | cons symbol tail ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          have tailEnough : tail.length ≤ fuel := by simpa using enough
          have nonempty : code symbol ++ encodeWord tail ≠ [] := by
            intro empty
            have h := congrArg List.length empty
            simp [code_length] at h
          rw [encodeWord_cons]
          simp only [decodeBlocks, nonempty, ↓reduceIte,
            List.take_left' (code_length symbol), List.drop_left' (code_length symbol),
            decodeBlock_code, ih fuel tailEnough]
          rfl

/-- The exact bitword present seventeen zero-deletions into a selected18 block. -/
theorem event_word (tail : List Symbol) :
    (CTS.iterate SOnly38.program 17
      (encode ⟨(⟨17, by decide⟩ : Symbol) :: tail, true⟩)).data =
      true :: false :: encodeWord tail := by
  change (CTS.iterate SOnly38.program 17
    ⟨boundaryPhase true, code ⟨17, by decide⟩ ++ encodeWord tail⟩).data = _
  rw [consume_partial SOnly38.program (code ⟨17, by decide⟩) (encodeWord tail)
    (boundaryPhase true) 17 (by rw [code_length]; decide)]
  have dropped : (code (⟨17, by decide⟩ : Symbol)).drop 17 = [true, false] := by decide
  have scanned : scan SOnly38.program (boundaryPhase true)
      ((code (⟨17, by decide⟩ : Symbol)).take 17) = [] := by decide
  simp only [dropped, scanned, List.append_nil, List.cons_append, List.nil_append]

/-- Recover the whole source word from its unaligned current CTS event data. -/
theorem decodeEventWord_correct (tail : List Symbol) :
    decodeEventWord (true :: false :: encodeWord tail) = some (18 :: published tail) := by
  change (decodeBlocks (encodeWord tail).length (encodeWord tail)).map (18 :: ·) = _
  rw [decodeBlocks_encode tail _ (by rw [encodeWord_length]; omega)]
  rfl

theorem readMachineBits_correct (tail : List Symbol) (front rest : List Nat) (value : Nat)
    (wordEq : 18 :: published tail = front ++ List.replicate (4 ^ (2 * value + 4)) 16 ++ rest)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) (notHead : rest.head? ≠ some 16) :
    readMachineBits (true :: false :: encodeWord tail) = some value := by
  unfold readMachineBits
  rw [decodeEventWord_correct]
  simp only [Option.bind_some]
  rw [wordEq]
  exact SOnlyResult.readMachineValue_correct front rest value no16 notHead

/-- Numerical readout at the actual phase17 CTS prestate of a selected source head. -/
theorem source_event_result (tail : List Symbol) (front rest : List Nat) (value : Nat)
    (wordEq : 18 :: published tail = front ++ List.replicate (4 ^ (2 * value + 4)) 16 ++ rest)
    (no16 : ∀ symbol ∈ front, symbol ≠ 16) (notHead : rest.head? ≠ some 16) :
    readMachineBits (CTS.iterate SOnly38.program 17
      (encode ⟨(⟨17, by decide⟩ : Symbol) :: tail, true⟩)).data = some value := by
  rw [event_word]
  exact readMachineBits_correct tail front rest value wordEq no16 notHead

end SOnlyResultBits

#print axioms SOnlyResultBits.decodeBlocks_encode
#print axioms SOnlyResultBits.event_word
#print axioms SOnlyResultBits.decodeEventWord_correct
#print axioms SOnlyResultBits.source_event_result
