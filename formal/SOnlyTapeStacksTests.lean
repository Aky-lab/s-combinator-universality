import SOnlyTapeStacks

open SOnlyTapeStacks

namespace TapeStacksTests

def backtrack : Machine 4 3 where
  start := 0
  blank := 0
  transition q _ := match q.val with
    | 0 => some ⟨1, 2, .left⟩
    | 1 => some ⟨2, 1, .right⟩
    | 2 => some ⟨3, 0, .right⟩
    | _ => none

def finalBacktrack : StackConfig 4 3 := ⟨3, 2, [0, 1], []⟩

example : run (stackStep backtrack) 3 (stackInput backtrack [1, 2]) =
    some finalBacktrack := by decide

example : run (encodedStep backtrack) 3 (encodeStacks (stackInput backtrack [1, 2])) =
    some (encodeStacks finalBacktrack) := by decide

example : run (stackStep backtrack) 4 (stackInput backtrack [1, 2]) = none := by decide

example : HaltsAfter (tapeStep backtrack) 3 (tapeInput backtrack [1, 2]) :=
  (input_haltsAfter_iff backtrack [1, 2] 3).mpr ⟨finalBacktrack, by decide, by decide⟩

example : (run (tapeStep backtrack) 3 (tapeInput backtrack [1, 2])).map
    (fun c => (c.position, c.cells (-1), c.cells 0, c.cells 1, c.cells 2)) =
    some (1, 1, 0, 2, 0) := by decide

def emptyWalk : Machine 3 2 where
  start := 0
  blank := 0
  transition q _ := match q.val with
    | 0 => some ⟨1, 1, .left⟩
    | 1 => some ⟨2, 1, .right⟩
    | _ => none

example : run (stackStep emptyWalk) 2 (stackInput emptyWalk []) =
    some ⟨2, 1, [1], []⟩ := by decide

example : (run (tapeStep emptyWalk) 2 (tapeInput emptyWalk [])).map
    (fun c => (c.position, c.cells (-2), c.cells (-1), c.cells 0, c.cells 1)) =
    some (0, 0, 1, 1, 0) := by decide

def stays : Machine 2 2 where
  start := 0
  blank := 0
  transition q _ := if q = 0 then some ⟨1, 1, .stay⟩ else none

example : run (stackStep stays) 1 (stackInput stays []) =
    some ⟨1, 1, [], []⟩ := by decide

example : stackCode 3 [1, 2] = 14 := by decide
example : stackCode 3 [] = 0 := by decide
example : stackCode 3 [0] = 1 := by decide
example : decodeDigit (0 : Fin 3) 0 = 0 := by decide
example : decodeDigit (0 : Fin 3) 3 = 2 := by decide

end TapeStacksTests

#print axioms SOnlyTapeStacks.apply_represents
#print axioms SOnlyTapeStacks.input_run_represents
#print axioms SOnlyTapeStacks.input_haltsAfter_iff
#print axioms SOnlyTapeStacks.input_halts_iff
#print axioms SOnlyTapeStacks.input_diverges_iff
#print axioms SOnlyTapeStacks.code_pop
#print axioms SOnlyTapeStacks.stackCode_injective
#print axioms SOnlyTapeStacks.encodedRun_encodeStacks
#print axioms SOnlyTapeStacks.input_encoded_haltsAfter_iff
