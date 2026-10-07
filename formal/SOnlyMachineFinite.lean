import SOnlyMachineClock

/-!
# Effective dense counter numbering and the complete finite-input front end
-/
namespace SOnlyMachineFinite

open SOnlyMachineBP2 (Enumeration Command Program State)
open SOnlyMachine (put)

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

variable {α : Type} [DecidableEq α]

/-- Effective zero-based numbering; published positive BP2 labels add one. -/
def number (e : Enumeration α) (i : α) : Fin e.order.length :=
  ⟨e.order.idxOf i, List.idxOf_lt_length_of_mem (e.complete i)⟩

def unnumber (e : Enumeration α) (i : Fin e.order.length) : α := e.order[i.val]

@[simp] theorem unnumber_number (e : Enumeration α) (i : α) : unnumber e (number e i) = i := by
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (e.complete i))

@[simp] theorem number_unnumber (e : Enumeration α) (i : Fin e.order.length) : number e (unnumber e i) = i := by
  apply Fin.ext
  exact e.nodup.idxOf_getElem i.val i.isLt

/-- Relabeling only changes counter identifiers, never code positions. -/
def renameCommand {β : Type} (f : α → β) : Command α → Command β
  | .inc i => .inc (f i)
  | .dec i => .dec (f i)

def renameProgram {β : Type} (f : α → β) (P : Program α) : Program β := P.map (renameCommand f)

def encode (e : Enumeration α) (s : State α) : State (Fin e.order.length) :=
  ⟨s.pc, fun i => s.value (unnumber e i)⟩

theorem put_number (e : Enumeration α) (v : α → Nat) (i : α) (n : Nat) :
    (fun j => put v i n (unnumber e j)) = put (fun j => v (unnumber e j)) (number e i) n := by
  funext j
  have he : unnumber e j = i ↔ j = number e i := by
    constructor
    · intro h; have := congrArg (number e) h; simpa using this
    · intro h; rw [h, unnumber_number]
  simp [put, he]

theorem execute_number (e : Enumeration α) (command : Command α) (s : State α) :
    SOnlyMachineBP2.execute (renameCommand (number e) command) (encode e s) =
      encode e (SOnlyMachineBP2.execute command s) := by
  cases command with
  | inc i => simp [SOnlyMachineBP2.execute, encode, renameCommand, put_number]
  | dec i =>
    by_cases h : s.value i = 0 <;>
      simp [SOnlyMachineBP2.execute, encode, renameCommand, h, put_number]

theorem advance_number (e : Enumeration α) (P : Program α) (s : State α) :
    SOnlyMachineBP2.advance (renameProgram (number e) P) (encode e s) =
      encode e (SOnlyMachineBP2.advance P s) := by
  cases h : P[s.pc]? with
  | none => simp [SOnlyMachineBP2.advance, SOnlyMachineBP2.step?, renameProgram, encode, h]
  | some command =>
    simp only [SOnlyMachineBP2.advance, SOnlyMachineBP2.step?, renameProgram, encode,
      List.getElem?_map, h, Option.map_some, Option.getD_some]
    exact execute_number e command s

theorem run_number (e : Enumeration α) (P : Program α) (k : Nat) (s : State α) :
    SOnlyMachineBP2.run (renameProgram (number e) P) k (encode e s) =
      encode e (SOnlyMachineBP2.run P k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [SOnlyMachineBP2.run_succ, advance_number, ih]
    rfl

@[simp] theorem halted_number (e : Enumeration α) (P : Program α) (s : State α) :
    SOnlyMachineBP2.Halted (renameProgram (number e) P) (encode e s) ↔ SOnlyMachineBP2.Halted P s := by
  simp [SOnlyMachineBP2.Halted, renameProgram, encode]

/-- Every advertised numerical label is actually used in the code. -/
def Dense (P : Program α) : Prop := ∀ i, Command.inc i ∈ P ∨ Command.dec i ∈ P

theorem dense_number (e : Enumeration α) (P : Program α) (h : Dense P) :
    Dense (renameProgram (number e) P) := by
  intro i
  rcases h (unnumber e i) with hi | hi
  · left
    have := List.mem_map_of_mem (f := renameCommand (number e)) hi
    simpa [renameProgram, renameCommand] using this
  · right
    have := List.mem_map_of_mem (f := renameCommand (number e)) hi
    simpa [renameProgram, renameCommand] using this

/-- Source call-site counter enumeration, retaining data registers first. -/
def auxList {d n : Nat} : List (Fin (n + 1)) → List (SOnlyMachine.Cell d n)
  | [] => []
  | q :: tail => .I q :: .S q :: .F q :: .U q :: .V q :: auxList tail

theorem mem_auxList {d n : Nat} (items : List (Fin (n + 1))) (c : SOnlyMachine.Cell d n) :
    c ∈ auxList items ↔ match c with
      | .data _ => False
      | .I q => q ∈ items
      | .S q => q ∈ items
      | .F q => q ∈ items
      | .U q => q ∈ items
      | .V q => q ∈ items := by
  induction items with
  | nil => cases c <;> simp [auxList]
  | cons q tail ih => cases c <;> simp [auxList, ih]

theorem auxList_nodup {d n : Nat} (items : List (Fin (n + 1))) (h : items.Nodup) :
    (auxList (d := d) items).Nodup := by
  induction items with
  | nil => simp [auxList]
  | cons i tail ih =>
    have hi := (List.nodup_cons.mp h).1
    have ht := ih (List.nodup_cons.mp h).2
    simp [auxList, List.nodup_cons, mem_auxList, hi, ht]

def machineCells (d n : Nat) : Enumeration (SOnlyMachine.Cell d n) where
  order := (List.finRange (d + 1)).map SOnlyMachine.Cell.data ++ auxList (List.finRange (n + 1))
  nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_, auxList_nodup _ (List.nodup_finRange _), ?_⟩
    · simpa only [List.Nodup, List.pairwise_map, ne_eq, SOnlyMachine.Cell.data.injEq] using List.nodup_finRange (d + 1)
    · intro a ha b hb he
      subst b
      rcases List.mem_map.mp ha with ⟨i, hi, he⟩
      subst a
      simpa [mem_auxList] using hb
  complete := by
    intro c
    cases c <;> simp [mem_auxList, List.mem_finRange]

/-- The syntactic compiler does not execute the source or use a time bound. -/
def typedProgram (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    Program (SOnlyMachineClock.BPCell (SOnlyMachine.Cell d n)) :=
  SOnlyMachineClock.program (SOnlyMachine.compile M) (machineCells d n)
    (SOnlyMachine.encode M (SOnlyMachine.initial M input))

def targetCells (d n : Nat) : Enumeration (SOnlyMachineClock.BPCell (SOnlyMachine.Cell d n)) :=
  SOnlyMachineWaterfallBP2.cells (SOnlyMachineClock.clocks (machineCells d n))

def compile (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    Program (Fin (targetCells d n).order.length) :=
  renameProgram (number (targetCells d n)) (typedProgram M input)

/-- Main finite-input front-end halting theorem, with all target counters zero. -/
theorem halt_iff (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    (∃ k, SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩)) ↔
    (∃ k, M.instruction (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).label = .halt) := by
  have hrun : ∀ k, SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩ =
      encode (targetCells d n) (SOnlyMachineBP2.run (typedProgram M input) k ⟨0, fun _ => 0⟩) := by
    intro k
    exact run_number (targetCells d n) (typedProgram M input) k ⟨0, fun _ => 0⟩
  have hiff : (∃ k, SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩)) ↔
      (∃ k, SOnlyMachineBP2.Halted (typedProgram M input)
      (SOnlyMachineBP2.run (typedProgram M input) k ⟨0, fun _ => 0⟩)) := by
    apply exists_congr
    intro k
    rw [hrun]
    exact halted_number (targetCells d n) (typedProgram M input) _
  exact hiff.trans ((SOnlyMachineClock.halt_iff (SOnlyMachine.compile M) (machineCells d n)
    (SOnlyMachine.encode M (SOnlyMachine.initial M input))).trans
    (SOnlyMachine.arbitrary_input_halt_iff M input))

/-- Every Waterfall value cell appears in the sweep, every pending cell in its
zero test, and the marker in the final pair. Thus no numerical label is unused. -/
theorem waterfall_dense (e : Enumeration α) (w : α → Nat) (A : α → α → Nat) (halt : α) :
    Dense (SOnlyMachineWaterfallBP2.compile e w A halt) := by
  intro c
  right
  cases c with
  | value i =>
    have hm : SOnlyMachineWaterfallBP2.Cell.value i ∈
        SOnlyMachineBP2.unary (SOnlyMachineWaterfallBP2.cells e).order SOnlyMachineWaterfallBP2.sweepWeight := by
      apply List.count_pos_iff.mp
      simp [SOnlyMachineWaterfallBP2.sweepWeight]
    have hs : Command.dec (SOnlyMachineWaterfallBP2.Cell.value i) ∈ SOnlyMachineWaterfallBP2.sweep e :=
      List.mem_map_of_mem (f := Command.dec) hm
    simp only [SOnlyMachineWaterfallBP2.compile, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hs))
  | zero i =>
    have ht : Command.dec (SOnlyMachineWaterfallBP2.Cell.zero i) ∈
        e.order.flatMap SOnlyMachineWaterfallBP2.test := by
      apply List.mem_flatMap.mpr
      exact ⟨i, e.complete i, by simp [SOnlyMachineWaterfallBP2.test]⟩
    simp only [SOnlyMachineWaterfallBP2.compile, List.mem_append]
    exact Or.inl (Or.inr ht)
  | marker =>
    simp only [SOnlyMachineWaterfallBP2.compile, List.mem_append]
    exact Or.inr (by simp)

theorem compile_dense (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) : Dense (compile M input) :=
  dense_number (targetCells d n) (typedProgram M input) (waterfall_dense _ _ _ _)

theorem compile_nonempty (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) :
    0 < (compile M input).length := by
  simpa only [compile, renameProgram, List.length_map, typedProgram, SOnlyMachineClock.program] using
    SOnlyMachineWaterfallBP2.compile_nonempty (SOnlyMachineClock.clocks (machineCells d n))
      (fun c => SOnlyMachineClock.normalized (SOnlyMachine.encode M (SOnlyMachine.initial M input)) c + 5)
      (SOnlyMachineClock.row (SOnlyMachine.compile M)) (.action .halt)

def outputCell (d n : Nat) : SOnlyMachineClock.BPCell (SOnlyMachine.Cell d n) :=
  .value (.data (.data 0))

/-- Original register zero is the first numerical BP2 counter. -/
theorem output_number_zero (d n : Nat) : (number (targetCells d n) (outputCell d n)).val = 0 := by
  simp [number, targetCells, SOnlyMachineWaterfallBP2.cells, SOnlyMachineClock.clocks,
    machineCells, outputCell, List.finRange_succ, SOnlyMachineClock.clockList]

theorem counter_count_pos (d n : Nat) : 0 < (targetCells d n).order.length := by
  have hi := (number (targetCells d n) (outputCell d n)).isLt
  rw [output_number_zero] at hi
  exact hi

def firstCounter (d n : Nat) : Fin (targetCells d n).order.length := ⟨0, counter_count_pos d n⟩

@[simp] theorem first_is_output (d n : Nat) : number (targetCells d n) (outputCell d n) = firstCounter d n := by
  apply Fin.ext
  exact output_number_zero d n

/-- Every actual halting run of the dense numerical program has output 2v+3
in its first counter, where v is the final source register zero. -/
theorem halt_output (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) (k : Nat)
    (hk : SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩)) :
    M.instruction (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).label = .halt ∧
    (SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩).value (firstCounter d n) =
      2 * (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0 + 3 := by
  have hrun := run_number (targetCells d n) (typedProgram M input) k (⟨0, fun _ => 0⟩ : State _)
  change SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩ = _ at hrun
  have htyped : SOnlyMachineBP2.Halted (typedProgram M input)
      (SOnlyMachineBP2.run (typedProgram M input) k ⟨0, fun _ => 0⟩) := by
    rw [hrun] at hk
    exact (halted_number (targetCells d n) (typedProgram M input) _).mp hk
  obtain ⟨ham, hout⟩ := SOnlyMachineClock.halt_output (SOnlyMachine.compile M) (machineCells d n)
    (SOnlyMachine.encode M (SOnlyMachine.initial M input)) k htyped (.data 0)
  obtain ⟨hvalue, hsource⟩ := SOnlyMachine.halt_output M (SOnlyMachine.initial M input) k ham
  refine ⟨hsource, ?_⟩
  rw [hrun, ← first_is_output]
  simp only [encode, State.value, unnumber_number]
  change (SOnlyMachineBP2.run (typedProgram M input) k ⟨0, fun _ => 0⟩).value (outputCell d n) = _
  rw [hvalue] at hout
  simpa only [typedProgram, outputCell, SOnlyMachine.normal_data] using hout

/-- Fixed source-independent reader for the first target counter. -/
theorem readout_correct (M : SOnlyMachine.Machine d n) (input : Fin (d + 1) → Nat) (k : Nat)
    (hk : SOnlyMachineBP2.Halted (compile M input)
      (SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩)) :
    SOnlyMachineWaterfallBP2.readOutput
      ((SOnlyMachineBP2.run (compile M input) k ⟨0, fun _ => 0⟩).value (firstCounter d n)) =
      (SOnlyMachine.sourceRun M k (SOnlyMachine.initial M input)).value 0 := by
  rw [(halt_output M input k hk).2]
  exact SOnlyMachineWaterfallBP2.readOutput_correct _

end SOnlyMachineFinite
