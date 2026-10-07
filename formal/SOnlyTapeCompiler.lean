import StackMacros
import SOnlyTapeStacks
import SOnlyTapeCompilerCheckpoints

/-!
A constructive finite INC/DECJZ/HALT compiler for finite-alphabet Turing
machines. Labels are enumerated explicitly, rather than supplied as a
whole-program implementation premise. Registers 0 and 1 hold the two stack
codes; register 2 is shared zero-restored scratch.
-/
namespace SOnlyTapeCompiler
open SOnlyMachine SOnlyStack
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

inductive Phase (symbols : Nat) where
  | boundary | pushEntry | transfer | transferAdd | quotientAdd
  | multiplyAdd : Fin (symbols+1) → Phase symbols
  | digitAdd : Fin (symbols+1) → Phase symbols
  | consume : Fin (symbols+1) → Phase symbols
  | popTransfer : Fin (symbols+1) → Phase symbols
  | popTransferAdd : Fin (symbols+1) → Phase symbols
  deriving DecidableEq, Repr

structure Label (states symbols : Nat) where
  state : Fin states
  scanned : Fin symbols
  phase : Phase symbols
  deriving DecidableEq, Repr

def phases (symbols : Nat) : List (Phase symbols) :=
  [.boundary, .pushEntry, .transfer, .transferAdd, .quotientAdd] ++
  (List.finRange (symbols+1)).map .multiplyAdd ++
  (List.finRange (symbols+1)).map .digitAdd ++
  (List.finRange (symbols+1)).map .consume ++
  (List.finRange (symbols+1)).map .popTransfer ++
  (List.finRange (symbols+1)).map .popTransferAdd

@[simp] theorem mem_phases (p : Phase symbols) : p ∈ phases symbols := by
  cases p <;> simp [phases]

def labels (states symbols : Nat) : List (Label states symbols) :=
  (List.finRange states).flatMap fun q =>
    (List.finRange symbols).flatMap fun a =>
      (phases symbols).map fun p => ⟨q,a,p⟩

@[simp] theorem mem_labels (l : Label states symbols) : l ∈ labels states symbols := by
  rcases l with ⟨q,a,p⟩
  simp [labels]

def labelCount (states symbols : Nat) := (labels states symbols).length
abbrev PC (states symbols : Nat) := Fin (labelCount states symbols+1)

def pc (l : Label states symbols) : PC states symbols :=
  ⟨(labels states symbols).idxOf l, Nat.lt_succ_of_lt (List.idxOf_lt_length_of_mem (mem_labels l))⟩

@[simp] theorem lookup_pc (l : Label states symbols) :
    (labels states symbols)[(pc l).val]'(List.idxOf_lt_length_of_mem (mem_labels l)) = l := by
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (mem_labels l))

def withPhase (l : Label states symbols) (p : Phase symbols) : Label states symbols :=
  ⟨l.state,l.scanned,p⟩
def boundary (q : Fin states) (a : Fin symbols) : Label states symbols := ⟨q,a,.boundary⟩

def pushReg : SOnlyTapeStacks.Direction → Fin 3
  | .left => 1
  | _ => 0

def popReg : SOnlyTapeStacks.Direction → Fin 3
  | .left => 0
  | _ => 1

def mulLabel (l : Label states symbols) (j : Nat) : PC states symbols :=
  if h : j < symbols+1 then pc (withPhase l (.multiplyAdd ⟨j,h⟩))
  else pc (withPhase l .pushEntry)

def consumeLabel (l : Label states symbols) (j : Nat) : PC states symbols :=
  if h : j < symbols+1 then pc (withPhase l (.consume ⟨j,h⟩))
  else pc (withPhase l .quotientAdd)

def digitLabel (l : Label states symbols) (digit j : Nat) : PC states symbols :=
  if h : j < digit ∧ j < symbols+1 then pc (withPhase l (.digitAdd ⟨j,h.2⟩))
  else consumeLabel l 0

@[simp] theorem mulLabel_withPhase (l : Label states symbols) (p : Phase symbols) (j : Nat) :
    mulLabel (withPhase l p) j = mulLabel l j := rfl
@[simp] theorem consumeLabel_withPhase (l : Label states symbols) (p : Phase symbols) (j : Nat) :
    consumeLabel (withPhase l p) j = consumeLabel l j := rfl
@[simp] theorem digitLabel_withPhase (l : Label states symbols) (p : Phase symbols) (d j : Nat) :
    digitLabel (withPhase l p) d j = digitLabel l d j := rfl

def residue (symbols j : Nat) : Fin (symbols+1) := ⟨min j symbols, by omega⟩

def exitLabel (m : SOnlyTapeStacks.Machine states symbols)
    (a : SOnlyTapeStacks.Action states symbols) (j : Nat) : PC states symbols :=
  pc (boundary a.next (SOnlyTapeStacks.decodeDigit m.blank j))

/-- Explicit finite-control instruction for each enumerated label. -/
def emit (m : SOnlyTapeStacks.Machine states symbols) (l : Label states symbols) :
    Instruction 2 (labelCount states symbols) :=
  match m.transition l.state l.scanned with
  | none => .halt
  | some a =>
    let x := pushReg a.move
    let y := popReg a.move
    let loc := fun p => pc (withPhase l p)
    match l.phase with
    | .boundary =>
      let dest := if a.move = .stay then pc (boundary a.next a.write) else loc .pushEntry
      .dec 2 dest dest
    | .pushEntry => .dec x (mulLabel l 0) (loc .transfer)
    | .multiplyAdd j => .inc 2 (mulLabel l (j.val+1))
    | .transfer => .dec 2 (loc .transferAdd) (digitLabel l (SOnlyTapeStacks.digit a.write) 0)
    | .transferAdd => .inc x (loc .transfer)
    | .digitAdd j => .inc x (digitLabel l (SOnlyTapeStacks.digit a.write) (j.val+1))
    | .consume j => .dec y (consumeLabel l (j.val+1)) (loc (.popTransfer j))
    | .quotientAdd => .inc 2 (consumeLabel l 0)
    | .popTransfer j => .dec 2 (loc (.popTransferAdd j)) (exitLabel m a j.val)
    | .popTransferAdd j => .inc y (loc (.popTransfer j))

/-- Total finite program. The extra label is an unreachable padding HALT.
The initial scanned symbol is finite input-interface data. -/
def compile (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols) :
    Machine 2 (labelCount states symbols) where
  entry := pc (boundary m.start initial)
  instruction q :=
    if h : q.val < (labels states symbols).length then emit m ((labels states symbols)[q.val])
    else .halt

@[simp] theorem compile_row (m : SOnlyTapeStacks.Machine states symbols)
    (initial : Fin symbols) (l : Label states symbols) :
    (compile m initial).instruction (pc l) = emit m l := by
  have h := List.idxOf_lt_length_of_mem (mem_labels l)
  simp only [compile,pc,h,↓reduceDIte,List.getElem_idxOf]

/-- Literal assembled push rows, discharged against the total program. -/
def pushRows (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (l : Label states symbols) (a : SOnlyTapeStacks.Action states symbols)
    (ha : m.transition l.state l.scanned = some a) :
    PushRows (compile m initial) (pushReg a.move) 2 (symbols+1) (SOnlyTapeStacks.digit a.write) where
  entry := pc (withPhase l .pushEntry)
  multiplyAdd := mulLabel l
  transfer := pc (withPhase l .transfer)
  transferAdd := pc (withPhase l .transferAdd)
  digitAdd := digitLabel l (SOnlyTapeStacks.digit a.write)
  done := consumeLabel l 0
  entry_row := by simp [emit,ha,withPhase,mulLabel]
  multiply_rows := by
    intro j hj
    simp [mulLabel,hj,emit,withPhase,ha]
  multiply_back := by simp [mulLabel]
  transfer_row := by simp [emit,ha,withPhase,consumeLabel,digitLabel]
  transfer_add_row := by simp [emit,ha,withPhase]
  digit_rows := by
    intro j hj
    have hbase := SOnlyTapeStacks.digit_lt_base a.write
    have hjbase : j < symbols+1 := by omega
    simp [digitLabel,hj,hjbase,emit,withPhase,ha,consumeLabel]
  digit_done := by simp [digitLabel]

/-- Literal assembled residue and transfer rows. -/
def popRows (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (l : Label states symbols) (a : SOnlyTapeStacks.Action states symbols)
    (ha : m.transition l.state l.scanned = some a) :
    PopRows (compile m initial) (popReg a.move) 2 (symbols+1) where
  consume := consumeLabel l
  quotientAdd := pc (withPhase l .quotientAdd)
  transfer := fun j => pc (withPhase l (.popTransfer (residue symbols j)))
  transferAdd := fun j => pc (withPhase l (.popTransferAdd (residue symbols j)))
  done := exitLabel m a
  consume_rows := by
    intro j hj
    have hmin : min j symbols = j := Nat.min_eq_left (by omega)
    simp [consumeLabel,hj,emit,withPhase,ha,residue,hmin]
  cycle_end := by simp [consumeLabel]
  quotient_row := by simp [emit,ha,withPhase,consumeLabel]
  transfer_rows := by
    intro j hj
    have hmin : min j symbols = j := Nat.min_eq_left (by omega)
    simp [emit,withPhase,ha,residue,hmin]
  transfer_add_rows := by
    intro j hj
    simp [emit,ha,withPhase]

/-- Exactly two unbounded stack values and zero scratch at each checkpoint. -/
def registers (left right : Nat) : Fin 3 → Nat :=
  fun i => if i = 0 then left else if i = 1 then right else 0

@[simp] theorem registers_left (l r : Nat) : registers l r 0 = l := by simp [registers]
@[simp] theorem registers_right (l r : Nat) : registers l r 1 = r := by simp [registers]
@[simp] theorem registers_scratch (l r : Nat) : registers l r 2 = 0 := by simp [registers]

@[simp] theorem values_left (l r a : Nat) : values (registers l r) 0 2 a 0 = registers a r := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    simp only [Fin.ext_iff]
    change i.val = 0 ∨ i.val = 1 ∨ i.val = 2
    omega
  rcases hi with hi | hi | hi <;> subst i <;> simp [values,registers,put]

@[simp] theorem values_right (l r a : Nat) : values (registers l r) 1 2 a 0 = registers l a := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
    simp only [Fin.ext_iff]
    change i.val = 0 ∨ i.val = 1 ∨ i.val = 2
    omega
  rcases hi with hi | hi | hi <;> subst i <;> simp [values,registers,put]

def encode (c : SOnlyTapeStacks.EncodedConfig states symbols) :
    SourceState 2 (labelCount states symbols) :=
  ⟨registers c.left c.right,pc (boundary c.state c.scanned)⟩

/-- Every nonhalting arithmetic two-stack transition is compiled into a
positive finite number of literal source-machine instructions. -/
theorem action_executes (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (c : SOnlyTapeStacks.EncodedConfig states symbols) (a : SOnlyTapeStacks.Action states symbols)
    (ha : m.transition c.state c.scanned = some a) :
    ∃ time, 0 < time ∧ sourceRun (compile m initial) time (encode c) =
      encode (SOnlyTapeStacks.applyEncoded m.blank a c) := by
  let l := boundary c.state c.scanned
  have hal : m.transition l.state l.scanned = some a := ha
  cases hm : a.move with
  | stay =>
    refine ⟨1,by omega,?_⟩
    simp [sourceRun,sourceStep,encode,compile_row,emit,boundary,ha,hm,
      SOnlyTapeStacks.applyEncoded]
  | left =>
    have hfirst : sourceStep (compile m initial) (encode c) =
        ⟨registers c.left c.right,pc (withPhase l .pushEntry)⟩ := by
      simp [sourceStep,encode,emit,boundary,ha,hm,l,withPhase]
    obtain ⟨kp,hp⟩ := push_macro (compile m initial) (pushReg a.move) 2
      (by simp [hm,pushReg]) (symbols+1) (SOnlyTapeStacks.digit a.write)
      (pushRows m initial l a hal) (registers c.left c.right) c.right
    have hp' : sourceRun (compile m initial) kp
        ⟨registers c.left c.right,pc (withPhase l .pushEntry)⟩ =
        ⟨registers c.left ((symbols+1)*c.right+SOnlyTapeStacks.digit a.write),consumeLabel l 0⟩ := by
      simpa [pushRows,hm,pushReg] using hp
    obtain ⟨kr,hr⟩ := pop_macro_div_mod (compile m initial) (popReg a.move) 2
      (by simp [hm,popReg]) (symbols+1) (by omega) (popRows m initial l a hal)
      (registers c.left ((symbols+1)*c.right+SOnlyTapeStacks.digit a.write)) c.left
    have hr' : sourceRun (compile m initial) kr
        ⟨registers c.left ((symbols+1)*c.right+SOnlyTapeStacks.digit a.write),consumeLabel l 0⟩ =
        encode (SOnlyTapeStacks.applyEncoded m.blank a c) := by
      simpa [popRows,hm,popReg,encode,SOnlyTapeStacks.applyEncoded,exitLabel,Nat.add_comm] using hr
    refine ⟨1+(kp+kr),by omega,?_⟩
    rw [show 1+(kp+kr) = (kp+kr)+1 by omega,sourceRun,hfirst,sourceRun_add,hp',hr']
  | right =>
    have hfirst : sourceStep (compile m initial) (encode c) =
        ⟨registers c.left c.right,pc (withPhase l .pushEntry)⟩ := by
      simp [sourceStep,encode,emit,boundary,ha,hm,l,withPhase]
    obtain ⟨kp,hp⟩ := push_macro (compile m initial) (pushReg a.move) 2
      (by simp [hm,pushReg]) (symbols+1) (SOnlyTapeStacks.digit a.write)
      (pushRows m initial l a hal) (registers c.left c.right) c.left
    have hp' : sourceRun (compile m initial) kp
        ⟨registers c.left c.right,pc (withPhase l .pushEntry)⟩ =
        ⟨registers ((symbols+1)*c.left+SOnlyTapeStacks.digit a.write) c.right,consumeLabel l 0⟩ := by
      simpa [pushRows,hm,pushReg] using hp
    obtain ⟨kr,hr⟩ := pop_macro_div_mod (compile m initial) (popReg a.move) 2
      (by simp [hm,popReg]) (symbols+1) (by omega) (popRows m initial l a hal)
      (registers ((symbols+1)*c.left+SOnlyTapeStacks.digit a.write) c.right) c.right
    have hr' : sourceRun (compile m initial) kr
        ⟨registers ((symbols+1)*c.left+SOnlyTapeStacks.digit a.write) c.right,consumeLabel l 0⟩ =
        encode (SOnlyTapeStacks.applyEncoded m.blank a c) := by
      simpa [popRows,hm,popReg,encode,SOnlyTapeStacks.applyEncoded,exitLabel,Nat.add_comm] using hr
    refine ⟨1+(kp+kr),by omega,?_⟩
    rw [show 1+(kp+kr) = (kp+kr)+1 by omega,sourceRun,hfirst,sourceRun_add,hp',hr']

/-- Positive single-transition simulation with no implementation premises. -/
theorem encoded_step_executes (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (c c' : SOnlyTapeStacks.EncodedConfig states symbols)
    (hc : SOnlyTapeStacks.encodedStep m c = some c') :
    ∃ time, 0 < time ∧ sourceRun (compile m initial) time (encode c) = encode c' := by
  cases ha : m.transition c.state c.scanned with
  | none => simp [SOnlyTapeStacks.encodedStep,ha] at hc
  | some a =>
    have he : SOnlyTapeStacks.applyEncoded m.blank a c = c' := by
      simpa [SOnlyTapeStacks.encodedStep,ha] using hc
    rw [← he]
    exact action_executes m initial c a ha

/-- Halt alignment is exact at every represented boundary. -/
theorem encoded_boundary_halt (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (c : SOnlyTapeStacks.EncodedConfig states symbols) :
    (compile m initial).instruction (encode c).label = .halt ↔
      SOnlyTapeStacks.encodedStep m c = none := by
  cases ha : m.transition c.state c.scanned <;>
    simp [encode,emit,boundary,ha,SOnlyTapeStacks.encodedStep]

/-- No internal compiled state can halt prematurely: cofinal positive-time
checkpoints and halt absorption cover all source-machine microsteps. -/
theorem encoded_halting_iff (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (c : SOnlyTapeStacks.EncodedConfig states symbols) :
    (∃ t, (compile m initial).instruction (sourceRun (compile m initial) t (encode c)).label = .halt) ↔
    ∃ k, SOnlyTapeStacks.HaltsAfter (SOnlyTapeStacks.encodedStep m) k c :=
  SOnlyTapeCompilerCheckpoints.halting_iff (SOnlyTapeStacks.encodedStep m) encode (compile m initial)
    (encoded_step_executes m initial) (encoded_boundary_halt m initial) c

/-- The fixed controller depends only on the finite TM; only its declared
entry label depends on the first input symbol. -/
theorem instruction_independent (m : SOnlyTapeStacks.Machine states symbols)
    (a b : Fin symbols) : (compile m a).instruction = (compile m b).instruction := rfl

def inputMachine (m : SOnlyTapeStacks.Machine states symbols) (input : List (Fin symbols)) :
    Machine 2 (labelCount states symbols) := compile m (SOnlyTapeStacks.ray m.blank input 0)

/-- Read the head into finite control and code the remaining rightward input.
Both left stack and shared scratch are initially zero. -/
def inputValues (symbols : Nat) (input : List (Fin symbols)) : Fin 3 → Nat :=
  registers 0 (SOnlyTapeStacks.stackCode symbols input.tail)

@[simp] theorem input_initial (m : SOnlyTapeStacks.Machine states symbols)
    (input : List (Fin symbols)) :
    SOnlyMachine.initial (inputMachine m input) (inputValues symbols input) =
      encode (SOnlyTapeStacks.encodeStacks (SOnlyTapeStacks.stackInput m input)) := rfl

/-- Every finite conventional tape computation has an exact literal-register
checkpoint, preserving all represented tape cells through the two-stack bridge. -/
theorem input_tape_simulate (m : SOnlyTapeStacks.Machine states symbols)
    (input : List (Fin symbols)) (n : Nat) (tape : SOnlyTapeStacks.TapeConfig states symbols)
    (hrun : SOnlyTapeStacks.run (SOnlyTapeStacks.tapeStep m) n
      (SOnlyTapeStacks.tapeInput m input) = some tape) :
    ∃ stacks elapsed, n ≤ elapsed ∧ SOnlyTapeStacks.Represents m.blank tape stacks ∧
      sourceRun (inputMachine m input) elapsed
        (SOnlyMachine.initial (inputMachine m input) (inputValues symbols input)) =
          encode (SOnlyTapeStacks.encodeStacks stacks) := by
  have hrep := SOnlyTapeStacks.input_run_represents m input n
  rw [hrun] at hrep
  cases hs : SOnlyTapeStacks.run (SOnlyTapeStacks.stackStep m) n
      (SOnlyTapeStacks.stackInput m input) with
  | none => simp [hs,SOnlyTapeStacks.OptionRelated] at hrep
  | some stacks =>
    have hr : SOnlyTapeStacks.run (SOnlyTapeStacks.encodedStep m) n
        (SOnlyTapeStacks.encodeStacks (SOnlyTapeStacks.stackInput m input)) =
        some (SOnlyTapeStacks.encodeStacks stacks) := by
      rw [SOnlyTapeStacks.encodedRun_encodeStacks,hs]
      rfl
    obtain ⟨elapsed,lower,executes⟩ := SOnlyTapeCompilerCheckpoints.simulate_run
      (SOnlyTapeStacks.encodedStep m) encode (inputMachine m input)
      (encoded_step_executes m _) n _ _ hr
    refine ⟨stacks,elapsed,lower,?_,?_⟩
    · simpa [hs,SOnlyTapeStacks.OptionRelated] using hrep
    · simpa using executes

/-- Exact conventional finite-TM halting equivalence, for every finite input,
with the concrete compiled machine and the ordinary source `initial` interface.
No bound on tape space or running time is an input to the compiler. -/
theorem input_halting_iff (m : SOnlyTapeStacks.Machine states symbols)
    (input : List (Fin symbols)) :
    (∃ n, SOnlyTapeStacks.HaltsAfter (SOnlyTapeStacks.tapeStep m) n
      (SOnlyTapeStacks.tapeInput m input)) ↔
    ∃ t, (inputMachine m input).instruction
      (sourceRun (inputMachine m input) t
        (SOnlyMachine.initial (inputMachine m input) (inputValues symbols input))).label = .halt := by
  rw [input_initial]
  unfold inputMachine
  rw [encoded_halting_iff]
  constructor
  · rintro ⟨n,h⟩
    exact ⟨n,(SOnlyTapeStacks.input_encoded_haltsAfter_iff m input n).mp h⟩
  · rintro ⟨n,h⟩
    exact ⟨n,(SOnlyTapeStacks.input_encoded_haltsAfter_iff m input n).mpr h⟩

/-- Register zero observes the chosen finite left-stack code. This is not a
claim that trailing blanks have been removed or that the head has been returned
to an output origin. Those are separate output-normalization obligations. -/
@[simp] theorem encoded_left_result (s : SOnlyTapeStacks.StackConfig states symbols) :
    (encode (SOnlyTapeStacks.encodeStacks s)).value 0 =
      SOnlyTapeStacks.stackCode symbols s.left := by simp [encode,SOnlyTapeStacks.encodeStacks]

/-- The concrete compiler also simulates the finite-list stack machine. -/
theorem stack_step_executes (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (s s' : SOnlyTapeStacks.StackConfig states symbols)
    (h : SOnlyTapeStacks.stackStep m s = some s') :
    ∃ time, 0 < time ∧ sourceRun (compile m initial) time
      (encode (SOnlyTapeStacks.encodeStacks s)) = encode (SOnlyTapeStacks.encodeStacks s') := by
  apply encoded_step_executes
  rw [SOnlyTapeStacks.encodedStep_encodeStacks,h]
  rfl

theorem stack_boundary_halt (m : SOnlyTapeStacks.Machine states symbols) (initial : Fin symbols)
    (s : SOnlyTapeStacks.StackConfig states symbols) :
    (compile m initial).instruction (encode (SOnlyTapeStacks.encodeStacks s)).label = .halt ↔
      SOnlyTapeStacks.stackStep m s = none := by
  rw [encoded_boundary_halt,SOnlyTapeStacks.encodedStep_encodeStacks]
  cases SOnlyTapeStacks.stackStep m s <;> simp

/-- Exact numerical-result correspondence for the chosen finite left stack,
including halts observed between compiled transition checkpoints.
This deliberately does not identify that code with a normalized tape output. -/
theorem input_left_stack_result_iff (m : SOnlyTapeStacks.Machine states symbols)
    (input : List (Fin symbols)) (result : Nat) :
    (∃ t, (inputMachine m input).instruction
        (sourceRun (inputMachine m input) t
          (SOnlyMachine.initial (inputMachine m input) (inputValues symbols input))).label = .halt ∧
      (sourceRun (inputMachine m input) t
        (SOnlyMachine.initial (inputMachine m input) (inputValues symbols input))).value 0 = result) ↔
    ∃ n stacks, SOnlyTapeStacks.run (SOnlyTapeStacks.stackStep m) n
        (SOnlyTapeStacks.stackInput m input) = some stacks ∧
      SOnlyTapeStacks.stackStep m stacks = none ∧
      SOnlyTapeStacks.stackCode symbols stacks.left = result := by
  rw [input_initial]
  exact SOnlyTapeCompilerCheckpoints.result_iff (SOnlyTapeStacks.stackStep m)
    (fun s => encode (SOnlyTapeStacks.encodeStacks s)) (inputMachine m input)
    (stack_step_executes m _) (stack_boundary_halt m _)
    (fun s => SOnlyTapeStacks.stackCode symbols s.left) (fun c => c.value 0)
    encoded_left_result (SOnlyTapeStacks.stackInput m input) result

@[simp] theorem phases_length (symbols : Nat) :
    (phases symbols).length = 5*(symbols+1)+5 := by
  simp [phases]
  omega

private theorem length_flatMap_constant (xs : List α) (f : α → List β)
    (k : Nat) (h : ∀ x, (f x).length = k) : (xs.flatMap f).length = xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [h,ih,Nat.succ_mul,Nat.add_comm]

/-- An explicit size formula: five scalar phases and five base-sized chains
per state/scanned-symbol pair, plus one padding label in `PC`. -/
theorem labelCount_eq (states symbols : Nat) :
    labelCount states symbols = states * (symbols * (5*(symbols+1)+5)) := by
  unfold labelCount labels
  rw [length_flatMap_constant _ _ (symbols*(5*(symbols+1)+5))]
  · simp
  · intro q
    rw [length_flatMap_constant _ _ (5*(symbols+1)+5)]
    · simp
    · intro a
      simp

end SOnlyTapeCompiler

#print axioms SOnlyTapeCompiler.action_executes
#print axioms SOnlyTapeCompiler.input_tape_simulate
#print axioms SOnlyTapeCompiler.input_halting_iff

#print axioms SOnlyTapeCompiler.compile
#print axioms SOnlyTapeCompiler.pc
#print axioms SOnlyTapeCompiler.pushRows
#print axioms SOnlyTapeCompiler.popRows
#print axioms SOnlyTapeCompiler.compile_row
#print axioms SOnlyTapeCompiler.values_left

#print axioms SOnlyTapeCompiler.input_left_stack_result_iff
#print axioms SOnlyTapeCompiler.labelCount_eq
