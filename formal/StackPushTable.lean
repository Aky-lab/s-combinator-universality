import StackMacros

/-! A total finite instruction table for the push macro. -/
namespace SOnlyStack
open SOnlyMachine
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-- Label space: `base` multiply increments, three loop rows, `digit`
    final increments, and one halting row. -/
abbrev PushLabel (base digit : Nat) := Fin (base + digit + 3 + 1)

def pushEntry (base digit : Nat) : PushLabel base digit := ⟨base, by omega⟩
def pushMultiplyAdd (base digit j : Nat) : PushLabel base digit :=
  ⟨min j base, by have := Nat.min_le_right j base; omega⟩
def pushTransfer (base digit : Nat) : PushLabel base digit := ⟨base+1, by omega⟩
def pushTransferAdd (base digit : Nat) : PushLabel base digit := ⟨base+2, by omega⟩
def pushDigitAdd (base digit j : Nat) : PushLabel base digit :=
  ⟨base+3+min j digit, by have := Nat.min_le_right j digit; omega⟩
def pushDone (base digit : Nat) : PushLabel base digit := ⟨base+digit+3, by omega⟩

/-- This machine has exactly two registers and a total, explicit table.
Register zero is the stack; register one is restored scratch. -/
def pushMachine (base digit : Nat) : Machine 1 (base+digit+3) where
  entry := pushEntry base digit
  instruction q :=
    if q.val < base then
      .inc 1 (pushMultiplyAdd base digit (q.val+1))
    else if q.val = base then
      .dec 0 (pushMultiplyAdd base digit 0) (pushTransfer base digit)
    else if q.val = base+1 then
      .dec 1 (pushTransferAdd base digit) (pushDigitAdd base digit 0)
    else if q.val = base+2 then
      .inc 0 (pushTransfer base digit)
    else if q.val < base+3+digit then
      .inc 0 (pushDigitAdd base digit (q.val-(base+3)+1))
    else .halt

theorem pushMachine_entry_row (base digit : Nat) :
    (pushMachine base digit).instruction (pushEntry base digit) =
      .dec 0 (pushMultiplyAdd base digit 0) (pushTransfer base digit) := by
  simp [pushMachine,pushEntry]

theorem pushMachine_multiply_rows (base digit j : Nat) (hj : j < base) :
    (pushMachine base digit).instruction (pushMultiplyAdd base digit j) =
      .inc 1 (pushMultiplyAdd base digit (j+1)) := by
  simp [pushMachine,pushMultiplyAdd,Nat.min_eq_left (Nat.le_of_lt hj),hj]

theorem pushMachine_multiply_back (base digit : Nat) :
    pushMultiplyAdd base digit base = pushEntry base digit := by
  simp [pushMultiplyAdd,pushEntry]

theorem pushMachine_transfer_row (base digit : Nat) :
    (pushMachine base digit).instruction (pushTransfer base digit) =
      .dec 1 (pushTransferAdd base digit) (pushDigitAdd base digit 0) := by
  simp [pushMachine,pushTransfer]

theorem pushMachine_transfer_add_row (base digit : Nat) :
    (pushMachine base digit).instruction (pushTransferAdd base digit) =
      .inc 0 (pushTransfer base digit) := by
  simp [pushMachine,pushTransferAdd]

theorem pushMachine_digit_rows (base digit j : Nat) (hj : j < digit) :
    (pushMachine base digit).instruction (pushDigitAdd base digit j) =
      .inc 0 (pushDigitAdd base digit (j+1)) := by
  have hmin : min j digit = j := Nat.min_eq_left (Nat.le_of_lt hj)
  have hn₀ : ¬ base+3+j < base := by omega
  have hn₁ : ¬ base+3+j = base := by omega
  have hn₂ : ¬ base+3+j = base+1 := by omega
  have hn₃ : ¬ base+3+j = base+2 := by omega
  have hlt : base+3+j < base+3+digit := by omega
  simp [pushMachine,pushDigitAdd,hmin,hn₀,hn₁,hn₂,hn₃,hlt]

theorem pushMachine_digit_done (base digit : Nat) :
    pushDigitAdd base digit digit = pushDone base digit := by
  apply Fin.ext
  simp [pushDigitAdd,pushDone]
  omega

theorem pushMachine_done_row (base digit : Nat) :
    (pushMachine base digit).instruction (pushDone base digit) = .halt := by
  have hn₀ : ¬ base+digit+3 < base := by omega
  have hn₁ : ¬ base+digit+3 = base := by omega
  have hn₂ : ¬ base+digit+3 = base+1 := by omega
  have hn₃ : ¬ base+digit+3 = base+2 := by omega
  have hn₄ : ¬ base+digit+3 < base+3+digit := by omega
  simp [pushMachine,pushDone,hn₀,hn₁,hn₂,hn₃,hn₄]

/-- All row obligations are discharged for the concrete finite machine. -/
def pushRows (base digit : Nat) : PushRows (pushMachine base digit) 0 1 base digit where
  entry := pushEntry base digit
  multiplyAdd := pushMultiplyAdd base digit
  transfer := pushTransfer base digit
  transferAdd := pushTransferAdd base digit
  digitAdd := pushDigitAdd base digit
  done := pushDone base digit
  entry_row := pushMachine_entry_row base digit
  multiply_rows := pushMachine_multiply_rows base digit
  multiply_back := pushMachine_multiply_back base digit
  transfer_row := pushMachine_transfer_row base digit
  transfer_add_row := pushMachine_transfer_add_row base digit
  digit_rows := pushMachine_digit_rows base digit
  digit_done := pushMachine_digit_done base digit

/-- Actual execution from the declared entry reaches `base*a+digit`, with
scratch zero and no assumptions on instruction rows. -/
theorem pushMachine_correct (base digit : Nat) (v : Fin 2 → Nat) (a : Nat) :
    ∃ k, sourceRun (pushMachine base digit) k
      ⟨values v 0 1 a 0, (pushMachine base digit).entry⟩ =
      ⟨values v 0 1 (base*a+digit) 0,pushDone base digit⟩ := by
  exact push_macro (pushMachine base digit) 0 1 (by decide) base digit
    (pushRows base digit) v a

/-- The reached state is genuinely halting. -/
theorem pushMachine_final_fixed (base digit : Nat) (v : Fin 2 → Nat) :
    sourceStep (pushMachine base digit) ⟨v,pushDone base digit⟩ =
      ⟨v,pushDone base digit⟩ := by
  simp [sourceStep,pushMachine_done_row]

end SOnlyStack
