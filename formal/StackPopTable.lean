import StackMacros

namespace SOnlyStack
open SOnlyMachine
set_option maxHeartbeats 4000000

namespace PopTable

def consume (k j : Nat) : Fin (4*(k+1)+1) := ⟨min j (k+1), by omega⟩
def quotientAdd (k : Nat) : Fin (4*(k+1)+1) := ⟨k+1,by omega⟩
def transfer (k j : Nat) : Fin (4*(k+1)+1) := ⟨k+2+min j k,by have := Nat.min_le_right j k; omega⟩
def transferAdd (k j : Nat) : Fin (4*(k+1)+1) := ⟨2*(k+1)+1+min j k,by have := Nat.min_le_right j k; omega⟩
def done (k j : Nat) : Fin (4*(k+1)+1) := ⟨3*(k+1)+1+min j k,by have := Nat.min_le_right j k; omega⟩

/-- A literal finite INC/DECJZ/HALT program for pop, for base `k+1`.
Its `4*(k+1)+1` labels contain no primitive arithmetic operations. -/
def machine {d : Nat} (k : Nat) (x t : Fin (d+1)) : Machine d (4*(k+1)) where
  entry := consume k 0
  instruction q :=
    if q.val < k+1 then .dec x (consume k (q.val+1)) (transfer k q.val)
    else if q.val = k+1 then .inc t (consume k 0)
    else if q.val ≤ 2*(k+1) then .dec t (transferAdd k (q.val-(k+2))) (done k (q.val-(k+2)))
    else if q.val ≤ 3*(k+1) then .inc x (transfer k (q.val-(2*(k+1)+1)))
    else .halt

@[simp] theorem consume_row {d : Nat} (k : Nat) (x t : Fin (d+1)) (j : Nat) (hj : j < k+1) :
    (machine k x t).instruction (consume k j) = .dec x (consume k (j+1)) (transfer k j) := by
  simp [machine,consume,Nat.min_eq_left (by omega : j ≤ k+1),hj]

@[simp] theorem cycle_end (k : Nat) : consume k (k+1) = quotientAdd k := by
  simp [consume,quotientAdd]

@[simp] theorem quotient_row {d : Nat} (k : Nat) (x t : Fin (d+1)) :
    (machine k x t).instruction (quotientAdd k) = .inc t (consume k 0) := by
  simp [machine,quotientAdd]

@[simp] theorem transfer_row {d : Nat} (k : Nat) (x t : Fin (d+1)) (j : Nat) (hj : j < k+1) :
    (machine k x t).instruction (transfer k j) = .dec t (transferAdd k j) (done k j) := by
  have hmin : min j k = j := Nat.min_eq_left (by omega)
  have hlt : ¬ k+2+j < k+1 := by omega
  have hne : k+2+j ≠ k+1 := by omega
  have hle : k+2+j ≤ 2*(k+1) := by omega
  have hsub : k+2+j-(k+2) = j := by omega
  simp only [machine,transfer,hmin,Fin.val_mk,hlt,hne,hle,↓reduceIte,hsub]

@[simp] theorem transfer_add_row {d : Nat} (k : Nat) (x t : Fin (d+1)) (j : Nat) (hj : j < k+1) :
    (machine k x t).instruction (transferAdd k j) = .inc x (transfer k j) := by
  have hmin : min j k = j := Nat.min_eq_left (by omega)
  have hlt : ¬ 2*(k+1)+1+j < k+1 := by omega
  have hne : 2*(k+1)+1+j ≠ k+1 := by omega
  have hnle : ¬ 2*(k+1)+1+j ≤ 2*(k+1) := by omega
  have hle : 2*(k+1)+1+j ≤ 3*(k+1) := by omega
  have hsub : 2*(k+1)+1+j-(2*(k+1)+1) = j := by omega
  simp only [machine,transferAdd,hmin,Fin.val_mk,hlt,hne,hnle,hle,↓reduceIte,hsub]

@[simp] theorem done_row {d : Nat} (k : Nat) (x t : Fin (d+1)) (j : Nat) (hj : j < k+1) :
    (machine k x t).instruction (done k j) = .halt := by
  have hmin : min j k = j := Nat.min_eq_left (by omega)
  have hlt : ¬ 3*(k+1)+1+j < k+1 := by omega
  have hne : 3*(k+1)+1+j ≠ k+1 := by omega
  have hnle : ¬ 3*(k+1)+1+j ≤ 2*(k+1) := by omega
  have hnle' : ¬ 3*(k+1)+1+j ≤ 3*(k+1) := by omega
  simp only [machine,done,hmin,Fin.val_mk,hlt,hne,hnle,hnle',↓reduceIte]

/-- Every operational macro hypothesis is discharged by the explicit table. -/
def rows {d : Nat} (k : Nat) (x t : Fin (d+1)) : PopRows (machine k x t) x t (k+1) where
  consume := consume k
  quotientAdd := quotientAdd k
  transfer := transfer k
  transferAdd := transferAdd k
  done := done k
  consume_rows := consume_row k x t
  cycle_end := cycle_end k
  quotient_row := quotient_row k x t
  transfer_rows := transfer_row k x t
  transfer_add_rows := transfer_add_row k x t

/-- Fully instantiated sourceRun pop theorem for every positive base. -/
theorem executes {d : Nat} (k : Nat) (x t : Fin (d+1)) (hne : x ≠ t)
    (v : Fin (d+1) → Nat) (a : Nat) :
    ∃ time, sourceRun (machine k x t) time ⟨values v x t a 0,consume k 0⟩ =
      ⟨values v x t (a/(k+1)) 0,done k (a%(k+1))⟩ :=
  pop_macro_div_mod (machine k x t) x t hne (k+1) (by omega) (rows k x t) v a

end PopTable
end SOnlyStack
