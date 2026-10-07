import SOnlyMachine

/-! Finite-stack macros for the ordinary register-machine source.
The existing proof modules are imported without modification. -/
namespace SOnlyStack
open SOnlyMachine
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

variable {d n : Nat}

theorem sourceRun_add (M : Machine d n) (a b : Nat) (s : SourceState d n) :
    sourceRun M (a + b) s = sourceRun M b (sourceRun M a s) := by
  induction a generalizing s with
  | zero => simp [sourceRun]
  | succ a ih => simpa [sourceRun, Nat.succ_add] using ih (sourceStep M s)

def Reaches (M : Machine d n) (s t : SourceState d n) : Prop :=
  ∃ k, sourceRun M k s = t

theorem Reaches.refl (M : Machine d n) (s : SourceState d n) : Reaches M s s := ⟨0, rfl⟩
theorem Reaches.trans {M : Machine d n} {s t u : SourceState d n}
    (h : Reaches M s t) (h' : Reaches M t u) : Reaches M s u := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  exact ⟨a+b, by rw [sourceRun_add,ha,hb]⟩
theorem Reaches.step {M : Machine d n} {s t : SourceState d n}
    (h : sourceStep M s = t) : Reaches M s t := ⟨1,h⟩

theorem inc_step (M : Machine d n) (v : Fin (d+1) → Nat)
    (i : Fin (d+1)) (a b : Fin (n+1)) (h : M.instruction a = .inc i b) :
    Reaches M ⟨v,a⟩ ⟨put v i (v i+1),b⟩ :=
  Reaches.step (by simp [sourceStep,h])

theorem dec_pos_step (M : Machine d n) (v : Fin (d+1) → Nat)
    (i : Fin (d+1)) (a b c : Fin (n+1)) (h : M.instruction a = .dec i b c)
    (hv : v i ≠ 0) : Reaches M ⟨v,a⟩ ⟨put v i (v i-1),b⟩ :=
  Reaches.step (by simp [sourceStep,h,hv])

theorem dec_zero_step (M : Machine d n) (v : Fin (d+1) → Nat)
    (i : Fin (d+1)) (a b c : Fin (n+1)) (h : M.instruction a = .dec i b c)
    (hv : v i = 0) : Reaches M ⟨v,a⟩ ⟨v,c⟩ :=
  Reaches.step (by simp [sourceStep,h,hv])

/-- A finite straight-line sequence of exactly `count` INC instructions. -/
theorem inc_chain (M : Machine d n) (i : Fin (d+1)) (count : Nat)
    (label : Nat → Fin (n+1))
    (code : ∀ j, j < count → M.instruction (label j) = .inc i (label (j+1)))
    (v : Fin (d+1) → Nat) :
    sourceRun M count ⟨v,label 0⟩ = ⟨put v i (v i+count),label count⟩ := by
  induction count generalizing label v with
  | zero => simp [sourceRun]
  | succ count ih =>
    rw [sourceRun]
    have hc := code 0 (by omega)
    simp only [sourceStep,hc]
    have h := ih (fun j => label (j+1))
      (by intro j hj; exact code (j+1) (by omega)) (put v i (v i+1))
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Two finite instructions implement an ordinary transfer loop. -/
theorem transfer (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (loop add done : Fin (n+1))
    (hloop : M.instruction loop = .dec t add done)
    (hadd : M.instruction add = .inc x loop)
    (v : Fin (d+1) → Nat) (k : Nat) :
    Reaches M ⟨put v t k,loop⟩
      ⟨put (put v t 0) x (v x+k),done⟩ := by
  induction k generalizing v with
  | zero =>
    have h := dec_zero_step M (put v t 0) t loop add done hloop (by simp)
    have he : put (put v t 0) x (v x) = put v t 0 := by
      have hx : put v t 0 x = v x := by simp [hne]
      rw [← hx, put_self]
    simpa [he] using h
  | succ k ih =>
    have h₁ := dec_pos_step M (put v t (k+1)) t loop add done hloop (by simp)
    have h₂ := inc_step M (put v t k) x add loop hadd
    have h₃ := ih (put v x (v x+1))
    have hc : put (put v t k) x (v x+1) = put (put v x (v x+1)) t k :=
      put_comm v t x k (v x+1) (Ne.symm hne)
    have hjoin : Reaches M ⟨put v t (k+1),loop⟩
        ⟨put (put v x (v x+1)) t k,loop⟩ := by
      apply h₁.trans
      simpa [hne,hc] using h₂
    apply hjoin.trans
    have he : put (put (put v x (v x+1)) t 0) x (put v x (v x+1) x+k) =
        put (put v t 0) x (v x+(k+1)) := by
      funext j
      by_cases hj : j=x <;> by_cases ht : j=t <;> simp_all [put,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rw [he] at h₃
    exact h₃

/-- Canonical values for the stack and its single scratch register. -/
def values (v : Fin (d+1) → Nat) (x t : Fin (d+1)) (a b : Nat) :=
  put (put v x a) t b

@[simp] theorem values_t (v : Fin (d+1) → Nat) (x t : Fin (d+1)) (a b : Nat) :
    values v x t a b t = b := by simp [values]
@[simp] theorem values_x (v : Fin (d+1) → Nat) (x t : Fin (d+1)) (hne : x ≠ t) (a b : Nat) :
    values v x t a b x = a := by simp [values,hne]
@[simp] theorem values_put_t (v : Fin (d+1) → Nat) (x t : Fin (d+1)) (a b c : Nat) :
    put (values v x t a b) t c = values v x t a c := by simp [values]
@[simp] theorem values_put_x (v : Fin (d+1) → Nat) (x t : Fin (d+1)) (hne : x ≠ t) (a b c : Nat) :
    put (values v x t a b) x c = values v x t c b := by
  funext j
  by_cases hj : j=x <;> by_cases ht : j=t <;> simp_all [values,put]

/-- The literal decrement / `base` increments loop multiplies a stack value.
The hypotheses are its finite instruction rows in an otherwise arbitrary machine. -/
theorem multiply_loop (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (loop done : Fin (n+1)) (add : Nat → Fin (n+1))
    (hloop : M.instruction loop = .dec x (add 0) done)
    (hadd : ∀ j, j < base → M.instruction (add j) = .inc t (add (j+1)))
    (hback : add base = loop) (v : Fin (d+1) → Nat) (k z : Nat) :
    Reaches M ⟨values v x t k z,loop⟩ ⟨values v x t 0 (z+base*k),done⟩ := by
  induction k generalizing z with
  | zero =>
    simpa using dec_zero_step M (values v x t 0 z) x loop (add 0) done hloop (by simp [hne])
  | succ k ih =>
    have h₁ := dec_pos_step M (values v x t (k+1) z) x loop (add 0) done hloop (by simp [hne])
    have h₂ : Reaches M ⟨values v x t k z,add 0⟩ ⟨values v x t k (z+base),loop⟩ := by
      exact ⟨base,by simpa [hback] using inc_chain M t base add hadd (values v x t k z)⟩
    have h₁' : Reaches M ⟨values v x t (k+1) z,loop⟩ ⟨values v x t k z,add 0⟩ := by
      simpa [hne] using h₁
    have h := h₁'.trans (h₂.trans (ih (z+base)))
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Transfer with canonical register values, preserving all other registers. -/
theorem transfer_values (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (loop add done : Fin (n+1))
    (hloop : M.instruction loop = .dec t add done)
    (hadd : M.instruction add = .inc x loop)
    (v : Fin (d+1) → Nat) (a b : Nat) :
    Reaches M ⟨values v x t a b,loop⟩ ⟨values v x t (a+b) 0,done⟩ := by
  have h := transfer M x t hne loop add done hloop hadd (put v x a) b
  have he : put (put (put v x a) t 0) x (put v x a x+b) = values v x t (a+b) 0 := by
    simp only [put_same]
    exact values_put_x v x t hne a 0 (a+b)
  rw [he] at h
  exact h

/-- A push block consists of a multiplication loop, transfer loop, and fixed
finite digit-increment chain. There are no macro instructions in its semantics. -/
structure PushRows (M : Machine d n) (x t : Fin (d+1)) (base digit : Nat) where
  entry : Fin (n+1)
  multiplyAdd : Nat → Fin (n+1)
  transfer : Fin (n+1)
  transferAdd : Fin (n+1)
  digitAdd : Nat → Fin (n+1)
  done : Fin (n+1)
  entry_row : M.instruction entry = .dec x (multiplyAdd 0) transfer
  multiply_rows : ∀ j, j < base → M.instruction (multiplyAdd j) = .inc t (multiplyAdd (j+1))
  multiply_back : multiplyAdd base = entry
  transfer_row : M.instruction transfer = .dec t transferAdd (digitAdd 0)
  transfer_add_row : M.instruction transferAdd = .inc x transfer
  digit_rows : ∀ j, j < digit → M.instruction (digitAdd j) = .inc x (digitAdd (j+1))
  digit_done : digitAdd digit = done

/-- Quantified finite actual execution of push, with exactly one scratch register
restored to zero. Arbitrary untouched registers retain their original values. -/
theorem push_macro (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base digit : Nat) (rows : PushRows M x t base digit)
    (v : Fin (d+1) → Nat) (a : Nat) :
    ∃ k, sourceRun M k ⟨values v x t a 0,rows.entry⟩ =
      ⟨values v x t (base*a+digit) 0,rows.done⟩ := by
  have h₁ := multiply_loop M x t hne base rows.entry rows.transfer rows.multiplyAdd
    rows.entry_row rows.multiply_rows rows.multiply_back v a 0
  have h₂ := transfer_values M x t hne rows.transfer rows.transferAdd (rows.digitAdd 0)
    rows.transfer_row rows.transfer_add_row v 0 (base*a)
  have h₃ : Reaches M ⟨values v x t (base*a) 0,rows.digitAdd 0⟩
      ⟨values v x t (base*a+digit) 0,rows.done⟩ := by
    refine ⟨digit,?_⟩
    simpa [hne,rows.digit_done] using
      inc_chain M x digit rows.digitAdd rows.digit_rows (values v x t (base*a) 0)
  have h₁' : Reaches M ⟨values v x t a 0,rows.entry⟩
      ⟨values v x t 0 (base*a),rows.transfer⟩ := by simpa using h₁
  have h₂' : Reaches M ⟨values v x t 0 (base*a),rows.transfer⟩
      ⟨values v x t (base*a) 0,rows.digitAdd 0⟩ := by simpa using h₂
  exact h₁'.trans (h₂'.trans h₃)

/-- A finite chain of successful ordinary DECJZ instructions. -/
theorem dec_chain (M : Machine d n) (i : Fin (d+1)) (count : Nat)
    (label failure : Nat → Fin (n+1))
    (code : ∀ j, j < count → M.instruction (label j) = .dec i (label (j+1)) (failure j))
    (v : Fin (d+1) → Nat) (a : Nat) :
    sourceRun M count ⟨put v i (a+count),label 0⟩ = ⟨put v i a,label count⟩ := by
  induction count generalizing label failure with
  | zero => simp [sourceRun]
  | succ count ih =>
    rw [sourceRun]
    have hc := code 0 (by omega)
    simp only [sourceStep,hc,put_same]
    have hn : a+(count+1) ≠ 0 := by omega
    simp only [hn,↓reduceIte,put_put]
    have he : a+(count+1)-1 = a+count := by omega
    rw [he]
    simpa [Nat.add_assoc] using ih (fun j => label (j+1)) (fun j => failure (j+1))
      (by intro j hj; exact code (j+1) (by omega))

/-- The finite residue cycle and one residue-specific transfer loop per digit. -/
structure PopRows (M : Machine d n) (x t : Fin (d+1)) (base : Nat) where
  consume : Nat → Fin (n+1)
  quotientAdd : Fin (n+1)
  transfer : Nat → Fin (n+1)
  transferAdd : Nat → Fin (n+1)
  done : Nat → Fin (n+1)
  consume_rows : ∀ j, j < base → M.instruction (consume j) = .dec x (consume (j+1)) (transfer j)
  cycle_end : consume base = quotientAdd
  quotient_row : M.instruction quotientAdd = .inc t (consume 0)
  transfer_rows : ∀ j, j < base → M.instruction (transfer j) = .dec t (transferAdd j) (done j)
  transfer_add_rows : ∀ j, j < base → M.instruction (transferAdd j) = .inc x (transfer j)

/-- Every full residue cycle consumes exactly `base` stack units and increments
scratch once, by executing `base+1` ordinary source instructions. -/
theorem pop_cycle (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat) (a z : Nat) :
    Reaches M ⟨values v x t (a+base) z,rows.consume 0⟩
      ⟨values v x t a (z+1),rows.consume 0⟩ := by
  have hc := dec_chain M x base rows.consume rows.transfer rows.consume_rows
    (values v x t 0 z) a
  have h₁ : Reaches M ⟨values v x t (a+base) z,rows.consume 0⟩
      ⟨values v x t a z,rows.quotientAdd⟩ := by
    exact ⟨base,by simpa [hne,rows.cycle_end] using hc⟩
  have h₂ := inc_step M (values v x t a z) t rows.quotientAdd (rows.consume 0) rows.quotient_row
  apply h₁.trans
  simpa using h₂

/-- Quotient/remainder computation is a terminating finite-control execution,
proved for all quotient and residue values, rather than assumed as an oracle. -/
theorem pop_consume (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat)
    (q r z : Nat) (hr : r < base) :
    Reaches M ⟨values v x t (base*q+r) z,rows.consume 0⟩
      ⟨values v x t 0 (z+q),rows.transfer r⟩ := by
  induction q generalizing z with
  | zero =>
    have hc := dec_chain M x r rows.consume rows.transfer
      (by intro j hj; exact rows.consume_rows j (by omega)) (values v x t 0 z) 0
    have h₁ : Reaches M ⟨values v x t r z,rows.consume 0⟩ ⟨values v x t 0 z,rows.consume r⟩ := by
      exact ⟨r,by simpa [hne] using hc⟩
    have h₂ := dec_zero_step M (values v x t 0 z) x (rows.consume r)
      (rows.consume (r+1)) (rows.transfer r) (rows.consume_rows r hr) (by simp [hne])
    simpa using h₁.trans h₂
  | succ q ih =>
    have h₁ := pop_cycle M x t hne base rows v (base*q+r) z
    have h := h₁.trans (ih (z+1))
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Pop returns the quotient in the stack register and the remainder in its exit
label. Scratch is reset to zero, including empty-stack pop. -/
theorem pop_macro (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat)
    (q r : Nat) (hr : r < base) :
    ∃ k, sourceRun M k ⟨values v x t (base*q+r) 0,rows.consume 0⟩ =
      ⟨values v x t q 0,rows.done r⟩ := by
  have h₁ := pop_consume M x t hne base rows v q r 0 hr
  have h₂ := transfer_values M x t hne (rows.transfer r) (rows.transferAdd r) (rows.done r)
    (rows.transfer_rows r hr) (rows.transfer_add_rows r hr) v 0 q
  have h₁' : Reaches M ⟨values v x t (base*q+r) 0,rows.consume 0⟩
      ⟨values v x t 0 q,rows.transfer r⟩ := by simpa using h₁
  have h₂' : Reaches M ⟨values v x t 0 q,rows.transfer r⟩
      ⟨values v x t q 0,rows.done r⟩ := by simpa using h₂
  exact h₁'.trans h₂'

/-- The same operational theorem stated with ordinary natural division/modulo. -/
theorem pop_macro_div_mod (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (hbase : 0 < base) (rows : PopRows M x t base)
    (v : Fin (d+1) → Nat) (a : Nat) :
    ∃ k, sourceRun M k ⟨values v x t a 0,rows.consume 0⟩ =
      ⟨values v x t (a/base) 0,rows.done (a%base)⟩ := by
  have h := pop_macro M x t hne base rows v (a/base) (a%base) (Nat.mod_lt a hbase)
  have he : base*(a/base)+a%base = a := by
    simpa [Nat.add_comm] using Nat.mod_add_div a base
  simpa [he] using h

end SOnlyStack
