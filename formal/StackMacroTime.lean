import StackMacros

/-! Exact positive execution lengths for composable finite stack macros. -/
namespace SOnlyStack
open SOnlyMachine
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {d n : Nat}

theorem sourceRun_join (M : Machine d n) {a b : Nat} {s t u : SourceState d n}
    (h : sourceRun M a s = t) (h' : sourceRun M b t = u) :
    sourceRun M (a+b) s = u := by rw [sourceRun_add,h,h']

theorem transfer_exact (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (loop add done : Fin (n+1))
    (hloop : M.instruction loop = .dec t add done)
    (hadd : M.instruction add = .inc x loop)
    (v : Fin (d+1) → Nat) (a b : Nat) :
    sourceRun M (2*b+1) ⟨values v x t a b,loop⟩ = ⟨values v x t (a+b) 0,done⟩ := by
  induction b generalizing a with
  | zero => simp [sourceRun,sourceStep,hloop]
  | succ b ih =>
    have htwo : sourceRun M 2 ⟨values v x t a (b+1),loop⟩ =
        ⟨values v x t (a+1) b,loop⟩ := by
      simp [sourceRun,sourceStep,hloop,hadd,hne]
    have h := sourceRun_join M htwo (ih (a+1))
    have he : 2+(2*b+1) = 2*(b+1)+1 := by omega
    rw [he] at h
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem multiply_exact (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (loop done : Fin (n+1)) (add : Nat → Fin (n+1))
    (hloop : M.instruction loop = .dec x (add 0) done)
    (hadd : ∀ j, j < base → M.instruction (add j) = .inc t (add (j+1)))
    (hback : add base = loop) (v : Fin (d+1) → Nat) (a z : Nat) :
    sourceRun M ((base+1)*a+1) ⟨values v x t a z,loop⟩ =
      ⟨values v x t 0 (z+base*a),done⟩ := by
  induction a generalizing z with
  | zero => simp [sourceRun,sourceStep,hloop,hne]
  | succ a ih =>
    have hblock : sourceRun M (base+1) ⟨values v x t (a+1) z,loop⟩ =
        ⟨values v x t a (z+base),loop⟩ := by
      rw [sourceRun]
      simp only [sourceStep,hloop,values_x v x t hne,Nat.add_eq_zero_iff,
        Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel,values_put_x v x t hne]
      simpa [hback] using inc_chain M t base add hadd (values v x t a z)
    have h := sourceRun_join M hblock (ih (z+base))
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Exact push cost; in particular every invocation has positive duration,
even if it leaves the encoded value unchanged. -/
theorem push_macro_exact (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base digit : Nat) (rows : PushRows M x t base digit)
    (v : Fin (d+1) → Nat) (a : Nat) :
    sourceRun M (((base+1)*a+1)+(2*(base*a)+1)+digit)
      ⟨values v x t a 0,rows.entry⟩ = ⟨values v x t (base*a+digit) 0,rows.done⟩ := by
  have h₁ := multiply_exact M x t hne base rows.entry rows.transfer rows.multiplyAdd
    rows.entry_row rows.multiply_rows rows.multiply_back v a 0
  have h₂ := transfer_exact M x t hne rows.transfer rows.transferAdd (rows.digitAdd 0)
    rows.transfer_row rows.transfer_add_row v 0 (base*a)
  have h₃ := inc_chain M x digit rows.digitAdd rows.digit_rows (values v x t (base*a) 0)
  have h₁' : sourceRun M ((base+1)*a+1) ⟨values v x t a 0,rows.entry⟩ =
      ⟨values v x t 0 (base*a),rows.transfer⟩ := by simpa using h₁
  have h₂' : sourceRun M (2*(base*a)+1) ⟨values v x t 0 (base*a),rows.transfer⟩ =
      ⟨values v x t (base*a) 0,rows.digitAdd 0⟩ := by simpa using h₂
  have h₃' : sourceRun M digit ⟨values v x t (base*a) 0,rows.digitAdd 0⟩ =
      ⟨values v x t (base*a+digit) 0,rows.done⟩ := by simpa [hne,rows.digit_done] using h₃
  exact sourceRun_join M (sourceRun_join M h₁' h₂') h₃'

theorem push_macro_positive (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base digit : Nat) (rows : PushRows M x t base digit)
    (v : Fin (d+1) → Nat) (a : Nat) :
    ∃ k, 0 < k ∧ sourceRun M k ⟨values v x t a 0,rows.entry⟩ =
      ⟨values v x t (base*a+digit) 0,rows.done⟩ :=
  ⟨_,by omega,push_macro_exact M x t hne base digit rows v a⟩

@[simp] theorem push_entry_nonhalting (M : Machine d n) (x t : Fin (d+1))
    (base digit : Nat) (rows : PushRows M x t base digit) :
    M.instruction rows.entry ≠ .halt := by rw [rows.entry_row]; simp

 theorem pop_cycle_exact (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat) (a z : Nat) :
    sourceRun M (base+1) ⟨values v x t (a+base) z,rows.consume 0⟩ =
      ⟨values v x t a (z+1),rows.consume 0⟩ := by
  have hc := dec_chain M x base rows.consume rows.transfer rows.consume_rows
    (values v x t 0 z) a
  have h₁ : sourceRun M base ⟨values v x t (a+base) z,rows.consume 0⟩ =
      ⟨values v x t a z,rows.quotientAdd⟩ := by simpa [hne,rows.cycle_end] using hc
  have h₂ : sourceRun M 1 ⟨values v x t a z,rows.quotientAdd⟩ =
      ⟨values v x t a (z+1),rows.consume 0⟩ := by
    simp [sourceRun,sourceStep,rows.quotient_row]
  exact sourceRun_join M h₁ h₂

theorem pop_consume_exact (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat)
    (q r z : Nat) (hr : r < base) :
    sourceRun M ((base+1)*q+r+1) ⟨values v x t (base*q+r) z,rows.consume 0⟩ =
      ⟨values v x t 0 (z+q),rows.transfer r⟩ := by
  induction q generalizing z with
  | zero =>
    have hc := dec_chain M x r rows.consume rows.transfer
      (by intro j hj; exact rows.consume_rows j (by omega)) (values v x t 0 z) 0
    have h₁ : sourceRun M r ⟨values v x t r z,rows.consume 0⟩ =
        ⟨values v x t 0 z,rows.consume r⟩ := by simpa [hne] using hc
    have h₂ : sourceRun M 1 ⟨values v x t 0 z,rows.consume r⟩ =
        ⟨values v x t 0 z,rows.transfer r⟩ := by
      simp [sourceRun,sourceStep,rows.consume_rows r hr,hne]
    simpa using sourceRun_join M h₁ h₂
  | succ q ih =>
    have h₁ := pop_cycle_exact M x t hne base rows v (base*q+r) z
    have h := sourceRun_join M h₁ (ih (z+1))
    simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- Exact pop cost in quotient/remainder form. Both final zero tests count,
so even empty pop takes two source instructions. -/
theorem pop_macro_exact (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat)
    (q r : Nat) (hr : r < base) :
    sourceRun M (((base+1)*q+r+1)+(2*q+1))
      ⟨values v x t (base*q+r) 0,rows.consume 0⟩ = ⟨values v x t q 0,rows.done r⟩ := by
  have h₁ := pop_consume_exact M x t hne base rows v q r 0 hr
  have h₂ := transfer_exact M x t hne (rows.transfer r) (rows.transferAdd r) (rows.done r)
    (rows.transfer_rows r hr) (rows.transfer_add_rows r hr) v 0 q
  have h₁' : sourceRun M ((base+1)*q+r+1) ⟨values v x t (base*q+r) 0,rows.consume 0⟩ =
      ⟨values v x t 0 q,rows.transfer r⟩ := by simpa using h₁
  have h₂' : sourceRun M (2*q+1) ⟨values v x t 0 q,rows.transfer r⟩ =
      ⟨values v x t q 0,rows.done r⟩ := by simpa using h₂
  exact sourceRun_join M h₁' h₂'

theorem pop_macro_positive (M : Machine d n) (x t : Fin (d+1)) (hne : x ≠ t)
    (base : Nat) (rows : PopRows M x t base) (v : Fin (d+1) → Nat)
    (q r : Nat) (hr : r < base) :
    ∃ k, 0 < k ∧ sourceRun M k ⟨values v x t (base*q+r) 0,rows.consume 0⟩ =
      ⟨values v x t q 0,rows.done r⟩ :=
  ⟨_,by omega,pop_macro_exact M x t hne base rows v q r hr⟩

@[simp] theorem pop_entry_nonhalting (M : Machine d n) (x t : Fin (d+1))
    (base : Nat) (hbase : 0 < base) (rows : PopRows M x t base) :
    M.instruction (rows.consume 0) ≠ .halt := by rw [rows.consume_rows 0 hbase]; simp

end SOnlyStack
