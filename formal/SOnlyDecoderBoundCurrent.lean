import SOnlyDecoderBound
import SOnlyCurrentDecoder

/-!
# The current-tree result reader uses only input-size carrier fuel

This is an extensional identity for the already selected numerical decoder,
including every malformed or nonaccepting input. It does not replace the
first-preorder witness by a more convenient witness.
-/
namespace SOnlyDecoderBoundCurrent

open PureSFormal PureSFormal.PureS

theorem subterm_size_le (term : Term) (address : Address) (part : Term)
    (located : term.subterm? address = some part) : part.size ≤ term.size := by
  induction address generalizing term with
  | nil => simp only [Term.subterm?] at located; cases located; exact Nat.le_refl _
  | cons direction rest ih =>
      cases term with
      | s => cases direction <;> simp [Term.subterm?] at located
      | app left right =>
          cases direction with
          | left =>
              have := ih left located
              simp only [Term.size]
              omega
          | right =>
              have := ih right located
              simp only [Term.size]
              omega

theorem findShell_size_le (term shell : Term)
    (found : SOnlyCurrentDecoder.findShell term = some shell) : shell.size ≤ term.size := by
  obtain ⟨address, located, _⟩ := SOnlyCurrentDecoder.findShell_sound term shell found
  exact subterm_size_le term address shell located

def readShellFuel (shell : Term) : Option Nat := do
  let snapshot ← shell.subterm? SOnlyEventTransfer.auditAddress
  let bits ← SOnlyDecoderBound.carrierFuel SOnly38.program SOnly38.dispatcher.tree
    snapshot.size snapshot
  SOnlyResultBits.readMachineBits (true :: bits)

theorem readShellFuel_eq (shell : Term) :
    readShellFuel shell = SOnlyWitnessResult.readShell shell := by
  unfold readShellFuel SOnlyWitnessResult.readShell SOnlyEventTransfer.readPrestate
    SOnlyEventTransfer.readAudit
  cases found : shell.subterm? SOnlyEventTransfer.auditAddress with
  | none => rfl
  | some snapshot =>
      change (SOnlyDecoderBound.carrierFuel SOnly38.program SOnly38.dispatcher.tree
        snapshot.size snapshot).bind (fun bits => SOnlyResultBits.readMachineBits (true :: bits)) =
        ((CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot).map
          (true :: ·)).bind SOnlyResultBits.readMachineBits
      rw [SOnlyDecoderBound.carrierFuel_eq _ _ _ _ (Nat.le_refl _)]
      cases CheckpointDecoder.decodeCarrier? SOnly38.program SOnly38.dispatcher.tree snapshot <;> rfl

/-- The same fixed first-preorder selection, with input-size-bounded carrier
recursion at its one selected audit. -/
def readFuel (term : Term) : Option Nat :=
  (SOnlyCurrentDecoder.findShell term).bind readShellFuel

theorem readFuel_eq (term : Term) : readFuel term = SOnlyCurrentDecoder.read term := by
  unfold readFuel SOnlyCurrentDecoder.read
  cases SOnlyCurrentDecoder.findShell term with
  | none => rfl
  | some shell => exact readShellFuel_eq shell

/-- The carrier budget at any selected witness is bounded by the supplied
whole current tree, not by a source runtime or past trajectory index. -/
theorem selected_audit_size_le (term shell snapshot : Term)
    (found : SOnlyCurrentDecoder.findShell term = some shell)
    (located : shell.subterm? SOnlyEventTransfer.auditAddress = some snapshot) :
    snapshot.size ≤ term.size := by
  exact Nat.le_trans (subterm_size_le _ _ _ located) (findShell_size_le term shell found)

end SOnlyDecoderBoundCurrent

#print axioms SOnlyDecoderBoundCurrent.readFuel_eq
#print axioms SOnlyDecoderBoundCurrent.selected_audit_size_le
