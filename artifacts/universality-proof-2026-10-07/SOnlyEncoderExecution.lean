import SOnlyUniversality

namespace SOnlyEncoderExecution
open PureSFormal

def haltMachine : SOnlyMachine.Machine 0 0 :=
  ⟨fun _ => .halt, 0⟩
def zeroInput : Fin 1 → Nat := fun _ => 0

def tinyProgram : SOnlyMachineBP2.Program Nat := [.inc 0]

#eval (SOnlyMachineNat.compile haltMachine zeroInput).length
#eval (SOnlyMachineNat.counterCount 0 0)
#eval SOnlySimulation.compilerDepth (SOnlyMachineNat.compile haltMachine zeroInput)
#eval (SOnlySimulation.compiledBits 1 tinyProgram).length
#eval (SOnly38.encode (SOnlySimulation.compiledBits 1 tinyProgram)).size

#print axioms SOnlyUniversality.encode
#print axioms SOnlySimulation.machineBits
#print axioms SOnlyMachineNat.compile
#print axioms SOnlySimulation.compiledBits
#print axioms SOnlyUniversality.event
#print axioms SOnlyUniversality.decode
end SOnlyEncoderExecution
