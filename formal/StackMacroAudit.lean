import StackMacroTime
import StackPushTable
import StackPopTable

#print axioms SOnlyStack.push_macro
#print axioms SOnlyStack.pop_macro_div_mod
#print axioms SOnlyStack.push_macro_exact
#print axioms SOnlyStack.pop_macro_exact
#print axioms SOnlyStack.push_macro_positive
#print axioms SOnlyStack.pop_macro_positive
#print axioms SOnlyStack.pushMachine_correct
#print axioms SOnlyStack.PopTable.executes

namespace SOnlyStack
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
open SOnlyMachine

/-- Concrete base-three push, as a fully kernel-reduced source trajectory. -/
example :
    (sourceRun (pushMachine 3 2) 74
      ⟨values (fun _ => 0) 0 1 7 0, (pushMachine 3 2).entry⟩).value 0 = 23 := by decide
example :
    (sourceRun (pushMachine 3 2) 74
      ⟨values (fun _ => 0) 0 1 7 0, (pushMachine 3 2).entry⟩).value 1 = 0 := by decide

/-- Base-three pop of 23 returns quotient seven and digit two in finite control. -/
example :
    (sourceRun (PopTable.machine 2 (0 : Fin 3) 2) 46
      ⟨values (fun _ => 17) 0 2 23 0, PopTable.consume 2 0⟩).value 0 = 7 := by decide
example :
    (sourceRun (PopTable.machine 2 (0 : Fin 3) 2) 46
      ⟨values (fun _ => 17) 0 2 23 0, PopTable.consume 2 0⟩).value 1 = 17 := by decide
example :
    (sourceRun (PopTable.machine 2 (0 : Fin 3) 2) 46
      ⟨values (fun _ => 17) 0 2 23 0, PopTable.consume 2 0⟩).value 2 = 0 := by decide
example :
    (sourceRun (PopTable.machine 2 (0 : Fin 3) 2) 46
      ⟨values (fun _ => 17) 0 2 23 0, PopTable.consume 2 0⟩).label = PopTable.done 2 2 := by decide

/-- Empty pop follows the zero-residue exit after exactly two zero tests. -/
example :
    sourceRun (PopTable.machine 2 (0 : Fin 3) 2) 2
      ⟨values (fun _ => 17) 0 2 0 0, PopTable.consume 2 0⟩ =
      ⟨values (fun _ => 17) 0 2 0 0, PopTable.done 2 0⟩ := by rfl
end SOnlyStack
