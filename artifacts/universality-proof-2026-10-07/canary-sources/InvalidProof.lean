module
public import Lean
import all Lean.Environment

open Lean in
elab "add_invalid_proof" : command => do
  modifyEnv fun env =>
    let info := { name := `invalidFalse, levelParams := [], type := .const ``False [], value := .const ``False [] }
    let constants := env.constants.insert `invalidFalse $ ConstantInfo.thmInfo info
    let kenv := (private_decl% Lean.Kernel.Environment.mk) constants
      env.toKernelEnv.quotInit
      env.toKernelEnv.diagnostics
      env.toKernelEnv.const2ModIdx
      ((private_decl% Lean.Kernel.Environment.extensions) env.toKernelEnv)
      ((private_decl% Lean.Kernel.Environment.irBaseExts) env.toKernelEnv)
      env.header
    let decl := .axiomDecl { info with isUnsafe := false }
    (private_decl% Lean.Environment.updateBaseAfterKernelAdd) env kenv decl

add_invalid_proof
