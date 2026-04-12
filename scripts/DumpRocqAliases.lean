/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zongyuan Liu
-/

import Lean
import Iris.Std.RocqIgnore

/-!
# Dump Rocq Aliases

A lean_exe that loads the Iris environment, collects all `Rocq.*` namespace
declarations (created by `@[rocq_alias]`) and all `#rocq_ignore` entries,
and writes them to a JSON file.

Usage: `lake exe dumpRocqAliases [output-path]`
Default output: `.lake/rocq_aliases.json`
-/

open Lean

/-- Extract the target constant name from a declaration's value expression.
    For aliases created by `@[rocq_alias]`, the value is `mkConst leanName levels`. -/
private def extractTargetName (info : ConstantInfo) : Option Name :=
  match info with
  | .thmInfo val => val.value.constName?
  | .defnInfo val => val.value.constName?
  | _ => none

/-- Collect all `Rocq.*` aliases from the environment and return `(rocqName, leanName)` pairs.
    Each `@[rocq_alias foo]` creates a declaration `Rocq.foo` whose value points to the Lean name. -/
private def collectRocqAliases (env : Environment) : Array (Name × Name) :=
  env.constants.fold (init := #[]) fun acc name info =>
    if name.getRoot == `Rocq then
      match extractTargetName info with
      | some target =>
        let rocqName := name.replacePrefix `Rocq .anonymous
        acc.push (rocqName, target)
      | none => acc
    else acc

/-- Build a JSON object from collected data. -/
private def buildJson (aliases : Array (Name × Name))
    (ignores : Array (Name × String)) : Json :=
  let aliasArr := aliases.map fun (rocq, lean) =>
    Json.mkObj [("rocq", rocq.toString), ("lean", lean.toString)]
  let ignoreArr := ignores.map fun (rocq, reason) =>
    Json.mkObj [("rocq", rocq.toString), ("reason", reason)]
  Json.mkObj [("aliases", Json.arr aliasArr), ("ignores", Json.arr ignoreArr)]

/-- Discover all `.lean` source files under a directory and convert to module names.
    E.g., `src/Iris/BI/Sbi.lean` → `Iris.BI.Sbi` -/
private partial def discoverModules (srcDir : System.FilePath) : IO (Array Name) := do
  let mut result : Array Name := #[]
  let mut worklist : Array (System.FilePath × Name) := #[(srcDir / "Iris", `Iris)]
  while h : worklist.size > 0 do
    let (dir, modPrefix) := worklist[0]
    worklist := worklist.eraseIdx 0
    for entry in (← dir.readDir) do
      if (← entry.path.isDir) then
        worklist := worklist.push (entry.path, modPrefix ++ entry.fileName.toName)
      else if entry.fileName.endsWith ".lean" then
        let stem := (entry.fileName.dropEnd 5).toString
        result := result.push (modPrefix ++ stem.toName)
  return result

unsafe def main (args : List String) : IO Unit := do
  let outputPath := args.head? |>.getD ".lake/rocq_aliases.json"
  -- Initialize Lean
  Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  -- Discover all Iris .olean modules to bypass `module` re-export filtering.
  -- `module` files don't re-export declarations created by privately-imported
  -- metaprograms like @[rocq_alias], so we import every module directly.
  let srcDir : System.FilePath := "src"
  let modules ← discoverModules srcDir
  let env ← importModules (modules.map ({ module := · }))
    {} (trustLevel := 1024) (loadExts := true)
  -- Collect aliases from Rocq namespace
  let aliases := collectRocqAliases env
  -- Collect ignores from the environment extension
  let ignores := rocqIgnoreExt.getState env
  -- Build and write JSON
  let json := buildJson aliases ignores
  IO.FS.writeFile outputPath (json.pretty ++ "\n")
  IO.println s!"Wrote {aliases.size} aliases and {ignores.size} ignores to {outputPath}"
