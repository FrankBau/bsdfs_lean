/-
Copyright (c) 2026 Frank Bauernöppel. Released under the MIT license as described in the file LICENSE.
-/
import Lean

/-!
  The statement check of `comparator.json`, without the comparator tool: every theorem it names has the same statement in
  the challenge and in the solution module, and every constant of this package the statements depend on (through types and
  definition bodies, not proofs) is the same in both.  The rest of what comparator checks is done elsewhere: the axioms by
  the `#guard_msgs` in `Bsdfs/MainTheorems.lean`, the proofs by `leanchecker`.

  Run from the repository root, after `lake build` and `lake build Bsdfs.Challenge`:
    lake env lean --run CheckChallenge.lean
-/

open Lean

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.allImportedModuleNames[idx.toNat]!
  | none => .anonymous

/-- the constants of the package `pkg` that `todo` depends on, through types and definition bodies -/
partial def deps (env : Environment) (pkg : Name) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: todo, seen =>
    if seen.contains n || !pkg.isPrefixOf (moduleOf env n) then deps env pkg todo seen else
    let refs := match env.find? n with
      | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
      | some (.opaqueInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
      | some (.inductInfo d) => d.type.getUsedConstants ++ d.ctors.toArray
      | some (.ctorInfo d) => d.type.getUsedConstants.push d.induct
      | some ci => ci.type.getUsedConstants
      | none => #[]
    deps env pkg (refs.toList ++ todo) (seen.insert n)

/-- everything about a constant that the kernel sees, except the proofs of theorems -/
def fingerprint : ConstantInfo → String
  | .defnInfo d => s!"def {d.levelParams} : {repr d.type} := {repr d.value}"
  | .opaqueInfo d => s!"opaque {d.levelParams} : {repr d.type} := {repr d.value}"
  | .inductInfo d => s!"inductive {d.levelParams} : {repr d.type} params {d.numParams} indices {d.numIndices} ctors {d.ctors}"
  | .thmInfo d => s!"theorem {d.levelParams} : {repr d.type}"
  | ci => s!"{ci.levelParams} : {repr ci.type}"

/-- the statements of `theorems` and the fingerprints of the constants of `pkg` they depend on -/
def summary (env : Environment) (pkg : Name) (theorems : Array Name) : Except String (Array (Name × String)) := do
  let mut out := #[]
  let mut roots := #[]
  for n in theorems do
    let some (.thmInfo d) := env.find? n | throw s!"{n} is not a theorem of {env.mainModule}"
    out := out.push (n, fingerprint (.thmInfo d))
    roots := roots ++ d.type.getUsedConstants
  for n in (deps env pkg roots.toList {}).toArray.qsort (·.toString < ·.toString) do
    out := out.push (n, fingerprint (env.find? n).get!)
  return out

def main : IO UInt32 := do
  let cfg ← IO.ofExcept <| Json.parse (← IO.FS.readFile "comparator.json")
  let challenge := (← IO.ofExcept <| cfg.getObjValAs? String "challenge_module").toName
  let solution := (← IO.ofExcept <| cfg.getObjValAs? String "solution_module").toName
  let theorems := (← IO.ofExcept <| cfg.getObjValAs? (Array String) "theorem_names").map String.toName
  initSearchPath (← findSysroot)
  let pkg := challenge.getRoot
  let c ← IO.ofExcept <| summary (← importModules #[{ module := challenge }] {}) pkg theorems
  let s ← IO.ofExcept <| summary (← importModules #[{ module := solution }] {}) pkg theorems
  let mut ok := true
  for (n, fc) in c do
    match s.find? (·.1 == n) with
    | none => IO.eprintln s!"{n}: used by {challenge}, not by {solution}"; ok := false
    | some (_, fs) => if fc != fs then IO.eprintln s!"{n}: differs between {challenge} and {solution}"; ok := false
  for (n, _) in s do
    unless c.any (·.1 == n) do IO.eprintln s!"{n}: used by {solution}, not by {challenge}"; ok := false
  if !ok then return 1
  IO.println s!"{challenge} and {solution} agree: {theorems.size} statements and the {c.size - theorems.size} constants of {pkg} they depend on"
  return 0
