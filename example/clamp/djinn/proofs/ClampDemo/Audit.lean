/-  Audit.lean — generated; `cargo djinn verify` runs it (`lake env lean --run`,
    once per phase: `statements`, then `replay`) after `lake build`. It imports
    only `Lean` and reads the built modules as data, so nothing `Proofs`
    defines takes part. Per obligation: declared by
    `Obligations.lean` with the statement `Statements.lean` elaborates without
    `Proofs`; only propext, Classical.choice and Quot.sound as axioms; and
    every constant of this package it reaches checked again by the kernel. -/
import Lean
open Lean

namespace Djinn.Audit

def nm (cs : List String) : Name := cs.foldl Name.mkStr .anonymous

def ns : Name := nm ["ClampDemo"]
def owner : Name := nm ["ClampDemo", "Obligations"]
def reference : Name := nm ["ClampDemo", "Statements"]

def obligations : Array Name := #[
  nm ["ClampDemo", "Obligations", "clamp", "unambiguous"],
  nm ["ClampDemo", "Obligations", "clamp", "impl_correct"],
  nm ["ClampDemo", "Obligations", "clamp", "exists"],
  nm ["ClampDemo", "Obligations", "count_negative", "unambiguous"],
  nm ["ClampDemo", "Obligations", "count_negative", "impl_correct"],
  nm ["ClampDemo", "Obligations", "count_negative", "exists"],
  nm ["ClampDemo", "Obligations", "min", "unambiguous"],
  nm ["ClampDemo", "Obligations", "min", "impl_correct"],
  nm ["ClampDemo", "Obligations", "min", "exists"],
  nm ["ClampDemo", "Obligations", "max", "unambiguous"],
  nm ["ClampDemo", "Obligations", "max", "impl_correct"],
  nm ["ClampDemo", "Obligations", "max", "exists"]]

def allowed : Array Name := #[nm ["propext"], nm ["Classical", "choice"], nm ["Quot", "sound"]]

abbrev EnvM := ReaderT Environment Id

instance : MonadEnv EnvM where
  getEnv := read
  modifyEnv _ := pure ()

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

/-- One line of output, whatever a name holds. -/
def clean (s : String) : String := s.map fun c => if c.toNat < 32 then ' ' else c

def kernelParts : ConstantInfo → Option (String × List Name × Expr × Option Expr)
  | .axiomInfo v => some ("axiom", v.levelParams, v.type, none)
  | .defnInfo v => some ("def", v.levelParams, v.type, some v.value)
  | .thmInfo v => some ("theorem", v.levelParams, v.type, some v.value)
  | .opaqueInfo v => some ("opaque", v.levelParams, v.type, some v.value)
  | _ => none

/-- Is `o` a theorem of `Obligations.lean` stating what `Statements.lean` does?
    Constants elaborated with the statement (`match` auxiliaries) are compared
    too; every other constant it mentions must come from the same module. -/
def sameStatement (env : Environment) (refFind : Name → Option ConstantInfo) (refModuleOf : Name → Option Name) (o : Name) : Except String Unit := do
  let some (.thmInfo t) := env.find? o | throw "it is not a theorem"
  if moduleOf env o != some owner then throw "it is not declared by Obligations.lean"
  let some (.axiomInfo a) := refFind o | throw "it is missing from Statements.lean"
  if t.levelParams != a.levelParams || !(t.type == a.type) then
    throw "its statement differs from the one Statements.lean elaborates without the proofs (does Proofs change how it elaborates: a macro, an elaborator, an instance?)"
  let mut todo := t.type.getUsedConstants.toList
  let mut seen : NameSet := {}
  repeat
    match todo with
    | [] => break
    | k :: rest =>
      todo := rest
      if seen.contains k then continue
      seen := seen.insert k
      match moduleOf env k, refModuleOf k with
      | some m, some m' =>
        if m == owner && m' == reference then
          match (env.find? k).bind kernelParts, (refFind k).bind kernelParts with
          | some (k1, l1, t1, v1), some (k2, l2, t2, v2) =>
            if k1 != k2 || l1 != l2 || !(t1 == t2) || !(v1 == v2) then
              throw s!"`{k}` in its statement differs"
            todo := t1.getUsedConstants.toList ++ (v1.map (·.getUsedConstants.toList)).getD [] ++ todo
          | _, _ => throw s!"`{k}` in its statement differs"
        else if m != m' || m == owner then
          throw s!"`{k}` in its statement comes from {m}, not {m'}"
      | _, _ => throw s!"`{k}` in its statement is unknown"
  return ()

/-- The constants of a built module, read as data (no import, no initializer):
    the `.olean`, and the `.olean.private` of a `module` (later parts override). -/
def moduleConstants (m : Name) : IO (Std.HashMap Name ConstantInfo × Array Import) := do
  let base ← findOLean m
  let priv := OLeanLevel.adjustFileName base .private
  let files := if (← priv.pathExists) then #[base, priv] else #[base]
  let parts ← readModuleDataParts files
  let mut cs : Std.HashMap Name ConstantInfo := {}
  let mut imps : Array Import := #[]
  for (d, _) in parts do
    for c in d.constants do
      cs := cs.insert c.name c
    for i in d.imports do
      if !imps.any (·.module == i.module) then imps := imps.push i
  return (cs, imps)

/-- The modules `roots` import, transitively, among the modules of `env`. -/
def closureIn (env : Environment) (roots : Array Import) : NameSet := Id.run do
  let mut idx : Std.HashMap Name Nat := {}
  for m in env.header.moduleNames, i in [0:env.header.moduleNames.size] do
    idx := idx.insert m i
  let mut seen : NameSet := {}
  let mut todo := roots.toList.map (·.module)
  repeat
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      seen := seen.insert m
      if let some i := idx[m]? then
        if let some d := env.header.moduleData[i]? then
          todo := d.imports.toList.map (·.module) ++ todo
  return seen

/-- Phase `statements`: one environment (the obligations and what they import);
    `Statements.olean` is read as data, its other constants are those of its
    imports as `env` has them (its import closure within `env`). The judgement
    is `sameStatement`'s, and the axioms of each obligation. -/
def phaseStatements : IO Unit := do
  let env ← importModules #[{ module := owner }] {}
  let (refC, refImports) ← moduleConstants reference
  let closure := closureIn env refImports
  let refModuleOf (k : Name) : Option Name :=
    if refC.contains k then some reference
    else match moduleOf env k with
      | some m => if closure.contains m then some m else none
      | none => none
  let refFind (k : Name) : Option ConstantInfo :=
    match refC[k]? with
    | some c => some c
    | none => if (refModuleOf k).isSome then env.find? k else none
  for o in obligations, i in [0:obligations.size] do
    match sameStatement env refFind refModuleOf o with
    | .error e => IO.println s!"djinn-audit {i} statement {clean e}"
    | .ok () =>
      let axs := ((collectAxioms o : EnvM (Array Name)).run env).filter (!allowed.contains ·)
      if axs.contains (nm ["sorryAx"]) then IO.println s!"djinn-audit {i} sorry"
      else if axs.isEmpty then IO.println s!"djinn-audit {i} ok"
      else IO.println s!"djinn-audit {i} axioms {clean (", ".intercalate (axs.toList.map toString))}"

/-- Phase `replay`: the package's own modules (under `.lake/build`, or in the
    namespace) are read as data from `Obligations` down; what they import is
    the trusted base, imported once. The constants the obligations reach among
    the package's are replayed onto the base by the kernel; the number replayed. -/
def replayUntrusted (build : String) : IO Nat := do
  let mut todoM := [owner]
  let mut seenM : NameSet := {}
  let mut mine : Std.HashMap Name ConstantInfo := {}
  let mut imps : Array Import := #[]
  repeat
    match todoM with
    | [] => break
    | m :: rest =>
      todoM := rest
      if seenM.contains m then continue
      seenM := seenM.insert m
      let p ← IO.FS.realPath (← findOLean m)
      if p.toString.startsWith build || ns.isPrefixOf m then
        let (cs, is) ← moduleConstants m
        for (k, c) in cs do
          mine := mine.insert k c
        todoM := is.toList.map (·.module) ++ todoM
      else if !imps.any (·.module == m) then
        imps := imps.push { module := m }
  let base ← importModules imps {}
  let mut todo := obligations.toList
  let mut seen : NameSet := {}
  let mut newC : Std.HashMap Name ConstantInfo := {}
  repeat
    match todo with
    | [] => break
    | k :: rest =>
      todo := rest
      if seen.contains k then continue
      seen := seen.insert k
      match mine[k]? with
      | none =>
        if (base.find? k).isNone then throw <| IO.userError s!"unknown constant `{k}`"
      | some ci =>
        newC := newC.insert k ci
        todo := ci.getUsedConstantsAsSet.toList ++ todo
        match ci with
        | .inductInfo v => todo := v.all ++ v.ctors ++ todo
        | .ctorInfo v => todo := v.induct :: todo
        | .recInfo v => todo := v.all ++ todo
        | _ => pure ()
  discard <| base.replay newC
  return newC.size

def phaseReplay : IO Unit := do
  let build := (← IO.FS.realPath ((← IO.currentDir) / ".lake" / "build")).toString ++ "/"
  -- the kernel recurses deeply on big proofs: on a thread of its own, whose
  -- stack `--tstack` sizes (the main thread's is the OS's)
  let t ← IO.asTask (prio := .dedicated) (replayUntrusted build)
  match t.get with
  | .ok n => IO.println s!"djinn-audit replay ok {n}"
  | .error e => IO.println s!"djinn-audit replay fail {clean (toString e)}"
  IO.println s!"djinn-audit end {obligations.size}"

end Djinn.Audit

/- Two phases, two processes: each imports the Mathlib-based library once (a
   second `importModules` in one process cannot map the oleans at their
   addresses and copies them into the heap: gigabytes). -/
open Djinn.Audit in
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["statements"] => phaseStatements
  | ["replay"] => phaseReplay
  | _ => IO.println "djinn-audit usage: statements | replay"
  return 0
