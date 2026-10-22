/-  Audit.lean — generated; `cargo djinn verify` runs it (`lake env lean --run`)
    after `lake build`. It imports only `Lean` and reads the built modules as
    data, so nothing `Proofs` defines takes part. Per obligation: declared by
    `Obligations.lean` with the statement `Statements.lean` elaborates without
    `Proofs`; only propext, Classical.choice and Quot.sound as axioms; and
    every constant of this package it reaches checked again by the kernel. -/
import Lean
open Lean

namespace Djinn.Audit

def nm (cs : List String) : Name := cs.foldl Name.mkStr .anonymous

def ns : Name := nm ["AnyDemo"]
def owner : Name := nm ["AnyDemo", "Obligations"]
def reference : Name := nm ["AnyDemo", "Statements"]

def obligations : Array Name := #[
  nm ["AnyDemo", "Obligations", "checked_div", "unambiguous"],
  nm ["AnyDemo", "Obligations", "checked_div", "wf"],
  nm ["AnyDemo", "Obligations", "checked_div", "impl_correct"],
  nm ["AnyDemo", "Obligations", "checked_div", "exists"],
  nm ["AnyDemo", "Obligations", "safe_div", "unambiguous"],
  nm ["AnyDemo", "Obligations", "safe_div", "ens_0"],
  nm ["AnyDemo", "Obligations", "safe_div", "wf"],
  nm ["AnyDemo", "Obligations", "safe_div", "impl_correct"],
  nm ["AnyDemo", "Obligations", "safe_div", "exists"],
  nm ["AnyDemo", "Obligations", "shrink", "unambiguous"],
  nm ["AnyDemo", "Obligations", "shrink", "wf"],
  nm ["AnyDemo", "Obligations", "shrink", "impl_correct"],
  nm ["AnyDemo", "Obligations", "shrink", "exists"],
  nm ["AnyDemo", "Obligations", "pick", "unambiguous"],
  nm ["AnyDemo", "Obligations", "pick", "impl_correct"],
  nm ["AnyDemo", "Obligations", "pick", "exists"],
  nm ["AnyDemo", "Obligations", "pick_twice", "unambiguous"],
  nm ["AnyDemo", "Obligations", "pick_twice", "ens_0"],
  nm ["AnyDemo", "Obligations", "pick_twice", "wf"],
  nm ["AnyDemo", "Obligations", "pick_twice", "impl_correct"],
  nm ["AnyDemo", "Obligations", "pick_twice", "exists"]]

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
def sameStatement (env ref : Environment) (o : Name) : Except String Unit := do
  let some (.thmInfo t) := env.find? o | throw "it is not a theorem"
  if moduleOf env o != some owner then throw "it is not declared by Obligations.lean"
  let some (.axiomInfo a) := ref.find? o | throw "it is missing from Statements.lean"
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
      match moduleOf env k, moduleOf ref k with
      | some m, some m' =>
        if m == owner && m' == reference then
          match (env.find? k).bind kernelParts, (ref.find? k).bind kernelParts with
          | some (k1, l1, t1, v1), some (k2, l2, t2, v2) =>
            if k1 != k2 || l1 != l2 || !(t1 == t2) || !(v1 == v2) then
              throw s!"`{k}` in its statement differs"
            todo := t1.getUsedConstants.toList ++ (v1.map (·.getUsedConstants.toList)).getD [] ++ todo
          | _, _ => throw s!"`{k}` in its statement differs"
        else if m != m' || m == owner then
          throw s!"`{k}` in its statement comes from {m}, not {m'}"
      | _, _ => throw s!"`{k}` in its statement is unknown"
  return ()

/-- The modules built from this package's sources (under `.lake/build`, or
    in the namespace): what the kernel checks again. -/
def untrustedModules (env : Environment) (build : String) : IO NameSet := do
  let mut s : NameSet := {}
  for m in env.header.moduleNames do
    let p ← IO.FS.realPath (← findOLean m)
    if p.toString.startsWith build || ns.isPrefixOf m then
      s := s.insert m
  return s

/-- Replay the package's constants the obligations reach onto an environment
    of the trusted modules they import; the number replayed. -/
def replayUntrusted (env : Environment) (bad : NameSet) (roots : Array Name) : IO Nat := do
  let isBad (n : Name) : Bool := match moduleOf env n with
    | some m => bad.contains m
    | none => true
  let mut todo := roots.toList
  let mut seen : NameSet := {}
  let mut newC : Std.HashMap Name ConstantInfo := {}
  repeat
    match todo with
    | [] => break
    | k :: rest =>
      todo := rest
      if seen.contains k || !isBad k then continue
      seen := seen.insert k
      let some ci := env.find? k | throw <| IO.userError s!"unknown constant `{k}`"
      newC := newC.insert k ci
      todo := ci.getUsedConstantsAsSet.toList ++ todo
      match ci with
      | .inductInfo v => todo := v.all ++ v.ctors ++ todo
      | .ctorInfo v => todo := v.induct :: todo
      | .recInfo v => todo := v.all ++ todo
      | _ => pure ()
  let mut imps : Array Import := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if bad.contains m then
      for i in d.imports do
        if !bad.contains i.module && !imps.any (·.module == i.module) then
          imps := imps.push { module := i.module }
  let base ← importModules imps {}
  discard <| base.replay newC
  return newC.size

end Djinn.Audit

open Djinn.Audit in
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := owner }] {}
  let ref ← importModules #[{ module := reference }] {}
  for o in obligations, i in [0:obligations.size] do
    match sameStatement env ref o with
    | .error e => IO.println s!"djinn-audit {i} statement {clean e}"
    | .ok () =>
      let axs := ((collectAxioms o : EnvM (Array Name)).run env).filter (!allowed.contains ·)
      if axs.contains (nm ["sorryAx"]) then IO.println s!"djinn-audit {i} sorry"
      else if axs.isEmpty then IO.println s!"djinn-audit {i} ok"
      else IO.println s!"djinn-audit {i} axioms {clean (", ".intercalate (axs.toList.map toString))}"
  let build := (← IO.FS.realPath ((← IO.currentDir) / ".lake" / "build")).toString ++ "/"
  -- the kernel recurses deeply on big proofs: on a thread of its own, whose
  -- stack `--tstack` sizes (the main thread's is the OS's)
  let bad ← untrustedModules env build
  let t ← IO.asTask (prio := .dedicated) (replayUntrusted env bad obligations)
  match t.get with
  | .ok n => IO.println s!"djinn-audit replay ok {n}"
  | .error e => IO.println s!"djinn-audit replay fail {clean (toString e)}"
  IO.println s!"djinn-audit end {obligations.size}"
  return 0
