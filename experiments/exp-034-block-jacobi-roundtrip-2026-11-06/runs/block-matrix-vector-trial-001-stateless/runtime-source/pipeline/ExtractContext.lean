import Lean
import Research

open Lean Elab Command Meta

/- Trusted extraction: no theorem proof terms or documentation are exported. -/
set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false
set_option maxHeartbeats 2000000

run_cmd do
  let result ← liftTermElabM do
    let env ← getEnv
    let mut entries : Array Json := #[]
    let mut names : Array Name := #[]
    for idx in [:env.header.moduleNames.size] do
      let moduleName := env.header.moduleNames[idx]!
      if !(moduleName.toString.startsWith "Research") then continue
      for info in env.header.moduleData[idx]!.constants do
        let name := info.name
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .defnInfo _ => "definition"
          | .axiomInfo _ => "axiom"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .opaqueInfo _ => "opaque"
          | _ => "auxiliary"
        if kind == "auxiliary" then continue
        let type ← ppExpr info.type
        let body ← match info with
          | .defnInfo v => pure (← ppExpr v.value).pretty
          | _ => pure ""
        let deps := match info with
          | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
          | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
          | _ => info.type.getUsedConstants
        names := names.push name
        entries := entries.push <| Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleName.toString),
          ("kind", toJson kind), ("type", toJson type.pretty),
          ("body", toJson body), ("dependencies", toJson (deps.map Name.toString))]
    liftM (m := IO) <| IO.println "Auditing project axiom dependencies"
    let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
    pure <| Json.mkObj [
      ("schema_version", toJson (1 : Nat)), ("declarations", toJson entries),
      ("axioms", toJson (state.axioms.map Name.toString))]
  liftIO <| IO.println ("FORMAL_CONTEXT_JSON:" ++ result.compress)
