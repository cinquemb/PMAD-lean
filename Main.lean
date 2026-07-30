import Lean
import PMADLean.Axioms
import PMADLean.Dynamics
import PMADLean.Metrics
import PMADLean.Probability
import PMADLean.Renormalization
import PMADLean.Vorticity
import PMADLean.Incompleteness
import PMADLean.GraphGen

open Lean

unsafe def main : IO Unit := do
  -- Explicitly pass an Array containing every single local module namespace target
  let modules := #[
    { module := `PMADLean.Axioms },
    { module := `PMADLean.Dynamics },
    { module := `PMADLean.Metrics },
    { module := `PMADLean.Probability },
    { module := `PMADLean.Renormalization },
    { module := `PMADLean.Vorticity },
    { module := `PMADLean.Incompleteness },
    { module := `PMADLean.GraphGen }
  ]
  
  Lean.withImportModules modules (opts := {}) (trustLevel := 0) fun env => do
    printTheoremGraph env
