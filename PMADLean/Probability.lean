import PMADLean.Axioms
import PMADLean.Dynamics
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open BigOperators Filter MeasureTheory Complex

-- Propagate the full decidable index properties to clear the summation blocks
variable {N : Type*} [DecidableEq N] [Fintype N]

/-- Definition: The Unified Phase-Overlap Functional (Eq. 5) evaluated 
    along a trajectory that strictly satisfies the PMAD dynamics (Eq. 2). -/
noncomputable def PhaseOverlapFunctional 
    (ϕ : Trajectory N) 
    (ω : N → ℝ) (κ : N → N → ℝ) (ξ : ℝ → N → ℝ) (B : ℝ) -- System Dynamics Parameters
    (_h_dyn : IsPmadFlow ϕ ω κ ξ B)                     -- The Dynamics Factor
    (i j : N) 
    (T : ℝ) : ℂ :=
  (1 / T) • (∫ t in (0)..T, exp (I * ((ϕ t i : ℝ) - (ϕ t j : ℝ))))

/-- Section XIII-C: The Attractor Basin Volume Contraction Rate (Eq. 69).
    The phase-space contraction rate Λ along the stable CLV bundles 
    is marked noncomputable due to the continuous Real.sin operation. -/
noncomputable def PhaseSpaceContractionRate 
    (ϕ : Trajectory N) 
    (κ : N → N → ℝ) 
    (t : ℝ) : ℝ :=
  - ∑ i, ∑ j, κ i j * Real.sin ((ϕ t j : ℝ) - (ϕ t i : ℝ))
