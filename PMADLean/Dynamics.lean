import PMADLean.Axioms
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open BigOperators Filter MeasureTheory

-- We use Fintype N to provide the bounded iteration constraints needed for the big sum symbol
variable {N : Type*} [DecidableEq N] [Fintype N]

/-- Definition: A trajectory satisfies the PMAD Phase Evolution flow (Eq. 2)
    iff its continuous derivative matches drive-locked quasienergies, 
    phase-mediated couplings, and bounded noise. -/
def IsPmadFlow (ϕ : Trajectory N) (ω : N → ℝ) (κ : N → N → ℝ) (ξ : ℝ → N → ℝ) (B : ℝ) : Prop :=
  -- Enforce strict Bounded Noise Constraint
  (∀ t i, |ξ t i| ≤ B) ∧
  -- Enforce the exact differential structure of Equation 2
  (∀ t i, HasDerivAt (fun t' => (ϕ t' i : ℝ))
    (ω i + ∑ j, κ i j * Real.sin (ϕ t j - ϕ t i) + ξ t i) t)

/-- Definition: A configuration's maximal Lyapunov exponent satisfies the
    PMAD Stability Criterion (A3 / Eq. 52) across long times using a limsup. -/
def IsAdmissibleAttractor (lambda_max : ℝ → ℝ) : Prop :=
  -- limsup_{T → ∞} (1/T) ∫₀ᵀ λ_max(t) dt < 0
  limsup (fun T => (1 / T) * ∫ t in (0)..T, lambda_max t) atTop < 0
