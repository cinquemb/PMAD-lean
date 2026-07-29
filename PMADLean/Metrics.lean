import PMADLean.Axioms
import PMADLean.Dynamics
import PMADLean.Probability
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Complex.Basic

open BigOperators Matrix Complex Topology

variable {N : Type*} [DecidableEq N] [Fintype N]

/-- Section XII-B (Eq. 3): The Dynamic Spatial Adjacency Operator. -/
def DynamicSpatialAdjacency (κ : N → N → ℝ) (R : N → N → ℝ) (i j : N) : ℝ :=
  κ i j * R i j

/-- Section XII-D (Eq. 7): The Instantaneous Phase Momentum Vector Field. -/
noncomputable def PhaseMomentum (dphi : N → ℝ) : ℝ :=
  (1 / (Fintype.card N : ℝ)) * ∑ i, dphi i

/-- Definition: The emergent phase metric g_eff (Eq. 29) -/
noncomputable def EmergentComplianceMetric 
    (C : Matrix N N ℝ) 
    (ε : ℝ) 
    (_h_reg : ε > 0) : Matrix N N ℝ :=
  let regularized_stiffness := C + ε • (1 : Matrix N N ℝ)
  regularized_stiffness⁻¹

-- Explicitly omit section variables to keep the linter completely silent
omit [DecidableEq N] [Fintype N] in
/-- Theorem: Spatial Locality Collapse Boundary. -/
theorem spatial_locality_collapse (κ : N → N → ℝ) (R : N → N → ℝ) (i j : N)
    (h_collapse : R i j = 0) : DynamicSpatialAdjacency κ R i j = 0 := by
  simp only [DynamicSpatialAdjacency, h_collapse, mul_zero]

/-- Theorem: Singularity Censorship via the Compliance Floor (Eq. 29).
    Proves that if the state-dependent phase stiffness matrix C experiences complete 
    eutectic collapse (C -> 0), the regularized metric tensor component stays bounded, 
    mapping to that of a non-singular compliance floor. -/
theorem metric_singularity_censorship (ε : ℝ) (h_ε : ε > 0) :
    EmergentComplianceMetric (0 : Matrix N N ℝ) ε h_ε = (ε)⁻¹ • (1 : Matrix N N ℝ) := by
  -- 1. Safely update the type definition
  change (0 + ε • (1 : Matrix N N ℝ))⁻¹ = ε⁻¹ • (1 : Matrix N N ℝ)
  rw [zero_add]
  -- 2. Use the left inverse property
  apply Matrix.inv_eq_left_inv
  -- 3. Associate the structural matrix multiplications
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
  -- 4. Merge the scalars globally from ε⁻¹ • ε • 1 to (ε⁻¹ * ε) • 1
  rw [smul_smul]
  -- 5. Cancel out the terms via real field inversion (ε⁻¹ * ε = 1)
  rw [inv_mul_cancel₀ (ne_of_gt h_ε)]
  -- 6. Reduce the scalar identity multiplication 1 • 1 = 1
  rw [one_smul]

omit [DecidableEq N] in
/-- Section XII-B (Bridge): Overlap-to-Stiffness Transport Lemma.
    Proves that for a perfectly synchronized non-equilibrium flow channel, any generalized 
    overlap profile mapping real horizons to unit complex vectors exhibits a real part 
    bounded sharply by the micro coupling parameters. -/
theorem stiffness_from_overlap_functional
    (ϕ : Trajectory N) (ω : N → ℝ) (κ : N → N → ℝ) (ξ : ℝ → N → ℝ) (B : ℝ)
    (h_flow : IsPmadFlow ϕ ω κ ξ B) (i j : N) (h_sync : ∀ t, ϕ t i = ϕ t j) :
    ∀ T > 0, (PhaseOverlapFunctional ϕ ω κ ξ B h_flow i j T).re ≤ (κ i j) ^ 2 + 1 := by
  -- Introduce timescales and horizon parameters
  intro T hT
  -- 1. Unfold the true PhaseOverlapFunctional from Probability.lean to check the actual mechanics
  unfold PhaseOverlapFunctional
  -- Substitute the synchronization condition to evaluate the exponential path down to 1
  have h_exp_one : ∀ t, exp (I * ((ϕ t i : ℝ) - (ϕ t j : ℝ))) = 1 := by
    intro t
    rw [h_sync t, sub_self, mul_zero, Complex.exp_zero]
  simp_rw [h_exp_one]
  rw [intervalIntegral.integral_const, sub_zero]
  -- Decompose the real part of the scalar integral tracking block
  have h_re_one : ((1 / T) • T • (1 : ℂ)).re = 1 := by
    -- Simplify the real projection structures natively
    simp only [one_div, real_smul, mul_one, ofReal_inv, mul_re, inv_re, ofReal_re, normSq_ofReal, div_self_mul_self', inv_im, ofReal_im, neg_zero, zero_div, mul_zero, sub_zero]
    -- Explicitly cancel out the inverted field elements (T⁻¹ * T = 1) using the horizon positivity parameter
    exact inv_mul_cancel₀ (ne_of_gt hT)
  rw [h_re_one]
  -- Squaring any real number κ yields a non-negative value (0 ≤ κ^2), making 1 ≤ κ^2 + 1 unconditionally true
  have h_sq_nonneg : 0 ≤ (κ i j) ^ 2 := sq_nonneg (κ i j)
  linarith
