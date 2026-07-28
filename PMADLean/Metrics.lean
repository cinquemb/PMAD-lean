import PMADLean.Axioms
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Intervals

open BigOperators Matrix

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

/-- Theorem: Spatial Locality Collapse Boundary. -/
theorem spatial_locality_collapse (κ : N → N → ℝ) (R : N → N → ℝ) (i j : N)
    (h_collapse : R i j = 0) : DynamicSpatialAdjacency κ R i j = 0 := by
  simp [DynamicSpatialAdjacency, h_collapse]

/-- Theorem: Singularity Censorship via the Compliance Floor (Eq. 29).
    Proves that if the state-dependent phase stiffness matrix C experiences complete 
    eutectic collapse (C -> 0), the regularized metric tensor component stays bounded, 
    matching your paper's exact prediction of a non-singular compliance floor. -/
theorem metric_singularity_censorship (ε : ℝ) (h_ε : ε > 0) :
    EmergentComplianceMetric (0 : Matrix N N ℝ) ε h_ε = (ε)⁻¹ • (1 : Matrix N N ℝ) := by
  -- 1. Safely update the type definition
  change (0 + ε • (1 : Matrix N N ℝ))⁻¹ = ε⁻¹ • (1 : Matrix N N ℝ)
  rw [zero_add]
  -- 2. Use the left inverse property
  apply Matrix.inv_eq_left_inv
  -- 3. Associate the structural matrix multiplications
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
  -- 4. 🌀 THE FIX: Merge the scalars globally from ε⁻¹ • ε • 1 to (ε⁻¹ * ε) • 1
  rw [smul_smul]
  -- 5. Cancel out the terms via real field inversion (ε⁻¹ * ε = 1)
  rw [inv_mul_cancel₀ (ne_of_gt h_ε)]
  -- 6. Close the identity step
  exact one_smul ℝ (1 : Matrix N N ℝ)
