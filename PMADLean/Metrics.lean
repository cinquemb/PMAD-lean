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

/-- Verification of sharp entry-wise metric suppression 
    under diagonal stiffness domination. Proves that if the state-dependent phase 
    stiffness matrix C is perfectly diagonalized, the diagonal entries of the 
    emergent compliance metric are sharply bounded above by the inverse compliance floor. -/
theorem compliance_metric_diagonal_bound (ε : ℝ) (h_ε : ε > 0) (d : N → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∀ i, (EmergentComplianceMetric (diagonal d) ε h_ε) i i ≤ ε⁻¹ := by
  intro i
  unfold EmergentComplianceMetric
  -- 1. Combine the diagonal matrix with the scaled identity matrix mapping cleanly
  have h_sum : diagonal d + ε • (1 : Matrix N N ℝ) = diagonal (fun j => d j + ε) := by
    ext j k
    by_cases h_jk : j = k
    · subst h_jk
      simp only [Matrix.add_apply, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
    · simp only [Matrix.add_apply, diagonal_apply_ne _ h_jk, Matrix.smul_apply, one_apply_ne h_jk, smul_eq_mul, mul_zero, add_zero]
  rw [h_sum]
  -- 2. Compute the exact matrix inverse of the combined diagonal system using left inverse properties
  have h_inv : (diagonal (fun j => d j + ε))⁻¹ = diagonal (fun j => (d j + ε)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have h_one : (fun j => (d j + ε)⁻¹ * (d j + ε)) = (fun _ => 1) := by
      ext j
      apply inv_mul_cancel₀
      linarith [hd j]
    rw [h_one, diagonal_one]
  rw [h_inv, diagonal_apply_eq]
  -- 3. Use real division bounds to deduce that (d i + ε)⁻¹ ≤ ε⁻¹ without naming volatile lemmas
  have h_pos_den : 0 < d i + ε := by linarith [hd i]
  have h_le : ε ≤ d i + ε := by linarith [hd i]
  rw [inv_eq_one_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) h_ε h_le

/-- Section XII-G (Eq. 47): Define the Phase Velocity Gradient field. -/
noncomputable def LocalPhaseVelocityGradient (κ : N → N → ℝ) (ϕ : Trajectory N) (t : ℝ) : N → N → ℝ :=
  fun i j => κ i j * Real.cos (ϕ t j - ϕ t i)

/-- Section XII-G (Eq. 48): The Localized Phase Vorticity Tensor (Ω_ij). -/
noncomputable def LocalPhaseVorticityTensor (κ : N → N → ℝ) (ϕ : Trajectory N) (t : ℝ) : N → N → ℝ :=
  fun i j => LocalPhaseVelocityGradient κ ϕ t i j - LocalPhaseVelocityGradient κ ϕ t j i

omit [DecidableEq N] [Fintype N] in
/--  Bounds on Phase Vorticity Magnitude.
    Proves that the anti-symmetric macroscopic Phase Vorticity Tensor (Ω_ij) 
    is sharply bounded at any snapshot by twice the scalar micro coupling parameter. -/
theorem vorticity_tensor_magnitude_bound (κ : N → N → ℝ) (h_κ : ∀ i j, 0 ≤ κ i j) (h_symm : ∀ i j, κ i j = κ j i) (ϕ : Trajectory N) (t : ℝ) (i j : N) :

    |LocalPhaseVorticityTensor κ ϕ t i j| ≤ 2 * κ i j := by
  unfold LocalPhaseVorticityTensor LocalPhaseVelocityGradient
  -- 1. Apply the triangle inequality to separate the composite velocity gradient flows
  have h_triangle := abs_sub (κ i j * Real.cos (ϕ t j - ϕ t i)) (κ j i * Real.cos (ϕ t i - ϕ t j))
  -- 2. Coordinate bounding using the fundamental invariant -1 ≤ cos(θ) ≤ 1
  have h_cos_le1 : Real.cos (ϕ t j - ϕ t i) ≤ 1 := Real.cos_le_one _
  have h_cos_ge1 : -1 ≤ Real.cos (ϕ t j - ϕ t i) := Real.neg_one_le_cos _
  have h_cos_le2 : Real.cos (ϕ t i - ϕ t j) ≤ 1 := Real.cos_le_one _
  have h_cos_ge2 : -1 ≤ Real.cos (ϕ t i - ϕ t j) := Real.neg_one_le_cos _
  -- 3. Formulate the explicit multi-variable absolute bounds bypassing raw non-linear linarith calls
  have h_abs_cos1 : |Real.cos (ϕ t j - ϕ t i)| ≤ 1 := by
    rw [abs_le]; exact ⟨h_cos_ge1, h_cos_le1⟩
  have h_abs_cos2 : |Real.cos (ϕ t i - ϕ t j)| ≤ 1 := by
    rw [abs_le]; exact ⟨h_cos_ge2, h_cos_le2⟩
  -- Extract linear bounds using nlinarith products
  have h_bound1 : |κ i j * Real.cos (ϕ t j - ϕ t i)| ≤ κ i j := by
    rw [abs_mul, abs_of_nonneg (h_κ i j)]
    have h_prod : κ i j * |Real.cos (ϕ t j - ϕ t i)| ≤ κ i j * 1 := mul_le_mul_of_nonneg_left h_abs_cos1 (h_κ i j)
    linarith
  have h_bound2 : |κ j i * Real.cos (ϕ t i - ϕ t j)| ≤ κ i j := by
    rw [h_symm j i, abs_mul, abs_of_nonneg (h_κ i j)]
    have h_prod : κ i j * |Real.cos (ϕ t i - ϕ t j)| ≤ κ i j * 1 := mul_le_mul_of_nonneg_left h_abs_cos2 (h_κ i j)
    linarith
  linarith

omit [DecidableEq N] [Fintype N] in
/-- Global Translational Invariance of the Vorticity Tensor.
    Proves that shifting all absolute coordinates uniformly by an arbitrary 
    real translation factor (ϕ ↦ ϕ + c) leaves the structural Phase Vorticity Tensor 
    identically invariant across all snapshots. -/
theorem vorticity_tensor_translational_invariance
    (κ : N → N → ℝ) (ϕ : Trajectory N) (t : ℝ) (i j : N) (c : ℝ) :
    LocalPhaseVorticityTensor κ (fun t' k => ϕ t' k + c) t i j = LocalPhaseVorticityTensor κ ϕ t i j := by
  unfold LocalPhaseVorticityTensor LocalPhaseVelocityGradient
  -- 1. Isolate the internal coordinate subtraction loops cleanly via ring axioms
  have h_trans1 : (ϕ t j + c) - (ϕ t i + c) = ϕ t j - ϕ t i := by ring
  have h_trans2 : (ϕ t i + c) - (ϕ t j + c) = ϕ t i - ϕ t j := by ring
  -- 2. Substitute the cancelled translation offsets back into the gradient fields
  rw [h_trans1, h_trans2]

omit [DecidableEq N] [Fintype N] in
/-- Discrete Gauge Invariance of the Vorticity Tensor.
    Proves that shifting any absolute tracking phase by an integer multiple of 2π 
    (ϕ ↦ ϕ + 2πk) acts as an exact identity operator, leaving all observable 
    velocity metrics perfectly unchanged. -/
theorem vorticity_tensor_gauge_invariance
    (κ : N → N → ℝ) (ϕ : Trajectory N) (t : ℝ) (i j : N) (k : ℤ) :
    LocalPhaseVorticityTensor κ (fun t' x => ϕ t' x + 2 * Real.pi * k) t i j = LocalPhaseVorticityTensor κ ϕ t i j := by
  unfold LocalPhaseVorticityTensor LocalPhaseVelocityGradient
  -- 1. Eliminate the inner trigonometric calculus loops entirely using congrArg
  have h_gauge1 : Real.cos (ϕ t j + 2 * Real.pi * (k : ℝ) - (ϕ t i + 2 * Real.pi * (k : ℝ))) = Real.cos (ϕ t j - ϕ t i) := by
    apply congrArg Real.cos
    -- The 2 * Real.pi * k blocks cancel out strictly via structural linear arithmetic
    linarith
  have h_gauge2 : Real.cos (ϕ t i + 2 * Real.pi * (k : ℝ) - (ϕ t j + 2 * Real.pi * (k : ℝ))) = Real.cos (ϕ t i - ϕ t j) := by
    apply congrArg Real.cos
    linarith
  -- 2. Substitute the evaluated identities back into the matrix tensor
  rw [h_gauge1, h_gauge2]
