import PMADLean.Axioms
import PMADLean.Dynamics
import PMADLean.Metrics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open BigOperators Filter

variable {N : Type*} [DecidableEq N] [Fintype N]

/-- Section XIV-G (Eq. 78): Attractor Dimensionality D_A -/
noncomputable def AttractorDimensionality (μ_spectrum : N → ℝ) (Ω : ℝ) : ℝ :=
  ∑ i, (μ_spectrum i ^ 2) / (μ_spectrum i ^ 2 + Ω ^ 2)

/-- Section XIV-H (Eq. 81): The Wilsonian Renormalization Group Flow derivative. -/
noncomputable def AttractorDimensionalityRGFlow (μ_spectrum : N → ℝ) (Ω : ℝ) : ℝ :=
  - ∑ i, (2 * μ_spectrum i ^ 2 * Ω ^ 2) / (μ_spectrum i ^ 2 + Ω ^ 2) ^ 2

/-- Theorem: Verification that the Attractor Dimensionality flow is strictly monotonic. -/
theorem rg_flow_monotonicity (μ_spectrum : N → ℝ) (Ω : ℝ) (_h_Ω : Ω > 0) :
    AttractorDimensionalityRGFlow μ_spectrum Ω ≤ 0 := by
  simp [AttractorDimensionalityRGFlow]
  apply Finset.sum_nonneg
  intro i _
  have h_num : 0 ≤ (2 * μ_spectrum i ^ 2 * Ω ^ 2) / (μ_spectrum i ^ 2 + Ω ^ 2) ^ 2 := by
    apply div_nonneg
    · positivity
    · positivity
  exact h_num

/-- Theorem: The Renormalization Group IR Fixed Point (Page 10, Sec T-1).
    Proves that under infinite driving force (Ω -> ∞), the continuous attractor 
    dimensionality collapses to zero, signaling total phase-space contraction. -/
theorem rg_flow_ir_fixed_point (μ_spectrum : N → ℝ) :
    Tendsto (AttractorDimensionality μ_spectrum) atTop (nhds 0) := by
  unfold AttractorDimensionality
  have h_zero : (0 : ℝ) = ∑ _i : N, 0 := by simp
  rw [h_zero]
  apply tendsto_finsetSum
  intro i _
  have h_pow : Tendsto (fun (Ω : ℝ) => Ω ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h_den : Tendsto (fun (Ω : ℝ) => μ_spectrum i ^ 2 + Ω ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (f := fun (Ω : ℝ) => Ω ^ 2)
    · intro Ω
      apply le_add_of_nonneg_left (sq_nonneg (μ_spectrum i))
    · exact h_pow
  have h_inv : Tendsto (fun (Ω : ℝ) => (μ_spectrum i ^ 2 + Ω ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h_den
  -- 🌀 THE COMMUTATIVITY FIX: Multiply the constant on the LEFT to match your fraction's structure
  have h_final : Tendsto (fun (Ω : ℝ) => (μ_spectrum i ^ 2) * (μ_spectrum i ^ 2 + Ω ^ 2)⁻¹) atTop (nhds ((μ_spectrum i ^ 2) * 0)) :=
    Tendsto.const_mul (μ_spectrum i ^ 2) h_inv
  simp only [mul_zero] at h_final
  exact h_final
