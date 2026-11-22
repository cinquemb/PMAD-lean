# PMAD-lean: Formal Verification of Phase-Mediated Attractor Dynamics

[![Zenodo](https://zenodo.org/badge/DOI/10.5281/zenodo.18511169.svg)](https://doi.org/10.5281/zenodo.18511169)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0005--5585--0584-brightgreen)](https://orcid.org/0009-0005-5585-0584)
[![SSRN](https://img.shields.io/badge/SSRN-10.2139/ssrn.6837299-brightblue)](https://dx.doi.org/10.2139/ssrn.6837299)
[![iNSpire HEP](https://img.shields.io/badge/iNSpire%20HEP-3167050-brightred)](https://inspirehep.net/authors/3167050)


An open-source mathematical repository containing the formal machine-checked verification of **Phase-Mediated Attractor Dynamics (PMAD)**, coded and verified using the **Lean 4** interactive theorem prover and the **Mathlib** ecosystem (and compiling Physlib postulates)

This library codifies the theoretical foundations presented in the companion manuscript, demonstrating that classical metric spacetime geometry, emergent effective force fields, and quantum measurement statistics (the Born rule) arise natively as reductions of non-autonomous phase-space attractor selection rather than fundamental postulates.

## Repository Status
* **Toolchain Snapshot:** `v4.33.0-rc1` (Aligned with Mathlib's modular infrastructure)
* **Compilation Status:** 100% Successful Pass (`17,498 jobs built clean`)
* **Logical Cloture:** Fully mathematically closed without placeholders (`sorry`-free core)

---

## Formal Verification Dependency Graph

Below is the strict dependency architecture certified by the Lean compiler kernel. Rather than isolating individual definitions, this pipeline maps the actual **logical transport arrows** from micro phase axioms down to macroscopic spacetime geometries:

### 📦 Axioms.lean (Foundations)
<details open>
<summary><b>View Module Elements (5 items)</b></summary>

```text
┌─── [Axioms.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  PhaseState                     
│  ├─ ⚙️ [DEF]  Trajectory                     
│  ├─ ⚙️ [DEF]  IsDynamicallyStable            
│  ├─ ⚙️ [DEF]  AttractorSet                   
│  ├─ ⚙️ [DEF]  UbiquitousResonance            
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Dynamics.lean (Attractor Convergence)
<details open>
<summary><b>View Module Elements (50 items)</b></summary>

```text
┌─── [Dynamics.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  IsPmadFlow                      ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  IsAdmissibleAttractor          
│  ├─ ⚙️ [DEF]  PhaseFlowDerivative             ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  PhaseSpaceOccupationDensity     ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  WeaveVertexType                
│  ├─ ⚙️ [DEF]  ClusterSeed                    
│  ├─ ⚙️ [DEF]  mutate_seed                    
│  ├─ ⚙️ [DEF]  laurent_space_eval             
│  ├─ ⚙️ [DEF]  laurent_state_evaluation        ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  IsLaurentShielded               ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  IsClassOneStable                ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  IsGloballyAcyclic              
│  ├─ ⚙️ [DEF]  IsMullerLocallyAcyclic         
│  ├─ ⚙️ [DEF]  IsLocallyAcyclicAt             
│  ├─ ⚙️ [DEF]  IsKuramotoSyncFlow              ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  KuramotoJacobian                ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  TimeAveragedStiffnessMatrix     ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  IsVariationalSolution           ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  stableSubspace                 
│  ├─ ⚙️ [DEF]  neutralSubspace                
│  ├─ ⚙️ [DEF]  unstableSubspace               
│  ├─ ⚙️ [DEF]  CovariantTangentSplitting       ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] kuramoto_jacobian_on_gauge_orbit  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] uniform_jacobian_zero_sum_eigenvalue  ➔ Outbound to: Axioms.Trajectory
│  ├─ ⬜ [TRIV] kuramoto_gronwall_contraction  
│  ├─ 🔥 [CORE] uniform_variational_sum_conserved  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] uniform_variational_zero_sum_contraction  ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  uniform_kuramoto_tangent_splitting  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] kuramoto_detuning_spectral_contraction  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] kuramoto_flow_converges_to_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.Trajectory, Axioms.AttractorSet
│  ├─ 🔥 [CORE] kuramoto_sync_flow_converges_to_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.AttractorSet
│  ├─ ⬜ [TRIV] jordan_ineq_nonneg             
│  ├─ 🔥 [CORE] kuramoto_gauge_orbit_forward_invariant  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] kuramoto_attractor_carries_clv_splitting  ➔ Outbound to: Axioms.Trajectory
│  ├─ ⬜ [TRIV] jordan_signed_mul_sin          
│  ├─ 🔥 [CORE] uniform_kuramoto_detuning_to_dissipation  ➔ Outbound to: Axioms.Trajectory, Axioms.UbiquitousResonance
│  ├─ 🔥 [CORE] resonant_kuramoto_detuning_to_dissipation  ➔ Outbound to: Axioms.Trajectory, Axioms.UbiquitousResonance
│  ├─ 🔥 [CORE] tubular_gauge_attractor_of_contraction  ➔ Outbound to: Axioms.PhaseState, Axioms.Trajectory, Axioms.AttractorSet
│  ├─ 🔥 [CORE] pmad_flow_converges_to_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.Trajectory, Axioms.AttractorSet
│  ├─ 🔥 [CORE] pmad_flow_attractor_and_clv_splitting  ➔ Outbound to: Axioms.PhaseState, Axioms.Trajectory, Axioms.AttractorSet
│  ├─ 🔥 [CORE] uniform_kuramoto_converges_to_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.AttractorSet, Axioms.UbiquitousResonance
│  ├─ 🔥 [CORE] resonant_kuramoto_converges_to_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.AttractorSet, Axioms.UbiquitousResonance
│  ├─ 🔥 [CORE] kuramoto_strong_coupling_limit_to_pmad_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.Trajectory, Axioms.AttractorSet, Axioms.UbiquitousResonance
│  ├─ 🔥 [CORE] global_phase_gauge_invariance   ➔ Outbound to: Axioms.Trajectory
│  ├─ ⬜ [TRIV] stability_under_bounded_perturbations 
│  ├─ ⬜ [TRIV] laurent_eval_scale_bound       
│  ├─ ⬜ [TRIV] eventually_sign_preserved_of_tendsto 
│  ├─ ⬜ [TRIV] cell_mutation_scale_bounds     
│  ├─ 🔥 [CORE] laurent_shielded_mutation_invariant  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] cluster_flow_converges_to_attractor  ➔ Outbound to: Axioms.PhaseState, Axioms.Trajectory, Axioms.AttractorSet
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Probability.lean (Born Rule & Bounds)
<details open>
<summary><b>View Module Elements (17 items)</b></summary>

```text
┌─── [Probability.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  PhaseOrderParameter             ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  PhaseOverlapFunctional          ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ ⚙️ [DEF]  PhaseSpaceContractionRate       ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  MacroscopicBornProbability      ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ ⚙️ [DEF]  AmplitudeWeight                
│  ├─ ⚙️ [DEF]  TimeSeriesSample               
│  ├─ ⚙️ [DEF]  IsInArnoldTongue                ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] phase_order_parameter_bounds_constructive  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] overlap_limit_of_matched_noiseless_flow  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] uncoupled_flow_volume_conservation  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] born_rule_resonance_limit       ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] born_rule_derived_from_paper_dynamics  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] born_rule_general_weighted_limit  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] born_rule_bounded_noise_concentration  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] derive_ftc_evolution            ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory
│  ├─ 🔥 [CORE] born_rule_noise_degradation_bound_derive_ftc_evolution  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Axioms.IsDynamicallyStable, Axioms.AttractorSet, Dynamics.pmad_flow_converges_to_attractor
│  ├─ ⬜ [TRIV] data_pipeline_discretization_bound 
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Metrics.lean (Compliance Geometry)
<details open>
<summary><b>View Module Elements (31 items)</b></summary>

```text
┌─── [Metrics.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  AttractorDimensionality        
│  ├─ ⚙️ [DEF]  PhaseMomentum                  
│  ├─ ⚙️ [DEF]  EmergentComplianceMetric       
│  ├─ ⚙️ [DEF]  LocalPhaseVelocityGradient      ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  LocalPhaseVorticityTensor       ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  ComplianceFloor                
│  ├─ ⚙️ [DEF]  phaseInnerProduct              
│  ├─ ⚙️ [DEF]  phaseNorm                       ➔ Outbound to: Dynamics.CovariantTangentSplitting
│  ├─ ⚙️ [DEF]  SubspaceHyperAngle              ➔ Outbound to: Axioms.Trajectory, Dynamics.CovariantTangentSplitting
│  ├─ ⚙️ [DEF]  CLVComplianceFloor              ➔ Outbound to: Axioms.Trajectory, Dynamics.CovariantTangentSplitting
│  ├─ ⚙️ [DEF]  NormalizedMetricTraceDensity   
│  ├─ ⚙️ [DEF]  DynamicSpatialAdjacency        
│  ├─ ⚙️ [DEF]  ClusterTranscendenceDegree     
│  ├─ 🔥 [CORE] resonance_monotonicity          ➔ Outbound to: Axioms.UbiquitousResonance
│  ├─ ⬜ [TRIV] spatial_locality_collapse      
│  ├─ ⬜ [TRIV] metric_singularity_censorship  
│  ├─ 🔥 [CORE] stiffness_from_overlap_functional  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Probability.PhaseOverlapFunctional
│  ├─ ⬜ [TRIV] compliance_metric_diagonal_bound 
│  ├─ 🔥 [CORE] vorticity_tensor_magnitude_bound  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] vorticity_tensor_translational_invariance  ➔ Outbound to: Axioms.Trajectory
│  ├─ 🔥 [CORE] vorticity_tensor_gauge_invariance  ➔ Outbound to: Axioms.Trajectory
│  ├─ ⬜ [TRIV] compliance_floor_monotonicity  
│  ├─ ⬜ [TRIV] compliance_floor_divergence_bounds 
│  ├─ 🔥 [CORE] uniform_kuramoto_clv_orthogonal_compliance  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Dynamics.uniform_kuramoto_tangent_splitting
│  ├─ 🔥 [CORE] clv_compliance_floor_pos        ➔ Outbound to: Axioms.Trajectory, Dynamics.TimeAveragedStiffnessMatrix, Dynamics.CovariantTangentSplitting
│  ├─ 🔥 [CORE] clv_regularized_stiffness_diagonal_bound  ➔ Outbound to: Axioms.Trajectory, Dynamics.TimeAveragedStiffnessMatrix, Dynamics.CovariantTangentSplitting
│  ├─ 🔥 [CORE] coordinate_independence         ➔ Outbound to: Axioms.Trajectory
│  ├─ ⬜ [TRIV] compliance_metric_positivity   
│  ├─ ⬜ [TRIV] attractor_dimensionality_bounds 
│  ├─ ⬜ [TRIV] attractor_dimensionality_le_trans_degree 
│  ├─ ⬜ [TRIV] thermodynamic_density_regularity_bound 
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Renormalization.lean (Scale Decay)
<details open>
<summary><b>View Module Elements (13 items)</b></summary>

```text
┌─── [Renormalization.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  AttractorDimensionalityRGFlow  
│  ├─ ⚙️ [DEF]  ContinuousAttractorDimensionality 
│  ├─ ⚙️ [DEF]  ContinuousAttractorDimensionalityRGFlow 
│  ├─ ⬜ [TRIV] rg_flow_monotonicity           
│  ├─ 🔥 [CORE] rg_flow_ir_fixed_point          ➔ Outbound to: Metrics.AttractorDimensionality
│  ├─ 🔥 [CORE] compliance_floor_bounds_rg_spectrum  ➔ Outbound to: Metrics.metric_singularity_censorship, Metrics.AttractorDimensionality, Metrics.EmergentComplianceMetric
│  ├─ 🔥 [CORE] dynamics_to_renormalization_capacity_bound  ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Metrics.AttractorDimensionality
│  ├─ 🔥 [CORE] rg_flow_finite_monotonicity     ➔ Outbound to: Metrics.AttractorDimensionality
│  ├─ 🔥 [CORE] rg_flow_uv_bounds               ➔ Outbound to: Metrics.AttractorDimensionality
│  ├─ ⬜ [TRIV] rg_flow_component_bounds       
│  ├─ 🔥 [CORE] rg_flow_c_theorem_analog        ➔ Outbound to: Metrics.AttractorDimensionality
│  ├─ ⬜ [TRIV] continuous_rg_flow_monotonicity 
│  ├─ ⬜ [TRIV] continuous_rg_flow_finite_monotonicity 
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Vorticity.lean (Spacetime Synthesis)
<details open>
<summary><b>View Module Elements (83 items)</b></summary>

```text
┌─── [Vorticity.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  MacroscopicPhaseCurrent        
│  ├─ ⚙️ [DEF]  PhaseVelocityGradient           ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  PhaseVorticityTensor            ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  UnifiedMacroscopicSpacetimeMetricDim 
│  ├─ ⚙️ [DEF]  LocalFrameDraggingVector        ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  FrameDraggingMetricComponent   
│  ├─ ⚙️ [DEF]  UnifiedMacroscopicSpacetimeMetric 
│  ├─ ⚙️ [DEF]  SynthesizedSpacetimeMetric1     ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOrderParameter, Metrics.AttractorDimensionality, Dynamics.ClusterSeed, Dynamics.PhaseSpaceOccupationDensity
│  ├─ ⚙️ [DEF]  SynthesizedSpacetimeMetricDim   ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOrderParameter, Metrics.SubspaceHyperAngle, Metrics.AttractorDimensionality, Metrics.CLVComplianceFloor, Dynamics.PhaseSpaceOccupationDensity
│  ├─ ⚙️ [DEF]  SynthesizedSpacetimeMetricDimCLV  ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOrderParameter, Metrics.AttractorDimensionality, Metrics.CLVComplianceFloor, Dynamics.PhaseSpaceOccupationDensity, Dynamics.CovariantTangentSplitting
│  ├─ ⚙️ [DEF]  TransportArrow                 
│  ├─ ⚙️ [DEF]  PureMicroscaleMetric            ➔ Outbound to: Axioms.Trajectory, Dynamics.ClusterSeed
│  ├─ ⚙️ [DEF]  mutate_seed_seq                 ➔ Outbound to: Dynamics.mutate_seed, Dynamics.ClusterSeed
│  ├─ ⚙️ [DEF]  mutate_matrix_real             
│  ├─ ⚙️ [DEF]  mutate_matrix_real_seq         
│  ├─ ⚙️ [DEF]  sgnReal                        
│  ├─ ⚙️ [DEF]  mutate_c_matrix_real           
│  ├─ ⚙️ [DEF]  mutate_c_matrix_real_seq       
│  ├─ ⚙️ [DEF]  extendBC                       
│  ├─ ⚙️ [DEF]  mutate_g_matrix_real           
│  ├─ ⚙️ [DEF]  mutate_joint_pattern_real_seq  
│  ├─ ⚙️ [DEF]  VarietyChart                   
│  ├─ ⚙️ [DEF]  evaluate_chart_path            
│  ├─ ⚙️ [DEF]  physicalChartFamily            
│  ├─ ⚙️ [DEF]  RealMutationEquivalent          ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  RecurrentGIntersection          ➔ Outbound to: Axioms.Trajectory
│  ├─ ⚙️ [DEF]  AsymptoticGIntersection        
│  ├─ ⚙️ [DEF]  variety_invariant              
│  ├─ 🔥 [CORE] vorticity_tensor_antisymmetric  ➔ Outbound to: Axioms.Trajectory
│  ├─ ⬜ [TRIV] compliance_floor_prevents_spacetime_singularity 
│  ├─ 🔥 [CORE] pmad_unification_censorship     ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Axioms.Trajectory, Probability.PhaseOrderParameter, Dynamics.ClusterSeed, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] pmad_unification_censorship_dim  ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Axioms.Trajectory, Probability.PhaseOrderParameter, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] phase_space_occupation_density_sum_bound  ➔ Outbound to: Axioms.Trajectory, Dynamics.PhaseSpaceOccupationDensity, Dynamics.PhaseFlowDerivative
│  ├─ 🔥 [CORE] pmad_unification_censorship_dim_alltime  ➔ Outbound to: Axioms.Trajectory, Metrics.clv_compliance_floor_pos, Probability.PhaseOrderParameter, Metrics.CLVComplianceFloor, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] pmad_clv_core_collapse_censorship  ➔ Outbound to: Axioms.Trajectory, Metrics.clv_compliance_floor_pos, Metrics.SubspaceHyperAngle, Metrics.CLVComplianceFloor, Dynamics.CovariantTangentSplitting
│  ├─ 🔥 [CORE] pmad_unification_censorship_dim_clv_alltime  ➔ Outbound to: Axioms.Trajectory, Metrics.clv_compliance_floor_pos, Probability.PhaseOrderParameter, Metrics.SubspaceHyperAngle, Metrics.CLVComplianceFloor, Dynamics.PhaseSpaceOccupationDensity, Dynamics.CovariantTangentSplitting
│  ├─ ⬜ [TRIV] matrix_grid_double_sum_bound   
│  ├─ ⬜ [TRIV] complex_norm_from_real_bound   
│  ├─ 🔥 [CORE] phase_overlap_locked_time_collapse  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.PhaseOverlapFunctional
│  ├─ 🔥 [CORE] complex_norm_error_bound_single_slot  ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.AmplitudeWeight, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] complex_norm_error_bound_matrix_grid  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Probability.PhaseOverlapFunctional, Probability.AmplitudeWeight
│  ├─ 🔥 [CORE] derive_order_parameter_handshake_from_dynamics  ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Probability.AmplitudeWeight, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] derive_arnold_tongue_emergence_identity  ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Probability.IsInArnoldTongue, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] pmad_micro_censorship_alltime   ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Axioms.Trajectory, Renormalization.dynamics_to_renormalization_capacity_bound, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Metrics.AttractorDimensionality, Probability.AmplitudeWeight, Probability.IsInArnoldTongue, Renormalization.rg_flow_finite_monotonicity, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] pmad_micro_censorship_alltime_noisy  ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Axioms.Trajectory, Renormalization.dynamics_to_renormalization_capacity_bound, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Metrics.AttractorDimensionality, Metrics.CLVComplianceFloor, Probability.IsInArnoldTongue, Renormalization.rg_flow_finite_monotonicity, Dynamics.PhaseSpaceOccupationDensity, Dynamics.CovariantTangentSplitting
│  ├─ 🔥 [CORE] pmad_micro_censorship_clv_noisy  ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Axioms.Trajectory, Probability.PhaseOverlapFunctional, Metrics.clv_compliance_floor_pos, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Metrics.SubspaceHyperAngle, Metrics.CLVComplianceFloor, Probability.IsInArnoldTongue, Dynamics.PhaseSpaceOccupationDensity, Dynamics.CovariantTangentSplitting
│  ├─ ⬜ [TRIV] macroscopic_geodesic_completeness_invariant 
│  ├─ ⬜ [TRIV] eventually_sign_preserved_of_tendsto 
│  ├─ ⬜ [TRIV] eventually_neg_sign_preserved_of_tendsto 
│  ├─ 🔥 [CORE] vorticity_tensor_limit_bridges_cluster_seed  ➔ Outbound to: Axioms.Trajectory, Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] vorticity_to_cluster_sign_bridge  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Probability.PhaseOverlapFunctional, Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] derived_vorticity_to_cluster_bridge  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] derived_vorticity_to_cluster_sign_bridge  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] pmad_uniform_positive_channel_implies_seed_positive  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] pmad_realizes_local_acyclic_channel  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.IsLocallyAcyclicAt, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] pmad_realizes_mutation_scale_bound  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.IsLocallyAcyclicAt, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Dynamics.cell_mutation_scale_bounds, Dynamics.mutate_seed, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] mutate_seed_of_positive_positive  ➔ Outbound to: Dynamics.mutate_seed, Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] pmad_realizes_mutation_increment  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.IsLocallyAcyclicAt, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Dynamics.mutate_seed, Probability.MacroscopicBornProbability
│  ├─ ⬜ [TRIV] tendsto_mutate_matrix_real     
│  ├─ 🔥 [CORE] tendsto_mutate_matrix_real_seq  ➔ Outbound to: Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] mutate_matrix_real_seq_cast     ➔ Outbound to: Dynamics.mutate_seed, Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] mutation_seq_limit_transport    ➔ Outbound to: Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] eventual_sign_along_path        ➔ Outbound to: Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] pmad_realizes_eventual_sign_along_path  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ ⬜ [TRIV] tendsto_mutate_c_matrix_real   
│  ├─ ⬜ [TRIV] tendsto_mutate_c_matrix_real_seq 
│  ├─ ⬜ [TRIV] pmad_c_vector_sign_coherence_obstruction 
│  ├─ ⬜ [TRIV] extended_mutation_seq_limit_transport 
│  ├─ ⬜ [TRIV] tendsto_mutate_g_matrix_real   
│  ├─ ⬜ [TRIV] extended_g_matrix_seq_limit_transport_helper 
│  ├─ ⬜ [TRIV] extended_g_matrix_seq_limit_transport 
│  ├─ 🔥 [CORE] pmad_drives_extended_g_matrix_transport  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ ⬜ [TRIV] evaluate_chart_path_eq_mutate_joint_seq 
│  ├─ 🔥 [CORE] pmad_realizes_exchange_graph_morphism  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ ⬜ [TRIV] evaluate_chart_path_generalized 
│  ├─ ⬜ [TRIV] quasienergy_sideband_invariance_under_mutation 
│  ├─ 🔥 [CORE] pmad_morphism_respects_path_concatenation  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Probability.MacroscopicBornProbability
│  ├─ ⬜ [TRIV] macro_current_invariant_under_mutation 
│  ├─ 🔥 [CORE] mutation_attractor_recurrent_intersection  ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Probability.IsInArnoldTongue, Dynamics.PhaseSpaceOccupationDensity
│  ├─ 🔥 [CORE] variety_invariant_is_sufficient_classification  ➔ Outbound to: Axioms.Trajectory, Probability.PhaseOverlapFunctional, Dynamics.IsPmadFlow, Probability.PhaseOrderParameter, Dynamics.ClusterSeed, Probability.IsInArnoldTongue, Dynamics.PhaseSpaceOccupationDensity
│  ├─ ⬜ [TRIV] variety_invariant_is_mutation_invariant 
│  ├─ ⬜ [TRIV] variety_invariant_separates_mutation_classes 
│  ├─ ⬜ [TRIV] cluster_seed_non_equivalence_certificate 
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Incompleteness.lean (Decoupled Limits)
<details open>
<summary><b>View Module Elements (11 items)</b></summary>

```text
┌─── [Incompleteness.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  FullPhaseSpace                 
│  ├─ ⚙️ [DEF]  EmergentEffectiveForce         
│  ├─ ⚙️ [DEF]  VisibleSubmanifoldEvolution    
│  ├─ ⚙️ [DEF]  EmergentClusterForce            ➔ Outbound to: Dynamics.ClusterSeed
│  ├─ ⚙️ [DEF]  SeedEmergentMetric              ➔ Outbound to: Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] visible_submanifold_decoupling_limit  ➔ Outbound to: Metrics.resonance_monotonicity
│  ├─ 🔥 [CORE] resonance_modulation_of_manifold_evolution  ➔ Outbound to: Metrics.resonance_monotonicity, Metrics.DynamicSpatialAdjacency, Axioms.UbiquitousResonance
│  ├─ 🔥 [CORE] hidden_sector_backaction_invariant  ➔ Outbound to: Axioms.Trajectory, Axioms.PhaseState, Dynamics.ClusterSeed, Axioms.IsDynamicallyStable, Dynamics.mutate_seed, Axioms.AttractorSet
│  ├─ 🔥 [CORE] mutation_preserves_metric_regularity  ➔ Outbound to: Dynamics.mutate_seed, Dynamics.ClusterSeed
│  ├─ 🔥 [CORE] attractor_trajectory_to_metric_link  ➔ Outbound to: Axioms.Trajectory, Axioms.PhaseState, Dynamics.IsPmadFlow, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Axioms.IsDynamicallyStable, Axioms.AttractorSet, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] closed_loop_metric_backaction_fixed_point  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsClassOneStable, Dynamics.cluster_flow_converges_to_attractor, Dynamics.IsLaurentShielded, Dynamics.IsPmadFlow, Axioms.PhaseState, Dynamics.ClusterSeed, Probability.AmplitudeWeight, Axioms.AttractorSet, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 Test.lean (spiral-vm runtime example)
<details open>
<summary><b>View Module Elements (16 items)</b></summary>

```text
┌─── [Test.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  SpiralAlgoConfig               
│  ├─ ⚙️ [DEF]  executionStepCount             
│  ├─ ⚙️ [DEF]  IsSubExponentiallyBounded      
│  ├─ ⚙️ [DEF]  CoprimeInitialState            
│  ├─ ⚙️ [DEF]  PhaseGradientStep              
│  ├─ ⚙️ [DEF]  DualToneWaveform               
│  ├─ ⚙️ [DEF]  MeanFieldState                 
│  ├─ ⬜ [TRIV] executionStepCount_polynomial  
│  ├─ 🔥 [CORE] spiral_shor_like_subexponential_bound  ➔ Outbound to: Dynamics.IsPmadFlow, Probability.TimeSeriesSample
│  ├─ 🔥 [CORE] pmad_trajectory_discretization_bridge  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Probability.data_pipeline_discretization_bound, Probability.TimeSeriesSample
│  ├─ 🔥 [CORE] pmad_rg_attractor_convergence_time  ➔ Outbound to: Dynamics.IsAdmissibleAttractor, Axioms.Trajectory, Dynamics.IsPmadFlow, Metrics.AttractorDimensionality, Renormalization.rg_flow_c_theorem_analog, Renormalization.dynamics_to_renormalization_capacity_bound, Dynamics.pmad_flow_converges_to_attractor
│  ├─ 🔥 [CORE] gradient_descent_runtime_linearity  ➔ Outbound to: Metrics.AttractorDimensionality, Renormalization.rg_flow_c_theorem_analog
│  ├─ 🔥 [CORE] dual_tone_attractor_smoothing   ➔ Outbound to: Metrics.AttractorDimensionality, Renormalization.rg_flow_c_theorem_analog
│  ├─ ⬜ [TRIV] mean_field_velocity_bounded    
│  ├─ 🔥 [CORE] global_non_linear_lattice_convergence  ➔ Outbound to: Metrics.AttractorDimensionality
│  ├─ 🔥 [CORE] stochastic_gradient_linearity   ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Metrics.AttractorDimensionality, Probability.AmplitudeWeight, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.MacroscopicBornProbability
└──────────────────────────────────────────────────────────────────────┘
```
</details>

```text
       │
       ▼ [Cross-Module Dependency Pipeline]
```
### 📦 PhyslibBridge.lean (Show equivalence with Physlib)
<details open>
<summary><b>View Module Elements (8 items)</b></summary>

```text
┌─── [PhyslibBridge.lean] ──────────────────────────────────────────────────┐
│  ├─ ⚙️ [DEF]  K0                             
│  ├─ ⚙️ [DEF]  K1                             
│  ├─ ⚙️ [DEF]  bundledPmadPhaseDampingChannel  ➔ Outbound to: Dynamics.IsPmadFlow
│  ├─ 🔥 [CORE] physlib_quantum_probability_general_bridge  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Probability.AmplitudeWeight, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.MacroscopicBornProbability
│  ├─ 🔥 [CORE] amplitude_weight_equals_quantum_norm  ➔ Outbound to: Probability.AmplitudeWeight
│  ├─ 🔥 [CORE] physlib_off_diagonal_decoherence_bound  ➔ Outbound to: Axioms.Trajectory, Dynamics.IsPmadFlow, Probability.AmplitudeWeight, Probability.born_rule_noise_degradation_bound_derive_ftc_evolution, Probability.MacroscopicBornProbability
│  ├─ ⬜ [TRIV] bundled_pmad_channel_evaluation 
│  ├─ 🔥 [CORE] pmad_flow_tracks_bundled_cptp_output  ➔ Outbound to: Dynamics.IsPmadFlow, Axioms.Trajectory, Probability.MacroscopicBornProbability, Probability.AmplitudeWeight
└──────────────────────────────────────────────────────────────────────┘
```
</details>

---

## High Level Core Verified Architecture
The code tree is mapped inside the PMADLean/ library module to mirror the specific derivation pathways of the manuscript, emphasizing inter-module implication arrows:
1. Axioms.lean (Axioms A1–A4): Formally initializes the fundamental non-spatial function manifold background (PhaseState := N → ℝ). Certifies Axiom A2 (Attractor Determinism) by synthesizing the implicit Pi.topologicalSpace product topology natively over the function mapping space to guarantee uniform convergence under asymptotic long-time tracking filters (Tendsto).
2. Dynamics.lean (Equations 2, 20–24, & 75–77): Establishes the non-autonomous flow evolution equations driven by drive-locked quasienergies, phase-mediated coupling parameters, and bounded noise boundaries (\(\vert{}\xi_i(t)\vert{} \le B\)), alongside the tangent-space variational cocycle and Covariant Lyapunov Vector (CLV) subbundle splitting. Includes:
	• pmad_flow_converges_to_attractor & uniform_kuramoto_converges_to_attractor: Proves that any bound-compliant trajectory family is trapped within a closed coordinate bounding envelope, satisfying neighborhood filter convergence onto the synchronization gauge orbit.
	• KuramotoJacobian, TimeAveragedStiffnessMatrix, & IsVariationalSolution: Formalizes the instantaneous Jacobian \(J_{ij}(\phi, t) = \partial \dot{\phi}_i / \partial \phi_j\), the time-averaged stiffness operator \(C_{ij} = \kappa_{ij}\langle\cos(\phi_j - \phi_i)\rangle_T\), and the linearized variational flow \(\dot{v}(t) = J(\phi, t)v(t)\).
	• CovariantTangentSplitting, uniform_kuramoto_tangent_splitting, & kuramoto_attractor_carries_clv_splitting: Decomposes the tangent bundle along the synchronization gauge orbit into the neutral orbit tangent \(E^{c}\), trivial unstable subspace \(E^u = \bot\), and \((N-1)\)-dimensional transverse stable subspace \(E^{s}\), proving forward covariance and exponential norm contraction along \(E^{s}\) via kuramoto_gronwall_contraction.
	• global_phase_gauge_invariance: Rigorously proves that shifting all absolute coordinates uniformly by an arbitrary real translation constant (\(\phi \mapsto \phi + c\)) leaves the core differential flow structure perfectly invariant.
	• stability_under_bounded_perturbations: Verifies that an attractor configuration remains robustly stable (IsDynamicallyStable) under external perturbations when bounded beneath a negative Lyapunov exponent energy threshold (\(\lambda_{\max} < -\delta\)).
3. Metrics.lean (Equations 29, 47, 50, & 58): Machine-checks the Singularity Censorship Theorem (metric_singularity_censorship) and endogenizes the dynamic compliance floor \(\epsilon(t) = \alpha \cot \theta_{\mathrm{CLV}}(t)\) directly from the CLV subbundles in Dynamics.lean. Includes:
	• SubspaceHyperAngle & CLVComplianceFloor: Computes the principal hyper-angle \(\theta_{\mathrm{CLV}}(t)\) between split.E_s t and split.E_u t and drives ComplianceFloor α θ directly from the dynamical tangent-space splitting.
	• clv_compliance_floor_pos & clv_regularized_stiffness_diagonal_bound: Proves strict positivity of CLVComplianceFloor under sheared subbundles (\(0 < \theta_{\mathrm{CLV}}(t) < \pi / 2\)) and connects TimeAveragedStiffnessMatrix directly into EmergentComplianceMetric.
	• uniform_kuramoto_clv_orthogonal_compliance: Certifies the isotropic flat-space baseline (\(\theta_{\mathrm{CLV}} = \pi / 2\), \(\epsilon = 0\)) on the homogeneous synchronization attractor.
	• stiffness_from_overlap_functional: A re-coupled transport arrow linking synchronized trajectories from Probability.lean to sharp upper bounds on real phase stiffness channels.
	• coordinate_independence: Machine-checks that the phase velocity gradient fields are invariant under an index permutation (\(\sigma : N \simeq N\)), proving observables are independent of arbitrary geometric indexing.
	• compliance_metric_positivity & compliance_metric_diagonal_bound: Proves strict diagonal positive definiteness and entry-wise suppression of EmergentComplianceMetric for all \(\epsilon > 0\).
	• compliance_floor_monotonicity & compliance_floor_divergence_bounds: Proves that as stable and unstable pathways collapse (\(\theta \to 0\)), the compliance floor spikes monotonically and stays lower-bounded.
	• resonance_monotonicity, attractor_dimensionality_bounds, & thermodynamic_density_regularity_bound: Verifies monotonic resonance weighting, discrete spectral capacity bounds (\(0 \le D_A \le \vert{}N\vert{}\)), and finite trace compliance in the continuum limit (\(\vert{}N\vert{} \to \infty\)).
4. Probability.lean (Equations 5, 66, & 69): Codifies the complex continuous time-averaging over the unified phase-overlap functional \(\mathcal{O}_{ij}\) (PhaseOverlapFunctional) and the continuous volume contraction rate \(\Lambda(t)\) (PhaseSpaceContractionRate). Proves modulus behavior via overlap_limit_of_matched_noiseless_flow and includes uncoupled_flow_volume_conservation, bridging back to the dynamics core to verify phase volume conservation metrics under uncoupled baseline flows. Includes:
	• born_rule_resonance_limit & born_rule_derived_from_paper_dynamics: Extracts real projection profiles from the unified complex Phase Overlap space via MacroscopicBornProbability to prove that noiseless resonance recovers unitary Born-rule measurement statistics.
	• data_pipeline_discretization_bound: Resolves empirical sampling constraints by proving that a discrete 1D timeline array (TimeSeriesSample) mapping a continuous trajectory retains strict linear Lipschitz error bounds scaled by the temporal grid resolution \(\Delta t\).
5. Renormalization.lean (Equations 79–82): Formalizes the spectral trace dimensionality selection rule \(D_{A}\) as a non-local Wilsonian filtering kernel under variation of the continuous drive scale parameter \(\Omega \). Includes:
	• rg_flow_monotonicity, rg_flow_finite_monotonicity, & rg_flow_c_theorem_analog: Proves negative-definite RG flow monotonicity and discrete Zamolodchikov C-theorem dimensional compression across scale updates (\(\Omega_1 \le \Omega_2\)).
	• rg_flow_uv_bounds & rg_flow_ir_fixed_point: Verifies the UV baseline bounds and the infrared fixed-point collapse (\(D_A \to 0\) as \(\Omega \to \infty\)).
	• dynamics_to_renormalization_capacity_bound: Shows that stable attractor bounds from Dynamics.lean restrict the maximum fractal dimension of the space to the total finite node capacity (\(D_A \le \vert{}N\vert{}\)).
	• continuous_rg_flow_monotonicity & continuous_rg_flow_finite_monotonicity: Verifies continuous Lebesgue integral RG monotonicity over spectral densities \(\rho(\mu) \ge 0\).
6. Vorticity.lean (Equations 48, 49, 51, & 52): Formalizes Phase Vorticity \(\Omega _{ij}\) as the tensor curl of asymmetric macroscopic phase velocity gradients and synthesizes the regularized \(d\)-dimensional Kerr–Newman spacetime metric driven by the endogenous CLV compliance floor. Includes:
	• SynthesizedSpacetimeMetricDimCLV: Replaces static regularization with the endogenous CLVComplianceFloor α split t inside UnifiedMacroscopicSpacetimeMetricDim.
	• pmad_clv_core_collapse_censorship: Constructively evaluates the matrix inverse under simultaneous stiffness and vorticity collapse (\(C = 0, \Omega_{\mathrm{tensor}} = 0\)) to prove entry-wise regularity bounded by \((\mathrm{CLVComplianceFloor}\ \alpha\ \mathrm{split}\ t)^{-1}\).
	• pmad_unification_censorship_dim_clv_alltime & pmad_micro_censorship_clv_noisy: Certifies all-time non-degeneracy of the endogenous compliance floor (\(\epsilon(t) > 0\)) alongside global \(g_{00}\) and noisy microscale metric bounds.
	• vorticity_tensor_antisymmetric, vorticity_tensor_magnitude_bound, vorticity_tensor_translational_invariance, & vorticity_tensor_gauge_invariance: Verifies anti-symmetry, coupling bounds, translational invariance, and discrete \(2\pi\) gauge invariance of the vorticity tensor.
	• compliance_floor_prevents_spacetime_singularity & macroscopic_geodesic_completeness_invariant: Proves that a non-vanishing compliance floor (\(\epsilon > 0\)) enforces finite bounds on macroscopic spacetime metric elements.
7. Incompleteness.lean (Equations 72–74): Formally maps out the open-system visible submanifold transformations under unresolved hidden-sector dissipation boundaries, verifying the limit properties when background interaction channels decouple via visible_submanifold_decoupling_limit.

---





---

## Quick Start & Compilation

To pull down the precompiled Mathlib binary dependencies and build this PMAD proof matrix locally, follow these standard `elan` / `lake` commands:

```bash
# 1. Clone the repository
git clone https://github.com/cinquemb/PMAD-lean
cd PMAD-lean

# 2. Resync package toolchains and compile manifests
lake update

# 3. Pull down precompiled Mathlib binaries from the community cache
lake exe cache get

# 4. Execute the complete verification compilation pass
lake build
```

Upon a successful pass, the typechecker will verify all custom theorem dependencies and report a clean build configuration. Active section variable linter warnings are left active by design to cleanly audit unconstrained degrees of freedom reserved for downstream many-body extensions.

---

## Publication Context & Citation

For the LaTeX declarations block or manuscript citations, please use:

```bibtex
@software{mcfarlaneblake2026pmad,
  author = {McFarlane-Blake, Cinque},
  title = {PMAD-lean: Formal Verification of Phase-Mediated Attractor Dynamics},
  year = {2026},
  publisher = {GitHub},
  journal = {GitHub Repository},
  howpublished \(= {\url{https://github.com/cinquemb/PMAD-lean}} \)}
```


