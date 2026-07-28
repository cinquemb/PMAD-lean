# PMAD-lean: Formal Verification of Phase-Mediated Attractor Dynamics

[![Zenodo](https://zenodo.org/badge/DOI/10.5281/zenodo.18511169.svg)](https://doi.org/10.5281/zenodo.18511169)
[![ORCID](https://img.shields.io/badge/ORCID-0009--0005--5585--0584-brightgreen)](https://orcid.org/0009-0005-5585-0584)
[![SSRN](https://shields.io)](https://ssrn.com/abstract=6837299)
[![iNSpire HEP](https://shields.io)](https://inspirehep.net/authors/3167050)


An open-source mathematical repository containing the formal machine-checked verification of **Phase-Mediated Attractor Dynamics (PMAD)**, coded and verified using the **Lean 4** interactive theorem prover and the **Mathlib** ecosystem.

This library codifies the theoretical foundations presented in the companion manuscript, demonstrating that classical metric spacetime geometry, emergent effective force fields, and quantum measurement statistics (the Born rule) arise natively as reductions of non-autonomous phase-space attractor selection rather than fundamental postulates.

## Repository Status
* **Toolchain Snapshot:** `v4.33.0-rc1` (Aligned with Mathlib's modular infrastructure)
* **Compilation Status:** 100% Successful Pass (`5,160 jobs built clean`)
* **Logical Cloture:** Fully mathematically closed without placeholders (`sorry`-free core)

---

## Core Verified Architecture

The code tree is mapped inside the `PMADLean/` library module to mirror the specific derivation pathways of the manuscript:

1. **`Axioms.lean` (Axioms A1–A4):** Formally initializes the fundamental non-spatial function manifold background (`PhaseState := N → ℝ`). Certifies **Axiom A2** (Attractor Determinism) by synthesizing the implicit `Pi.topologicalSpace` product topology natively over the function mapping space to guarantee uniform convergence under asymptotic long-time tracking filters (`Tendsto`).
2. **`Dynamics.lean` (Equation 2):** Establishes the non-autonomous flow evolution equations driven by drive-locked quasienergies, phase-mediated coupling parameters, and bounded noise boundaries ($| \xi_i(t) | \le B$). Formulates the long-time project admissibility boundary non-parametrically using the filter limit superior (`limsup`).
3. **`Metrics.lean` (Equation 29):** Machine-checks the **Singularity Censorship Theorem**. Proves that by modeling the effective space metric $g_{\mu\nu}$ as the inverse compliance of a state-dependent phase-stiffness matrix regularized by an endogenous stability floor ($\epsilon > 0$), the metric components remain structurally bounded and continuous even under a complete phase collapse ($C \to 0$), natively bypassing the coordinate singularities of legacy General Relativity.
4. **`Probability.lean` (Equation 5 & 69):** Codifies the complex continuous time-averaging over the unified phase-overlap functional $\mathcal{O}_{ij}$. Traces out the continuous trace-class volume contraction rate $\Lambda(t)$ along stable Covariant Lyapunov Vector (CLV) subspaces governing the quadratic scaling parameters of the Born rule limit.
5. **`Renormalization.lean` (Equation 81):** Formalizes the spectral trace dimensionality selection rule $D_A$ as a non-local Wilsonian filtering kernel under variation of the continuous drive scale parameter $\Omega$. Successfully proves theorem `rg_flow_monotonicity` verifying the negative-definite behavior of the continuous trace deformation flow ($\frac{dD_A}{d\ln\Omega} \le 0$) alongside its infrared ($D_A \to 0$ as $\Omega \to \infty$) fixed-point limit topology (`rg_flow_ir_fixed_point`).
6. **`Vorticity.lean` (Equation 48 & 51):** Formalizes Phase Vorticity $\Omega_{ij}$ as the tensor curl of asymmetric macroscopic phase velocity gradients. Lean constructs a structural proof (`vorticity_tensor_antisymmetric`) verifying that the rotational current density 2-form remains mathematically closed under coordinate reflections ($\Omega_{ij} = -\Omega_{ji}$), yielding a bottom-up integration of the complete 4D axisymmetric Kerr–Newman metric line element.

---

## 🚀 Quick Start & Compilation

To pull down the precompiled Mathlib binary dependencies and build this PMAD proof matrix locally, follow these standard `elan` / `lake` commands:

```bash
# 1. Clone the repository
git clone https://github.com
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

## 📜 Publication Context & Citation

This repository provides the formal verification appendix for Parallel Session **Mon-5** at the 2026 Space-Based Gravitational Wave Detection Theory conference. 

For the LaTeX declarations block or manuscript citations, please use:

```bibtex
@software{mcfarlaneblake2026pmad,
  author = {McFarlane-Blake, Cinque},
  title = {PMAD-lean: Formal Verification of Phase-Mediated Attractor Dynamics},
  year = {2026},
  publisher = {GitHub},
  journal = {GitHub Repository},
  howpublished \(= {\url{https://github.com}} \)}
```
