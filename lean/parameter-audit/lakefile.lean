import Lake
open Lake DSL

package qrhParameterAudit where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target] lean_lib QRHParameterAudit where
  srcDir := ".."

-- Only the scalar support modules are needed; the Hecke formalization is separate.
lean_lib QRHScalarSupport where
  srcDir := ".."
  roots := #[`OAI.NumberTheory.DirichletL.Detector.Euler,
    `OAI.NumberTheory.DirichletL.Detector.Local,
    `OAI.NumberTheory.DirichletL.Detector.CorrectionBounds,
    `OAI.NumberTheory.DirichletL.Detector.EulerCoordinatesScalar,
    `OAI.NumberTheory.DirichletL.Detector.EulerRegion,
    `OAI.NumberTheory.DirichletL.Detector.EulerHolomorphic,
    `OAI.NumberTheory.DirichletL.Detector.NormalProduct,
    `OAI.NumberTheory.DirichletL.PrincipalSlotKernel,
    `OAI.NumberTheory.DirichletL.Inversion.TerminalExponent,
    `OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent,
    `OAI.NumberTheory.DirichletL.Detector.LowReflectedLength,
    `OAI.NumberTheory.DirichletL.Endpoint,
    `OAI.NumberTheory.DirichletL.Parameters,
    `OAI.NumberTheory.DirichletL.ParametersSlotLengths,
    `OAI.NumberTheory.DirichletL.Improved.FloorScales]
