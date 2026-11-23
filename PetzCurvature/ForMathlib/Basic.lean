/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Small lemmas Mathlib lacks

General facts used by the curvature computation, each a candidate for Mathlib.

## Main statements

* `fderiv_clm_apply_const`, `fderiv_clm_apply_apply_const`: the directional derivative of a field
  of (bi)linear maps applied to fixed vectors.
* `ContinuousLinearMap.IsInvertible.bilinearComp`: a bilinear map invertible as a map to the dual
  stays invertible after composing both arguments with invertible maps.
* `LinearMap.BilinForm.isInvertible_of_separatingLeft`, `LinearMap.BilinForm.isInvertible_of_pos`:
  in finite dimension, a continuous bilinear form that separates points on the left (for instance a
  positive definite one) is invertible as a map `E →L[ℝ] (E →L[ℝ] ℝ)`.
* `Matrix.inv_diagonal_ofReal`: the inverse of a diagonal matrix with nonzero real entries.
-/

/-! ### Derivatives of fields of linear maps -/

section FDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F F' F'' : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']

/-- The derivative of `y ↦ c y v` at `x` in the direction `X` is `fderiv 𝕜 c x X v`. -/
theorem fderiv_clm_apply_const {c : E → F →L[𝕜] F'} {x : E} (hc : DifferentiableAt 𝕜 c x)
    (v : F) (X : E) : fderiv 𝕜 (fun y ↦ c y v) x X = fderiv 𝕜 c x X v := by
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

/-- The derivative of `y ↦ c y v w` at `x` in the direction `X` is `fderiv 𝕜 c x X v w`. -/
theorem fderiv_clm_apply_apply_const {c : E → F →L[𝕜] F' →L[𝕜] F''} {x : E}
    (hc : DifferentiableAt 𝕜 c x) (v : F) (w : F') (X : E) :
    fderiv 𝕜 (fun y ↦ c y v w) x X = fderiv 𝕜 c x X v w := by
  rw [fderiv_clm_apply_const (hc.clm_apply (differentiableAt_const v)),
    fderiv_clm_apply_const hc]

end FDeriv

/-! ### Invertible bilinear maps -/

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {M N P M' N' : Type*} [NormedAddCommGroup M]
  [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup P]
  [NormedSpace 𝕜 P] [NormedAddCommGroup M'] [NormedSpace 𝕜 M'] [NormedAddCommGroup N']
  [NormedSpace 𝕜 N']

/-- A bilinear map `B : M →L N →L P` invertible as a map `M →L (N →L P)`, composed with two
invertible maps `gM : M' →L M` and `gN : N' →L N`, is invertible as a map `M' →L (N' →L P)`. -/
theorem IsInvertible.bilinearComp {B : M →L[𝕜] N →L[𝕜] P} (hB : B.IsInvertible)
    {gM : M' →L[𝕜] M} (hM : gM.IsInvertible) {gN : N' →L[𝕜] N} (hN : gN.IsInvertible) :
    (B.bilinearComp gM gN).IsInvertible := by
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨eM, rfl⟩ := hM
  obtain ⟨eN, rfl⟩ := hN
  refine ⟨eM.trans (b.trans (eN.symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 P))), ?_⟩
  ext u w
  simp

end ContinuousLinearMap

namespace LinearMap.BilinForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- In finite dimension, a bilinear form that separates points on the left (if `B v w = 0` for
every `w` then `v = 0`; the first half of `LinearMap.BilinForm.Nondegenerate`) is invertible as a
map `E →L[ℝ] (E →L[ℝ] ℝ)`. -/
theorem isInvertible_of_separatingLeft (hB : B.toBilinForm.SeparatingLeft) : B.IsInvertible := by
  have hinj : Function.Injective (B : E →ₗ[ℝ] (E →L[ℝ] ℝ)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hB v fun w ↦ by simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L w) hv
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq,
      Subspace.dual_finrank_eq]
  exact ⟨(LinearMap.linearEquivOfInjective _ hinj hdim).toContinuousLinearEquiv, rfl⟩

/-- A positive definite form is invertible as a map to covectors, in finite dimension. -/
theorem isInvertible_of_pos (hpos : ∀ v, v ≠ 0 → 0 < B v v) : B.IsInvertible :=
  isInvertible_of_separatingLeft fun v hv ↦ by
    by_contra h
    exact (hpos v h).ne' (hv v)

end LinearMap.BilinForm

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse of a diagonal matrix with nonzero real entries. -/
theorem inv_diagonal_ofReal {v : n → ℝ} (hv : ∀ i, v i ≠ 0) :
    (diagonal fun i ↦ (v i : ℂ))⁻¹ = diagonal fun i ↦ (((v i)⁻¹ : ℝ) : ℂ) := by
  refine inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  push_cast
  exact inv_mul_cancel₀ (by exact_mod_cast hv i)

end Matrix
