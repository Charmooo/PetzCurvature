/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smoothness of parametric interval integrals

For `f : H × ℝ → E` with `H` finite-dimensional, if `f` is `Cⁿ` at `(x₀, t)` for every `t` in
`[a, b]`, then `x ↦ ∫ t in a..b, f (x, t)` is `Cⁿ` at `x₀`, and its derivative is the integral of
the partial derivative `D₁f (x, t) = Df (x, t) ∘ inl`.

The hypothesis is pointwise in `t`, so it allows integrands that are smooth only near
`{x₀} × [a, b]`, such as resolvents `((1 - t) x + t)⁻¹` near an invertible `x₀`. By the tube lemma
(`IsCompact.eventually_forall_of_forall_eventually`) it holds on `closedBall x₀ r × [a, b]` for some
`r > 0`. There the partial derivative is bounded by compactness, and Mathlib's dominated
differentiation (`hasFDerivAt_integral_of_dominated_of_fderiv_le''`) applies. Smoothness of every
finite order follows by induction, through `contDiffAt_succ_iff_hasFDerivAt`.

## Main statements

* `eventually_forall_contDiffAt_of_forall`: the tube lemma for `ContDiffAt` on `{x₀} × [a, b]`.
* `hasFDerivAt_intervalIntegral_of_contDiffAt`: differentiation under the integral sign.
* `contDiffAt_intervalIntegral_of_contDiffAt`: `Cⁿ` regularity of the integral.
-/

open MeasureTheory Filter Set Metric ContinuousLinearMap
open scoped Topology Interval

universe u v

variable {H : Type u} {E : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}

omit [FiniteDimensional ℝ H] in
/-- **Tube lemma** for smoothness: if `f` is `Cⁿ` at `(x₀, t)` for every `t ∈ [a, b]`, then also
at `(x, t)` for `x` near `x₀` and every `t ∈ [a, b]`. -/
theorem eventually_forall_contDiffAt_of_forall {f : H × ℝ → E} {x₀ : H} {n : ℕ}
    (hf : ∀ t ∈ [[a, b]], ContDiffAt ℝ n f (x₀, t)) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ [[a, b]], ContDiffAt ℝ n f (x, t) :=
  isCompact_uIcc.eventually_forall_of_forall_eventually fun t ht ↦
    ((hf t ht).eventually (by simp)).mono fun _ hz ↦ hz

omit [FiniteDimensional ℝ H] in
/-- The partial derivative in the first variable: `D₁f (x, t) = Df (x, t) ∘ inl`. -/
theorem hasFDerivAt_comp_prodMk_left {f : H × ℝ → E} {x : H} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x, t)) :
    HasFDerivAt (fun y ↦ f (y, t)) ((fderiv ℝ f (x, t)).comp (inl ℝ H ℝ)) x :=
  hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)

omit [NormedSpace ℝ E] in
/-- A continuous function on `[a, b]` is integrable and measurable for `volume.restrict (Ι a b)`. -/
theorem aestronglyMeasurable_restrict_uIoc_of_continuousOn {g : ℝ → E}
    (hg : ContinuousOn g [[a, b]]) : AEStronglyMeasurable g (volume.restrict (Ι a b)) :=
  (hg.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc

/-- If `f` is `C¹` at `(x, t)` for `x` in the closed ball of radius `r` and `t ∈ [a, b]`, then the
partial derivative `D₁f` is bounded there. -/
theorem exists_bound_fderiv_comp_inl {f : H × ℝ → E} {x₀ : H} {r : ℝ}
    (hf : ∀ x ∈ closedBall x₀ r, ∀ t ∈ [[a, b]], ContDiffAt ℝ 1 f (x, t)) :
    ∃ C, ∀ x ∈ closedBall x₀ r, ∀ t ∈ [[a, b]],
      ‖(fderiv ℝ f (x, t)).comp (inl ℝ H ℝ)‖ ≤ C := by
  have hK : IsCompact (closedBall x₀ r ×ˢ [[a, b]]) :=
    (isCompact_closedBall x₀ r).prod isCompact_uIcc
  have hc : ContinuousOn (fun z : H × ℝ ↦ (fderiv ℝ f z).comp (inl ℝ H ℝ))
      (closedBall x₀ r ×ˢ [[a, b]]) := fun z hz ↦
    (((hf z.1 hz.1 z.2 hz.2).continuousAt_fderiv one_ne_zero).clm_comp
      continuousAt_const).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨C, fun x hx t ht ↦ hC (x, t) ⟨hx, ht⟩⟩

/-- **Differentiation under the integral sign** over `[a, b]`: if `f` is `C¹` at `(x₀, t)` for
every `t ∈ [a, b]`, then `x ↦ ∫ t in a..b, f (x, t)` has derivative `∫ t in a..b, D₁f (x₀, t)` at
`x₀`. -/
theorem hasFDerivAt_intervalIntegral_of_contDiffAt {f : H × ℝ → E} {x₀ : H}
    (hf : ∀ t ∈ [[a, b]], ContDiffAt ℝ 1 f (x₀, t)) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, f (x, t))
      (∫ t in a..b, (fderiv ℝ f (x₀, t)).comp (inl ℝ H ℝ)) x₀ := by
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_forall_contDiffAt_of_forall hf)
  have hball : ∀ x ∈ closedBall x₀ (ε / 2), ∀ t ∈ [[a, b]], ContDiffAt ℝ 1 f (x, t) :=
    fun x hx ↦ hεf (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith))
  obtain ⟨C, hC⟩ := exists_bound_fderiv_comp_inl hball
  have hcont : ∀ x ∈ closedBall x₀ (ε / 2), ContinuousOn (fun t ↦ f (x, t)) [[a, b]] :=
    fun x hx t ht ↦ ((hball x hx t ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hx₀ : x₀ ∈ closedBall x₀ (ε / 2) := mem_closedBall_self (by linarith)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (s := ball x₀ (ε / 2))
    (F := fun x t ↦ f (x, t)) (F' := fun x t ↦ (fderiv ℝ f (x, t)).comp (inl ℝ H ℝ))
    (bound := fun _ ↦ C) (ball_mem_nhds x₀ (by linarith)) ?_ ((hcont x₀ hx₀).intervalIntegrable)
    ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [ball_mem_nhds x₀ (half_pos hε)] with x hx
    exact aestronglyMeasurable_restrict_uIoc_of_continuousOn (hcont x (ball_subset_closedBall hx))
  · refine aestronglyMeasurable_restrict_uIoc_of_continuousOn fun t ht ↦ ?_
    exact ((((hball x₀ hx₀ t ht).continuousAt_fderiv one_ne_zero).comp
      (continuousAt_const.prodMk continuousAt_id)).clm_comp continuousAt_const).continuousWithinAt
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx ↦ ?_
    exact hC x (ball_subset_closedBall hx) t (uIoc_subset_uIcc ht)
  · refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx ↦ ?_
    exact hasFDerivAt_comp_prodMk_left
      ((hball x (ball_subset_closedBall hx) t (uIoc_subset_uIcc ht)).differentiableAt one_ne_zero)

/-- The derivative of `x ↦ ∫ t in a..b, f (x, t)` in a direction `v` is the integral of the
directional derivatives of the slices `x ↦ f (x, t)`. -/
theorem fderiv_intervalIntegral_apply_of_contDiffAt {f : H × ℝ → E} {x₀ : H}
    (hf : ∀ t ∈ [[a, b]], ContDiffAt ℝ 1 f (x₀, t)) (v : H) :
    fderiv ℝ (fun x ↦ ∫ t in a..b, f (x, t)) x₀ v =
      ∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ v := by
  have hc : ContinuousOn (fun t ↦ (fderiv ℝ f (x₀, t)).comp (inl ℝ H ℝ)) [[a, b]] := fun t ht ↦
    ((((hf t ht).continuousAt_fderiv one_ne_zero).comp
      (continuousAt_const.prodMk continuousAt_id)).clm_comp continuousAt_const).continuousWithinAt
  rw [(hasFDerivAt_intervalIntegral_of_contDiffAt hf).fderiv,
    ContinuousLinearMap.intervalIntegral_apply hc.intervalIntegrable]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  exact congrArg (· v)
    (hasFDerivAt_comp_prodMk_left ((hf t ht).differentiableAt one_ne_zero)).fderiv.symm

/-- Continuity of a parametric interval integral where the integrand is continuous on
`{x₀} × [a, b]`. -/
theorem continuousAt_intervalIntegral_of_continuousAt {f : H × ℝ → E} {x₀ : H}
    (hf : ∀ t ∈ [[a, b]], ContDiffAt ℝ 0 f (x₀, t)) :
    ContinuousAt (fun x ↦ ∫ t in a..b, f (x, t)) x₀ := by
  obtain ⟨ε, hε, hεf⟩ := Metric.eventually_nhds_iff.1 (eventually_forall_contDiffAt_of_forall hf)
  have hball : ∀ x ∈ closedBall x₀ (ε / 2), ∀ t ∈ [[a, b]], ContinuousAt f (x, t) :=
    fun x hx t ht ↦ (hεf (lt_of_le_of_lt (mem_closedBall.1 hx) (by linarith)) t ht).continuousAt
  have hK : IsCompact (closedBall x₀ (ε / 2) ×ˢ [[a, b]]) :=
    (isCompact_closedBall x₀ _).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := f) fun z hz ↦
    (hball z.1 hz.1 z.2 hz.2).continuousWithinAt
  have hcont : ∀ x ∈ closedBall x₀ (ε / 2), ContinuousOn (fun t ↦ f (x, t)) [[a, b]] :=
    fun x hx t ht ↦ ((hball x hx t ht).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  refine intervalIntegral.continuousAt_of_dominated_interval (F := fun x t ↦ f (x, t))
    (bound := fun _ ↦ C) ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [ball_mem_nhds x₀ (half_pos hε)] with x hx
    exact aestronglyMeasurable_restrict_uIoc_of_continuousOn (hcont x (ball_subset_closedBall hx))
  · filter_upwards [ball_mem_nhds x₀ (half_pos hε)] with x hx
    exact Eventually.of_forall fun t ht ↦
      hC (x, t) ⟨ball_subset_closedBall hx, uIoc_subset_uIcc ht⟩
  · refine Eventually.of_forall fun t ht ↦ ?_
    exact ContinuousAt.comp (g := f) (f := fun x : H ↦ (x, t))
      (hball x₀ (mem_closedBall_self (by linarith)) t (uIoc_subset_uIcc ht))
      (continuousAt_id.prodMk continuousAt_const)

/-- **Smoothness of a parametric interval integral**: if `f` is `Cⁿ` at `(x₀, t)` for every
`t ∈ [a, b]`, then `x ↦ ∫ t in a..b, f (x, t)` is `Cⁿ` at `x₀`. -/
theorem contDiffAt_intervalIntegral_of_contDiffAt (n : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : H × ℝ → E}
      {x₀ : H}, (∀ t ∈ [[a, b]], ContDiffAt ℝ n f (x₀, t)) →
        ContDiffAt ℝ n (fun x ↦ ∫ t in a..b, f (x, t)) x₀ := by
  induction n with
  | zero =>
    intro E _ _ f x₀ hf
    obtain ⟨ε, hε, hεf⟩ :=
      Metric.eventually_nhds_iff.1 (eventually_forall_contDiffAt_of_forall hf)
    refine contDiffAt_zero.2 ⟨ball x₀ ε, ball_mem_nhds x₀ hε, fun x hx ↦ ?_⟩
    exact (continuousAt_intervalIntegral_of_continuousAt (hεf hx)).continuousWithinAt
  | succ n ih =>
    intro E _ _ f x₀ hf
    obtain ⟨ε, hε, hεf⟩ :=
      Metric.eventually_nhds_iff.1 (eventually_forall_contDiffAt_of_forall hf)
    rw [Nat.cast_succ] at hf ⊢
    refine contDiffAt_succ_iff_hasFDerivAt.2
      ⟨fun x ↦ ∫ t in a..b, (fderiv ℝ f (x, t)).comp (inl ℝ H ℝ),
        ⟨ball x₀ ε, ball_mem_nhds x₀ hε, fun x hx ↦
          hasFDerivAt_intervalIntegral_of_contDiffAt fun t ht ↦ (hεf hx t ht).of_le ?_⟩,
        ih fun t ht ↦ ((hf t ht).fderiv_right (m := n) le_rfl).clm_comp contDiffAt_const⟩
    exact_mod_cast Nat.le_add_left 1 n
