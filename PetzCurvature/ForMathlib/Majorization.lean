/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Claude (Anthropic)
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Majorization and the Schur–Ostrowski criterion

Majorization of real vectors and a differential criterion for Schur-concavity.

A vector `x : Fin n → ℝ` is **majorized** by `y` (`x` is more mixed than `y`) if both have the same
sum and, once sorted increasingly, every partial sum of the `k` smallest entries of `x` is at
least that of `y`. Equivalently (with equal totals), the sums of the `k` largest entries of `x` are
at most those of `y`.

The **Schur–Ostrowski criterion**: a permutation-invariant function whose gradient at every
increasingly sorted point is antitone in the index (larger entries have smaller partial
derivatives) does not decrease when its argument is replaced by a majorized one. The proof joins
the sorted vectors by a segment, which stays sorted, and rearranges the derivative along it by
Abel summation; it needs no chain of T-transforms.

The **strict criterion**: if moreover the gradient at a sorted point is strictly smaller at a
strictly larger entry, the function increases strictly unless the two sorted vectors agree. Along
the segment, entries may tie and the gradient need not be strictly antitone; but `z · v < 0` for
the point `z` and the direction `v` of the segment (before its end), and by Abel summation this
gives a gap `zᵢ < zᵢ₊₁` at an index where the partial sum of `v` is positive. The gradient drops
strictly across that gap, so the derivative along the segment is positive.

## Main definitions

* `Majorization.sortInc x`: `x` sorted increasingly.
* `Majorization.toSeq x`: `x` as a sequence, `0` beyond `n`.
* `IsMajorizedBy x y`: `x` is majorized by `y`.

## Main statements

* `Majorization.sum_mul_nonneg_of_antitone`: Abel summation, `0 ≤ ∑ Gₖ dₖ` for `G` antitone and
  nonnegative and partial sums of `d` nonnegative.
* `Majorization.sum_mul_eq_sum_sub_mul`: Abel summation as an identity.
* `Majorization.sum_mul_pos_of_antitone_of_sum_eq_zero`: its strict form.
* `Majorization.exists_comp_eq_of_sortInc_eq`: vectors with the same sorted form are
  permutations of each other.
* `le_of_isMajorizedBy`: the Schur–Ostrowski criterion.
* `lt_of_isMajorizedBy`: the strict Schur–Ostrowski criterion.
* `isMajorizedBy_const`: the uniform vector is majorized by every vector with the same total.

## References

* [R. Bhatia, *Matrix Analysis*][bhatia1997], Chapter II

-/

open Finset Set

namespace Majorization

/-! ### Abel summation -/

/-- **Abel summation, as a sign**: if `G₀ ≥ G₁ ≥ ⋯ ≥ Gₙ₋₁ ≥ 0` and every partial sum of `d` is
nonnegative, then `∑ₖ Gₖ dₖ ≥ 0`. -/
theorem sum_mul_nonneg_of_antitone (n : ℕ) {G d : ℕ → ℝ}
    (hG : ∀ i j, i ≤ j → j < n → G j ≤ G i) (hG0 : ∀ i < n, 0 ≤ G i)
    (hd : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, d i) : 0 ≤ ∑ i ∈ range n, G i * d i := by
  induction n generalizing G with
  | zero => simp
  | succ n ih =>
    have e : ∑ i ∈ range (n + 1), G i * d i =
        ∑ i ∈ range n, (G i - G n) * d i + G n * ∑ i ∈ range (n + 1), d i := by
      rw [sum_range_succ, sum_range_succ, mul_add, mul_sum]
      simp only [sub_mul, sum_sub_distrib]
      ring
    rw [e]
    refine add_nonneg (ih (fun i j hij hj ↦ sub_le_sub_right (hG i j hij (by omega)) _)
      (fun i hi ↦ sub_nonneg.2 (hG i n hi.le (by omega))) fun k hk ↦ hd k (by omega))
      (mul_nonneg (hG0 n (by omega)) (hd (n + 1) le_rfl))

/-- The same with total sum `0`, and no sign condition on `G`. -/
theorem sum_mul_nonneg_of_antitone_of_sum_eq_zero (n : ℕ) {G d : ℕ → ℝ}
    (hG : ∀ i j, i ≤ j → j < n → G j ≤ G i) (hd : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, d i)
    (htot : ∑ i ∈ range n, d i = 0) : 0 ≤ ∑ i ∈ range n, G i * d i := by
  rcases n with _ | n
  · simp
  have e : ∑ i ∈ range (n + 1), G i * d i =
      ∑ i ∈ range (n + 1), (G i - G n) * d i + G n * ∑ i ∈ range (n + 1), d i := by
    simp only [sub_mul, sum_sub_distrib, mul_sum]
    ring
  rw [e, htot, mul_zero, add_zero]
  exact sum_mul_nonneg_of_antitone (n + 1)
    (fun i j hij hj ↦ sub_le_sub_right (hG i j hij hj) _)
    (fun i hi ↦ sub_nonneg.2 (hG i n (by omega) (by omega))) hd

/-- **Abel summation**: `∑_{i ≤ m} Gᵢ dᵢ = ∑_{i < m} (Gᵢ - Gᵢ₊₁) Dᵢ₊₁ + Gₘ Dₘ₊₁`, with
`Dₖ = ∑_{j < k} dⱼ` the partial sums of `d`. -/
theorem sum_mul_eq_sum_sub_mul (G d : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), G i * d i = ∑ i ∈ range m, (G i - G (i + 1)) * ∑ j ∈ range (i + 1), d j +
      G m * ∑ j ∈ range (m + 1), d j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun i ↦ (G i - G (i + 1)) * _) m,
      sum_range_succ d (m + 1)]
    ring

/-- **Abel summation, strict**: with total sum `0`, `G` antitone and the partial sums of `d`
nonnegative, `∑ₖ Gₖ dₖ > 0` as soon as `G` drops strictly, `Gᵢ₊₁ < Gᵢ`, at an index where the
partial sum `d₀ + ⋯ + dᵢ` is positive. -/
theorem sum_mul_pos_of_antitone_of_sum_eq_zero (n : ℕ) {G d : ℕ → ℝ}
    (hG : ∀ i j, i ≤ j → j < n → G j ≤ G i) (hd : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, d i)
    (htot : ∑ i ∈ range n, d i = 0)
    (hpos : ∃ i, i + 1 < n ∧ G (i + 1) < G i ∧ 0 < ∑ j ∈ range (i + 1), d j) :
    0 < ∑ i ∈ range n, G i * d i := by
  obtain ⟨i, hi, hGi, hDi⟩ := hpos
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_mul_eq_sum_sub_mul, htot, mul_zero, add_zero]
  refine sum_pos' (fun j hj ↦ ?_) ⟨i, Finset.mem_range.2 (by omega), mul_pos (sub_pos.2 hGi) hDi⟩
  rw [Finset.mem_range] at hj
  exact mul_nonneg (sub_nonneg.2 (hG j (j + 1) (by omega) (by omega))) (hd _ (by omega))

/-! ### Sorting and partial sums -/

variable {n : ℕ}

/-- `x` sorted increasingly. -/
noncomputable def sortInc (x : Fin n → ℝ) : Fin n → ℝ :=
  x ∘ Tuple.sort x

theorem monotone_sortInc (x : Fin n → ℝ) : Monotone (sortInc x) :=
  Tuple.monotone_sort x

/-- A vector as a sequence, `0` beyond `n`. -/
def toSeq (x : Fin n → ℝ) (k : ℕ) : ℝ :=
  if h : k < n then x ⟨k, h⟩ else 0

theorem toSeq_val (x : Fin n → ℝ) (i : Fin n) : toSeq x i = x i := by
  simp [toSeq, i.2]

theorem sum_range_toSeq (x : Fin n → ℝ) : ∑ i ∈ range n, toSeq x i = ∑ i, x i := by
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ toSeq_val x i

theorem sum_sortInc (x : Fin n → ℝ) : ∑ i, sortInc x i = ∑ i, x i :=
  Equiv.sum_comp (Tuple.sort x) x

/-- Two vectors with the same increasing rearrangement are permutations of each other. -/
theorem exists_comp_eq_of_sortInc_eq {x y : Fin n → ℝ} (h : sortInc x = sortInc y) :
    ∃ σ : Equiv.Perm (Fin n), x ∘ σ = y := by
  refine ⟨Tuple.sort x * (Tuple.sort y)⁻¹, funext fun i ↦ ?_⟩
  simpa [sortInc, Equiv.Perm.mul_apply] using congrFun h ((Tuple.sort y)⁻¹ i)

/-- For `t` increasing on `[0, n)` and `k ≤ n`, the mean of the first `k` terms is at most the
mean of all `n`: `n ∑_{i<k} tᵢ ≤ k ∑_{i<n} tᵢ`. -/
theorem card_mul_sum_range_le {t : ℕ → ℝ} {n k : ℕ} (ht : ∀ i j, i ≤ j → j < n → t i ≤ t j)
    (hk : k ≤ n) : n * ∑ i ∈ range k, t i ≤ k * ∑ i ∈ range n, t i := by
  have e : n * ∑ i ∈ range k, t i - k * ∑ i ∈ range n, t i =
      ∑ i ∈ range k, ∑ j ∈ range n, (t i - t j) := by
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
  have h0 : ∑ i ∈ range k, ∑ j ∈ range k, (t i - t j) = 0 := by
    simp only [sum_sub_distrib]
    rw [sum_comm (f := fun i j ↦ t j)]
    exact sub_self _
  have h1 : ∑ i ∈ range k, ∑ j ∈ Ico k n, (t i - t j) ≤ 0 :=
    sum_nonpos fun i hi ↦ sum_nonpos fun j hj ↦ by
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Ico] at hj
      exact sub_nonpos.2 (ht i j (by omega) hj.2)
  have e2 : ∑ i ∈ range k, ∑ j ∈ range n, (t i - t j) =
      ∑ i ∈ range k, ∑ j ∈ range k, (t i - t j) + ∑ i ∈ range k, ∑ j ∈ Ico k n, (t i - t j) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ (sum_range_add_sum_Ico _ hk).symm
  linarith

end Majorization

open Majorization

/-- **Majorization**: `x` is majorized by `y` (`x` is more mixed than `y`) if the totals agree and,
both sorted increasingly, the sum of the `k` smallest entries of `x` is at least that of `y`, for
every `k`. -/
def IsMajorizedBy {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∑ i, x i = ∑ i, y i ∧
    ∀ k ≤ n, ∑ i ∈ range k, toSeq (sortInc y) i ≤ ∑ i ∈ range k, toSeq (sortInc x) i

/-- **The Schur–Ostrowski criterion.** Let `F` be invariant under permutations of the entries on a
convex set `U` closed under permutations, with directional derivatives
`d/dt F(z + t v) = ∑ₐ ∇F(z)ₐ vₐ` at every point of `U`, whose gradient at every increasingly
sorted point of `U` is antitone in the index. If `x` is majorized by `y` (both in `U`), then
`F y ≤ F x`. -/
theorem le_of_isMajorizedBy {n : ℕ} {F : (Fin n → ℝ) → ℝ} {grad : (Fin n → ℝ) → Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hU : Convex ℝ U)
    (hperm : ∀ z ∈ U, ∀ σ : Equiv.Perm (Fin n), z ∘ σ ∈ U ∧ F (z ∘ σ) = F z)
    (hder : ∀ z ∈ U, ∀ v : Fin n → ℝ,
      HasDerivAt (fun t : ℝ ↦ F (z + t • v)) (∑ a, grad z a * v a) 0)
    (hgrad : ∀ z ∈ U, Monotone z → Antitone (grad z))
    {x y : Fin n → ℝ} (hx : x ∈ U) (hy : y ∈ U) (hxy : IsMajorizedBy x y) : F y ≤ F x := by
  obtain ⟨hxU, hFx⟩ := hperm x hx (Tuple.sort x)
  obtain ⟨hyU, hFy⟩ := hperm y hy (Tuple.sort y)
  set x' := sortInc x
  set y' := sortInc y
  rw [← hFx, ← hFy]
  set v := x' - y'
  set z : ℝ → Fin n → ℝ := fun t ↦ y' + t • v
  have hzU : ∀ t ∈ Icc (0 : ℝ) 1, z t ∈ U := fun t ht ↦ hU.add_smul_sub_mem hyU hxU ht
  have hzmono : ∀ t ∈ Icc (0 : ℝ) 1, Monotone (z t) := fun t ht i j hij ↦ by
    have h1 := monotone_sortInc x hij
    have h2 := monotone_sortInc y hij
    simp only [z, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith [ht.1, ht.2]
  have hg : ∀ t, z t ∈ U → HasDerivAt (fun s ↦ F (z s)) (∑ a, grad (z t) a * v a) t := by
    intro t ht
    have h := HasDerivAt.comp_sub_const t t (by simpa using hder (z t) ht v)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ ?_)
    simp only [z, add_assoc, ← add_smul, add_sub_cancel]
  have hmono : MonotoneOn (fun s ↦ F (z s)) (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t ht ↦ (hg t (hzU t ht)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      exact fun t ht ↦
        (hg t (hzU t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have htU := hzU t (Ioo_subset_Icc_self ht)
      rw [(hg t htU).deriv]
      have hG := hgrad (z t) htU (hzmono t (Ioo_subset_Icc_self ht))
      have key := sum_mul_nonneg_of_antitone_of_sum_eq_zero n (G := toSeq (grad (z t)))
        (d := toSeq v)
        (fun i j hij hj ↦ by
          simp only [toSeq, hj, lt_of_le_of_lt hij hj, ↓reduceDIte]
          exact hG (Fin.mk_le_mk.2 hij))
        (fun k hk ↦ by
          have h := hxy.2 k hk
          have e : ∑ i ∈ range k, toSeq v i =
              ∑ i ∈ range k, toSeq x' i - ∑ i ∈ range k, toSeq y' i := by
            rw [← sum_sub_distrib]
            refine sum_congr rfl fun i _ ↦ ?_
            simp only [toSeq, v, Pi.sub_apply]
            split_ifs <;> simp
          rw [e]
          linarith)
        (by
          rw [sum_range_toSeq]
          simp only [v, Pi.sub_apply, sum_sub_distrib, sum_sortInc, x', y', hxy.1, sub_self])
      have e : ∑ i ∈ range n, toSeq (grad (z t)) i * toSeq v i = ∑ a, grad (z t) a * v a := by
        rw [Finset.sum_range]
        exact sum_congr rfl fun i _ ↦ by rw [toSeq_val, toSeq_val]
      linarith
  have h01 := hmono ⟨le_refl (0 : ℝ), zero_le_one⟩ ⟨zero_le_one, le_refl (1 : ℝ)⟩ zero_le_one
  have e0 : z 0 = y' := by simp [z]
  have e1 : z 1 = x' := by simp [z, v]
  have h := h01
  simp only [e0, e1] at h
  exact h

/-- **The strict Schur–Ostrowski criterion.** Under the hypotheses of `le_of_isMajorizedBy`, if
moreover at every increasingly sorted point `z` of `U` the gradient is strictly smaller at a
strictly larger entry (`zₐ < z_b` implies `∇F(z)_b < ∇F(z)ₐ`), and the increasing rearrangements
of `x` and `y` differ, then `F y < F x`. Entries may tie along the segment between the sorted
vectors, where the gradient need not drop; the proof finds, at every point before the end, a gap
across which it does drop while the partial sum of the direction is positive. -/
theorem lt_of_isMajorizedBy {n : ℕ} {F : (Fin n → ℝ) → ℝ} {grad : (Fin n → ℝ) → Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hU : Convex ℝ U)
    (hperm : ∀ z ∈ U, ∀ σ : Equiv.Perm (Fin n), z ∘ σ ∈ U ∧ F (z ∘ σ) = F z)
    (hder : ∀ z ∈ U, ∀ v : Fin n → ℝ,
      HasDerivAt (fun t : ℝ ↦ F (z + t • v)) (∑ a, grad z a * v a) 0)
    (hgrad : ∀ z ∈ U, Monotone z → Antitone (grad z))
    (hgrad_lt : ∀ z ∈ U, Monotone z → ∀ a b, z a < z b → grad z b < grad z a)
    {x y : Fin n → ℝ} (hx : x ∈ U) (hy : y ∈ U) (hxy : IsMajorizedBy x y)
    (hne : sortInc x ≠ sortInc y) : F y < F x := by
  obtain ⟨hxU, hFx⟩ := hperm x hx (Tuple.sort x)
  obtain ⟨hyU, hFy⟩ := hperm y hy (Tuple.sort y)
  set x' := sortInc x
  set y' := sortInc y
  rw [← hFx, ← hFy]
  set v := x' - y'
  set z : ℝ → Fin n → ℝ := fun t ↦ y' + t • v
  have hzU : ∀ t ∈ Icc (0 : ℝ) 1, z t ∈ U := fun t ht ↦ hU.add_smul_sub_mem hyU hxU ht
  have hzmono : ∀ t ∈ Icc (0 : ℝ) 1, Monotone (z t) := fun t ht i j hij ↦ by
    have h1 := monotone_sortInc x hij
    have h2 := monotone_sortInc y hij
    simp only [z, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    nlinarith [ht.1, ht.2]
  have hg : ∀ t, z t ∈ U → HasDerivAt (fun s ↦ F (z s)) (∑ a, grad (z t) a * v a) t := by
    intro t ht
    have h := HasDerivAt.comp_sub_const t t (by simpa using hder (z t) ht v)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ ?_)
    simp only [z, add_assoc, ← add_smul, add_sub_cancel]
  -- the partial sums of `v`
  have hD : ∀ k ≤ n, 0 ≤ ∑ i ∈ range k, toSeq v i := fun k hk ↦ by
    have h := hxy.2 k hk
    have e : ∑ i ∈ range k, toSeq v i =
        ∑ i ∈ range k, toSeq x' i - ∑ i ∈ range k, toSeq y' i := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [toSeq, v, Pi.sub_apply]
      split_ifs <;> simp
    rw [e]
    linarith
  have hDn : ∑ i ∈ range n, toSeq v i = 0 := by
    rw [sum_range_toSeq]
    simp only [v, Pi.sub_apply, sum_sub_distrib, sum_sortInc, x', y', hxy.1, sub_self]
  have hseq : ∀ w : Fin n → ℝ, ∑ i ∈ range n, toSeq w i * toSeq v i = ∑ a, w a * v a := fun w ↦ by
    rw [Finset.sum_range]
    exact sum_congr rfl fun i _ ↦ by rw [toSeq_val, toSeq_val]
  -- `x' · v ≤ 0` and `v · v > 0`, so `z t · v < 0` for `t < 1`
  have hxv : ∑ a, x' a * v a ≤ 0 := by
    have h := sum_mul_nonneg_of_antitone_of_sum_eq_zero n (G := fun i ↦ -toSeq x' i)
      (d := toSeq v) (fun i j hij hj ↦ by
        simp only [toSeq, hj, lt_of_le_of_lt hij hj, ↓reduceDIte, neg_le_neg_iff]
        exact monotone_sortInc x (Fin.mk_le_mk.2 hij)) hD hDn
    simp only [neg_mul, sum_neg_distrib, neg_nonneg] at h
    rwa [hseq] at h
  have hvv : 0 < ∑ a, v a * v a := by
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra! h
      exact hne (funext fun a ↦ sub_eq_zero.1 (h a))
    exact sum_pos' (fun b _ ↦ mul_self_nonneg _) ⟨a, mem_univ _, mul_self_pos.2 ha⟩
  have hzv : ∀ t < 1, ∑ a, z t a * v a < 0 := fun t ht ↦ by
    have e : ∑ a, z t a * v a = ∑ a, x' a * v a - (1 - t) * ∑ a, v a * v a := by
      simp only [z, v, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sum,
        ← sum_sub_distrib]
      exact sum_congr rfl fun a _ ↦ by ring
    rw [e]
    nlinarith
  have hstrict : StrictMonoOn (fun s ↦ F (z s)) (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) ?_ ?_
    · exact fun t ht ↦ (hg t (hzU t ht)).continuousAt.continuousWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht' := Ioo_subset_Icc_self ht
      have htU := hzU t ht'
      rw [(hg t htU).deriv]
      have hG := hgrad (z t) htU (hzmono t ht')
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        rcases n with _ | m
        · exact absurd (funext fun i ↦ i.elim0) hne
        · exact ⟨m, rfl⟩
      -- a gap of `z t` where the partial sum of `v` is positive
      have hgap : ∃ i, i + 1 < m + 1 ∧ toSeq (z t) i < toSeq (z t) (i + 1) ∧
          0 < ∑ j ∈ range (i + 1), toSeq v j := by
        have e := sum_mul_eq_sum_sub_mul (toSeq (z t)) (toSeq v) m
        rw [hDn, mul_zero, add_zero, hseq] at e
        have hneg := hzv t ht.2
        rw [e] at hneg
        obtain ⟨i, hi, hfi⟩ := Finset.exists_lt_of_sum_lt (g := fun _ ↦ (0 : ℝ))
          (by simpa using hneg)
        rw [Finset.mem_range] at hi
        have hz : toSeq (z t) i ≤ toSeq (z t) (i + 1) := by
          simp only [toSeq, show i < m + 1 by omega, ↓reduceDIte,
            show i + 1 < m + 1 by omega]
          exact hzmono t ht' (Fin.mk_le_mk.2 (by omega))
        have hd := hD (i + 1) (by omega)
        refine ⟨i, by omega, lt_of_le_of_ne hz fun h ↦ ?_, lt_of_le_of_ne hd fun h ↦ ?_⟩
        · rw [h, sub_self, zero_mul] at hfi
          exact lt_irrefl _ hfi
        · rw [← h, mul_zero] at hfi
          exact lt_irrefl _ hfi
      obtain ⟨i, hi, hzi, hDi⟩ := hgap
      have key := sum_mul_pos_of_antitone_of_sum_eq_zero (m + 1) (G := toSeq (grad (z t)))
        (d := toSeq v)
        (fun i j hij hj ↦ by
          simp only [toSeq, hj, lt_of_le_of_lt hij hj, ↓reduceDIte]
          exact hG (Fin.mk_le_mk.2 hij)) hD hDn
        ⟨i, hi, by
          simp only [toSeq, hi, show i < m + 1 by omega, ↓reduceDIte] at hzi ⊢
          exact hgrad_lt (z t) htU (hzmono t ht') _ _ hzi, hDi⟩
      rwa [hseq] at key
  have h01 := hstrict ⟨le_refl (0 : ℝ), zero_le_one⟩ ⟨zero_le_one, le_refl (1 : ℝ)⟩ zero_lt_one
  have e0 : z 0 = y' := by simp [z]
  have e1 : z 1 = x' := by simp [z, v]
  simp only [e0, e1] at h01
  exact h01

/-- **The uniform vector is the most mixed**: `(c, …, c)` is majorized by every vector with the
same total `n c`. -/
theorem isMajorizedBy_const {n : ℕ} {c : ℝ} {y : Fin n → ℝ} (hy : ∑ i, y i = n * c) :
    IsMajorizedBy (fun _ ↦ c) y := by
  refine ⟨by simp [hy], fun k hk ↦ ?_⟩
  have hc : ∑ i ∈ range k, toSeq (sortInc fun _ : Fin n ↦ c) i = k * c := by
    rw [sum_congr rfl fun i hi ↦ show toSeq (sortInc fun _ : Fin n ↦ c) i = c by
      simp [toSeq, sortInc, show i < n by rw [Finset.mem_range] at hi; omega]]
    simp
  rw [hc]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  have h := card_mul_sum_range_le (t := toSeq (sortInc y)) (fun i j hij hj ↦ by
      simp only [toSeq, hj, lt_of_le_of_lt hij hj, ↓reduceDIte]
      exact monotone_sortInc y (Fin.mk_le_mk.2 hij)) hk
  rw [sum_range_toSeq, sum_sortInc, hy] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith
