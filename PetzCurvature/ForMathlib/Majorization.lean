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

## Main definitions

* `Majorization.sortInc x`: `x` sorted increasingly.
* `Majorization.toSeq x`: `x` as a sequence, `0` beyond `n`.
* `IsMajorizedBy x y`: `x` is majorized by `y`.

## Main statements

* `Majorization.sum_mul_nonneg_of_antitone`: Abel summation, `0 ≤ ∑ Gₖ dₖ` for `G` antitone and
  nonnegative and partial sums of `d` nonnegative.
* `le_of_isMajorizedBy`: the Schur–Ostrowski criterion.
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
