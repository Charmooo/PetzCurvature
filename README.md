# PetzCurvature

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24460110.svg)](https://doi.org/10.5281/zenodo.24460110)

A Lean 4 + Mathlib proof of **Petz's conjecture** for the Kubo–Mori metric: on the faithful
density matrices of any size, the scalar curvature of the Bogoliubov–Kubo–Mori (BKM) metric
increases under mixing. If the eigenvalues of `ρ` are majorized by those of `ϱ` (`ρ` is more
mixed), then `S(ϱ) ≤ S(ρ)`. The theorem is in [`PetzCurvature/Main.lean`](PetzCurvature/Main.lean),
whose docstring lists the definitions the statement depends on.

The conjecture was first solved by Suvrit Sra (*A Proof of Petz's Conjecture on the Scalar
Curvature of the Kubo–Mori Metric*, preprint, October 2026), albeit without an accompanying Lean
certification. This library is a Lean formalization of a slightly different proof, along
Dittmann's route.

```lean
theorem PetzCurvature.scalarCurvature_bkmChart_le_of_isMajorizedBy
    {d : Type*} [Fintype d] [DecidableEq d] {ρ ϱ : Matrix d d ℂ}
    (hρ : ρ.PosDef) (hϱ : ϱ.PosDef) (hρtr : ρ.trace = 1) (hϱtr : ϱ.trace = 1)
    (hmix : IsMajorizedBy (hρ.1.eigenvalues ∘ (Fintype.equivFin d).symm)
      (hϱ.1.eigenvalues ∘ (Fintype.equivFin d).symm)) :
    scalarCurvature (bkmChart (tracelessHermitian d) ϱ) 0 ≤
      scalarCurvature (bkmChart (tracelessHermitian d) ρ) 0
```


## Which statement

This is the conjecture as Petz stated it, **Conjecture 6.3** of Petz 1994 (p. 791): "the scalar
curvature is monotone with respect to the 'more mixed' partial ordering of density matrices". It
is also Dittmann's (60), `ρ ≻ ϱ ⟹ S_ρ ≥ S_ϱ`, and Gibilisco–Isola's Conjecture 8.2 (the BKM
scalar curvature is Schur-increasing).

Also proved in `Main.lean`:

* `scalarCurvature_bkmChart_lt_of_isMajorizedBy`: the strict form. If moreover the spectra of `ρ`
  and `ϱ` differ (`hne : ∀ σ : Equiv.Perm d, hρ.1.eigenvalues ∘ σ ≠ hϱ.1.eigenvalues`), then
  `S(ϱ) < S(ρ)`.
* `scalarCurvature_bkmChart_traceState`: at the trace state `1/n`,
  `S = (n² − 1)(n² − 4)/8` (Petz's Theorem 6.2, Dittmann's Corollary 3).
* `scalarCurvature_bkmChart_le_traceState`: the trace state has the largest scalar curvature, the
  consequence Petz draws right after the conjecture.
* `antitoneOn_scalarCurvature_bkmChart_gibbsState`: Petz's condition (i). The scalar curvature
  of the Gibbs state `e^{-βH} / Tr e^{-βH}` decreases in the inverse temperature `β ≥ 0`, that is,
  it increases with the temperature (Petz 1994, pp. 791–792). As Petz says, this follows from the
  conjecture because heating mixes: the Gibbs distributions are ordered by majorization
  (`isMajorizedBy_gibbsDist`, `ForMathlib/Gibbs.lean`).

**The strict form** needs the proviso that the spectra differ. Petz's equivalent condition (ii)
and Andai's Conjecture 2.1 are written with `>` but with no such proviso, so as written they fail
at `ρ = ϱ`. Of Dittmann's four inequalities only (62) has to be strict for the strict form, and its
certificate gives that directly (its Taylor coefficients are not all zero).

**Cross-check against Petz's numbers.** [`scripts/petz1994_table.py`](scripts/petz1994_table.py)
evaluates the closed form that Lean proves equal to the scalar curvature
(`scalarCurvature_bkmChart_eq_hs`), with `hs` built from the integrals `bkmIntegral₂` and
`bkmIntegral₃` exactly as defined. It does this at the ten `3 × 3` states of Petz's numerical table
(Petz 1994, p. 791) and reproduces every printed digit, from `4.9999` at the trace state down to
`−459501` near a pure state. So the normalization of the metric and the sign convention of the
curvature agree with Petz's independent computation.

## The route

Petz conjectured the monotonicity in 1994 and proved it for qubits. Dittmann (1999) gave the scalar
curvature in closed form (his Theorem 2) and reduced the conjecture to four inequalities (62)–(65)
for one function `hs` of three variables (his Theorem 3), but did not prove them. This library
formalizes both theorems and proves all four inequalities.

1. **Curvature of a metric in a chart** (`Curvature/`). The Christoffel, Riemann, Ricci and scalar
   curvature maps of a field of bilinear forms on a normed space, how they change under a change of
   chart, and the curvature of a metric whose derivative is totally symmetric (a Hessian metric):
   `S = ¼ (|T|² − |τ|²)` in an orthonormal basis.
2. **The BKM metric** (`KuboMori/`). The BKM form `∫₀¹ Re tr(A R B R) ds`, `R = ((1 − s)ρ + s)⁻¹`,
   is smooth with a totally symmetric derivative. At a diagonal state its scalar curvature is a
   sum over triples of eigenvalues (completeness-kernel contractions, without writing down a
   basis), which is **Dittmann's Theorem 2**,
   `S = ∑_{[n]³} hs(lᵢ, lⱼ, lₖ) − ∑ᵢ hs(lᵢ, lᵢ, lᵢ) + (n² − 1)(n² − 2)/4`. It extends to every
   faithful state by unitary invariance. The BKM form is the usual resolvent integral
   `∫₀^∞ Re tr(A (ρ + t)⁻¹ B (ρ + t)⁻¹) dt` (`KuboMori/Resolvent.lean`).
3. **Mixing** (`Dittmann/Mixing.lean`). Under (62)–(65), the gradient of the eigenvalue sum is
   ordered opposite to the eigenvalues, and the Schur–Ostrowski criterion
   (`ForMathlib/Majorization.lean`) gives **Dittmann's Theorem 3**.
4. **The inequalities** (`Dittmann/Plane.lean`, `Space.lean`, `Certificates/`,
   `Inequalities.lean`). Off the diagonals, `hs` and its second derivatives are rational
   functions of `x, y, z, log x − log z, log y − log z`. The polynomial identities are checked
   by kernel computation (`Certificate/ListPoly.lean`). The numerators are `≤ 0` by Taylor
   certificates for exponential polynomials (`Certificate/ExpPolynomial.lean`): on the plane
   `x = y` for (62) and (63), and on six sectors of the `(log x, log y)` plane for (64) and (65).
   Concavity then gives the four inequalities.

## Layout

| Directory | Contents |
| --- | --- |
| `ForMathlib/` | General lemmas Mathlib lacks: majorization and Schur–Ostrowski, the majorization ordering of Gibbs distributions, differentiation under the integral over a compact interval, invertibility of bilinear forms. |
| `Certificate/` | Reflection for polynomial identities (`ListPoly`) and sign certificates for exponential polynomials (`ExpPolynomial`). |
| `Curvature/` | Local Riemannian geometry: curvature maps, pullback, Hessian metrics. |
| `KuboMori/` | The BKM form and kernel, the chart on density matrices, Dittmann's Theorem 2. |
| `Dittmann/` | Theorem 3 and the inequalities (62)–(65). |
| `Main.lean` | Petz's conjecture, the trace-state value and maximum, Gibbs states. |
| `scripts/` | `petz1994_table.py`: numerical cross-check against Petz 1994 (needs `mpmath`). |

## Building

Lean `v4.34.1`, Mathlib `v4.34.1`.

```bash
lake exe cache get
```

```bash
lake build
```

A cold build of the library takes about 6 minutes on an 18-core laptop. Most of it is the twelve
sector certificates, which `Certificates/LowerHalf.lean` and `Certificates/UpperHalf.lean` check in
parallel (about 5 minutes each, up to about 9 GB of memory each, so about 20 GB together).

## References

* D. Petz, *Geometry of canonical correlation on the state space of a quantum system*,
  J. Math. Phys. 35 (1994) 780–795.
* J. Dittmann, *On the curvature of monotone metrics and a conjecture concerning the Kubo–Mori
  metric*, Linear Algebra Appl. 315 (2000) 83–112, arXiv:quant-ph/9906009.
* H. Shima, *The Geometry of Hessian Structures*, World Scientific, 2007.
* S. Sra, *A Proof of Petz's Conjecture on the Scalar Curvature of the Kubo–Mori Metric*,
  preprint v1, 9 October 2026, https://suvrit.github.io/papers/kubo-metric/.

## Authors

Adam Bornemann and Claude (Anthropic).

## License

Apache 2.0, see `LICENSE`.
