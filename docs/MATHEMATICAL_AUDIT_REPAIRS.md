# Mathematical Revision Notes

This document records substantive revisions made during theorem-level review.
Each entry identifies the mathematical issue, the reason a correction was
needed, the adopted formulation, and the status of the resulting statement.
The definitive statements and proofs are those in the manuscript.

## Conditional complete-data-law stability

**Issue.** An earlier pushforward estimate used an upper bound on
\(\|DF\|\) as if it were a global Lipschitz constant on a parameter region that
could be nonconvex or disconnected.

**Reason.** A derivative bound controls changes along admissible paths, but it
does not compare values on different connected components. A map may have
zero derivative on each of two components and take different constants on the
two components.

**Correction.** Corollary `cor:data-law` separates horizontal displacement
from conditional-mass reweighting. With \(\Delta=\|z-z'\|\), it uses

\[
W_1(\mu_z,\mu_{z'})
\leq \frac{M_F}{s_0}\Delta
+\frac{D_F}{2}\bigl(e^{2C_0\Delta}-1\bigr),
\]

where \(M_F\) controls \(DF\) along horizontal trajectories and
\(D_F=\operatorname{diam}F(\mathcal K_G)\) controls reallocated mass in data
space.

**Status.** Proved under Assumption Q.

## Fibers at the parameter-space boundary

**Issue.** Full row rank of \(DH\) in the ambient space does not by itself
ensure that \(\mathcal K\cap H^{-1}(z)\) is a manifold with boundary.

**Reason.** Tangency between a level set and \(\partial\mathcal K\) can produce
non-neat intersections, including isolated boundary points attached to a
higher-dimensional fiber.

**Correction.** Assumption Q now requires

\[
DH(v)(T_v\partial\mathcal K)=\mathbb R^r
\]

on the relevant boundary. The regular-level-set theorem with boundary then
gives neat fibers with
\(\partial S_z=S_z\cap\partial\mathcal K\).

**Status.** The abstract transport theorems are proved with this condition.
Its global validity for the full EIT polygon family remains open.

## Bidirectional no-exit

**Issue.** An informal no-exit condition did not specify the existence
interval, uniqueness, state constraint, or reverse transport.

**Correction.** Definition `def:no-exit` requires, for every ordered pair of
observations in the convex regular region and every initial point on the first
fiber, a unique horizontal-flow solution on \([0,1]\) that remains in the
parameter region. The same requirement applies to the reverse ordered pair.

**Status.** The fiber and conditional-measure transport results are proved
under this explicit hypothesis. Whole-prior EIT verification is not claimed.

## Quantitative nonlinear spectral tube

**Issue.** A generic appeal to the implicit-function theorem did not provide
the domain, image radius, or constants required by a quantitative covering
argument.

**Correction.** Lemma `lem:quantitative-graph` supplies an explicit contraction
in singular coordinates. Under the theorem's radius and Hessian conditions it
constructs the exact-fiber graph \(a=g(b)\), bounds \(g\) and \(Dg\), and shows
that the noisy normal displacement lies in an ellipsoid with semiaxes
proportional to \(\delta/\sigma_i\). Theorem `thm:nonlinear-tube` consequently
obtains

\[
\mathcal N_\varepsilon(F(Q_{v_0,\delta}))
\leq
\left(1+\frac{C_dL_FR}{\varepsilon}\right)^{d-r}
\prod_{i=1}^r
\left(1+\frac{C_dL_F\delta}{\sigma_i\varepsilon}\right).
\]

**Status.** Proved under the stated local assumptions. The result is a
covering upper bound and does not assert constant rank outside the controlled
neighborhood.

## Density distortion along horizontal trajectories

**Issue.** A bound on \(\|\nabla\log w\|\) had been described as global
Euclidean Lipschitz continuity on a potentially nonconvex set.

**Correction.** The proof of Theorem `thm:measure-transport` integrates
\(\nabla\log w\) along the horizontal trajectory, which remains in the
regular region by no-exit. This is the only pathwise comparison required.

**Status.** The Radon--Nikodym, transported total-variation, and
Wasserstein-1 estimates are proved under Assumption Q.

## Derivative comparison for moving image manifolds

**Issue.** A chord-based Taylor argument did not ensure that the straight
segment between two transported points remained in the derivative-control
region.

**Correction.** The proof of Theorem `thm:moving-manifold` uses

\[
DF(v(1))-DF(v(0))
=\int_0^1 D^2F(v(t))[\dot v(t)]\,dt
\]

along the admissible horizontal flow.

**Status.** Proved with intrinsic tangent noncollapse and fiberwise
injectivity. No positive-reach conclusion is drawn from curvature alone.

## Scale range in conditional entropy

**Issue.** An unrestricted expression of the form
\(C+k\log(1/\varepsilon)\) cannot hold for arbitrarily large \(\varepsilon\),
because its right-hand side eventually becomes negative.

**Correction.** Corollary `cor:random-entropy` is stated for
\(0<\varepsilon\leq1\). Compactness and monotonicity absorb intermediate
scales into the observation-dependent constant.

**Status.** Proved on the stated scale range.

## Version-pinned diffusion consequence

**Issue.** The covering and score assumptions differ between versions of the
external diffusion analysis.

**Correction.** Corollary `cor:ddpm` cites Liang--Huang--Chen,
arXiv:2501.12982v2, Assumptions 1--3 and Theorem 2. It evaluates the fiber
cover at the single scale used by that version and retains the external
score-error and distributional hypotheses.

**Status.** This is an external, pointwise conditional corollary. It is not a
uniform in-observation result and is not counted as an independently proved
diffusion theorem.

## Random-mask observation space

**Issue.** Masks with different numbers of retained coordinates do not share
a single natural Euclidean observation space.

**Correction.** The observation is defined on the standard-Borel countable
disjoint union

\[
\bigsqcup_{m\in\mathcal M}
\bigl(\{m\}\times\mathbb R^{q_m}\bigr).
\]

The support result is formulated using regular conditional distributions on
this space. The random-mask extension of conditional-measure transport also
requires the mask-conditional prior to satisfy the density assumptions.

**Status.** Proved in the stated measure-theoretic setting.

## Intrinsic tangent noncollapse

**Issue.** A notation based on an orthonormal frame for \(\ker DH\) could be
read as assuming that the kernel bundle admits a global smooth frame.

**Correction.** The hypothesis is written intrinsically as

\[
\inf_v\inf_{\substack{u\in\ker DH(v)\\ \|u\|=1}}
\|DF(v)u\|>0.
\]

Local frames are introduced only within local arguments.

**Status.** No global bundle-triviality assumption is used.

## Exact dimension versus covering upper bound

**Issue.** The dimension of the ambient regular level set and the covering
dimension of an arbitrary compact intersection must be distinguished.

**Correction.** Theorem `thm:fiber-entropy` states that the ambient regular
level set has dimension \(d-r\), while the compact fiber subset and its image
have covering upper exponent at most \(d-r\).

**Status.** Proved. Equality for the image fiber is not claimed.

## Regression checks

The test suite includes examples designed to detect the corresponding
statement errors:

- disconnected components for which \(DF=0\) does not imply a zero global
  Lipschitz constant;
- a boundary-tangent level set showing that ambient submersion alone does not
  imply neatness;
- the inverse-singular-value axes of a linear tube; and
- the observation-path identity for a nonlinear pseudoinverse flow.

These tests check algebra and implementations. They do not replace analytic
proof or verify the global EIT assumptions.

## Remaining mathematical scope

No known unresolved proof is included in the confirmed in-repository theorem set.
The following questions remain outside that set: global EIT boundary
transversality and no-exit, positive uniform reach, conditional-score
regularity, uniform or observation-averaged diffusion convergence, noisy
posterior regularity, finite-sample conditional estimation, and continuum FEM
convergence. They are described in [Future work](FUTURE_WORK.md).
