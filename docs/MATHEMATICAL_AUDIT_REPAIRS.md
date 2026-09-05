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
+D_F\tanh(C_0\Delta),
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

## Regular-tube bootstrap and ambient flow

**Issue.** No-exit states that a horizontal trajectory remains in
\(\mathcal K\), whereas the full-row-rank identity
\(DH\,DH^\dagger=I\) is assumed only on a neighborhood of
\(\mathcal K_G=\mathcal K\cap H^{-1}(G)\). Using that identity along the whole
trajectory without an intermediate argument would be circular.

**Correction.** Lemma `lem:regular-tube-bootstrap` argues up to a hypothetical
first exit from \(\mathcal U_Q\). Before that exit,
\(H(v(t))=(1-t)z+tz'\in G\); continuity and no-exit would therefore place the
first exit point back in \(\mathcal K_G\subset\mathcal U_Q\), a contradiction.
The trajectory consequently stays in the common regular tube. The lemma also
uses the `C1` pseudoinverse field and compact continuation to supply an ambient
`C1` local flow through time one, making the derivative estimates for the
time-one map unambiguous.

**Status.** Proved under Assumption Q; existence on the full interval remains
part of the explicit no-exit hypothesis rather than a consequence of rank.

## Polygon admissibility corners

**Issue.** A polygon parameter region defined by several simultaneous
admissibility inequalities is generally a manifold with corners or a
stratified set, not automatically a compact manifold with `C2` boundary.

**Correction.** The manuscript now states that Assumption Q applies only on a
verified smooth full-dimensional compact subdomain with `C2` boundary,
boundary submersion, and no-exit. A lower-dimensional stratum would require a
separate intrinsic formulation and reference measure. The manuscript does not
identify positive numerical margins with a proof that the complete
rejection-defined polygon prior has `C2` boundary, and it does not transport
across changes of active constraint.

**Status.** The abstract smooth-domain theorem is proved. A corners or
stratified extension for the full polygon prior remains outside the claim set.

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

The proof now describes \((U_r,\Sigma_r,V_r)\) as the leading rank-\(r\)
truncated singular block. If the base Jacobian has rank greater than \(r\),
the unselected nonzero directions are deliberately absorbed into the coarse
\((d-r)\)-dimensional factor; only when \(r=\operatorname{rank}J_0\) does the
product contain the complete nonzero spectrum.

## Density distortion along horizontal trajectories

**Issue.** A bound on \(\|\nabla\log w\|\) had been described as global
Euclidean Lipschitz continuity on a potentially nonconvex set.

**Correction.** The proof of Theorem `thm:measure-transport` integrates
\(\nabla\log w\) along the horizontal trajectory, which remains in the
regular region by no-exit. This is the only pathwise comparison required.

**Status.** The Radon--Nikodym, transported total-variation, and
Wasserstein-1 estimates are proved under Assumption Q.

## Uniform total-variation sharpening

**Issue.** The earlier estimate
\(\operatorname{TV}\le\tfrac12(e^{2C_0\Delta}-1)\) was valid but could exceed
one and discarded the normalization of the Radon--Nikodym density.

**Correction.** If
\(f=d\nu_{z'}/d\widetilde\nu_{z'}\), then
\(e^{-a}\le f\le e^a\), \(\int f\,d\widetilde\nu_{z'}=1\), and
\(a=2C_0\Delta\). The elementary inequality

\[
\frac{|f-1|}{f+1}\le\frac{e^a-1}{e^a+1}=\tanh(a/2)
\]

gives

\[
\operatorname{TV}(\nu_{z'},\widetilde\nu_{z'})
\le\tanh(C_0\Delta).
\]

The parameter-law and complete-data-law bounds are correspondingly sharpened
to

\[
W_p(\nu_z,\nu_{z'})
\le \frac{\Delta}{s_0}
+D_{\mathcal K}\tanh(C_0\Delta)^{1/p}
\]

and

\[
W_1(\mu_z,\mu_{z'})
\le \frac{M_F}{s_0}\Delta+D_F\tanh(C_0\Delta).
\]

**Status.** Proved from the normalized density-ratio bounds; the TV term is
now uniformly at most one.

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

## Image-rank-refined entropy

**Issue.** The ambient fiber dimension \(d-r\) can overstate the complexity of
the complete-data image when \(F\) collapses directions tangent to the
observation fiber.

**Correction.** Corollary `cor:image-rank-entropy` assumes that

\[
\operatorname{rank}\left(DF(v)|_{\ker DH(v)}\right)=\ell
\]

on a relatively open neighborhood of the compact fiber inside the regular
level set. The constant-rank theorem for the restricted manifold map and a
finite-chart argument give covering upper exponent \(\ell\). If \(\ell=0\),
the image is finite even though the parameter fiber need not be. Since
\(H=PF\), one has \(\ker DF\subseteq\ker DH\); when the ambient ranks are
constant, rank--nullity gives

\[
\ell=\operatorname{rank}DF-\operatorname{rank}DH.
\]

The random-mask corollary now uses an explicitly named Borel full-measure good
set and permits \(\ell(m,z)\) in place of \(2n_v-r(m,z)\) only when this
additional constant-rank hypothesis is certified. The pointwise DDPM
corollary accepts either positive certified exponent. A zero exponent is kept
as a finite-support statement and is not inserted into an external theorem
formulated for positive intrinsic dimension.

**Status.** Proved as an image-space covering upper bound. Constant restricted
rank alone gives neither global injectivity nor an embedded image nor a
matching entropy lower bound. Numerical ranks do not certify the hypothesis.

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
