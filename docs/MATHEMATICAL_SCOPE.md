# Mathematical scope and interpretation

## Population model

All entropy and disintegration statements concern a population random variable
`V` with density on a compact finite-dimensional parameter region. A finite
training set has finite support and therefore cannot literally carry the
continuum entropy exponent used by the theory.

For a finite or countable mask family, define

\[
X=F(V),\qquad Y=P_MX,\qquad Z=(M,Y).
\]

The relevant fiber is

\[
S_{m,z}=E\cap(P_mF)^{-1}(z).
\]

When mask dimensions differ, the observation variable is formally valued in
the countable disjoint union

\[
\mathsf Z=
\bigsqcup_{m\in\mathcal M}
\bigl(\{m\}\times\mathbb R^{q_m}\bigr),
\]

not in an unspecified common Euclidean space.

## Assumption levels

The project uses three distinct levels of hypotheses.

1. **Single-fiber regularity.** Constant rank is required on an open
   neighborhood of one compact fiber. This makes the ambient level set a
   `d-r` dimensional manifold and gives the compact fiber subset a local
   entropy upper exponent. It does not force an arbitrary intersection with
   `E` to have dimension exactly `d-r`. If the restricted differential
   `DF|ker(DH)` has constant rank `ell` on a relative neighborhood of the
   compact fiber in the regular level set, the image covering upper exponent
   can be sharpened to `ell`.
2. **Quantitative local tubes.** A smallest selected singular value, a Hessian
   bound, and a controlled neighborhood radius yield explicit finite-scale
   constants and a product over the selected leading directions. It contains
   the complete nonzero spectrum when the selected rank is the Jacobian rank;
   otherwise the unselected directions remain in the coarse factor.
3. **Whole-family transport.** Assumption Q requires full row rank on a compact
   observation tube, positive density regularity, convex observation paths,
   boundary submersion, and a formally defined bidirectional no-exit property.
   Ambient full row rank alone neither prevents trajectories from leaving a
   parameter set with boundary nor excludes tangential boundary intersections.

The boundary condition is

\[
DH(v)(T_v\partial\mathcal K)=\mathbb R^r,
\qquad
v\in\partial\mathcal K\cap H^{-1}(G).
\]

It makes the level sets neat manifolds with
`boundary(S_z) = S_z intersection boundary(K)`. Bidirectional no-exit means
that, for every ordered pair `z,z'` in the convex observation region and every
initial point in `S_z`, the minimum-norm horizontal-lift ODE has a unique
solution throughout `[0,1]`, remains in `K`, and also satisfies the reverse
ordered-pair requirement. A bootstrap in the manuscript first uses full rank
on `U_Q` to obtain `H(v(t)) = (1-t)z + tz'` up to a hypothetical first exit.
No-exit and continuity then place that exit point back in `K_G`, a
contradiction. Thus the complete trajectory lies in the common regular tube.
The pseudoinverse field is `C1` there, so standard ambient-flow parameter
dependence makes the derivatives of the time-one map well defined.

The `C2`-boundary assumption is not a cosmetic description of an arbitrary
polygon generator. A region cut out by several simultaneous angle, side,
convexity, and separation inequalities is generally a manifold with corners
or a stratified set. The whole-family transport theorems apply only on a
verified smooth full-dimensional compact subdomain with `C2` boundary that
satisfies boundary submersion and no-exit. A lower-dimensional stratum would
require a separate intrinsic theorem and reference measure. No transport
across changes of active constraint is proved.

The completed EIT study supports the first two levels locally. It does not
verify boundary submersion or bidirectional no-exit over the entire
rejection-defined polygon population.

## Conditional-law transport and the data map

The conditional parameter-law estimate controls density change along the
actual horizontal flow. In particular, a gradient bound on the coarea weight
is integrated along that admissible trajectory; it is not asserted to imply
ambient global Lipschitz continuity on a nonconvex or disconnected set.

For the data law `mu_z = F_# nu_z`, write

\[
M_F=\sup_{\mathcal U_Q}\|DF\|_{\mathrm{op}},
\qquad
D_F=\operatorname{diam}F(\mathcal K_G).
\]

The repaired bound is

\[
W_1(\mu_z,\mu_{z'})
\le
\frac{M_F}{s_0}\Delta
+D_F\tanh(C_0\Delta),
\qquad
\Delta=\|z-z'\|.
\]

The first term moves mass along horizontal trajectories and the second controls
the mass reweighting on the data image. This distinction is necessary: a zero
derivative on each of two disconnected components does not force `F` to take
the same constant value on both components.

## Metric dependence

Rank is invariant under invertible parameter reparameterization. Singular
values are not. Every stability interpretation therefore fixes both a
parameter norm and an observation norm. Under anisotropic Gaussian noise, the
appropriate observation geometry is determined by

\[
\widetilde J=\Gamma^{-1/2}J.
\]

## Upper bounds versus intrinsic equality

At the single-fiber level, the theory gives

\[
\dim\bigl(H^{-1}(z)\cap U\bigr)=d-r,
\qquad
\overline{\dim}_{\mathrm{cover}}F(S_z)\le d-r.
\]

Under the additional constant restricted-rank hypothesis,

\[
\ell=\operatorname{rank}\left(DF|_{\ker DH}\right),
\qquad
\overline{\dim}_{\mathrm{cover}}F(S_z)\le\ell.
\]

Because `H=PF`, `ker(DF)` is contained in `ker(DH)`. If `DF` and `DH` have
constant ambient ranks `s` and `r` on the relevant relative neighborhood,
rank--nullity gives

\[
\ell=s-r.
\]

For `ell = 0`, the complete-data map is locally constant on the stated
relative neighborhood `W` inside the regular level set, and compactness makes
`F(S_z)` finite; the parameter fiber itself may still be infinite. This
refinement is made on the ambient regular level set,
so it remains an upper bound for an arbitrary compact or cornered intersection
with `E`. It does not imply that the image is embedded or that its covering
dimension equals `ell`.

Under the stronger boundary-submersion hypotheses of Assumption Q, `S_z`
itself is a neat `d-r` dimensional manifold with boundary.

It does not assert equality in image space. The forward map may collapse
tangential directions, and the actual conditional probability may occupy a
smaller subset of the geometric image fiber.

## Novelty boundary

Classical ingredients are cited and used as tools: the constant-rank theorem,
coarea disintegration, pseudoinverse sensitivity, Fisher information,
whitening, and log-determinant design. The contribution claimed here is the
specific chain from masked inverse observations to conditional image entropy,
its quantitative full-spectrum noisy form, and its insertion into the entropy
step of the existing EIT conditional diffusion argument.

## External diffusion consequence

The random-mask entropy estimate is stated on an explicitly named Borel
full-law-measure good set and for `0 < epsilon <= 1`. At the single scale
required by Liang--Huang--Chen, arXiv version 2, Assumption 1, it supplies the
version-pinned intrinsic-dimension input to that paper's Theorem 2. The
certified positive exponent may be the default `2*n_v-r`, or `ell` when the
constant image-rank hypothesis is also verified. A zero exponent only gives a
finite-support conclusion here; it is not substituted into an external
theorem formulated for positive intrinsic dimension. The resulting DDPM
statement remains conditional on that theorem's unweighted average score-error
and remaining distributional assumptions.

Later versions of the external analysis use a different set of assumptions
and are not invoked in this release. Adapting the corollary to another version
requires a separate assumption-by-assumption verification and remains future
work.

This application is pointwise: it applies for almost every fixed regular
`(m,z)` for which a positive certified covering exponent is selected, and its
covering constants may depend on `(m,z)`. No uniform-in-`z`,
observation-averaged, or newly proved finite-sample diffusion rate is claimed.

## Statements deliberately excluded

- Direct total-variation continuity between measures supported on distinct
  fibers. Such measures are generally mutually singular.
- A Wasserstein-2 Lipschitz theorem from total variation alone.
- Positive uniform reach from curvature alone.
- Score regularity from density and gradient-density `L1` estimates alone.
- Global smoothness of moving discontinuous polygon inclusions as an
  `L-infinity` conductivity chart.
- Equality between numerical thresholded rank and exact differential rank.
- Whole-prior EIT boundary submersion or bidirectional no-exit from local
  numerical continuation alone.
- Applicability of the smooth-boundary transport theorem across corners or
  active-constraint changes in the full polygon admissibility region.
- A uniform conditional DDPM rate from pointwise fiber covering constants.
