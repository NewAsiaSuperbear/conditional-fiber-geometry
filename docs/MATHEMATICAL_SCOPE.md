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
   `E` to have dimension exactly `d-r`.
2. **Quantitative local tubes.** A smallest selected singular value, a Hessian
   bound, and a controlled neighborhood radius yield explicit finite-scale
   constants and the full spectral product.
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
ordered-pair requirement.

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
+\frac{D_F}{2}\bigl(e^{2C_0\Delta}-1\bigr),
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

The random-mask entropy estimate is stated for `0 < epsilon <= 1`. At the
single scale required by Liang--Huang--Chen, arXiv version 2, Assumption 1, it
supplies the version-pinned intrinsic-dimension input to that paper's
Theorem 2. The resulting DDPM statement is conditional on that theorem's
unweighted average score-error and remaining distributional assumptions.

Later versions of the external analysis use a different set of assumptions
and are not invoked in this release. Adapting the corollary to another version
requires a separate assumption-by-assumption verification and remains future
work.

This application is pointwise: it applies for almost every fixed regular
`(m,z)`, and its covering constants may depend on `(m,z)`. No uniform-in-`z`,
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
- A uniform conditional DDPM rate from pointwise fiber covering constants.
