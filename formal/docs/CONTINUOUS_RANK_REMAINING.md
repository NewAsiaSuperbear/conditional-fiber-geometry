# Continuous rank remaining work

## Contract

The intended theorem is for a genuine probability measure `ν` on `ι → α`,
with finite nonempty `ι`, a linear order on `α`, permutation invariance of
`ν`, and `ν`-almost-everywhere injective coordinate vectors.  Its conclusion
is an equality of measures on the finite type `Fin (Fintype.card ι)`:

```lean
ν.map (fun x => coordinateRank x truth) =
  (PMF.uniformOfFintype (Fin (Fintype.card ι))).toMeasure
```

The source law remains a `Measure`; no continuous law is converted to a PMF.
Only the finite-valued rank pushforward may be represented by `toPMF`.

## Implemented and compiled

`CFG/Statistics/ContinuousRank.lean` contains and compiles:

* `ExchangeableMeasure` and `NoTiesAE` for genuine measures;
* `exchangeableMeasure_map_coordinateRank_eq`, showing that exchangeability
  makes all coordinate rank pushforwards equal, under explicit measurability
  hypotheses for the rank and coordinate permutation;
* `iidPi_exchangeableMeasure`, reusing the product-measure permutation theorem;
* `iidPi_noTiesAE`, reusing the atomless iid no-ties theorem.
* `measurable_rankNat_of_measurableSet_lt` and
  `measurable_coordinateRank_of_measurableSet_lt`, using the measurable set
  of strict comparisons and a finite sum of measurable indicator functions;
* `coordinateRank_bijective_of_injective` and
  `ae_coordinateRank_surjective`, establishing the a.e. finite rank
  permutation needed by the counting argument.
* `ae_rank_indicator_sum_eq_one` and `rank_event_mass_sum_eq_one`, proving
  the finite indicator sum by `lintegral_finsetSum` for a genuine measure;
* `continuousRank_event_mass_eq_inv_card` and `continuousRank_uniform`, the
  full exchangeable, a.e.-tie-free uniform rank theorem;
* `iidPi_continuousRank_uniform`, an iid specialization with explicit
  measurable strict-comparison and permutation hypotheses discharged.
* `iidPi_real_continuousRank_uniform`, instantiating strict-comparison
  measurability from `(isOpen_lt continuous_fst continuous_snd).measurableSet`.

Validation command and result:

```text
cd formal
lake build CFG.Statistics.ContinuousRank
-- exit code 0; warningAsError is enabled in lakefile.lean
```

## Completed chain and remaining applicability boundary

1. The general uniform-rank theorem is complete.  It keeps the source law as
   a genuine `Measure`; only the finite rank pushforward is compared with
   `PMF.uniformOfFintype.toMeasure`.

2. The rank measurability bridge is proved from an explicit measurable
   strict-comparison set, and the real-valued iid corollary instantiates it
   from the Euclidean order topology.

3. The extrema interval event is now connected to interior rank, including
   its pointwise equivalence under no ties. The resulting probability chain is
   implemented in `CFG/Statistics/IntervalRankEvent.lean`, including the
   real iid probability theorem and the `n = 16` corollary.

No unfinished theorem, `sorry`, `admit`, axiom, or PMF assumption for the
continuous source law was added to the production import graph.

Theorem applicability still requires the true iid atomless law. Approximate
conditional samplers, correlated chains, rounded ties and arbitrary credible
intervals are not certified by these results.
