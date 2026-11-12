/-
Copyright (c) 2026 Jeanne Boursier and Sylvia Serfaty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier, Sylvia Serfaty
-/
module

public import MultipoleBKT.Appendix.GeneralExpansionK.RouteOmitted.ModelIntegral

/-!
# Omitted-domain integration for Lemma A.7

See Lemma A.7 and (A.51).

The original quadratic minimum is normalized by `odd_family_normalized`.
The retained even mark, including both endpoint squares, is normalized by
`even_family_normalized`. `internal_boundary_envelope` multiplies both
alternatives by their actual common support and omitted density, treating
zero support first. `omittedEnvelope_bound` sums all selected original shapes
and original even marks before their configuration integrals. It keeps
`N/h²` and the radial logarithm until the `vectorWeight_gain` is applied.

## Uniformity and parameter order

All original-term integral theorems choose their coefficient before `X`,
for a fixed positive label count `k`. `internal_baseline_pointwise_uniform`
exposes the coefficient `partConst β Cv` before `X`. The tree, mark and
parity multiplicities are bounded using only `k`.

`screened_omitted_integral hχ hβ hM p₀ k hk1 hε₀` accepts every positive
`ε₀`. Its coefficient follows epsilon and precedes `X`, lambda and N.
It requires `0 < lam`, `lam ≤ ε₀` and `lam ≤ 1`. The last two bounds follow
from `lam ≤ min 1 ε₀` in the minus-model estimate. The radial extension
keeps `eps^((4-β)*k)` below four and `(1+log eps)^(2*k-1)` at or above four
in the coefficient when epsilon exceeds one. It uses the same moments and
absorbs logarithms only after position integration.

`screened_omitted_integral_small hχ hβ hM p₀ k hk1` and
`frozen_omitted_integral hχ hβ p₀ k hk1` choose the coefficient before
epsilon as well as `X`. They require `eps ≤ 1`. The frozen theorem accepts
`1 ≤ M` after lambda, so its coefficient is chosen in the scope of
`lemma_A8_plus` before that hypothesis is introduced.

## Integral estimates

Only the baseline term remains on the omitted domain in either comparison.
The frozen term has no dependence on `Z`.

* `screened_omitted_integral` bounds the omitted part in `lemma_A8_minus`.
  Its coefficient is chosen before the final constant and includes `ε₀^(-2)`.
  It takes `X hX hXne hV`, `lam hlam`, the bounds `lam ≤ ε₀` and `lam ≤ 1`,
  and the cluster data `Xs Es F hXs hEs' hF N`.
* `frozen_omitted_integral` bounds the omitted part in `lemma_A8_plus`.
  Its coefficient is chosen before epsilon. It takes `X hX hXne hV`,
  `ε₀ lam hlam hlε hε1 hM1`, `V Z`, and `Xs Es F hXs hEs' hF`.
  Here `hM1` follows from `hM3` and `1 ≤ 3^pBeta`. The bound contributes
  `C*ε₀^(-2)` to the epsilon-dependent coefficient and `C` to the
  epsilon-independent bad-point coefficient. The stronger area-only bound is
  `screened_omitted_integral_small`.
* `hHflip` and `hSflip` identify `omittedAverage` with the exact reversal
  average of `F₂`. With measurability and boundedness,
  `abs_integral_le_of_avg` transfers this bound to the absolute real integral.
* For individual parity subsets, `cluster_omitted_integral` applies when
  `eps ≤ 1`, and `cluster_omitted_integral_at` applies for fixed positive
  epsilon and `lam ≤ 1`. The corresponding `omitted_integral` and
  `omitted_integral_at` take near and far graph data. Their graph and parity
  hypotheses follow from `cluster_far_subset`, `source_cluster_graph` and
  `actual_source_odd`.
-/

public section
