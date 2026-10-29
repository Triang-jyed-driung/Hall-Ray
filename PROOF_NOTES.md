# Proof notes

## Final status

`HallRay.main_theorem : HallRay.MainTheorem` is proved in `lean/HallRay/Main.lean`.
`./check` builds both formalizations, verifies the independently expanded Lean statement in `lean/ProofAudit.lean`, and runs the Rocq assumption audit and kernel check.
In the Lean library there are no `sorry`, `admit`, or custom axioms. The final Lean proof depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The conclusion is the paper's main assertion: for every plane norm, every sufficiently small positive simultaneous approximation constant is attained at a vector outside ℚ². The extra uncountability, Lie-torus embedding, and general-proper-function assertions are outside this formalization's scope.

The Rocq entry point is `rocq/HallRayTheorem.v`; its assumptions are printed
by `rocq/Audit.v` and summarized in `README.md`. The module names below refer
to the Lean implementation under `lean/HallRay/`.

## Main dependency chain

1. `Dani.lean` proves the complete Dani correspondence for arbitrary plane norms, rational and irrational vectors. Nearest integer points and shortest lattice vectors exist; no smoothness or strict convexity is assumed.
2. Explicit branches contract both coding coordinates by 1/900. Coding is constructed by Cauchy limits, not assumed. The normalized marked return, determinant-one integral marking, and lattice factor identities are exact.
3. `FiberProducts.lean` proves the relative finite-word product estimate. Its sharper bound is `(1/10)*(1/900)^N`, implying the paper's `600^-N` estimate.
4. Periodic fibers have infinite order. Elliptic fibers therefore have irrational rotation angles. The defect limit exists, has determinant one, and is not a rotation in the constant-rotation coordinates.
5. Compact periodic representatives have finite attained height maxima. The beginning/end/bulk decomposition gives convergence of these maxima, including when the initial fiber varies. The limiting maximum is continuous and diverges at a nontrivial parabolic endpoint.
6. `StageConstruction.lean` performs the summable induction. Its finite stages retain a geometric fiber reserve. `ConcatenationSequence.lean` constructs the actual infinite word and proves its prefix and overlap agreements.
7. `BlockShadowing.lean` compares every flight of the final word with the corresponding periodic block. Each late block has an upper height bound and a near-maximum witness. `CodedHallRay.lean` converts these into an exact real-time orbit limsup.
8. `NearIdentityHeight.lean` proves that left multipliers tending to the identity preserve height limsups. `ForgettingPast.lean` factors the stable chart coordinate into such a multiplier and removes a fixed time translation.
9. `Main.lean` obtains the dynamical Hall ray and applies the unconditional Dani correspondence.

## Differences from the paper

### Elementary infinite-order obstruction

`MonodromyObstruction.lean` replaces the Galois S₃ argument by an integer-cubic calculation. An integer cubic with determinant one and roots `A,r,r`, where `0<r<1`, would have a rational repeated root. Integrality then forces an integer in `(0,1)`, a contradiction. `InfiniteOrder.lean` connects this to every positive-time periodic word.

### Qualitative conjugator bounds

`Elliptic.lean` uses a GL₂ conjugator, without normalizing its determinant to one. Only conjugations matter. Compactness supplies common bounds; the paper's particular numerical conjugator bound is unnecessary.

### Exact nonorthogonality certificate

`DefectAlgebra.lean` and `NonorthogonalDefect.lean` use exact polynomial identities rather than decimal interval arithmetic. For `N_s(u)=fiberNumerator s u`, `u1=phi b u`, `u2=phi a u1`, the finite numerator product is

```
N_a(u2) * N_a(u1) * N_b(u)
 = [[99*y+1009, -99*x-81], [20*y+101, 1011-20*x]].
```

The commutator's `(1,0)` numerator at the constant fixed point reduces to

```
2*(101*alpha^4 - 1010*alpha^2 + 200*alpha - 10)/alpha^4 > 200.
```

A positive denominator bound and the quantitative defect-limit error show the limiting commutator remains nonzero. This implies strict trace amplitude greater than four and supplies elliptic/parabolic phases.

### Compact representatives instead of a quotient-space API

The proof works with marked-frame representatives and proves that systole is invariant under equal represented lattices. It does not construct the full Lie-group quotient or embedded tori. The limiting skeleton is a compact closure of beginning/end data; bulk circles arise as accumulation points. This suffices for maxima convergence and concatenation.

### Degeneration without singular-value decomposition

The normalized centered matrix `J_v` has square `-I` and norm tending to infinity at the parabolic endpoint. An approximate operator-norm maximizer produces a strongly contracted unit vector. Rotations place any fixed bulk vector in this direction. A fixed sufficiently large flow time then makes the first chart column arbitrarily short, uniformly over bounded initial fibers.

### Forgetting the past without properness

Near-identity left multiplication changes every vector length by uniform multiplicative factors tending to one. The inverse-systole limsup is consequently unchanged, including at zero or infinity. This avoids using the general proper-function version of the paper's argument.

## Lean implementation notes

- Matrix estimates use `open scoped Matrix.Norms.L2Operator`.
- Explicit inner/outer functions in `Continuous.comp` and `Tendsto.comp` avoid costly elaboration of nested products involving symbolic words and subtypes.
- `Function.comp_def` and explicit natural-number cast simplifications are often needed with Lean 4.35's module transparency.
- `filter_upwards` handles eventual statements; frequently statements use `Frequently.mono` and subsequence extraction.
