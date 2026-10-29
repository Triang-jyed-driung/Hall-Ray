# Hall ray formalization

Lean and Rocq formalizations of the **main Hall-ray theorem** in Cheung–Wang–Zhang, *Existence of a Hall ray in higher dimensional Lagrange spectra*, based on the supplied paper. Local paper sources and the archive are excluded from version control.

**The main theorem is proved**, without `sorry` or custom axioms:

- `HallRay.hall_ray N : HasHallRay N`
- `HallRay.main_theorem : MainTheorem` (Lean)
- `hall_ray : hall_ray_claim` in `rocq/HallRayTheorem.v` (Rocq)

For every norm `N` on the real plane, this gives a positive `ρ₀` such that every `0 < ρ < ρ₀` is the simultaneous approximation constant of some `x ∈ ℝ² \ ℚ²`. This is the paper's small-constant formulation of a Hall ray.

## Verify

```sh
./check
```

This builds both formalizations, runs `lean/ProofAudit.lean`, and runs
`rocq check` on all Rocq modules. Rocq's `Audit.v` also prints the assumptions
of the main theorem and key intermediate results.

### Prerequisites

- Lean via Elan, with the version pinned in `lean/lean-toolchain` (4.35.0).
- Mathlib dependencies pinned in `lean/lake-manifest.json`; Lake may download
  them on the first build. Existing dependencies live in `lean/.lake/`.
- Rocq and its standard library (tested with Rocq 9.3.0), GNU Make, and Python 3
  for the exact defect-certificate generator.

The verification script also supports this machine's `lean-4.35.0` toolchain
alias. Other installations use the pinned toolchain normally.

### Repository layout

```text
lean/
  HallRay/             Lean proof modules
  HallRay.lean         Complete library import
  ProofAudit.lean      Statement and axiom audit
  lakefile.toml        Lake project configuration
  lake-manifest.json   Pinned dependencies
  lean-toolchain       Pinned Lean version
rocq/
  *.v                  Rocq proof modules
  Audit.v              Statement and assumption audit
  Makefile             Build and kernel verification
  _CoqProject          Logical namespace configuration
PROOF_NOTES.md         Proof structure and implementation notes
check                  Verify both formalizations
```

### Logical assumptions

The Lean audit guards the final theorem's dependencies to exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The Rocq main theorem currently reports:

- `ClassicalDedekindReals.sig_not_dec`
- `ClassicalDedekindReals.sig_forall_dec`
- `RelationalChoice.relational_choice`
- `FunctionalExtensionality.functional_extensionality_dep`
- `ClassicalUniqueChoice.dependent_unique_choice`
- `Description.constructive_definite_description`
- `Classical_Prop.classic`

These describe the current implementations, not minimal axioms needed for the
mathematical theorem. No reduction to dependent choice or a weaker foundation
has been verified in this repository.

## Proof map

| Part | Main files |
| --- | --- |
| Arbitrary plane norms and full Dani correspondence | `PlaneNorm`, `NearestInteger`, `DaniBounds`, `DaniUpper`, `Dani` |
| Contracting branches, two-sided coding, marked and lattice returns | `Branches`, `Contraction`, `Coding`, `ReturnMap`, `Suspension`, `Lattices` |
| Fiber estimates and periodic words | `FiberEstimates`, `FiberProducts`, `PeriodicWords` |
| Infinite order, irrational rotations, nonorthogonal defect | `InfiniteOrder`, `Elliptic`, `DefectLimit`, `NonorthogonalDefect` |
| Periodic asymptotics, compact models, continuous maxima and degeneration | `PeriodicEstimates`, `LimitingMaxima`, `DepthDegeneration`, `PeriodicMaximaConvergence` |
| Summable concatenation and whole-flight shadowing | `StageConstruction`, `ConcatenationSequence`, `BlockShadowing`, `CodedHallRay` |
| Forgetting the past and the final theorem | `NearIdentityHeight`, `ForgettingPast`, `Main` |

The Lean files above are under `lean/HallRay/`. `lean/HallRay.lean` imports the complete Lean library. `PROOF_NOTES.md` explains some choices differing from the paper.

## Scope

This proves the main theorem for arbitrary plane norms, including nonsmooth norms. In Lean, spectra and systoles use extended nonnegative reals, preserving zero and infinity correctly. Shortest-vector attainment and marking invariance are proved.

The paper's additional uncountability assertion, embedded-torus statements, and ray theorem for every continuous proper function are **not** formalized here. The dynamical construction is specialized to inverse systole, which suffices for the main Hall-ray theorem.
