# lean-operator-theory

Unitary power dilation, von Neumann's polynomial inequality, and
the Crouzeix--Palencia numerical-range bound for bounded operators
on complex Hilbert spaces, formalized in Lean 4 against Mathlib.
Prepared for submission to
[Palomar](https://palomar-registry.org).

## Main results

For a bounded operator on a complex Hilbert space:

- `exists_unitary_power_dilation`: every contraction has an
  inner-product-preserving embedding into a larger Hilbert space and a
  unitary whose powers compress back to the original operator's powers.
- `vonNeumann_inequality`: for every contraction and complex polynomial,
  the operator norm of the polynomial applied to the contraction is
  bounded by the supremum norm of the polynomial on the closed
  unit disk.
- `crouzeix_palencia`: the closure of the numerical range of every
  bounded operator is a (1 + √2)-polynomial spectral set.

## Scope

The numerical range encodes the "shadow" of an operator seen through
inner products. Crouzeix and Palencia proved that this shadow controls
the polynomial functional calculus with the Crouzeix--Palencia constant 1 + √2 —
any polynomial applied to the operator is bounded by that factor times
the polynomial's supremum on the numerical range. This connects
classical dilation theory (Sz.-Nagy, von Neumann) to modern
numerical-range spectral sets.

The dilation uses a bilateral repeated-interaction model (not the
classical Sz.-Nagy--Foiaș unilateral shift). The Crouzeix--Palencia
bound follows the Ransford--Schwenninger (2018) short proof — a
quartic-inequality argument — not the original 2017 paper. Both
results are independent capstones; the only shared dependency is a
spectral-mapping bound for normal operators. The selected boundary
records the polynomial specialization of the paper's stronger
spectral-set theorem. The audience is researchers in operator theory,
numerical linear algebra, and the formalization community working on
functional analysis in Lean/Mathlib.

No numerical-range, von Neumann inequality, or Crouzeix material
exists in Mathlib at the pinned revision (v4.33.0). Cross-prover
novelty has not been searched.

For a detailed proof route in plain mathematics, see
`BLUEPRINT.md`.

## Trust boundary

- `CrouzeixPalenciaChallenge.lean` (63 lines) imports only Mathlib.
  Every definition needed by the theorem statements is given
  explicitly — zero definition holes. Only the three advertised
  theorem proofs are omitted.
- `CrouzeixPalenciaSolution.lean` imports the completed proof
  development.
- `comparator-crouzeix-palencia.json` lists all three theorems and
  no definition holes.
- The proved declarations use only `propext`, `Quot.sound`, and
  `Classical.choice`.

## Proof architecture

```text
Halmos one-step dilation
          │
          ▼
Schäffer unitary power dilation ──► von Neumann inequality

numerical range ──► spectrum enclosure
          │
          ├── resolvent/Cauchy machinery
          ├── positive double-layer kernels
          └── smooth convex outer approximation
                              │
                              ▼
                    Crouzeix--Palencia
```

Principal source modules:

- `Operator/Dilation/Schaeffer.lean`;
- `Operator/Crouzeix/VonNeumann.lean`;
- `Operator/Crouzeix/SmoothSupportDomain.lean`; and
- supporting numerical-range and spectral-set modules under
  `Operator/NumericalRange/` and `Operator/SpectralSet/`.

## Build and verify

Lean and Mathlib 4.33.0 are pinned.

```bash
lake exe cache get
lake build
python3 scripts/check_boundary.py
```

For a local Comparator smoke test:

```bash
export COMPARATOR=/path/to/comparator
export LEAN4EXPORT=/path/to/lean4export
export FAKE_LANDRUN=/path/to/fake-landrun.sh  # macOS only
scripts/run_comparator.sh
```

On 2026-08-30, all three declarations passed Comparator with Lean's
default kernel. That run predates the 2026-08-31 namespace-bridge fix:
the file renames left the Challenge and the proof library declaring
same-named top-level copies of `numericalRange`, `polynomialSupNorm`,
and `IsKPolynomialSpectralSet`, which elaborated to non-matching
internals and broke Comparator. The Challenge now declares its
boundary inside the `PalomarCrouzeixPalencia` namespace and the
Solution redeclares it as a bridge, delegating each theorem to the
library via `_root_`. Re-run on 2026-08-31 at the fixed HEAD: all
three declarations pass again. A negative control multiplied the
right-hand side of von Neumann's inequality by two; Comparator
rejected exactly that theorem while continuing to match the other two
declarations. Palomar runs its own pinned Comparator, Landrun
sandbox, and NanoDa kernel.

## License

Apache-2.0.
