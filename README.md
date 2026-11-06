# Jacobian library

A Lean library for algebraic geometry with an admission-free solution to the
Jacobian challenge over arbitrary fields.

The library is organized by mathematical subject:

- `Jacobian/AlgebraicGeometry/Curve/`: smooth proper curves, genus and scalar extension.
- `Jacobian/AlgebraicGeometry/BaseChange/`: field extension and its comparisons.
- `Jacobian/AlgebraicGeometry/Modules/`: invertible sheaves, duals, tensor products and rigidification.
- `Jacobian/AlgebraicGeometry/Picard/`: Picard groups, relative sheaves and their degree parts.
- `Jacobian/AlgebraicGeometry/Cohomology/`: module-sheaf cohomology and scalar extension.
- `Jacobian/AlgebraicGeometry/Group/`: proper rigidity and pointed morphisms of group schemes.
- `Jacobian/AlgebraicGeometry/AbelianVariety/`: Albanese varieties and their universal property.
- `Jacobian/AlgebraicGeometry/Hilbert/`: effective divisors, ordered divisors and Abel maps.
- `Jacobian/AlgebraicGeometry/Descent/`: effective descent of schemes and morphisms.
- `Jacobian/AlgebraicGeometry/ProjectiveLine/`: the projective line over a field.

`Challenge.lean` is the unchanged original statement with its intentional
placeholders. It is independent of `Solution.lean` and the library.

`Solution.lean` implements all the original constructions and conclusions without
importing `Challenge.lean`: cohomological genus, a degree-zero Picard Jacobian and
its group structure, smoothness and dimension, properness and geometric
irreducibility, the normalized Abel–Jacobi map and its universal property among
all scheme morphisms, contravariant functoriality and curve-isomorphism
compatibility, and scalar-extension comparisons with identity and tower
coherence. The construction uses one Picard representative throughout.

The reusable Albanese results live in `Curve/Albanese.lean` and
`AbelianVariety/Albanese/UniversalProperty.lean`. Their factorization theorem
constructs the required divisor charts and field-fibre constancy; these are not
extra hypotheses imposed on the original curve.

```sh
lake build Jacobian Solution
lake build Challenge
```

The project uses **Lean 4.35.0-rc3**, with the toolchain and Mathlib dependency
pinned in `lean-toolchain` and `lakefile.toml`. The statement target is independent
of the library and solution. Build logs, source inventories, and development
notes are kept outside this package.

## Authors

- Axel Delaval
- Jie Xu
- Shitan Xu

Parts of the library are adapted from Weil's conjectures project; see
[NOTICE](NOTICE).

## License

This repository is licensed under the [Apache License, Version 2.0](LICENSE).
