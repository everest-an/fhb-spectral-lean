# FHB · the spectral core of the Fuxi Hypercube Benchmark

The hypercube walk underlying [`AwareLiquid/The-Fuxi-Hypercube-Math`](https://github.com/AwareLiquid/The-Fuxi-Hypercube-Math),
formalised in Lean 4.

## What this proves

Vertices are `(Z/2)^n` — for `n = 6` these are the 64 Fuxi "Earlier Heaven"
hexagrams.  The walk Hamiltonian is the hypercube adjacency

```lean
H ψ x = Σ_j ψ (flip_j x)
```

and it is diagonalised by the characters

```lean
χ_S x = ∏_{j ∈ S} (if x_j = 0 then 1 else -1) ,   S ⊆ Fin n .
```

```lean
theorem H_chi {n : ℕ} (S : Finset (Fin n)) (x : V n) :
    H (chi S) x = (n - 2 * S.card) * chi S x
```

The eigenvalues are therefore `n - 2·|S|`, with multiplicity `C(n, |S|)`.  Those
eigenvalues are exactly what makes the continuous-time walk on `Q_n` mix to the
uniform distribution *exactly* at `t = π/4`, and return exactly to its initial
state at `t = π` — Moore & Russell, [*Quantum Walks on the Hypercube*](https://arxiv.org/abs/quant-ph/0104137),
Theorem 2; FHB Theorem 3.

Supporting lemmas: `flip_apply_self`, `flip_apply_of_ne`, `factor_flip`
(flipping coordinate `j` negates that factor of `χ_S`), `chi_flip`
(`χ_S ∘ flip_j = (if j ∈ S then -1 else 1) · χ_S`), and `sum_ite_mem`
(`Σ_j (if j ∈ S then -1 else 1) = n - 2·|S|`).

## Trust level

`#print axioms FHBSpectral.H_chi` reports

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no custom axioms, no `native_decide`.

## Reproduce

```bash
lake exe cache get
lake build +FhbSpectral
lake env lean FhbSpectral.lean
```

Toolchain: `leanprover/lean4:v4.35.0-rc2`.  Mathlib revision pinned in
`lake-manifest.json`.

Axiom audit:

```bash
printf 'import FhbSpectral\nset_option pp.all true\n#print axioms FHBSpectral.H_chi\n' > Audit.lean
lake env lean Audit.lean
```

## Relation to the other FHB modules

| Module | Content |
|---|---|
| `fhb-hypercube` | `Q_n` model, commuting flips, amplitude of `|0…0⟩`, uniform mixing at `t = π/4`, exact return at `t = π` |
| **`fhb-spectral`** (this) | the spectrum `n - 2·|S|` that those amplitudes come from |
