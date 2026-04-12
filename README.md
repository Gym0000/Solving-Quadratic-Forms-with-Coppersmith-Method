# Solving Quadratic Forms with Coppersmith Method for Fixed Degree Isogenies Problem

This repository contains the SageMath code used in the experiments of the paper:

[**Better Bounds for Finding Fixed-Degree Isogenies via Coppersmith’s Method**]((https://eprint.iacr.org/2025/1812))  
M. A. Aardal, D. F. Aranha, Y. Feng, Y. Gao, Y. Pan (EUROCRYPT 2026)

The implementation focuses on solving 4-variable *integer* polynomial equations arising from quadratic forms

$$
f(x_1,x_2,x_3,x_4)=\mathbf{x}^T G \mathbf{x} - d = 0
$$

using a Jochemsz–May-style lattice construction and lattice reduction.

## Contents

- `experiment_fourvariables.sage`: main script (builds the lattice, reduces it, and recovers solutions).
- `output.txt`: example output log from running the script.

## Requirements

- SageMath (tested with SageMath 10.3).
- Optional: an external lattice reducer `flatter` available in `PATH`.
  - If `flatter` is not available, you can switch to Sage's built-in LLL in the script.

## Running

```bash
sage experiment_fourvariables.sage | tee output.txt
```