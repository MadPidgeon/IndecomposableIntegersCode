# Indecomposable algebraic integers code

The code in this repository accompanies the (draft) paper "Indecomposable Algebraic Integers" by Daniël van Gent, available at https://arxiv.org/abs/2111.00499. The code requires SageMath version 10.9.

## Files

* **library.sage** contains SageMath code that computes decompositions and indecomposability proofs of algebraic integers. 

* **data.txt** contains the computed candidates for indecomposability of degree 3. 

## Usage

**data.txt** is created by `initialize_algebraic_integers`, and may be read from and written to by `read_algebraic_integers` and `write_algebraic_integers`. The function `compute_all` attempts to compute for each candidate indecomposable a decomposition or an indecomposability proof. The results can be verified using `verify_all`.

The file **data.txt** is formatted as follows. Each line describes an algebraic integer `alpha` by the coefficients `f0 f1 f2 f3` of its minimal polynomial. This is then followed by the string `decomposable` if `alpha` is decomposable, `indecomposable` if it is indecomposable, or `indeterminate` if no conclusion has been reached. If `alpha` is `decomposable`, the minimal polynomial of `beta` for some decomposition `(beta,alpha-beta)` is given, and if `alpha` is `indecomposable`, a proof polynomial is given. These are both polynomials over `QQ(alpha)`, and are represented coefficient-wise, with elements of `QQ(alpha)` represented by the coefficients of the corresponding degree 2 polynomials in `alpha`. 
