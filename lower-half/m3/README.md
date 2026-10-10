# Theorem 5: Conjecture F at (n, 3)

Computations for [`../../math/05-lower-half-m3.md`](../../math/05-lower-half-m3.md). Python 3 with python-flint, sympy,
mpmath and numpy. Run each command from this folder; set `OMP_NUM_THREADS=2` when running several at once.

## The proof for one n

```bash
python verify_n.py n
```

This checks the obligations (P0), (Pg), (P1) and (P2) of Section 3 of the note exactly, over the rationals, and ends
with `RESULT n = ...: ALL OBLIGATIONS VERIFIED` and a SHA-256 digest of the proved polynomials. Logs: `verify_n{n}.log`
for n = 1, …, 36 and n = 39, 42, …, 66. Run times are in the table of Section 4 of the note (up to about 99 minutes,
for n = 35).

## Checks (Section 6 of the note)

| Command | What it checks | Log |
|---|---|---|
| `python crosscheck_conditions.py n diag` (n = 3, …, 9) | the polynomial conditions against 60-digit numerical differentiation of F built from the definitions | `crosscheck.log` |
| `python endtoend_check.py n` | the certificate identity and the positivity of every certificate matrix on random matrices, 40 digits | `endtoend.log` |
| `python show_n3.py` | all polynomials for n = 3, printed in full | `show_n3.log` |
| `python p0_constant_terms.py 1 2 3 ...` | the constant terms in obligation (P0) | `p0_constant_terms.log` |
| `python second-check/verify_polys_vs_direct.py n 8` (every other n in the proved set) | the same check | `second-check/verify_polys_vs_direct_all.log` |
| `python second-check/verify_polys_vs_direct.py n 10` (n = 4, 5, 6, 7) | the exact polynomials that `verify_n.py` proves SP, against F and its derivatives computed from the definitions, 80 digits | `second-check/verify_polys_vs_direct.log` |
| `python second-check/sympy_verify.py n` (n = 3, 6) | a second implementation in sympy, built from the quotient rule | `second-check/sympy_verify_n{n}.log` |
| `python second-check/direct_signs.py n 160 1` (n = 3, 4, 5, 7) | the four sign conditions straight from the definitions, 60 digits | `second-check/direct_signs_small.log` |
| `python second-check/direct_signs.py n 80 2` (n = 11, 17, 24, 36, 60) | the same, 60 digits; at n = 36 and 60 the small values of F far from the diagonal fall below 60-digit resolution | `second-check/direct_signs_large.log` |
| `python second-check/direct_signs.py n 80 2 250` (n = 36, 60) | the same points at 250 digits: no violation | `second-check/direct_signs_large_250digits.log` |
| `python second-check/direct_signs_hp.py 36 80 2` | the points flagged at 60 digits for n = 36, re-evaluated at 150 and 300 digits: all positive | `second-check/direct_signs_hp_n36.log` |
| `python second-check/direct_signs.py n 80 2 250` (n = 31, 32, 34, 63) | the four sign conditions straight from the definitions, 250 digits, 120 points per n: no violation | `second-check/direct_signs_new_250digits.log` |
| `python second-check/direct_signs.py n 120 1 250` (n = 35, 66) | the same, 180 points per n: no violation | `second-check/direct_signs_35_66_250digits.log` |
| `python verify_n.py n`, run again (n = 63, 66) | reproducibility: the same result and the same SHA-256 digest of the proved polynomials | `verify_n63_rerun.log`, `verify_n66_rerun.log` |

`crosscheck_conditions.py` uses the helper modules `m3flint.py` and `m3flint2.py` in this folder.
