# Lower half at (n, 4) and (4, n): rules, verifiers and logs

This folder holds the computations behind [`../../math/06-lower-half-m4.md`](../../math/06-lower-half-m4.md),
Theorem 6: Conjecture F at (n, 4) for n ∈ 𝒩₄ = {3, …, 14} ∪ {16, 18, 20, 22}.

**What a certificate is.** For each n, `rules/n{n}.json` is a table of rational numbers γ. It defines the function
k(x, y; e, f) of Section 3 of the note, a polynomial in x^{1/q}, y^{1/q}, e^{1/q}, f^{1/q}, where q = 2 for even n and
q = 4 for odd n. The theorem for this n follows from two exact facts about the table:
- **(S)** the share identity k(x,y;e,f) + k(e,f;x,y) = 2K_n(x,e,y,f), checked coefficient by coefficient;
- **(P)** the kernel matrix C(1, s) is positive semidefinite for 0 < s ≤ 1. This is proved by showing that every
  leading principal minor of its nonzero part is positive on (0, 1).

`rules/n4_simple.json` is a second table for n = 4, with small integer entries; Section 4.1 of the note checks it by
hand.

## The JSON format

| field | meaning |
|---|---|
| `n`, `qd` | the case and the root order q (exponents are integers in units of 1/q; N = n·q) |
| `exponents_units` | the live kernel exponents i (rows of C); exponents above N/2 are dead and their rows vanish |
| `var`, `z` | the free table entries: `var[k] = [[a, b], [i, j]]` is a pair of sorted pairs, and `z[k]` its exact rational value |
| `zero_rows`, `minor_degrees` | informational |

Every other entry is fixed:
- γ(p; p) = κ(p ∪ p);
- γ(p′; p) = 2κ(p ∪ p′) − γ(p; p′);
- γ(p; ⟨i, j⟩) = 0 when j is a dead exponent.

Here κ is the coefficient of K_n in root variables (Section 3 of the note).

## Verifiers

Run each command from this folder.

| Command | What it checks | Logs |
|---|---|---|
| `python verify_rule_independent.py rules/n{n}.json` | (S) coefficientwise against K_n rebuilt from its definition; (P) by exact fraction-free elimination over ℚ[s] (per parity block). Each minor is certified to have no root in (0, 1), by a Descartes sign test after s = t/(1+t) or, when that is inconclusive, by Arb root isolation. Then a 60-digit end-to-end test on random (A, B), d = 3, 4: certificate value = cycle sum = word average minus Tr((A^{n/4}B)^4) computed from the words, and every G^{ab} positive semidefinite | `logs/verify_rule_independent_n{n}.log` |
| `python verify_independent.py rules/n{n}.json` (n ≤ 10), `python verify_independent_fast.py rules/n{n}.json` (n ≥ 11) | a second exact verifier written with sympy: (S) as a polynomial identity, the parity splitting, and the minors via sympy's real-root isolation. The fast variant replaces only the elimination by a separately written integer Bareiss loop | `logs/final_indep_n{n}.log`, `logs/final_indepfast_n{n}.log` |
| `python exact_rule.py ...` | the exact check run when each table was constructed: Bareiss over ℚ[s], then Descartes' rule with bisection (`exactcheck.py`) | `logs/final_exact_n{n}.log` |
| `python check_rule.py rules/n{n}.json 6` | 50-digit end-to-end test on random positive definite A, B | `logs/final_check_n{n}.log` |

`verify_rule_independent.py` and `verify_independent.py` were written separately. The first uses python-flint and Arb,
the second sympy.

## How the tables were found (not part of the proof)

- `polyrule.py`: the structure of a rule (free entries, fixed entries, the matrix C(s)).
- `polyrule_cp.py`: the search, a semidefinite program solved with Clarabel. Near s = 0 and s = 1 it samples in scaled
  coordinates, and it adds cutting planes.
- `exact_rule.py`: rounding to rationals, exact projection onto the endpoint equalities, and the first exact check.
- `final_rule.sh`: the commands that produced `rules/`, except n = 13. For n = 13 the search used the regularised
  option of `polyrule_cp.py` (it keeps the solution vector small), then the same exact step:
  `REG=1 PARITY=1 python polyrule_cp.py 13 4 sol/n13_q4_reg.npz` (log `logs/final_cp_n13.log`) and
  `PARITY=1 PROJ=rref python exact_rule.py 13 4 sol/n13_q4_reg.npz 40 rules/n13.json` (log `logs/final_exact_n13.log`).
- `m4core.py`, `m4sdp.py`: the kernel K_n, and the finite-spectrum share SDP. That SDP showed that certificates of this
  type exist.
- `n4_simple.py`: produces `rules/n4_simple.json`.

## Requirements

Python 3 with numpy, scipy, sympy, mpmath and python-flint; cvxpy and clarabel only for the search. Versions as in
[`../README.md`](../README.md).

From n = 13 on, the exact tables contain integers with more than 4300 digits. Python 3.11 and later refuse to
convert such integers to and from strings by default, so set `PYTHONINTMAXSTRDIGITS=0` before running the scripts
on those tables. `verify_rule_independent.py` lifts the limit itself.
