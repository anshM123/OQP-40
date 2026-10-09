# Lower half of OQP 40: scripts, certificates and logs

This folder holds the computations behind
[`../math/04-lower-half-new-cases.md`](../math/04-lower-half-new-cases.md):
- [`thm33/`](thm33/): the (3,3) case, Theorem 1 of the note. Symbolic computations for the conditions (I)–(III), a
  numerical check of the certificate, and the single-word counterexample.
- [`thm33/independent-check/`](thm33/independent-check/): an independent check of Theorem 1, with its own code.
- [`sos/`](sos/): the exact sum-of-squares certificates of Theorem 2 of the note, the non-existence certificates for
  (3,3) and (6,3), and our exact verifier.
- [`sos/independent-check/`](sos/independent-check/): an independent verifier for all 25 certificate files, with its
  own code.

Both checks are internal checks, made with newly written code. They are not external referee reports.

## Requirements

- Python 3 with numpy, scipy, sympy, mpmath and python-flint:
  `pip install numpy scipy sympy mpmath python-flint`.
  We used Python 3.12.10, numpy 2.5.3, scipy 1.18.1, sympy 1.14.0, mpmath 1.3.0 and python-flint 0.9.0.
- `sos/verify_certificate.py` and `thm33/perword33_example.py` need only the standard library.
- `thm33/independent-check/r5b_optimizer.py` and `r5b_optimizer_large.py` also need PyTorch (we used 2.11). The CPU is
  enough.
- The commands are written for a POSIX shell such as bash (for example, `certs/*.json` is expanded by the shell).
- We set `OMP_NUM_THREADS=2`. The run times below are wall-clock times on a laptop.

**Run each command from the folder that contains the script.** Each folder needs only its own files; the scripts in
`sos/independent-check/` also read `../certs/`.

## Names used inside the scripts

The scripts were written against our working notes, which are not included. Their comments and printed labels use the
numbering there.

| In the scripts | In [`../math/04-lower-half-new-cases.md`](../math/04-lower-half-new-cases.md) |
|---|---|
| Theorem 4; OQP40_RESULTS §8 | Theorem 1 |
| Lemma 5, Lemma 5′ | Lemma 2 |
| Lemma 6 | Lemma 3 |
| Lemma 7 | Lemma 4 |
| apex identity (6.1) | (2.1) |
| §8.3: the conditions (I)–(III) and N_I, N_II, N_III | Section 2.5 |
| OQP40_RESULTS section 7: the single-word counterexample | Section 3 |
| Fact 0.5 | Lemma 2.1 of [`../math/03-lower-half.md`](../math/03-lower-half.md) |
| SOS_RESULTS.md | Section 4 |
| Lemma 2.1 of SOS_RESULTS.md (odd m) | the obstruction without localizers in Section 4.4 |

- The scripts in `thm33/independent-check/` call themselves a "referee check". It is an internal check, not an
  external referee report. There, "the authors' code" means the scripts in `thm33/`, and the docstrings number the
  parts of the check as tasks: task 1 re-derives the proof, task 2 treats the conditions (I)–(III), and task 3 is
  the numerics.
- In `sos/independent-check/`, "the authors' verifier" is `sos/verify_certificate.py`, and "the task statement"
  means the claims of Section 4 of the note.
- `r4_numerics.py` also reports an identity from our working notes, f = Tr(AYBY) + 2 Tr((AB+BA)Y²) with
  Y = −i[A,B], and the ratio J = f / Tr(AYBY). The note does not use them.

## thm33/

The logs are in `thm33/logs/`.

| Log | Command (from `thm33/`) | Time | What it shows |
|---|---|---|---|
| `uc33_proof.log` | `python uc33_proof.py > logs/uc33_proof.log` | 2.5 min | (I)–(III) in the parametrisation C = p² − 5, B = (q² − p²)/4: their denominators, and a sign test at 20,000 points. Writes `uc33_conditions.pkl`. |
| `uc33_proof2.log` | `python uc33_proof2.py > logs/uc33_proof2.log` | 1 s | N_I, N_II, N_III as polynomials in v = q − p. Reads `uc33_conditions.pkl`, so run `uc33_proof.py` first. |
| `uc33_proof3.log` | `python uc33_proof3.py > logs/uc33_proof3.log` | 1 s | the discriminant 4c₀c₂ − c₁², and c(x), c₂ in the variable y = x − 5 |
| `thm4_check.log` | `python thm4_check.py > logs/thm4_check.log` | 2 s | the identity Φ(κ) = 3 Σ⟨R, G⟩ and the semidefiniteness of the certificate matrices on 300 random cases (3 to 8 distinct eigenvalues); the minimum of 𝒜₃,₃ / Tr((AB)³) over 2,000 random pairs, d = 4 to 24 |
| `perword33_example.log` | `python perword33_example.py > logs/perword33_example.log` | < 1 s | the single-word counterexample in exact arithmetic, and the instance of the Ando–Hiai–Okubo question |

The logs of `uc33_proof*.py` were produced on 2026-10-09 for this release. The other two are the logs of the
original runs.

## thm33/independent-check/

Each script writes its log next to itself, except `r2c_squared.py`, which prints to the screen.

| Log | Command (from `thm33/independent-check/`) | Time | What it shows |
|---|---|---|---|
| `r1_reduction.log` | `python r1_reduction.py` | 7 s | the reduction in exact algebra (the kernel κ, the word classes, the apex identity, E₁ = B²CG, the derivative formulas); the identities f = Φ(κ)/3 = Σ⟨R, G⟩ and the semidefiniteness claims in 256-bit ball arithmetic on 120 instances |
| `r2_symbolic.log` | `python r2_symbolic.py` | 1 s | (I)–(III) by direct differentiation in (B, C); they equal N_I, N_II, N_III exactly; all sign arguments |
| `r2b_closed_forms.log` | `python r2b_closed_forms.py` | 1 s | the closed forms of (I)–(III) in Section 2.5 |
| `r2c_squared.log` | `python r2c_squared.py > r2c_squared.log` | 1 s | the second route for (III). The log uses 4a₃ and 4d₃, so its factor 64B is 16 · 4B. |
| `r3_interval.log` | `python r3_interval.py` | 1 s | proof of (I)–(III) on {0 ≤ B ≤ C, C > 0} by verified interval arithmetic (131 boxes) |
| `r4_numerics.log` | `python r4_numerics.py` | 13 s | 7,485 exactly built pairs, d = 2 to 30, in ball arithmetic: no violation |
| `r4b_large_d.log` | `python r4b_large_d.py` | 7 s | 24 exactly built pairs with d = 50, 80, 100: no violation |
| `r5b_optimizer.log` | `python r5b_optimizer.py` | 2 min | L-BFGS searches for d = 2 to 8; every minimiser re-evaluated exactly (needs PyTorch) |
| `r5b_optimizer_large.log` | `python r5b_optimizer_large.py` | 20 s | the same for d = 10, 12, 16 (needs PyTorch) |
| `r6_perword.log` | `python r6_perword.py` | < 1 s | the single-word counterexample in exact arithmetic, and the formula for H in Section 3 |
| `r7_lemma67.log` | `python r7_lemma67.py` | 45 s | Lemma 3 tested on 400 point sets at 120 digits; the decomposition of Lemma 4 |
| `r8_alt.log` | `python r8_alt.py` | 7 s | the exponential bound of Section 2.6, at 40 digits, on 150 random pairs |

## sos/

The certificate format is described at the top of [`sos/verify_certificate.py`](sos/verify_certificate.py).

| Log | Command (from `sos/`) | Time | What it shows |
|---|---|---|---|
| `logs/verify_all.log` | `python verify_certificate.py certs/*.json` | 2 min | the 11 positive certificates: exact identities, all Gram blocks exactly positive semidefinite; the 14 non-existence certificates: moment matrices exactly positive semidefinite, y(f) < 0 |

`verify_certificate.py` rebuilds each target from the definitions of 𝒜ₙ,ₘ and p^mult. The order of the files in the
log depends on how the shell sorts `certs/*.json`.

## sos/independent-check/

The scripts read the certificates from `../certs/` and write to `logs/`. `indep_verify_positive.py`,
`indep_numeric.py` and `indep_nonexistence.py` append to their log, so a rerun adds a new run at the end, and they
also write a JSON summary.

| Log | Command (from `sos/independent-check/`) | Time | What it shows |
|---|---|---|---|
| `test_core.log` | `python test_core.py > logs/test_core.log` | 1 s | self-tests of the word and polynomial routines |
| `indep_verify_positive.log`, `indep_verify_positive_all.json` | `python indep_verify_positive.py` | 40 s | the 11 positive certificates: targets rebuilt from the claims, exact identities modulo rotation, exact LDLᵀ of every Gram block |
| `psd_crosscheck.log` | `python psd_crosscheck.py` | 20 s | every Gram block positive definite by Sylvester's criterion, in exact arithmetic |
| `indep_numeric_exact.log`, `indep_numeric_exact_all.json` | `python indep_numeric.py exact` | 1.5 min | 349 samples (a random positive semidefinite pair, sizes 2 to 8, against one certificate), in exact rational arithmetic |
| `indep_numeric_arb.log`, `indep_numeric_arb_all.json` | `python indep_numeric.py arb` | 3 min | 414 samples of the same kind, in ball arithmetic |
| `indep_numeric_arb_full68.log`, `indep_numeric_arb_F44_11-xx-yy_F34m_11-xx-yy_D34m_11-xx-yy_M34m_11-xx-yy_F64_11-xx-yy_full68.json` | `python indep_numeric.py arb --full68 F44_11-xx-yy.json F34m_11-xx-yy.json D34m_11-xx-yy.json M34m_11-xx-yy.json F64_11-xx-yy.json` | 3 min | 90 more ball-arithmetic samples for the five largest certificates (504 in all) |
| `indep_nonexistence.log`, `indep_nonexistence.json` | `python indep_nonexistence.py` | 5 s | the 14 non-existence certificates |
| `indep_chain.log` | `python indep_chain.py` | 20 s | from Conjecture F to the lower half: conventions, the exponential bound and the exchange of letters, at 40 digits |
| `tamper_tests.log` | `python tamper_tests.py` | 1.5 min | 17 negative controls |
| `hand_formulas.log` | `python hand_formulas.py` | < 1 s | the (4,2) identity of Section 4.1, and a similar identity for (2,4) |
| `lemma21_check.log` | `python lemma21_check.py` | 2 s | the obstruction without localizers (Section 4.4) at (3,3), (6,3), (9,3), (12,3) and (5,5) |

## Reproduction

On 2026-10-09 we re-ran every command above from copies of these folders. Every output agreed with the log here,
apart from run times, date lines and the order of the files in `sos/logs/verify_all.log`. The floating-point parts
(`thm4_check.py` and the searches in `r5b_optimizer*.py`) may differ in the last digits on other machines; every sign
that matters is decided in exact or ball arithmetic.
