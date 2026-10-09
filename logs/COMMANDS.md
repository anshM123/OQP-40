# How each log was produced

Python 3 with numpy, scipy, mpmath, sympy and python-flint; PyTorch with CUDA for the GPU searches.
Thread count: `OMP_NUM_THREADS=2`. Each command was run from `code/`.

| Log | Command | Notes |
|---|---|---|
| `verify_pinching.log` | `python verify_pinching.py` | default seed 2026 |
| `chalee_family.log` | `python chalee_family.py` | 60-digit mpmath |
| `chalee_frac.log` | `python chalee_frac.py` | 50-digit mpmath; the tail of the output (last 70 lines) was kept |
| `oqp40_second_order.log` | `python oqp40_second_order.py` | the (8,8) entry `-inf` is a floating-point overflow at extreme parameters; see `math/03-lower-half.md` §4 |
| `oqp40_lower_s{1,2,3}.log` | `python oqp40_lower.py SEED`, SEED = 1, 2, 3, each with `timeout 3000` | each run was stopped by the time limit after the cases listed (`exit 124`) |
| `oqp40_torch_sweep.log` | `python oqp40_torch.py d n m 384 2000 7` for d = 2..5 and (n,m) in {(3,4),(4,4),(3,5),(5,5),(4,6),(6,6),(3,7),(2,9)} | only the FINAL line of each run was kept; GPU results can differ in the last digits between runs |
| `oqp40_aux.log` | the commands are printed in the log itself (`$ python oqp40_aux.py MODE d n m 192 STEPS SEED`) | modes `pinch2`, `alt`, `frac`; the `pinch2` run gives the −1.38 figure of `math/03-lower-half.md` §6 |
| `split_F.log` | `python split_F.py` | |
| `freeregime.log` | `python freeregime.py` | 60 trials, running minimum printed after each |
| `negword_search.log` | `python negword_search.py 3 1` and `python negword_search.py 4 1` | |
| `icx_test.log` | `python icx_test.py` | Monte Carlo estimate of p_{x,3}, 4·10⁵ samples |
| `moment_test.log` | `python moment_test.py` | |

The independent check has its own scripts and logs in `../independent-check/scripts/`.

The new cases of the lower half ([`../math/04-lower-half-new-cases.md`](../math/04-lower-half-new-cases.md)) have their
own scripts, certificates and logs in `../lower-half/`. The command behind each of those logs is listed in
[`../lower-half/README.md`](../lower-half/README.md).
