"""Sanity: (1) the kernel reduction p_{n,4} - Tr((A^{n/4}B)^4) = Re sum_w T(w) K_n(alpha_w);
(2) an SDP certificate G satisfies the share identity and sum <S^{ab}, G^{ab}> equals the gap, for random A, B."""
import itertools
import sys

import numpy as np

from m4core import K_vec, word_average, F_rhs, certificate_value, check_identity, min_rel_eig, random_psd
from m4sdp import solve

rng = np.random.default_rng(1)
for n in [3, 4, 5, 6]:
    for trial in range(2):
        d = 4
        alpha = np.sort(np.exp(rng.uniform(0, 2, size=d)))
        U, _ = np.linalg.qr(rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d)))
        A = (U * alpha) @ U.conj().T
        B = random_psd(d, rng)
        gap = word_average(n, 4, A, B) - F_rhs(n, 4, A, B)
        # kernel sum
        wB, VB = np.linalg.eigh(B)
        Bh = (VB * np.sqrt(wB)) @ VB.conj().T
        W = [Bh @ np.outer(U[:, k], U[:, k].conj()) @ Bh for k in range(d)]
        tot = 0.0
        for w in itertools.product(range(d), repeat=4):
            T = np.trace(W[w[0]] @ W[w[1]] @ W[w[2]] @ W[w[3]])
            tot += (T * K_vec(n, np.array([[alpha[i] for i in w]]))[0]).real
        st, t, G, sc = solve(n, alpha, "margin")
        cv, _ = certificate_value(n, A, B, G)
        idt = check_identity(n, alpha, G)
        me = min(min_rel_eig(G).values())
        print(f"n={n} gap={gap:.10e} kernel_sum={tot:.10e} cert={cv:.10e} |rel diff| {abs(gap-tot)/abs(gap):.1e} "
              f"{abs(gap-cv)/abs(gap):.1e}; SDP {st} margin {t:.2e}, id err {idt:.1e}, min rel eig {me:.1e}")
