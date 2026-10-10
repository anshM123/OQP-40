"""Write Theorem B'' (the strip, RESULTS.md 8.4) and the completed Theorem B into RESULTS.md.
Usage: python tb_sx_finalize.py strip_section.md   (run tb_sx_table.py > tb_sx_table.md first)."""
import re
import sys

sec = open(sys.argv[1], encoding='utf-8').read()
table = open('tb_sx_table.md', encoding='utf-8').read().strip()
m = re.search(r'Total: (\d+) boxes, (\d+) s', table)
nbox, tsec = int(m.group(1)), int(m.group(2))
sec = sec.replace('STRIP_TABLE_PLACEHOLDER', table)
sec = sec.replace('STRIP_TOTALS', f'{nbox:,} boxes and cells, {tsec:,} s of computation')
res = open('RESULTS.md', encoding='utf-8').read()


def rep(old, new, count=1):
    global res
    assert old in res, old[:80]
    res = res.replace(old, new, count)


# section header
rep('## 8. Theorem B (all n >= N0): rigorous for s >= e^{3/n}, open for s < e^{3/n}',
    '## 8. Theorem B: Conjecture F at (n, 3) for every n >= 37 (computer-assisted)')
# the paragraph after Theorem B' and the "Not proved" paragraph
i0 = res.index('By Lemma 4 on the interval [e^{3/n}, inf) this gives')
i1 = res.index('### 8.1 eps-smooth closed forms')
res = res[:i0] + f'''Theorem B' is the part a >= 3 of Theorem B below; the strip 0 < a < 3, including the corner where s and t are both
close to 1, is Theorem B'' (8.4).

**Theorem B (rigorous, computer-assisted; not externally refereed).** For every integer n >= 37, and for the limit
kernel (eps = 0), the Gaussian-design certificate satisfies F > 0, F_s > 0, F_t < 0, F_st < 0 at every point
1 < s < t (Theorem B' for s >= e^{{3/n}}, Theorem B'' for s < e^{{3/n}}). Hence (B0) and (B1) hold, Lemma 4 makes E^R a
positive semidefinite kernel on (1, inf), and Proposition 6' gives A_{{n,3}}(A, B) >= Tr((A^{{n/3}} B)^3) for all positive
definite A, B: **Conjecture F at (n, 3), hence the lower half of OQP 40 at (n, 3) and (3, n), holds for every
n >= 37.** Together with the exact verifications for n <= 36 (published cases and Sections 4, 7) it holds for every
n >= 1. Computation: 1,084,767 boxes (Theorem B') + {nbox:,} boxes and cells (Theorem B''), all VERIFIED; the
formulas are checked against the definitions (8.1, 8.4). Independent checking of the code and of the runs is pending.

''' + res[i1:]
# replace the old 8.4
i0 = res.index('### 8.4 The open strip a < 3 and what is needed there')
i1 = res.index('### 8.5 N0')
res = res[:i0] + sec.rstrip('\n') + '\n\n' + res[i1:]
# 8.5
rep('''Within the verified region the conditions hold for every n >= 37 and in the limit, with no negative margin; smaller
N0 were not attempted''', '''The conditions hold for every n >= 37 and in the limit, with no negative margin anywhere (Theorems B' and B''); smaller
N0 were not attempted''')
# 8.7 reproduction
rep('''    python tb_table.py                                                      # table of 8.3''',
    '''    python tb_table.py                                                      # table of 8.3
    python tb_sx_test.py > tb_sx_test.log ; python tb_sx_dtail_test.py > tb_sx_dtail_test.log   # strip forms vs definitions
    python tb_sx_run.py corner > tb_sx_corner.log                           # S0
    python tb_sx_run.py direct 0 3 1/4 4 1/8 12 4 > tb_sx_direct.log        # S1
    python tb_sx_run.py --box nu 0 3/2 15/4 15/2 12 64 4 > tb_sx_nu_low_a.log   # S2 (and 3/2 3 ... > tb_sx_nu_low_b.log)
    python tb_sx_run.py nu 0 3 15/2 515 6 16 4 > tb_sx_nu.log               # S3
    python tb_sx_dtail.py 512 0 3 4 8 8 > tb_sx_dtail.log                   # S4
    python tb_sx_table.py > tb_sx_table.md                                  # table of 8.4''')
rep('''(C4), `tb_ddouble.py` (C5), `tb_bb.py` (C1, C2), `tb_astrip.py` (the hull approach for a -> 0 that fails, kept for
reference), `tb_formulas_mp.py` (mpmath versions and the reference definitions).''',
    '''(C4), `tb_ddouble.py` (C5), `tb_bb.py` (C1, C2), `tb_sx.py` (Taylor models in a for the strip, S0-S3),
`tb_sx_run.py` (strip driver), `tb_sx_dtail.py` (S4), `tb_astrip.py`, `tb_strip6.py` (earlier strip approaches that fail,
kept for reference), `tb_formulas_mp.py` (mpmath versions and the reference definitions).''')
# Section 0
rep('''- **Not proved: Conjecture F at (n, 3) for all n.** The session found why the route of the m3 note cannot be pushed to
  all n by a two-regime analysis as it stands (Section 2), a modified certificate that removes the obstruction
  numerically (Section 3), and (Section 8) a rigorous computer-assisted verification of the Lemma 4 conditions of
  the modified certificate for every n >= 37 on the whole region s >= e^{3/n} (Theorem B'). The strip
  1 < s < e^{3/n} (where E^R = O((s-1)^2)) remains open, so Theorem B is not established.''',
    '''- **Conjecture F at (n, 3) for all n: proved, computer-assisted (Theorem B, Section 8), not externally refereed.**
  The route of the m3 note cannot be pushed to all n as it stands (Section 2); a modified certificate removes the
  obstruction (Section 3), and Section 8 verifies the Lemma 4 conditions of the modified certificate in verified ball
  arithmetic for every n >= 37 at once (eps = 1/n an interval variable): Theorem B' (s >= e^{3/n}) and Theorem B''
  (the strip 1 < s < e^{3/n}, where E^R = O((s-1)^2), including the corner s, t -> 1). With n <= 36 (exact verifier)
  this gives Conjecture F, hence the lower half of OQP 40, at (n, 3) and (3, n) for every n. Independent checking of
  the code and the runs is pending.''')
rep('''     eps-smooth closed forms checked against the definitions). Open: 1 < s < e^{3/n} (Section 8.4).''',
    '''     eps-smooth closed forms checked against the definitions).
  7. Theorem B'' and Theorem B (Section 8.4, verified ball arithmetic, Taylor models in a): the same for
     1 < s < e^{3/n} (all t > s), hence for all 1 < s < t, every n >= 37 and the limit kernel; Conjecture F at (n, 3)
     for every n.''')
open('RESULTS.md', 'w', encoding='utf-8').write(res)
print('RESULTS.md updated:', nbox, 'strip boxes,', tsec, 's')
