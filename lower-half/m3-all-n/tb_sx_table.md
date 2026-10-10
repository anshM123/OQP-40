| chart | region (all eps in [0, 1/37]) | log | boxes | time (s) | certified lower bounds | result |
|---|---|---|---|---|---|---|
| S0 corner | 0 <= a <= 1/4, 0 <= b <= 1/4 | `tb_sx_corner.log` | 1 | 1.0 | aL1 >= 0.9176, abL3 >= 0.7504, bL2 >= 0.9045 | VERIFIED |
| S1 direct | 0 <= a <= 3 (12 strips), 1/4 <= b <= x0 + 4 | `tb_sx_direct.log` | 14491 | 740.6 | L2 >= 0.09819, aL1 >= 0.9905, aL3 >= 5.989e-05 | VERIFIED |
| S2 nu, --box | 0 <= a <= 3/2 (12 strips of 1/8), y1 + 15/4 <= b <= 15/2 | `tb_sx_nu_low_a.log` | 10122 | 1106.3 | L2 >= 0.05144, aL1 >= 0.9652, aL3 >= 2.647e-05 | VERIFIED |
| S2 nu, --box | 3/2 <= a <= 3 (12 strips of 1/8), y1 + 15/4 <= b <= 15/2 | `tb_sx_nu_low_b.log` | 652 | 56.7 | L2 >= 0.1365, aL1 >= 0.9999, aL3 >= 0.0001879 | VERIFIED |
| S3 nu | 0 <= a <= 3 (6 strips), 15/2 <= b <= 515 | `tb_sx_nu.log` | 13118 | 1481.1 | L2 >= 0.02818, aL1 >= 0.3046, aL3 >= 2.133e-05 | VERIFIED |
| S4 far tail | 0 <= a <= 3, d >= 512 | `tb_sx_dtail.log` | 256 | 11.4 | a L1 >= 0.8065, L2 >= 0.06803, a L3 >= 0.05467 | VERIFIED |

Total: 38640 boxes, 3397 s.
