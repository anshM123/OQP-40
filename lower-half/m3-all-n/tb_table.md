| chart | region (all eps in [0, 1/37]) | log | boxes / cells | time (s) | result |
|---|---|---|---|---|---|
| C3 stationary tail | a >= 64, 0 <= d <= 64 | `tb_tail2_A64.log` | 34689 | 202.8 | VERIFIED |
| C3 stationary tail | a >= 64, 64 <= d <= 512 | `tb_tail2_A64_far.log` | 165150 | 616.7 | VERIFIED |
| C5 double tail | a >= 64, d >= 512 | `tb_ddouble.log` | 256 | 0.0 | VERIFIED |
| C4 far tail | 3 <= a <= 64, d >= 512 | `tb_dtail.log` | 698 | 0.9 | VERIFIED |
| C1 core | 3 <= a <= 16, 3 <= d <= 16 | `tb_core_A1.log` | 279637 | 7374.7 | VERIFIED |
| C1 core | 16 <= a <= 64, 16 <= d <= 64 | `tb_core_A2a_hi.log` | 20469 | 644.5 | VERIFIED |
| C1 core | 16 <= a <= 64, 15/4 <= d <= 16 | `tb_core_A2a_lo1.log` | 246646 | 9036.9 | VERIFIED |
| C1 (mixed form) | 16 <= a <= 40, 3 <= d <= 15/4 | `tb_core_lo2_16_40.log` | 57232 | 1171.0 | VERIFIED |
| C1 (mixed form) | 40 <= a <= 64, 3 <= d <= 15/4 | `tb_core_lo2_40_64.log` | 62108 | 1274.7 | VERIFIED |
| C1 core | 3 <= a <= 16, 16 <= d <= 64 | `tb_core_A2b.log` | 6254 | 311.6 | VERIFIED |
| C1 core | 3 <= a <= 64, 64 <= d <= 512 | `tb_core_far.log` | 24073 | 1332.3 | VERIFIED |
| C2 d-strip | 3 <= a <= 8, 0 <= d <= 3 | `tb_dstrip_3_8.log` | 17239 | 425.3 | VERIFIED |
| C2 d-strip | 8 <= a <= 13, 0 <= d <= 3 | `tb_dstrip_8_13.log` | 13954 | 297.5 | VERIFIED |
| C2 d-strip | 13 <= a <= 18, 0 <= d <= 3 | `tb_dstrip_13_18.log` | 15780 | 333.1 | VERIFIED |
| C2 d-strip | 18 <= a <= 23, 0 <= d <= 3 | `tb_dstrip_18_23.log` | 16300 | 337.5 | VERIFIED |
| C2 d-strip | 23 <= a <= 28, 0 <= d <= 3 | `tb_dstrip_23_28.log` | 16402 | 347.8 | VERIFIED |
| C2 d-strip | 28 <= a <= 33, 0 <= d <= 3 | `tb_dstrip_28_33.log` | 16366 | 478.0 | VERIFIED |
| C2 d-strip | 33 <= a <= 48, 0 <= d <= 3 | `tb_dstrip_33_48.log` | 45180 | 988.7 | VERIFIED |
| C2 d-strip | 48 <= a <= 64, 0 <= d <= 3 | `tb_dstrip_48_64.log` | 46334 | 991.3 | VERIFIED |
