"""Measured byte laws for the non-WHIR parts of a SWIRL proof (lane/pq-whir-levers).

For ext2.py-style fixed points: these replace ext.py's child-calibrated constants.
All laws are exact on the runs listed (logs in results/pq-whir-levers/logs/):

GKR (LogUp fractional sumcheck), L = GKR depth = ceil(log2(sum over AIRs of interactions x rows)),
lifted heights; e.g. the L3 SHA AIR (43 interactions/row) has L = log2(rows) + 5:
    upstream                      72 L^2 + 264 L + 248   dummy L=9..15; SHA-AIR lane L=19,21,23
    gruen_gkr + gkr_derive_claims 48 L^2 + 192 L + 152   dummy L=9,11,13; SHA AIR L=23 (29,960 B)

Relations (batch-constraint proof), d = params.max_constraint_degree (must be >= every AIR's degree;
it sets the round-polynomial degree, NOT the AIR's actual degree), n = max log2(rows) - l_skip:
    48 * sum_cols (1 + rot_c)                      column openings; rot_c = column read at next row
                                                   (every column of an AIR with any next-row read,
                                                   or per column with next_mask)
  + 48 * ((d + 1) * (2^l_skip - 1) + 1)            univariate skip round
  + 48 * ((d + 1) * n - g)                         multilinear rounds; g = rounds in which no trace
                                                   is exhausted (gruen_zerocheck; else 0)
  + 96 * airs + 24 (+4 in the lever format: the g field)
    exact on: dummy h=12..14 (d=8 and d=4) and the child; SHA AIR 2^18: 48,940 vs 48,956 B measured.

Stacking proof: 352 + 96 * n_stack + 48 * W     (W = stacked width; exact at W=4..28, n_stack 17, 20)

next_mask fractions measured: gas-failure5 child 116/271 rotated columns; L3 SHA AIR 438/442 main +
16/18 table (so next_mask is worth ~0.3 KB on the SHA-dominated final layer, not 30 %).
"""
import math


def gkr_bytes(L, levers=True):
    return 48 * L * L + 192 * L + 152 if levers else 72 * L * L + 264 * L + 248


def relations_bytes(cols, rot_cols, d, n, airs=1, l_skip=2, gruen_rounds=0, lever_format=True):
    return (48 * (cols + rot_cols) + 48 * ((d + 1) * ((1 << l_skip) - 1) + 1)
            + 48 * ((d + 1) * n - gruen_rounds) + 96 * airs + 24 + 4 * lever_format)


def stacking_bytes(W, n_stack):
    return 352 + 96 * n_stack + 48 * W


def sha_air_L(rows):
    """GKR depth of the L3 SHA AIR at `rows` (power of two) rows: 43 interactions per row."""
    return int(math.log2(rows)) + 5


if __name__ == '__main__':
    # self-checks against measured runs
    assert gkr_bytes(23) == 29960 and gkr_bytes(23, False) == 44408 and gkr_bytes(13) == 10760
    assert stacking_bytes(15, 17) == 2704 and stacking_bytes(28, 20) == 3616
    assert relations_bytes(460, 460, 4, 12, gruen_rounds=12) == 47356        # gate 5 h=14, levers
    assert relations_bytes(460, 460, 8, 12, lever_format=False) == 50808      # gate 5 h=14, round 1
    assert relations_bytes(16, 16, 4, 10, lever_format=False) == 4824          # gz0-4
    print('laws OK')
