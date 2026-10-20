#!/usr/bin/env python3
"""Cost model for verifying one Ed25519 signature in a BabyBear-hosted AIR.

Inputs:
  * operation census from census.py (validated against the oracle fixtures);
  * SHA-512 AIR cost from
    research/near-compression/results/pq384-sha-air3/README.md:
      83 columns x 128 rows = 10,624 cells per compression, 17 interactions/row.

The only free parameter is `N` = cells per F_p multiplication for an
F_p = 2^255-19 emulation over BabyBear (p_BB = 2^31 - 2^27 + 1).  It is an
ASSUMPTION, swept here over {100, 120, 149, 200}, with 149 = the prototype chip's
  committed width (15+15+15+15+29+30+30, see FpChip.lean).  Everything else is derived.

Cell convention: one committed BabyBear element in one trace row, matching the
SHA figure (83 x 128).  Next-row openings are not counted, as in the SHA table.
"""
import json
import math

P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493

# ---- SHA-512 AIR (measured, pq384-sha-air3/README.md) ----------------------
SHA_COLS = 83
SHA_ROWS = 128
SHA_CELLS = SHA_COLS * SHA_ROWS          # 10,624
SHA_INTER_PER_ROW = 17
SHA_INTER = SHA_INTER_PER_ROW * SHA_ROWS  # 2,176

# ---- census (census.py, validated 7265/7265 fixtures) ---------------------
def census(ps, pk, sqrtM1=False, sign=True, abs_neg=True):
    point_adds = 512 + ps + pk + 1
    muls = 11 * point_adds + (519 + (1 if sqrtM1 else 0)) + 511
    addsub = 8 * point_adds + 2
    negs = 2 + 1 + (1 if abs_neg else 0) + (1 if sign else 0)
    return dict(point_adds=point_adds, doublings=512, muls=muls,
                addsub=addsub, negs=negs, inv=1, sqrt=1,
                exp_255_minus_2=1, exp_p5_over_8=1)


def sha_blocks(msg_len):
    n = 64 + msg_len                    # R (32) || A (32) || msg
    return math.ceil((n + 1 + 16) / 128)


#: cells per limbwise F_p addition/subtraction/negation: 15 output limbs plus a
#: carry/borrow cell (the canonical reduction itself is a lookup, not a cell).
#: An ASSUMPTION, and a cheap one: additions are a small fraction of the total.
CELLS_PER_ADD = 16
#: interactions per F_p mul row: limb range-check + canonical-output bound
INTER_PER_MUL = 2
#: interactions per F_p add/sub row
INTER_PER_ADD = 1


def model(N, ops, blocks, cells_per_add=CELLS_PER_ADD):
    field_cells = ops["muls"] * N + ops["addsub"] * cells_per_add + ops["negs"] * cells_per_add
    sha_cells = blocks * SHA_CELLS
    total = field_cells + sha_cells
    field_inter = ops["muls"] * INTER_PER_MUL + ops["addsub"] * INTER_PER_ADD + ops["negs"] * INTER_PER_ADD
    total_inter = field_inter + blocks * SHA_INTER
    return dict(field_cells=field_cells, sha_cells=sha_cells, total_cells=total,
                field_inter=field_inter, sha_inter=blocks * SHA_INTER, total_inter=total_inter)


if __name__ == "__main__":
    # canonical cases
    typical = census(125, 126)              # mean popcounts over the fixtures
    worst = census(252, 252)                # s, k < L means <= 252 set bits
    d1 = sha_blocks(32)                     # D1: msg = sha256(body), 32 bytes
    longmsg = sha_blocks(1087)              # widest accepting fixture

    print(f"SHA-512 AIR: {SHA_COLS} cols x {SHA_ROWS} rows = {SHA_CELLS} cells, "
          f"{SHA_INTER} interactions per compression")
    print(f"D1 blocks (msg=32B): {d1};  widest fixture (msg=1087B): {longmsg}")
    print()
    hdr = f"{'case':<26}{'muls':>8}{'add/sub':>9}{'blocks':>8}" + "".join(f"{'N='+str(n):>14}" for n in (100,120,149,200))
    print(hdr)
    for name, ops, blocks in [("typical (125,126)", typical, d1),
                              ("typical, worst msg", typical, longmsg),
                              ("worst-case (252,252)", worst, d1)]:
        row = f"{name:<26}{ops['muls']:>8}{ops['addsub']:>9}{blocks:>8}"
        for N in (100,120,149,200):
            row += f"{model(N, ops, blocks)['total_cells']:>14,}"
        print(row)
    print()
    for N in (100,120,149,200):
        m = model(N, typical, d1)
        print(f"N={N:<4} typical D1: field {m['field_cells']:>10,} + sha {m['sha_cells']:>7,} "
              f"= {m['total_cells']:>10,} cells; interactions {m['field_inter']:>7,} + {m['sha_inter']:,} "
              f"= {m['total_inter']:>7,}")
    print()
    print("Breakdown of the census for the typical case:")
    print(json.dumps(typical, indent=2))
    print()
    print("delta: each F_p mul cell costs", f"{typical['muls']:,}", "cells per signature")
