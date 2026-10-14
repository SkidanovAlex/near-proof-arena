import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.Tables.TxDefs` — `txV3`: the state-dependent part of the transactions

Lane `v3-d1-tables` (V3-D1-DESIGN §2.2, D1-N).  Definitions only (verifier-model import rule).

One **op** per `16` rows (byte lanes `0 … 15`, least significant first).  The ops are, in
order, every transaction that reaches step 3 of `processTx` (not a duplicate, validity flag
set) and then every local receipt; op `o` is public (`TXP` records `j = 16·o + lane`, `SIG`
record `o`) and its memory accesses happen at time `T = o + 1` (`MEM`, `AKMEM`).  `rcptV3D1`'s
incoming receipts write at `r + 1 + T0` with `T0 = #ops`.

**Debit op** (`kind = 0`, transaction `t`): public `strict`, `N = t.nonce`, `Bd = min(height·10⁶,
2⁶⁴−1)`, `C = txCost.totalCost`, `cok` (the cost does not overflow), `valid` on `SIG`
(`sizeOk ∧ Ed25519.verify`, native under D1-N), the claimed verdict `ok`, `tov` (the tokens
of the chunk overflow: no write, `processTx` step 8), `stage` (0: signer account absent, 1:
access key absent, 2: both present).  `cand = valid·cok`; `stage > 0 ⇒ cand`.
* `stage ≥ 1` — `FINAL (W_TX + 2o, 0, 0, vidA)` (signer walk, terminal VAL) and the 16-lane
  `MEM` read of the account value record `vidA` at `tpA < T`, written back at `T` with
  `amount − C` if `wr = ok·(1 − tov)`, else unchanged;
* `stage = 0` (and `cand`) — `FINAL (W_TX + 2o, 0, 1, 0)` (absent);
* `stage = 2` — `FINAL (W_TX + 2o + 1, 0, 0, vidK)` and the 8-lane `AKMEM` read of the key's
  nonce `kn` and `fa` (FullAccess) at `tpK < T`, written back with `N` if `wr`;
* `stage = 1` — `FINAL (W_TX + 2o + 1, 0, 1, 0)`.
The verdict is recomputed and must equal the public `ok` (`verifyAndCharge`): with `stage = 2`,
`fa` (a gas key or a function-call key always fails), the nonce (monotonic `N > kn`, strict
`N = kn + 1`; the overflow case `kn = 2⁶⁴ − 1` fails both), `N < Bd`, `amount ≥ C`, and the
storage stake on the new amount (`new + locked < 2¹²⁸ ∧ (new + locked ≥ 10¹⁹·storage ∨
storage ≤ 770)`); `ok = 0` for `stage < 2`.  Byte chains (16 lanes, each byte range-checked by
8 bit columns):

| chain | lane relation (`cin₀`) | result |
|---|---|---|
| N | `dN = N − kn − cin + 256·boN` (`1`) | `boN₁₅ = 0 ⇔ N > kn`; `dN = 0` (zero test `zN`) ⇔ `N = kn + 1` |
| B | `dB = Bd − N − cin + 256·boB` (`1`) | `boB₁₅ = 0 ⇔ N < Bd` |
| C | `rC = amt + σ·(C + cin − 256·coC)`, `σ = 2·kind − 1` (`0`) | debit: `new = amt − C`, `coC₁₅ = 0 ⇔ amt ≥ C`; credit: `aft = amt + dep`, no overflow |
| T | `tT + 256·coT = rC + lk + cin` (`0`) | `coT₁₅ = 0 ⇔ rC + locked < 2¹²⁸` |
| Q | `q + 256·cq = Σⱼ Sⱼ·st_{lane−j} + cin` (`0`), `S = 10¹⁹` (8 bytes), delay line `dl` | `q = 10¹⁹·storage` (`< 2¹²⁸`) |
| D | `dQ = tT − q − cin + 256·boQ` (`0`) | `boQ₁₅ = 0 ⇔ tot ≥ q` |
| S | `dS = 770ₗ − st − cin + 256·boS` (`0`) | `boS₁₅ = 0 ⇔ storage ≤ 770` |

**Credit op** (`kind = 1`, local receipt to the signer): `stage = 1` (signer walk terminal VAL),
`aft = amt + deposit` with no overflow, `aft ≠ u128::MAX`, `aft + locked < 2¹²⁸`, the storage
stake (hard constraints: a failing local receipt is out of domain, `r.success`); written at
`T`.
-/

namespace ZkFormal.NearV3.D1.TxV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1

/-! ## Columns -/

def act : Nat := 0
def lf : Nat := 1
def ll : Nat := 2
def lane : Nat := 3
def g : Nat := 4
def op : Nat := 5
-- public record fields
def kind : Nat := 6
def strict : Nat := 7
def okP : Nat := 8
def tov : Nat := 9
def stage : Nat := 10
def cok : Nat := 11
def xN : Nat := 12
def xB : Nat := 13
def xC : Nat := 14
-- op flags
def valid : Nat := 15
def s1 : Nat := 16
def s2 : Nat := 17
def cand : Nat := 18
def wr : Nat := 19
def fa : Nat := 20
def vidA : Nat := 21
def vidK : Nat := 22
def tpA : Nat := 23
def tpK : Nat := 24
-- memory values
def amt : Nat := 25
def lk : Nat := 26
def st : Nat := 27
def mo : Nat := 28
def kn : Nat := 29
def nk : Nat := 30
-- lanes
def lb (x : Nat) : Nat := 31 + x
def l1 : Nat := 35
def tb (x : Nat) : Nat := 36 + x
-- chain N
def dNb (x : Nat) : Nat := 50 + x
def boN : Nat := 58
def eN : Nat := 59
def iN : Nat := 60
def zN : Nat := 61
-- chain B
def dBb (x : Nat) : Nat := 62 + x
def boB : Nat := 70
-- chain C
def rCb (x : Nat) : Nat := 71 + x
def coC : Nat := 79
-- chain T
def tTb (x : Nat) : Nat := 80 + x
def coT : Nat := 88
-- chain Q
def qb (x : Nat) : Nat := 89 + x
def cqb (x : Nat) : Nat := 97 + x
def dl (x : Nat) : Nat := 109 + x
-- chain D
def dQb (x : Nat) : Nat := 116 + x
def boQ : Nat := 124
-- chain S
def dSb (x : Nat) : Nat := 125 + x
def boS : Nat := 133
-- credit: aft ≠ u128::MAX
def msum : Nat := 134
def minv : Nat := 135
-- verdict
def hN : Nat := 136
def hS : Nat := 137
def h1 : Nat := 138
def h2 : Nat := 139
def h3 : Nat := 140
def okC : Nat := 141
-- interaction gates
def gW : Nat := 142
def gK : Nat := 143
def gA : Nat := 144
/-- `lf·gW`, `lf·gK` (degree-1 multiplicities) -/
def fW : Nat := 145
def fK : Nat := 146
def width : Nat := 147

/-! ## Expressions -/

def byteC (f : Nat → Nat) : Expr := bits (fun x => c (f x)) 0 8
def byteN (f : Nat → Nat) : Expr := bits (fun x => n (f x)) 0 8

def dN : Expr := byteC dNb
def dB : Expr := byteC dBb
def rC : Expr := byteC rCb
def tT : Expr := byteC tTb
def q : Expr := byteC qb
def dQ : Expr := byteC dQb
def dS : Expr := byteC dSb
def cq : Expr := bits (fun x => c (cqb x)) 0 12
def cqN : Expr := bits (fun x => n (cqb x)) 0 12
def laneE : Expr := bits (fun x => c (lb x)) 0 4
def lo8 : Expr := not (c (lb 3))
def tbE : Expr := bits (fun x => c (tb x)) 0 14
/-- `σ = 2·kind − 1` (`−1` debit, `+1` credit). -/
def sigma : Expr := sub (smul 2 (c kind)) (k 1)

/-- `10¹⁹` little endian (`Params.storageAmountPerByte`). -/
def S_LE : List Nat := [0, 0, 232, 137, 4, 35, 199, 138]

/-- `Σⱼ Sⱼ·st_{lane−j}` with `st_{lane−j} = dl (j − 1)` for `j ≥ 1` (current or next row). -/
def convC : Expr :=
  sum ((S_LE.zip (List.range 8)).map fun (s, j) => smul s (if j = 0 then c st else c (dl (j - 1))))
def convN : Expr :=
  sum ((S_LE.zip (List.range 8)).map fun (s, j) => smul s (if j = 0 then n st else n (dl (j - 1))))

/-- `act·(1 − ll)`: a non-final lane of an op (the next row is the next lane). -/
def inOp : Expr := .mul (c act) (not (c ll))
def inOpE (e : Expr) : Expr := .mul inOp e
def first (e : Expr) : Expr := .mul (c lf) e
def lastE (e : Expr) : Expr := .mul (c ll) e

/-- Op constants (equal on the 16 lanes). -/
def opConst : List Nat :=
  [op, kind, strict, okP, tov, stage, cok, valid, s1, s2, cand, wr, fa, vidA, vidK, tpA, tpK]

def boolCols : List Nat :=
  [act, lf, ll, l1, kind, strict, okP, tov, cok, valid, s1, s2, fa, boN, eN, zN, boB, coC, coT,
   boQ, boS] ++ (List.range 4).map lb ++ (List.range 14).map tb ++
  (List.range 8).map dNb ++ (List.range 8).map dBb ++ (List.range 8).map rCb ++
  (List.range 8).map tTb ++ (List.range 8).map qb ++ (List.range 12).map cqb ++
  (List.range 8).map dQb ++ (List.range 8).map dSb

/-! ## Constraints -/

def cShape : List Expr :=
  boolCols.map (fun x => bool (c x)) ++
  [ -- row structure (16-row ops, then padding)
    .mul (c lf) (not (c act)), .mul (c ll) (not (c act)), .mul (c l1) (not (c act)),
    .mul .isFirst (sub (c act) (c lf)),
    .mul .isLast (.mul (c act) (not (c ll))),
    inOpE (not (n act)), inOpE (n lf),
    mul3 (c ll) (n act) (not (n lf)),
    mul3 .isTransition (not (c act)) (n act),
    sub (c lane) laneE,
    first (c lane), inOpE (sub (n lane) (.add (c lane) (k 1))), lastE (sub (c lane) (k 15)),
    first (c l1), inOpE (sub (n l1) (c lf)),
    .mul (c act) (sub (c g) (.add (smul LANES (c op)) (c lane))) ] ++
  opConst.map (fun x => inOpE (sub (n x) (c x)))

def cFlags : List Expr :=
  [ -- stage = s1 + s2, s2 ⇒ s1; activity
    .mul (c act) (sub (c stage) (.add (c s1) (c s2))),
    .mul (c s2) (not (c s1)), .mul (c s1) (not (c act)),
    .mul (c act) (sub (c cand) (.mul (c valid) (c cok))),
    -- debit: a walk only for a candidate; credit: the signer account is present, no key
    mul3 (not (c kind)) (c s1) (not (c cand)),
    .mul (c kind) (not (c s1)), .mul (c kind) (c s2), .mul (c kind) (not (c act)),
    -- gates
    .mul (c act) (sub (c gW) (.add (c kind) (.mul (not (c kind)) (c cand)))),
    sub (c gK) (.mul (not (c kind)) (c s1)),
    sub (c gA) (.mul (c s2) lo8),
    sub (c fW) (.mul (c lf) (c gW)), sub (c fK) (.mul (c lf) (c gK)),
    .mul (c act) (sub (c wr) (.add (c kind) (mul3 (not (c kind)) (c okP) (not (c tov))))),
    -- written values
    .mul (c act) (sub (c mo) (.add (c amt) (.mul (c wr) (sub rC (c amt))))),
    .mul (c act) (sub (c nk) (.add (c kn) (.mul (c wr) (sub (c xN) (c kn))))),
    -- the key's nonce has 8 bytes
    .mul (c (lb 3)) (c kn),
    -- memory times: tp ≤ op (< T = op + 1), 14 bits
    mul3 (c lf) (c s1) (sub (sub (c op) (c tpA)) tbE),
    mul3 (c l1) (c s2) (sub (sub (c op) (c tpK)) tbE) ]

/-- `lf: r₀ = e₀`, transitions: `n r = eₙ` (`e` built from the carry of the current row). -/
def chain (atFirst atNext : Expr) : List Expr := [first atFirst, inOpE atNext]

def cChains : List Expr :=
  -- N: dN = N − kn − cin + 256·boN, cin₀ = 1
  chain (sub dN (sub (sub (c xN) (c kn)) (sub (k 1) (smul 256 (c boN)))))
        (sub (byteN dNb) (sub (sub (n xN) (n kn)) (sub (c boN) (smul 256 (n boN))))) ++
  [ .mul (c act) (.mul dN (c eN)), .mul (c act) (sub (.mul dN (c iN)) (not (c eN))),
    first (sub (c zN) (c eN)), inOpE (sub (n zN) (.mul (c zN) (n eN))) ] ++
  -- B: dB = Bd − N − cin + 256·boB, cin₀ = 1
  chain (sub dB (sub (sub (c xB) (c xN)) (sub (k 1) (smul 256 (c boB)))))
        (sub (byteN dBb) (sub (sub (n xB) (n xN)) (sub (c boB) (smul 256 (n boB))))) ++
  -- C: rC = amt + σ·(C + cin − 256·coC), cin₀ = 0
  chain (sub rC (.add (c amt) (.mul sigma (sub (c xC) (smul 256 (c coC))))))
        (sub (byteN rCb) (.add (n amt) (.mul sigma (sub (.add (n xC) (c coC)) (smul 256 (n coC)))))) ++
  -- T: tT + 256·coT = rC + lk + cin, cin₀ = 0
  chain (sub (.add tT (smul 256 (c coT))) (.add rC (c lk)))
        (sub (.add (byteN tTb) (smul 256 (n coT))) (sum [byteN rCb, n lk, c coT])) ++
  -- Q: q + 256·cq = Σ Sⱼ·st_{lane−j} + cin, cin₀ = 0; the delay line starts at 0
  chain (sub (.add q (smul 256 cq)) convC)
        (sub (.add (byteN qb) (smul 256 cqN)) (.add convN cq)) ++
  (List.range 7).map (fun x => first (c (dl x))) ++
  [ inOpE (sub (n (dl 0)) (c st)) ] ++
  (List.range 6).map (fun x => inOpE (sub (n (dl (x + 1))) (c (dl x)))) ++
  -- D: dQ = tT − q − cin + 256·boQ, cin₀ = 0
  chain (sub dQ (sub (sub tT q) (smul 256 (c boQ))))
        (sub (byteN dQb) (sub (sub (byteN tTb) (byteN qb)) (sub (c boQ) (smul 256 (n boQ))))) ++
  -- S: dS = 770_lane − st − cin + 256·boS (770 = [2, 3]), cin₀ = 0
  chain (sub dS (sub (sub (k 2) (c st)) (smul 256 (c boS))))
        (sub (byteN dSb) (sub (sub (smul 3 (n l1)) (n st)) (sub (c boS) (smul 256 (n boS))))) ++
  -- credit: Σ (255 − aft) running
  chain (sub (c msum) (sub (k 255) rC)) (sub (n msum) (.add (c msum) (sub (k 255) (byteN rCb))))

def cVerdict : List Expr :=
  [ -- nonce: (N > kn) ∧ (strict ⇒ N = kn + 1)
    lastE (sub (c hN) (.mul (not (c boN)) (.add (not (c strict)) (.mul (c strict) (c zN))))),
    -- storage stake: no overflow ∧ (tot ≥ q ∨ storage ≤ 770)
    lastE (sub (c hS) (.mul (not (c coT)) (not (.mul (c boQ) (c boS))))),
    lastE (sub (c h1) (.mul (c s2) (c fa))),
    lastE (sub (c h2) (.mul (c h1) (c hN))),
    lastE (sub (c h3) (mul3 (c h2) (not (c boB)) (not (c coC)))),
    lastE (sub (c okC) (.mul (c h3) (c hS))),
    -- debit: the public verdict is the recomputed one
    .mul (lastE (not (c kind))) (sub (c okP) (c okC)),
    -- credit: no overflow, aft ≠ u128::MAX, aft + locked < 2^128, storage stake
    lastE (.mul (c kind) (c coC)), lastE (.mul (c kind) (c coT)),
    lastE (.mul (c kind) (sub (.mul (c msum) (c minv)) (k 1))),
    lastE (mul3 (c kind) (c boQ) (c boS)) ]

def constraints : List Expr := cShape ++ cFlags ++ cChains ++ cVerdict

/-! ## Interactions -/

def wA : Expr := .add (k W_TX) (smul 2 (c op))
def wK : Expr := sum [k W_TX, smul 2 (c op), k 1]
def tE : Expr := .add (c op) (k 1)

def interactions : List Interaction :=
  [ recv B_TXP (c act)
      [c g, c kind, c strict, c okP, c tov, c stage, c cok, c xN, c xB, c xC],
    recv B_SIG (c lf) [c op, c valid],
    recv B_FINAL (c fW) [wA, k 0, not (c s1), c vidA],
    recv B_FINAL (c fK) [wK, k 0, not (c s2), c vidK],
    recv B_MEM (c s1) [c vidA, c tpA, c lane, c amt, c lk, c st],
    send B_MEM (c s1) [c vidA, tE, c lane, c mo, c lk, c st],
    recv B_AKMEM (c gA) [c vidK, c tpK, c lane, c kn, c fa],
    send B_AKMEM (c gA) [c vidK, tE, c lane, c nk, c fa] ]

/-- `16 · (NT0 + n_loc) ≤ 16 · 8192 = 2^17` rows; aligned height `19`. -/
def maxLog : Nat := 19

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.D1.TxV3
