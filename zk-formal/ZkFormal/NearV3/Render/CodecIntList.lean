import ZkFormal.NearV3.Render.CodecDefs

/-!
# The integer constraints of the codec table, as an explicit list

`cIntT`: the 231 constraints of `Sched.Codec.constraints` outside `modE`, each with its index in
`constraints`, written with the column builders evaluated (`.col 2 false` for `c kR`, …; `sub` and `MA` kept).
It is generated from `constraints` (docs/logs/v3-elab-budget-2026-10.md) and tied to it by
`int_of_cInt`, which reduces `codec_int`'s goal `∀ e ∈ constraints, e ∉ modE → zev Z e = 0` to
`AllI Z cIntT`: one conjunct `IdxP i (zev Z e = 0)` per integer constraint, so that a single `simp` can
rewrite all of them at once and the residual goals keep their index (`IdxP`).
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

/-- `P` holds on every element (structural, so that it unfolds one cons at a time). -/
def AllE (P : Expr → Prop) : List Expr → Prop
  | [] => True
  | e :: es => P e ∧ AllE P es

theorem forall_of_AllE {P : Expr → Prop} : ∀ {L : List Expr}, AllE P L → ∀ e ∈ L, P e
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, ⟨h0, _⟩, _, List.Mem.head _ => h0
  | _ :: _, ⟨_, h1⟩, e, List.Mem.tail _ h => forall_of_AllE h1 e h

theorem mem_modE {j : Nat} {e : Expr} (h : modE[j]? = some e) : e ∈ modE := List.mem_of_getElem? h

/-- Indices (in `constraints`, 239 entries) of the eight `modE` constraints, with their positions in
`modE`. -/
def cdcModE : List (Nat × Nat) := [(52, 0), (55, 1), (58, 2), (61, 3), (64, 4), (67, 5), (157, 7), (160, 6)]

/-- The integer constraints with their indices in `constraints` (generated; see the module doc). -/
def cIntT : List (Nat × Expr) := [
  (0, (.mul (.col 0 false) (sub (.col 0 false) (.const 1)))),
  (1, (.mul (.col 1 false) (sub (.col 1 false) (.const 1)))),
  (2, (.mul (.col 2 false) (sub (.col 2 false) (.const 1)))),
  (3, (.mul (.col 3 false) (sub (.col 3 false) (.const 1)))),
  (4, (.mul (.col 4 false) (sub (.col 4 false) (.const 1)))),
  (5, (.mul (.col 5 false) (sub (.col 5 false) (.const 1)))),
  (6, (.mul (.col 8 false) (sub (.col 8 false) (.const 1)))),
  (7, (.mul (.col 27 false) (sub (.col 27 false) (.const 1)))),
  (8, (.mul (.col 28 false) (sub (.col 28 false) (.const 1)))),
  (9, (.mul (.col 29 false) (sub (.col 29 false) (.const 1)))),
  (10, (.mul (.col 32 false) (sub (.col 32 false) (.const 1)))),
  (11, (.mul (.col 34 false) (sub (.col 34 false) (.const 1)))),
  (12, (.mul (.col 43 false) (sub (.col 43 false) (.const 1)))),
  (13, (.mul (.col 45 false) (sub (.col 45 false) (.const 1)))),
  (14, (.mul (.col 48 false) (sub (.col 48 false) (.const 1)))),
  (15, (.mul (.col 65 false) (sub (.col 65 false) (.const 1)))),
  (16, (.mul (.col 68 false) (sub (.col 68 false) (.const 1)))),
  (17, (.mul (.col 69 false) (sub (.col 69 false) (.const 1)))),
  (18, (.mul (.col 70 false) (sub (.col 70 false) (.const 1)))),
  (19, (.mul (.col 73 false) (sub (.col 73 false) (.const 1)))),
  (20, (.mul (.col 74 false) (sub (.col 74 false) (.const 1)))),
  (21, (.mul (.col 77 false) (sub (.col 77 false) (.const 1)))),
  (22, (.mul (.col 54 false) (sub (.col 54 false) (.const 1)))),
  (23, (.mul (.col 16 false) (sub (.col 16 false) (.const 1)))),
  (24, (.mul (.col 17 false) (sub (.col 17 false) (.const 1)))),
  (25, (.mul (.col 18 false) (sub (.col 18 false) (.const 1)))),
  (26, (.mul (.col 19 false) (sub (.col 19 false) (.const 1)))),
  (27, (.mul (.col 20 false) (sub (.col 20 false) (.const 1)))),
  (28, (.mul (.col 21 false) (sub (.col 21 false) (.const 1)))),
  (29, (.mul (.col 22 false) (sub (.col 22 false) (.const 1)))),
  (30, (.mul (.col 23 false) (sub (.col 23 false) (.const 1)))),
  (31, (.mul (.col 79 false) (sub (.col 79 false) (.const 1)))),
  (32, (.mul (.col 80 false) (sub (.col 80 false) (.const 1)))),
  (33, (.mul (.col 81 false) (sub (.col 81 false) (.const 1)))),
  (34, (.mul (.col 82 false) (sub (.col 82 false) (.const 1)))),
  (35, (.mul (.col 83 false) (sub (.col 83 false) (.const 1)))),
  (36, (.mul (.col 84 false) (sub (.col 84 false) (.const 1)))),
  (37, (.mul (.col 85 false) (sub (.col 85 false) (.const 1)))),
  (38, (.mul (.col 86 false) (sub (.col 86 false) (.const 1)))),
  (39, (.mul (.col 2 false) (.mul (.col 35 false) (sub (.col 35 false) (.const 1))))),
  (40, (.mul (.col 2 false) (.mul (.col 40 false) (sub (.col 40 false) (.const 1))))),
  (41, (.mul (.col 2 false) (.mul (.col 58 false) (sub (.col 58 false) (.const 1))))),
  (42, (.mul (.col 2 false) (.mul (.col 60 false) (sub (.col 60 false) (.const 1))))),
  (43, (.mul (.col 2 false) (.mul (.col 78 false) (sub (.col 78 false) (.const 1))))),
  (44, (.mul (.col 2 false) (.mul (.col 89 false) (sub (.col 89 false) (.const 1))))),
  (45, (.mul (.col 2 false) (.mul (.col 90 false) (sub (.col 90 false) (.const 1))))),
  (46, (sub (.col 0 false) (.add (.col 1 false) (.add (.col 2 false) (.add (.col 3 false) (.col 4 false)))))),
  (47, (sub (.col 2 false) (.add (.col 27 false) (.add (.col 28 false) (.col 29 false))))),
  (48, (.mul (.col 5 false) (sub (.const 1) (.col 1 false)))),
  (49, (.mul .isLast (.col 0 false))),
  (50, (.mul (.mul .isTransition (sub (.const 1) (.col 0 false))) (.col 0 true))),
  (51, (.mul .isFirst (.mul (.col 0 false) (sub (.const 1) (.col 5 false))))),
  (53, (.mul (.col 2 false) (.mul (sub (.col 30 false) (.const 7)) (.col 32 false)))),
  (54, (.mul (sub (.const 1) (.col 2 false)) (.col 32 false))),
  (56, (.mul (.col 29 false) (.mul (sub (.col 30 false) (.const 2)) (.col 34 false)))),
  (57, (.mul (sub (.const 1) (.col 29 false)) (.col 34 false))),
  (59, (.mul (.col 2 false) (.mul (sub (.col 24 false) (sub (.col 11 false) (.const 1))) (.col 43 false)))),
  (60, (.mul (sub (.const 1) (.col 2 false)) (.col 43 false))),
  (62, (.mul (.col 1 false) (.mul (sub (.col 7 false) (.const 4)) (.col 45 false)))),
  (63, (.mul (sub (.const 1) (.col 1 false)) (.col 45 false))),
  (65, (.mul (.add (.col 3 false) (.col 4 false)) (.mul (sub (.col 46 false) (.add (.const 31) (.mul (.const 32) (.col 4 false)))) (.col 48 false)))),
  (66, (.mul (sub (.const 1) (.add (.col 3 false) (.col 4 false))) (.col 48 false))),
  (68, (.mul (.col 0 false) (.mul (.col 6 false) (.col 65 false)))),
  (69, (.mul (sub (.const 1) (.col 0 false)) (.col 65 false))),
  (70, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 6 true) (.col 6 false)))),
  (71, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 8 true) (.col 8 false)))),
  (72, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 9 true) (.col 9 false)))),
  (73, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 10 true) (.col 10 false)))),
  (74, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 11 true) (.col 11 false)))),
  (75, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 12 true) (.col 12 false)))),
  (76, (.mul (sub (.col 0 false) (.mul (.col 4 false) (.col 48 false))) (sub (.col 13 true) (.col 13 false)))),
  (77, (.mul (.add (.col 1 false) (.add (.col 2 false) (.col 3 false))) (sub (.col 7 true) (.add (.col 7 false) (.const 1))))),
  (78, (.mul (.mul (.col 4 false) (.col 48 false)) (.mul (.col 0 true) (sub (.const 1) (.col 5 true))))),
  (79, (.mul (.add (.col 1 false) (.add (.col 2 false) (.col 3 false))) (sub (.col 15 false) (.add (.mul (.const 1) (.col 16 false)) (.add (.mul (.const 2) (.col 17 false)) (.add (.mul (.const 4) (.col 18 false)) (.add (.mul (.const 8) (.col 19 false)) (.add (.mul (.const 16) (.col 20 false)) (.add (.mul (.const 32) (.col 21 false)) (.add (.mul (.const 64) (.col 22 false)) (.add (.mul (.const 128) (.col 23 false)) (.const 0)))))))))))),
  (80, (.mul (.add (.col 1 false) (.add (.col 2 false) (.col 3 false))) (sub (.col 14 false) (.add (.mul (.const 1) (.col 79 false)) (.add (.mul (.const 2) (.col 80 false)) (.add (.mul (.const 4) (.col 81 false)) (.add (.mul (.const 8) (.col 82 false)) (.add (.mul (.const 16) (.col 83 false)) (.add (.mul (.const 32) (.col 84 false)) (.add (.mul (.const 64) (.col 85 false)) (.add (.mul (.const 128) (.col 86 false)) (.const 0)))))))))))),
  (81, (.mul (sub (.const 1) (.col 8 false)) (.col 14 false))),
  (82, (sub (.col 73 false) (.mul (.col 8 false) (.add (.col 1 false) (.add (.col 2 false) (.col 3 false)))))),
  (83, (.mul (.col 5 false) (.col 7 false))),
  (84, (.mul (.col 5 false) (.col 24 false))),
  (85, (.mul (.col 5 false) (.col 30 false))),
  (86, (.mul (.col 5 false) (.col 31 false))),
  (87, (.mul (.col 5 false) (sub (.col 11 false) (.add (.col 25 false) (.mul (.const 256) (.col 26 false)))))),
  (88, (.mul (.col 5 false) (sub (.col 11 false) (.mul (.col 10 false) (.col 10 false))))),
  (89, (.mul (.col 5 false) (sub (.col 12 false) (.add (.col 33 false) (.add (.mul (.const 256) (.col 36 false)) (.mul (.const 65536) (.col 37 false))))))),
  (90, (.mul (.col 5 false) (sub (.col 13 false) (.add (.col 39 false) (.add (.mul (.const 256) (.col 41 false)) (.mul (.const 65536) (.col 42 false))))))),
  (91, (.mul (.col 1 false) (sub (.col 15 false) (.col 24 false)))),
  (92, (.mul (.col 1 false) (sub (.col 14 false) (.mul (.col 8 false) (.col 15 false))))),
  (93, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.const 1) (.col 1 true)))),
  (94, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 24 true) (.col 25 false)))),
  (95, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 25 true) (.col 26 false)))),
  (96, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 26 true) (.col 30 false)))),
  (97, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 30 true) (.col 31 false)))),
  (98, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 31 true) (.col 33 false)))),
  (99, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 33 true) (.col 36 false)))),
  (100, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 36 true) (.col 37 false)))),
  (101, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 37 true) (.col 39 false)))),
  (102, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 39 true) (.col 41 false)))),
  (103, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 41 true) (.col 42 false)))),
  (104, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 42 true) (.col 59 false)))),
  (105, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 59 true) (.col 61 false)))),
  (106, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 61 true) (.col 62 false)))),
  (107, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 62 true) (.col 63 false)))),
  (108, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 63 true) (.col 71 false)))),
  (109, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 71 true) (.col 72 false)))),
  (110, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 72 true) (.col 66 false)))),
  (111, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 66 true) (.col 67 false)))),
  (112, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 67 true) (.col 50 false)))),
  (113, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 50 true) (.col 51 false)))),
  (114, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 51 true) (.col 52 false)))),
  (115, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 52 true) (.col 35 false)))),
  (116, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 35 true) (.col 40 false)))),
  (117, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 40 true) (.col 58 false)))),
  (118, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 58 true) (.col 60 false)))),
  (119, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 60 true) (.col 78 false)))),
  (120, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 78 true) (.col 87 false)))),
  (121, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 87 true) (.col 88 false)))),
  (122, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 88 true) (.col 89 false)))),
  (123, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 89 true) (.col 90 false)))),
  (124, (.mul (.mul (.col 1 false) (sub (.const 1) (.col 45 false))) (sub (.col 90 true) (.col 53 false)))),
  (125, (.mul (.col 45 false) (sub (.const 1) (.col 27 true)))),
  (126, (.mul (.col 45 false) (.col 24 true))),
  (127, (.mul (.col 45 false) (.col 30 true))),
  (128, (.mul (.col 45 false) (sub (.const 1) (.col 54 true)))),
  (129, (.mul (.col 2 false) (sub (.col 24 false) (.add (.col 25 false) (.mul (.const 256) (.col 26 false)))))),
  (130, (.mul (.mul (.col 2 false) (sub (.const 1) (.col 32 false))) (sub (.col 30 true) (.add (.col 30 false) (.const 1))))),
  (131, (.mul (.mul (.col 2 false) (sub (.const 1) (.col 32 false))) (sub (.col 27 true) (.col 27 false)))),
  (132, (.mul (.mul (.col 2 false) (sub (.const 1) (.col 32 false))) (sub (.col 28 true) (.col 28 false)))),
  (133, (.mul (.mul (.col 2 false) (sub (.const 1) (.col 32 false))) (sub (.col 29 true) (.col 29 false)))),
  (134, (.mul (.mul (.col 2 false) (sub (.const 1) (.col 32 false))) (sub (.col 24 true) (.col 24 false)))),
  (135, (.mul (sub (.col 32 false) (.mul (.col 70 false) (.col 43 false))) (.col 30 true))),
  (136, (.mul (.mul (.col 32 false) (.col 27 false)) (sub (.const 1) (.col 28 true)))),
  (137, (.mul (.mul (.col 32 false) (.col 27 false)) (sub (.col 24 true) (.col 24 false)))),
  (138, (.mul (.mul (.col 32 false) (.col 28 false)) (sub (.const 1) (.col 29 true)))),
  (139, (.mul (.mul (.col 32 false) (.col 28 false)) (sub (.col 24 true) (.col 24 false)))),
  (140, (sub (.col 70 false) (.mul (.col 29 false) (.col 32 false)))),
  (141, (.mul (.mul (.col 70 false) (sub (.const 1) (.col 43 false))) (sub (.const 1) (.col 27 true)))),
  (142, (.mul (.mul (.col 70 false) (sub (.const 1) (.col 43 false))) (sub (.col 24 true) (.add (.col 24 false) (.const 1))))),
  (143, (.mul (.mul (.col 70 false) (.col 43 false)) (sub (.const 1) (.col 3 true)))),
  (144, (.mul (.mul (.col 70 false) (.col 43 false)) (.col 46 true))),
  (145, (.mul (.mul (.col 70 false) (.col 43 false)) (sub (.const 1) (.col 77 true)))),
  (146, (.mul (.col 77 false) (sub (.const 1) (.col 3 false)))),
  (147, (.mul (.col 77 false) (.col 46 false))),
  (148, (.mul (.add (.col 27 false) (.col 28 false)) (sub (.col 14 false) (.mul (.col 8 false) (.col 15 false))))),
  (149, (.mul (.mul (.col 32 false) (.col 28 false)) (.col 37 true))),
  (150, (.mul (.mul (.col 32 false) (.col 28 false)) (.col 38 true))),
  (151, (.mul (.mul (.col 32 false) (.col 28 false)) (.col 41 true))),
  (152, (.mul (.mul (.col 32 false) (.col 28 false)) (sub (.col 36 true) (.const 1)))),
  (153, (.mul (.mul (.col 32 false) (.col 28 false)) (sub (.col 35 true) (.const 1)))),
  (154, (.mul (sub (.col 29 false) (.col 70 false)) (sub (.col 37 true) (.add (.col 37 false) (.mul (.mul (.col 35 false) (.col 36 false)) (.col 14 false)))))),
  (155, (.mul (sub (.col 29 false) (.col 70 false)) (sub (.col 41 true) (.add (.col 41 false) (.mul (.mul (.col 35 false) (.col 36 false)) (.col 15 false)))))),
  (156, (.mul (sub (.col 29 false) (.col 70 false)) (sub (.col 38 true) (.add (.col 38 false) (.mul (.mul (sub (.const 1) (.col 38 false)) (sub (.const 1) (.col 35 false))) (.col 40 false)))))),
  (158, (.mul (sub (.col 29 false) (.col 70 false)) (sub (.col 35 true) (.mul (.col 35 false) (sub (.const 1) (.col 34 false)))))),
  (159, (.mul (.mul (.col 29 false) (sub (.const 1) (.col 35 false))) (.col 15 false))),
  (161, (.mul (.col 29 false) (.mul (.col 14 false) (sub (.const 1) (.col 40 false))))),
  (162, (.mul (.col 54 false) (sub (.const 1) (.col 27 false)))),
  (163, (.mul (.col 54 false) (.col 30 false))),
  (164, (.mul (.mul (.col 70 false) (sub (.const 1) (.col 43 false))) (sub (.const 1) (.col 54 true)))),
  (165, (.mul (sub (.col 2 false) (.col 70 false)) (sub (.col 58 true) (.col 58 false)))),
  (166, (.mul (sub (.col 2 false) (.col 70 false)) (sub (.col 63 true) (.col 63 false)))),
  (167, (.mul (sub (.col 2 false) (.col 70 false)) (sub (.col 87 true) (.col 87 false)))),
  (168, (.mul (sub (.col 2 false) (.col 70 false)) (sub (.col 89 true) (.col 89 false)))),
  (169, (.mul (sub (.col 2 false) (.col 70 false)) (sub (.col 57 true) (.col 57 false)))),
  (170, (sub (.col 55 false) (.mul (.mul (.col 29 false) (.col 34 false)) (.col 89 false)))),
  (171, (.mul (.mul (.col 29 false) (.col 34 false)) (.mul (sub (.const 1) (.col 89 false)) (.col 88 false)))),
  (172, (.mul (.mul (.col 29 false) (.col 34 false)) (.mul (sub (.const 1) (.col 89 false)) (.col 90 false)))),
  (173, (.mul (.mul (.col 29 false) (.col 34 false)) (sub (.col 88 true) (.col 88 false)))),
  (174, (.mul (.mul (.col 29 false) (.col 34 false)) (sub (.col 90 true) (.col 90 false)))),
  (175, (.mul (sub (.col 29 false) (.col 70 false)) (.mul (sub (.const 1) (.col 35 false)) (sub (.col 88 true) (.col 88 false))))),
  (176, (.mul (sub (.col 29 false) (.col 70 false)) (.mul (sub (.const 1) (.col 35 false)) (sub (.col 90 true) (.col 90 false))))),
  (177, (sub (.col 56 false) (.mul (.col 70 false) (.col 57 false)))),
  (178, (.mul (.mul (.col 29 false) (.col 34 false)) (sub (.col 66 false) (.add (.col 88 false) (.col 13 false))))),
  (179, (.mul (.mul (.col 29 false) (.col 34 false)) (sub (.col 67 false) (.const MA)))),
  (180, (.mul (.mul (.col 29 false) (.col 34 false)) (sub (.col 68 false) (.col 60 false)))),
  (181, (.mul (sub (.col 29 false) (.col 70 false)) (.mul (sub (.const 1) (.col 35 false)) (sub (.col 60 true) (.col 60 false))))),
  (182, (.mul (.mul (.col 29 false) (.col 34 false)) (sub (.col 60 true) (.col 60 false)))),
  (183, (.mul (.col 70 false) (sub (.col 78 false) (.add (.col 38 false) (.mul (sub (.const 1) (.col 38 false)) (.col 40 false)))))),
  (184, (.mul (.col 70 false) (sub (.col 59 false) (.add (.mul (.const MA) (.col 90 false)) (.mul (sub (.const 1) (.col 90 false)) (.add (.mul (.const MA) (.col 60 false)) (.mul (sub (.const 1) (.col 60 false)) (.add (.col 88 false) (.col 13 false))))))))),
  (185, (.mul (.col 70 false) (sub (.col 71 false) (sub (.col 59 false) (.mul (.col 58 false) (.col 12 false)))))),
  (186, (.mul (.col 70 false) (sub (.col 72 false) (.mul (.col 58 false) (.col 12 false))))),
  (187, (.mul (.col 70 false) (sub (.col 41 false) (.col 61 false)))),
  (188, (sub (.col 74 false) (.mul (.col 70 false) (.col 65 false)))),
  (189, (.mul (.col 74 false) (sub (.col 66 false) (.add (.col 62 false) (.col 63 false))))),
  (190, (.mul (.col 74 false) (sub (.col 67 false) (.add (.col 50 false) (.add (.mul (.const 256) (.col 51 false)) (.mul (.const 65536) (.col 52 false))))))),
  (191, (.mul (.col 74 false) (sub (.col 68 false) (.const 1)))),
  (192, (sub (.col 69 false) (.add (.mul (.col 29 false) (.col 34 false)) (.col 74 false)))),
  (193, (.mul (.col 3 false) (sub (.col 15 false) (.col 24 false)))),
  (194, (.mul (.col 3 false) (sub (.col 49 false) (.col 14 false)))),
  (195, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.const 1) (.col 3 true)))),
  (196, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 46 true) (.add (.col 46 false) (.const 1))))),
  (197, (.mul (.mul (.col 3 false) (.col 48 false)) (sub (.const 1) (.col 4 true)))),
  (198, (.mul (.mul (.col 3 false) (.col 48 false)) (sub (.col 46 true) (.const 32)))),
  (199, (.mul (.mul (.col 4 false) (sub (.const 1) (.col 48 false))) (sub (.const 1) (.col 4 true)))),
  (200, (.mul (.mul (.col 4 false) (sub (.const 1) (.col 48 false))) (sub (.col 46 true) (.add (.col 46 false) (.const 1))))),
  (201, (.mul (.col 4 false) (sub (.col 75 false) (sub (.col 46 false) (.const 32))))),
  (202, (.mul (.col 4 false) (sub (.col 76 false) (.col 49 false)))),
  (203, (.mul (.col 4 false) (.col 50 false))),
  (204, (.mul (.col 4 false) (.col 51 false))),
  (205, (.mul (.col 4 false) (.col 52 false))),
  (206, (.mul (.col 74 false) (sub (.col 75 false) (.col 25 false)))),
  (207, (.mul (.col 74 false) (sub (.col 76 false) (.col 26 false)))),
  (208, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 24 true) (.col 25 false)))),
  (209, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 25 true) (.col 26 false)))),
  (210, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 26 true) (.col 30 false)))),
  (211, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 30 true) (.col 31 false)))),
  (212, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 31 true) (.col 33 false)))),
  (213, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 33 true) (.col 36 false)))),
  (214, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 36 true) (.col 37 false)))),
  (215, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 37 true) (.col 39 false)))),
  (216, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 39 true) (.col 41 false)))),
  (217, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 41 true) (.col 42 false)))),
  (218, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 42 true) (.col 59 false)))),
  (219, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 59 true) (.col 61 false)))),
  (220, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 61 true) (.col 62 false)))),
  (221, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 62 true) (.col 63 false)))),
  (222, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 63 true) (.col 71 false)))),
  (223, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 71 true) (.col 72 false)))),
  (224, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 72 true) (.col 66 false)))),
  (225, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 66 true) (.col 67 false)))),
  (226, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 67 true) (.col 50 false)))),
  (227, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 50 true) (.col 51 false)))),
  (228, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 51 true) (.col 52 false)))),
  (229, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 52 true) (.col 35 false)))),
  (230, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 35 true) (.col 40 false)))),
  (231, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 40 true) (.col 58 false)))),
  (232, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 58 true) (.col 60 false)))),
  (233, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 60 true) (.col 78 false)))),
  (234, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 78 true) (.col 87 false)))),
  (235, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 87 true) (.col 88 false)))),
  (236, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 88 true) (.col 89 false)))),
  (237, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 89 true) (.col 90 false)))),
  (238, (.mul (.mul (.col 3 false) (sub (.const 1) (.col 48 false))) (sub (.col 90 true) (.col 53 false))))]

/-- `p`, tagged with the index `i` of its constraint (a structure, so that tags never unify across
indices). -/
structure IdxP (i : Nat) (p : Prop) : Prop where
  out : p

theorem idx_true (i : Nat) : IdxP i True = True := propext ⟨fun _ => trivial, fun _ => ⟨trivial⟩⟩

/-- Every listed constraint vanishes over the integers, each conjunct tagged with its index. -/
def AllI (Z : ZEnv) : List (Nat × Expr) → Prop
  | [] => True
  | (i, e) :: r => IdxP i (zev Z e = 0) ∧ AllI Z r

theorem forall_of_AllI {Z : ZEnv} : ∀ {L : List (Nat × Expr)}, AllI Z L → ∀ p ∈ L, zev Z p.2 = 0
  | [], _, _, h => absurd h List.not_mem_nil
  | (_, _) :: _, ⟨h0, _⟩, _, List.Mem.head _ => h0.out
  | (_, _) :: _, ⟨_, h1⟩, p, List.Mem.tail _ h => forall_of_AllI h1 p h

set_option hygiene false in
/-- The 239 goals `e ∉ modE → zev Z e = 0` of `int_of_cInt`, in the order of `constraints`. -/
local macro "cint_goals" : tactic => do
  let mut ts : Array (Lean.TSyntax `tactic) := #[]
  let mut k := 0
  for i in [0:239] do
    match cdcModE.lookup i with
    | some j =>
      let lit := Lean.Syntax.mkNumLit (toString j)
      ts := ts.push (← `(tactic| exact fun h => absurd (mem_modE (j := $lit) rfl) h))
    | none =>
      let lit := Lean.Syntax.mkNumLit (toString k)
      ts := ts.push (← `(tactic| exact fun _ => hs _ (List.mem_of_getElem? (i := $lit) rfl)))
      k := k + 1
  `(tactic| ($ts*))

set_option maxRecDepth 8192 in
/-- `codec_int`'s goal from the tagged list. -/
theorem int_of_cInt (Z : ZEnv) (h : AllI Z cIntT) : ∀ e ∈ constraints, e ∉ modE → zev Z e = 0 := by
  have hs := forall_of_AllI h
  apply forall_of_AllE
  repeat' apply And.intro
  all_goals try exact True.intro
  cint_goals

end ZkFormal.NearV3.Render.Cdc
